"""Checks for source selection and safe publication (no TeX installation needed)."""

import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('paper_pdfs', Path(__file__).parents[1] / 'paper_pdfs.py')
pdfs = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(pdfs)


class SelectionTests(unittest.TestCase):
    def setUp(self):
        self.config = {
            'C': {'directory': 'papers/C', 'roots': ['main.tex', 'supplement.tex']},
            'S3': {'directory': 'papers/S3', 'roots': ['note.tex'], 'depends_on': ['C']},
            'D': {'directory': 'papers/D', 'roots': ['main.tex']},
        }
        self.files = dict.fromkeys([
            *pdfs.GLOBAL_INPUTS, 'papers/C/main.tex', 'papers/C/supplement.tex',
            'papers/C/sections/proof.tex', 'papers/C/main.pdf', 'papers/C/figures/plot.pdf',
            'papers/C/removed_proofs/old.tex', 'papers/S3/note.tex', 'papers/D/main.tex',
            'papers/C/check.lean', 'papers/C/main.aux'], b'original')

    def hashes(self):
        return pdfs.fingerprints(self.config, list(self.files), self.files.__getitem__)[0]

    def test_section_edit_rebuilds_paper_and_external_reference_dependents(self):
        before = self.hashes()
        self.files['papers/C/sections/proof.tex'] = b'new proof'
        after = self.hashes()
        self.assertNotEqual(before['C'], after['C'])
        self.assertNotEqual(before['S3'], after['S3'])
        self.assertEqual(before['D'], after['D'])

    def test_new_and_deleted_inputs_are_detected(self):
        before = self.hashes()
        self.files['papers/C/new_section.tex'] = b'new section'
        self.assertNotEqual(before['C'], self.hashes()['C'])
        del self.files['papers/C/new_section.tex']
        self.assertEqual(before, self.hashes())
        del self.files['papers/C/sections/proof.tex']
        self.assertNotEqual(before['C'], self.hashes()['C'])

    def test_outputs_archives_and_build_debris_do_not_trigger_builds(self):
        before = self.hashes()
        for name in ['papers/C/main.pdf', 'papers/C/main.aux', 'papers/C/check.lean',
                     'papers/C/removed_proofs/old.tex']:
            self.files[name] = b'changed'
        self.assertEqual(before, self.hashes())
        self.files['papers/C/figures/plot.pdf'] = b'new figure'
        self.assertNotEqual(before['C'], self.hashes()['C'])

    def test_external_auxiliary_files_are_built_on_a_clean_checkout(self):
        self.assertEqual(pdfs.dependency_order(self.config, ['S3']), ['C', 'S3'])

    def test_dependency_cycles_fail(self):
        self.config['C']['depends_on'] = ['S3']
        with self.assertRaises(ValueError):
            pdfs.dependency_order(self.config, ['C'])

    def test_fatal_reference_warnings(self):
        for message in ["LaTeX Warning: Reference `main-thm' on page 1 undefined on input line 9.",
                        'LaTeX Warning: There were undefined references.',
                        'LaTeX Warning: There were multiply-defined labels.',
                        'Package xr Warning: No file supplement.aux']:
            self.assertRegex(message, pdfs.BAD_REFERENCES)
        self.assertNotRegex('Overfull \\hbox (0.1pt too wide)', pdfs.BAD_REFERENCES)


class PublishingTests(unittest.TestCase):
    def test_newer_source_commit_prevents_stale_pdf_push(self):
        with tempfile.TemporaryDirectory() as folder:
            work = Path(folder)
            pdfs.write_json(work / 'plan.json', {'source_sha': 'old'})
            with patch.object(pdfs, 'WORK', work), patch.object(pdfs, 'summary'), \
                 patch.dict(os.environ, {'GITHUB_ACTIONS': 'true', 'PDF_BRANCH': 'main'}), \
                 patch.object(pdfs, 'git', side_effect=['old', '', 'new']) as git:
                pdfs.publish()
                self.assertFalse(any(call.args[0] in ('add', 'commit', 'push')
                                     for call in git.call_args_list))

    def test_failed_build_leaves_state_and_output_manifest_untouched(self):
        with tempfile.TemporaryDirectory() as folder:
            work = Path(folder)
            state = work / 'state.json'
            state.write_text('{"C": "old"}')
            pdfs.write_json(work / 'plan.json', {
                'order': ['C'], 'groups': {'C': {}}, 'epochs': {'C': '1'}, 'hashes': {'C': 'new'}})
            with patch.object(pdfs, 'WORK', work), patch.object(pdfs, 'STATE', state), \
                 patch.object(pdfs, 'summary'), \
                 patch.object(pdfs, 'compile_group', side_effect=RuntimeError('TeX failed')):
                with self.assertRaises(RuntimeError):
                    pdfs.build()
            self.assertEqual(json.loads(state.read_text()), {'C': 'old'})
            self.assertFalse((work / 'outputs.json').exists())

    def test_publish_is_not_a_local_commit_command(self):
        with patch.dict(os.environ, {'GITHUB_ACTIONS': 'false'}):
            with self.assertRaises(RuntimeError):
                pdfs.publish()


if __name__ == '__main__':
    unittest.main()
