"""Checks for source selection and safe publication (no TeX installation needed)."""

import importlib.util
import json
import os
from contextlib import chdir
from pathlib import Path
import subprocess
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

    def test_tex_search_inputs_rebuild_paper_and_dependents(self):
        self.config['C']['texinputs'] = ['papers/common/sn-jnl']
        template = 'papers/common/sn-jnl/sn-jnl.cls'
        self.files[template] = b'original class'
        before = self.hashes()
        self.files[template] = b'updated class'
        after = self.hashes()
        self.assertNotEqual(before['C'], after['C'])
        self.assertNotEqual(before['S3'], after['S3'])
        self.assertEqual(before['D'], after['D'])

    def test_journal_class_search_path_is_configured(self):
        repository = Path(__file__).resolve().parents[2]
        config = json.loads((repository / pdfs.CONFIG).read_text(encoding='utf-8'))
        group = config['C']
        self.assertIn('problem131_chains_sn.tex', group['roots'])
        self.assertIn('kagey-problems/problem131/common/sn-jnl', group['texinputs'])
        self.assertIn('C', config['S3']['depends_on'])

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


class CompilationTests(unittest.TestCase):
    def test_texinputs_reach_every_pass_with_portable_paths_and_defaults(self):
        with tempfile.TemporaryDirectory(prefix='paper build ') as folder, chdir(folder):
            directory = Path(folder)
            (directory / 'main.pdf').write_bytes(b'%PDF-test')
            (directory / 'main.log').write_text('No reference warnings.')
            template = directory / 'shared template'
            group = {'directory': str(directory), 'roots': ['main.tex']}
            for separator in (':', ';'):
                for inherited in ('', 'user-tex-path'):
                    for configured in (False, True):
                        with self.subTest(separator=separator, inherited=inherited,
                                          configured=configured):
                            group['texinputs'] = ['shared template'] if configured else []
                            with patch.object(pdfs, 'WORK', directory / 'work'), \
                                 patch.object(pdfs, 'summary'), \
                                 patch.object(pdfs.os, 'pathsep', separator), \
                                 patch.dict(os.environ, {'TEXINPUTS': inherited}), \
                                 patch.object(pdfs.subprocess, 'run') as run:
                                run.return_value.returncode = 0
                                pdfs.compile_group('C', group, '123')
                            self.assertEqual(run.call_count, 3)
                            for call in run.call_args_list:
                                environment = call.kwargs['env']
                                if configured:
                                    paths = ['.', template.resolve().as_posix()]
                                    if inherited:
                                        paths.append(inherited)
                                    self.assertEqual(environment['TEXINPUTS'],
                                                     separator.join([*paths, '']))
                                else:
                                    self.assertEqual(environment['TEXINPUTS'], inherited)
                                self.assertEqual(environment['SOURCE_DATE_EPOCH'], '123')
                                self.assertEqual(call.kwargs['cwd'], directory)


class BibliographyTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='paper bibliography ')
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.group = {'directory': str(self.directory), 'roots': ['draft.v2.tex']}
        self.aux = lambda root, turn: (
            '\\citation{first}\n\\bibdata{references}\n\\bibstyle{plain}\n')
        self.commands, self.passes = [], {}
        self.bibtex_error = None
        self.produce_bbl = True

    def simulate(self, command, **kwargs):
        self.assertEqual(kwargs['cwd'], self.directory)
        self.assertEqual(kwargs['env']['SOURCE_DATE_EPOCH'], '123')
        self.assertEqual(kwargs['timeout'], 180)
        self.commands.append(command)
        if command[0] == 'pdflatex':
            root = command[-1]
            turn = self.passes[root] = self.passes.get(root, 0) + 1
            aux = self.aux(root, turn)
            if (self.directory / Path(root).with_suffix('.bbl')).exists():
                aux += '\\bibcite{first}{1}\n'
            (self.directory / Path(root).with_suffix('.aux')).write_text(aux)
            (self.directory / Path(root).with_suffix('.pdf')).write_bytes(b'%PDF-test')
            (self.directory / Path(root).with_suffix('.log')).write_text('No reference warnings.')
        else:
            self.assertEqual(command[0], 'bibtex')
            kwargs['stdout'].write('BibTeX transcript\n')
            if isinstance(self.bibtex_error, Exception):
                raise self.bibtex_error
            if self.bibtex_error:
                return subprocess.CompletedProcess(command, self.bibtex_error)
            if self.produce_bbl:
                (self.directory / (command[1] + '.bbl')).write_text('Generated bibliography')
        return subprocess.CompletedProcess(command, 0)

    def compile(self):
        with patch.object(pdfs, 'WORK', self.directory / 'work'), \
             patch.object(pdfs, 'summary'), patch('builtins.print'), \
             patch.object(pdfs.subprocess, 'run', side_effect=self.simulate):
            return pdfs.compile_group('paper', self.group, '123')

    def bibtex_commands(self):
        return [command for command in self.commands if command[0] == 'bibtex']

    def test_bibtex_runs_once_then_two_latex_passes_ignore_bibcite_changes(self):
        self.compile()
        self.assertEqual([command[0] for command in self.commands],
                         ['pdflatex', 'bibtex', 'pdflatex', 'pdflatex'])
        self.assertEqual(self.bibtex_commands(), [['bibtex', 'draft.v2']])
        transcript = self.directory / 'work/logs/paper/draft.v2-bibtex-pass1.txt'
        self.assertIn('BibTeX transcript', transcript.read_text())

    def test_manual_bibliography_does_not_run_bibtex(self):
        self.aux = lambda root, turn: '\\citation{first}\n\\bibcite{first}{1}\n'
        self.compile()
        self.assertEqual(self.bibtex_commands(), [])
        self.assertEqual(self.passes['draft.v2.tex'], 3)

    def test_existing_bibliography_is_refreshed_on_first_pass(self):
        (self.directory / 'draft.v2.bbl').write_text('Stale bibliography')
        self.compile()
        self.assertEqual(self.bibtex_commands(), [['bibtex', 'draft.v2']])
        self.assertEqual((self.directory / 'draft.v2.bbl').read_text(), 'Generated bibliography')

    def test_bibliography_input_changes_rerun_bibtex_and_delay_stabilization(self):
        for command in ('citation', 'bibdata', 'bibstyle'):
            with self.subTest(command=command):
                self.commands, self.passes = [], {}
                self.aux = lambda root, turn: (
                    '\\citation{first}\n\\bibdata{references}\n\\bibstyle{plain}\n' +
                    '\\' + command + '{' + ('before' if turn < 3 else 'after') + '}\n')
                self.compile()
                self.assertEqual(self.bibtex_commands(), [['bibtex', 'draft.v2']] * 2)
                self.assertEqual(self.passes['draft.v2.tex'], 5)
                self.assertTrue((self.directory / 'work/logs/paper/draft.v2-bibtex-pass3.txt').exists())

    def test_included_auxiliary_citation_changes_rerun_bibtex(self):
        def auxiliary(root, turn):
            (self.directory / 'section.aux').write_text(
                '\\citation{' + ('first' if turn < 3 else 'second') + '}\n' +
                '\\@input{./draft.v2.aux}\n')
            return '\\bibdata{references}\n\\bibstyle{plain}\n\\@input{section.aux}\n'
        self.aux = auxiliary
        self.compile()
        self.assertEqual(self.bibtex_commands(), [['bibtex', 'draft.v2']] * 2)
        self.assertEqual(self.passes['draft.v2.tex'], 5)

    def test_multiple_roots_have_separate_bibliographies(self):
        self.group['roots'].append('journal.tex')
        self.compile()
        self.assertEqual(self.bibtex_commands(), [['bibtex', 'draft.v2'], ['bibtex', 'journal']])
        self.assertEqual(self.passes, {'draft.v2.tex': 3, 'journal.tex': 3})

    def test_cross_document_labels_stabilize_and_are_published(self):
        self.group['reference_exports'] = [
            {'source': 'draft.v2.aux', 'output': 'main_refs.tex', 'url': 'draft.v2.pdf'}]
        self.aux = lambda root, turn: (
            r'\newlabel{x}{{' + ('1.1' if turn < 3 else '1.2') + r'}{2}{}{theorem.1}{}}' + '\n')
        outputs = self.compile()
        self.assertEqual(self.passes['draft.v2.tex'], 4)
        self.assertIn((self.directory / 'main_refs.tex').as_posix(), outputs)
        self.assertIn(r'{{1.2}{2}{}{theorem.1}{draft.v2.pdf}}',
                      (self.directory / 'main_refs.tex').read_text())

    def test_bibtex_failure_reports_transcript_and_stops(self):
        self.bibtex_error = 2
        with self.assertRaisesRegex(RuntimeError, 'BibTeX failed on pass 1; see .*bibtex-pass1'):
            self.compile()
        self.assertEqual(self.passes['draft.v2.tex'], 1)

    def test_missing_bibtex_reports_transcript_and_stops(self):
        self.bibtex_error = FileNotFoundError('bibtex unavailable')
        with self.assertRaisesRegex(RuntimeError, 'BibTeX could not start; see .*bibtex-pass1'):
            self.compile()
        transcript = self.directory / 'work/logs/paper/draft.v2-bibtex-pass1.txt'
        self.assertIn('bibtex unavailable', transcript.read_text())

    def test_bibtex_without_output_fails(self):
        self.produce_bbl = False
        with self.assertRaisesRegex(RuntimeError, 'BibTeX produced no bibliography'):
            self.compile()

    def test_bibtex_timeout_propagates_to_build_failure_handling(self):
        self.bibtex_error = subprocess.TimeoutExpired(['bibtex', 'draft.v2'], 180)
        with self.assertRaises(subprocess.TimeoutExpired):
            self.compile()

    def test_unstable_citations_exhaust_pass_limit(self):
        self.aux = lambda root, turn: '\\bibdata{references}\n\\citation{key' + str(turn) + '}\n'
        with self.assertRaisesRegex(RuntimeError, 'references did not stabilize after six passes'):
            self.compile()
        self.assertEqual(self.passes['draft.v2.tex'], 6)


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
