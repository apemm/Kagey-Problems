import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('latex_references', Path(__file__).parents[1] / 'latex_references.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ReferenceExports(unittest.TestCase):
    def test_abstract_stops_before_generated_labels(self):
        preamble = (r'{A {nested} abstract with \{escaped braces\}.}' + '\n' +
                    r'\newlabel{thm:x}{{1.2}{3}{Title}{theorem.1.2}{main.pdf}}')
        self.assertEqual(module.groups(preamble)[0],
                         r'A {nested} abstract with \{escaped braces\}.')

    def test_nested_title_and_external_destination(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)
            (path/'main.aux').write_text(r'\newlabel{thm:x}{{1.2}{3}{A {nested} title}{theorem.1.2}{}}'+'\n')
            config = [{'source':'main.aux', 'output':'main_refs.tex', 'url':'main.pdf'}]
            self.assertTrue(module.export_references(path, config))
            self.assertIn(r'{{1.2}{3}{A {nested} title}{theorem.1.2}{main.pdf}}', (path/'main_refs.tex').read_text())
            self.assertFalse(module.export_references(path, config))

    def test_plain_label_and_missing_first_pass(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)
            config = [{'source':'supp.aux', 'output':'refs.tex', 'url':'supp.pdf'}]
            self.assertFalse(module.export_references(path, config))
            (path/'supp.aux').write_text(r'\newlabel{x}{{S1}{2}}'+'\n')
            self.assertTrue(module.export_references(path, config))
            self.assertIn(r'{{S1}{2}{}{}{supp.pdf}}', (path/'refs.tex').read_text())


if __name__ == '__main__':
    unittest.main()
