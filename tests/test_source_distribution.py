import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'tools'))
import build_lean_project_bounded as builder
import check_source_tree as checker
from check_source_tree import allowed, inventory_errors, missing_imports
from lean_source import imports


class SourceDistributionTests(unittest.TestCase):
    def test_distribution_rejects_non_source_material(self):
        for name in ['.env', 'private/settings.json', 'SESSION_NOTES.md', 'docs/PLAN.md',
                     'output/build.log', 'TetraStereo/data.json', '../README.md']:
            with self.subTest(name=name):
                self.assertFalse(allowed(name))
        self.assertTrue(allowed('TetraStereo/OneCenter/Geometry.lean'))
        self.assertTrue(allowed('BUILDING.md'))
        self.assertTrue(allowed('source-modules.json'))

    def test_distribution_rejects_website_sources(self):
        self.assertFalse(allowed('site/index.html'))
        self.assertFalse(allowed('site/styles.css'))
        self.assertFalse(allowed('site/PLAN.md'))
        self.assertFalse(allowed('site/log.json'))

    def test_distribution_allows_only_named_readme_illustrations(self):
        self.assertTrue(allowed('assets/stereolib-banner.svg'))
        self.assertTrue(allowed('assets/two-reference-fixture.svg'))
        for name in ['assets/extra.svg', 'assets/data.json', 'assets/notes.md',
                     'assets/extra/stereolib-banner.svg']:
            with self.subTest(name=name):
                self.assertFalse(allowed(name))

    def test_inventory_matches_modules_without_including_umbrella(self):
        manifest = json.dumps({'version': 1, 'modules': ['TetraStereo.A']})
        self.assertEqual(inventory_errors(manifest, {'TetraStereo', 'TetraStereo.A'}), [])

    def test_inventory_detects_loss_of_unimported_module(self):
        sources = {'TetraStereo': 'import TetraStereo.A\n', 'TetraStereo.A': ''}
        manifest = json.dumps({
            'version': 1, 'modules': ['TetraStereo.A', 'TetraStereo.Isolated'],
        })
        self.assertEqual(missing_imports(sources), [])
        self.assertEqual(inventory_errors(manifest, set(sources)), [
            'Missing inventory module: TetraStereo.Isolated',
        ])

    def test_inventory_detects_unexpected_module(self):
        manifest = json.dumps({'version': 1, 'modules': ['TetraStereo.A']})
        self.assertEqual(inventory_errors(manifest, {'TetraStereo.A', 'TetraStereo.B'}), [
            'Unexpected source module: TetraStereo.B',
        ])

    def test_inventory_rejects_duplicate_names(self):
        manifest = json.dumps({'version': 1, 'modules': ['TetraStereo.A', 'TetraStereo.A']})
        self.assertEqual(inventory_errors(manifest, {'TetraStereo.A'}), [
            'Duplicate inventory module: TetraStereo.A',
        ])

    def test_inventory_rejects_malformed_json_and_schema(self):
        documents = [
            None, [], {}, {'modules': ['TetraStereo.A']},
            {'version': 2, 'modules': ['TetraStereo.A']},
            {'version': True, 'modules': ['TetraStereo.A']},
            {'version': 1.0, 'modules': ['TetraStereo.A']},
            {'version': 1, 'modules': ['TetraStereo.A'], 'unexpected': []},
        ]
        documents.extend({'version': 1, 'modules': modules} for modules in [
            None, 'TetraStereo.A', {}, [], [1], ['Mathlib'], ['TetraStereo'],
            ['TetraStereo/A'], ['TetraStereo..A'],
        ])
        for text in ['{broken'] + [json.dumps(document) for document in documents]:
            with self.subTest(text=text):
                errors = inventory_errors(text, {'TetraStereo.A'})
                self.assertTrue(errors)
                self.assertTrue(errors[0].startswith('Invalid source-modules.json:'))

    def test_checker_requires_tracked_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'TetraStereo.lean').write_text('', encoding='utf-8')
            (root / 'source-modules.json').write_text(
                json.dumps({'version': 1, 'modules': ['TetraStereo.A']}), encoding='utf-8',
            )
            with (
                patch.object(checker, '__file__', str(root / 'tools/check_source_tree.py')),
                patch.object(checker.subprocess, 'check_output',
                             return_value=b'100644 blob 0\tTetraStereo.lean\0'),
                patch('sys.stdout', new_callable=io.StringIO) as output,
            ):
                self.assertEqual(checker.main(), 1)
            self.assertIn('Missing tracked source-modules.json inventory', output.getvalue())

    def test_missing_local_import_is_detected(self):
        sources = {'TetraStereo.A': 'import Mathlib\nimport TetraStereo.Absent\n'}
        self.assertEqual(missing_imports(sources), [('TetraStereo.A', 'TetraStereo.Absent')])

    def test_import_parser_ignores_nested_comments(self):
        source = '/- /- import TetraStereo.Hidden -/ -/\nimport Mathlib\n' \
                 'import TetraStereo.Real\ndef s := "import TetraStereo.Fake"\n'
        self.assertEqual(imports(source), ['Mathlib', 'TetraStereo.Real'])

    def test_import_parser_does_not_scan_body_literals_or_identifiers(self):
        bodies = [
            "def quote : Char := '\"'\n",
            'def raw : String := r#""/-"#\n',
            'def «/-» : Nat := 0\n',
            'def «"» : Nat := 0\n',
        ]
        for body in bodies:
            with self.subTest(body=body):
                self.assertEqual(imports('import Mathlib\n' + body), ['Mathlib'])
                self.assertEqual(imports(body), [])

    def test_import_parser_handles_comments_between_header_tokens(self):
        source = (
            '/- leading /- nested -/ comment -/\n'
            'module/- module comment -/\nprelude\n'
            'public/- /- nested -/ comment -/meta import/- gap -/all Mathlib\n'
            '-- import TetraStereo.Hidden\n'
            'import TetraStereo.Real/- trailing /- nested -/ comment -/\n'
            'def value := 0\n'
        )
        self.assertEqual(imports(source), ['Mathlib', 'TetraStereo.Real'])

    def test_import_parser_rejects_unsupported_import_names(self):
        for name in ['TetraStereo.«Quoted»', 'TetraStereo.α', 'TetraStereo.A?']:
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, 'Unsupported Lean import identifier'):
                    imports(f'import {name}\n')

    def test_import_parser_rejects_unterminated_header_comments(self):
        with self.assertRaisesRegex(ValueError, 'Unterminated Lean comment'):
            imports('import Mathlib\n/- outer /- inner -/\n')

    def test_builder_fails_closed_on_missing_local_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'TetraStereo').mkdir()
            path = Path('TetraStereo/A.lean')
            (root / path).write_text('import TetraStereo.Absent\n')
            with self.assertRaisesRegex(ValueError, 'missing local imports'):
                builder.topological_plan(root, [path])


if __name__ == '__main__':
    unittest.main()
