"""Fail-closed tests for article coverage and root-module reachability."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "article_audit", ROOT / ".github/scripts/audit_formal.py"
)
assert SPEC is not None and SPEC.loader is not None
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


class ArticleCoverageTests(unittest.TestCase):
    def check_manifest(self, items):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "coverage.json"
            path.write_text(json.dumps({"schema_version": 1, "items": items}))
            return audit.article_inventory(path)

    def full_inventory(self):
        return [
            {"id": key, "declarations": ["TrafficShaping.checked"]}
            for key in sorted(audit.REQUIRED_ARTICLE_ITEMS)
        ]

    def test_full_inventory_is_accepted(self):
        self.assertEqual(
            self.check_manifest(self.full_inventory()),
            ({"TrafficShaping.checked"}, []),
        )

    def test_dropping_formula_is_rejected(self):
        items = [item for item in self.full_inventory() if item["id"] != "equation-19"]
        _, errors = self.check_manifest(items)
        self.assertIn("required article item missing: equation-19", errors)

    def test_duplicate_does_not_replace_a_missing_item(self):
        items = self.full_inventory()
        missing = items.pop()
        items.append(items[0].copy())
        _, errors = self.check_manifest(items)
        self.assertIn(f"required article item missing: {missing['id']}", errors)
        self.assertTrue(any("duplicate article item" in error for error in errors))

    def test_empty_or_invalid_declaration_is_rejected(self):
        items = self.full_inventory()
        items[0]["declarations"] = []
        items[1]["declarations"] = ["Mathlib.unrelated"]
        _, errors = self.check_manifest(items)
        self.assertTrue(any("has no Lean declarations" in error for error in errors))
        self.assertTrue(any("invalid article declaration" in error for error in errors))

    def test_root_rejects_orphan_and_missing_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tree = root / "TrafficShaping"
            tree.mkdir()
            (root / "TrafficShaping.lean").write_text(
                "import TrafficShaping.Proved\nimport TrafficShaping.Missing\n"
            )
            (tree / "Proved.lean").write_text("import Mathlib\n")
            (tree / "Orphan.lean").write_text("/- import TrafficShaping.Orphan -/\n")
            errors = audit.root_import_errors(root)
            self.assertIn("missing local Lean import: TrafficShaping.Missing", errors)
            self.assertIn(
                "Lean module is not reachable from the root import: TrafficShaping.Orphan",
                errors,
            )

    def test_transitive_import_is_sufficient(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tree = root / "TrafficShaping"
            tree.mkdir()
            (root / "TrafficShaping.lean").write_text("import TrafficShaping.A\n")
            (tree / "A.lean").write_text("import TrafficShaping.B\n")
            (tree / "B.lean").write_text("import Mathlib\n")
            self.assertEqual(audit.root_import_errors(root), [])

    def test_top_level_mock_cannot_escape_source_scan(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "TrafficShaping").mkdir()
            (root / "TrafficShaping.lean").write_text("import Mathlib\n")
            (root / "Mock.lean").write_text("axiom fake : False\n")
            self.assertIn(
                "unexpected top-level formal source: Mock.lean",
                audit.root_import_errors(root),
            )
            self.assertTrue(any(
                "forbidden source token 'axiom'" in error
                for error in audit.source_placeholder_errors(audit.source_files(root))
            ))


if __name__ == "__main__":
    unittest.main()
