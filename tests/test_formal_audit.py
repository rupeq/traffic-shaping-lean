"""Regression checks for the proof gate, including Lean's axiom-free format."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


audit = load_module("audit_formal", ROOT / ".github/scripts/audit_formal.py")
verify = load_module("verify_formal", ROOT / "verify_formal.py")


class KernelAuditTests(unittest.TestCase):
    def test_actual_lean_formats_are_both_counted(self):
        # Both lines were observed directly from the pinned Lean 4.33.1.
        output = (
            "'TrafficShaping.testBlockCount' does not depend on any axioms\n"
            "'TrafficShaping.Law.optimal_equal_prior_accuracy' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
        )
        names = [
            "TrafficShaping.testBlockCount",
            "TrafficShaping.Law.optimal_equal_prior_accuracy",
        ]
        self.assertEqual(audit.kernel_axiom_errors(output, names), ([], 2))
        self.assertEqual(len(verify.REPORT_RE.findall(output)), 2)

    def test_missing_report_is_rejected_even_if_other_is_axiom_free(self):
        output = "'TrafficShaping.a' does not depend on any axioms\n"
        errors, count = audit.kernel_axiom_errors(
            output, ["TrafficShaping.a", "TrafficShaping.b"]
        )
        self.assertEqual(count, 1)
        self.assertTrue(any("missing kernel axiom reports" in error for error in errors))

    def test_unapproved_axiom_is_rejected(self):
        output = "'TrafficShaping.a' depends on axioms: [propext, sorryAx]\n"
        errors, _ = audit.kernel_axiom_errors(output, ["TrafficShaping.a"])
        self.assertTrue(any("unexpected kernel axioms" in error for error in errors))

    def test_duplicate_and_unexpected_reports_are_rejected(self):
        line = "'TrafficShaping.a' does not depend on any axioms\n"
        errors, _ = audit.kernel_axiom_errors(
            line + line + "'TrafficShaping.b' depends on axioms: []\n",
            ["TrafficShaping.a"],
        )
        self.assertTrue(any("duplicate kernel" in error for error in errors))
        self.assertTrue(any("unexpected kernel" in error for error in errors))

    def test_comment_text_cannot_fabricate_audit_inventory(self):
        code = audit.strip_lean_noncode(
            "/- #print axioms TrafficShaping.fake -/\n"
            "#print axioms TrafficShaping.real\n"
        )
        self.assertEqual(audit.audited_declarations(code), ["TrafficShaping.real"])


if __name__ == "__main__":
    unittest.main()
