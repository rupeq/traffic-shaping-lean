"""Reject incomplete and stale evidence in the combined article gate."""
from __future__ import annotations

import unittest

import verify_article as gate


class ArticleGateTests(unittest.TestCase):
    def test_changed_transcribed_certificate_weight_is_rejected(self):
        errors = []
        gate.validate_lean_transcription(
            "def weights := [(scheduleA, 3), (scheduleB, 2)]",
            "def weights := [(scheduleA, 2), (scheduleB, 3)]", errors,
        )
        self.assertTrue(any("transcription differs" in error for error in errors))

    def test_transcription_allows_comment_and_whitespace_changes(self):
        errors = []
        gate.validate_lean_transcription(
            "-- generated certificate\ndef weight := 3",
            "def   weight := 3 /- verified in Lean -/", errors,
        )
        self.assertEqual(errors, [])

    def test_top_level_pass_cannot_replace_five_corollary_results(self):
        errors = []
        gate.validate_corollaries({"status": "PASS", "corollaries": {}}, errors)
        self.assertTrue(any("five required corollaries" in error for error in errors))
        self.assertTrue(any("parameter_sets" in error for error in errors))

    def test_all_table_rows_cannot_be_replaced_by_a_single_status(self):
        errors = []
        gate.validate_tables({"status": "PASS"}, errors)
        self.assertTrue(any("table_2.rows" in error for error in errors))
        self.assertTrue(any("table_3.rows" in error for error in errors))
        self.assertTrue(any("certificates" in error for error in errors))

    def test_stale_source_digest_is_rejected(self):
        errors = []
        gate.validate_code_hashes(
            {"code_sha256": "0" * 64, "saved_input_sha256": {}},
            "corollaries_check.py", errors,
        )
        self.assertTrue(any("code_sha256" in error for error in errors))
        self.assertTrue(any("missing saved-input" in error for error in errors))

    def test_input_hashes_cannot_name_files_outside_computations(self):
        errors = []
        script = "corollaries_check.py"
        gate.validate_code_hashes(
            {"code_sha256": gate.digest(gate.ROOT / "computations" / script),
             "saved_input_sha256": {"../verify_article.py": "0" * 64}},
            script, errors,
        )
        self.assertTrue(any("invalid input path" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
