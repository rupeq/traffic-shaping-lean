import copy
import csv
import unittest

from computations import table_consistency_check as checker


class TableConsistencyTests(unittest.TestCase):
    @staticmethod
    def _rows(name):
        with (checker.ROOT / name).open(newline="") as stream:
            return list(csv.DictReader(stream))

    def test_table_two_rejects_duplicate_and_missing_key(self):
        legacy, _ = checker.load_certificates()
        rows = self._rows("TABLE-1.csv")

        duplicate = rows[:-1] + [dict(rows[0])]
        with self.assertRaisesRegex(AssertionError, "duplicate Table 2 row"):
            checker.validate_table_two_rows(duplicate, legacy)

        missing = rows[:-1]
        with self.assertRaisesRegex(AssertionError, "Table 2 row count"):
            checker.validate_table_two_rows(missing, legacy)

    def test_table_three_rejects_duplicate_and_missing_key(self):
        _, extra = checker.load_certificates()
        rows = self._rows("TABLE-3.csv")

        duplicate = rows[:-1] + [dict(rows[0])]
        with self.assertRaisesRegex(AssertionError, "duplicate Table 3 row"):
            checker.validate_table_three_rows(duplicate, extra)

        missing = rows[:-1]
        with self.assertRaisesRegex(AssertionError, "Table 3 row count"):
            checker.validate_table_three_rows(missing, extra)

    def test_corrupted_rational_weight_is_rejected(self):
        legacy, _ = checker.load_certificates()
        record = copy.deepcopy(legacy[0])
        trace = next(iter(record["certificate"]["schedule_weights"]))
        record["certificate"]["schedule_weights"][trace] = "0"

        with self.assertRaisesRegex(AssertionError, "policy mismatch"):
            checker.check_certificate(record, "corrupted-weight")

    def test_corrupted_certificate_value_is_rejected(self):
        legacy, _ = checker.load_certificates()
        record = copy.deepcopy(legacy[0])
        record["certificate"]["delta"] = "0"

        with self.assertRaisesRegex(AssertionError, "delta/coverage mismatch"):
            checker.check_certificate(record, "corrupted-certificate")


if __name__ == "__main__":
    unittest.main()
