"""Regression checks for failure modes in the public Lean axiom audit."""
import unittest

from verify import parse_axiom_output


class AxiomAuditRegressionTests(unittest.TestCase):
    def test_valid_records_and_multiline_axioms(self):
        output = "'Demo.one' depends on axioms: [propext,\n Classical.choice]\n" + \
                 "'Demo.two' does not depend on any axioms\n"
        self.assertEqual(parse_axiom_output(output, ["Demo.one", "Demo.two"]),
                         {"Demo.one": ["Classical.choice", "propext"], "Demo.two": []})

    def test_duplicate_records_cannot_hide_dependencies(self):
        allowed = "'Demo.one' depends on axioms: [propext]\n"
        forbidden = "'Demo.one' depends on axioms: [sorryAx]\n"
        empty = "'Demo.one' does not depend on any axioms\n"
        for output in [allowed + allowed, forbidden + allowed,
                       empty + empty, forbidden + empty, empty + forbidden]:
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, "Duplicate"):
                parse_axiom_output(output, ["Demo.one"])

    def test_missing_extra_and_forbidden_records(self):
        cases = [
            ("", "coverage"),
            ("'Demo.one' depends on axioms: []\n'Demo.extra' depends on axioms: []", "coverage"),
            ("'Demo.one' depends on axioms: [sorryAx]", "Unapproved"),
            ("'Demo.one' depends on axioms: [Demo.customAxiom]", "Unapproved"),
        ]
        for output, message in cases:
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, message):
                parse_axiom_output(output, ["Demo.one"])


if __name__ == "__main__":
    unittest.main()
