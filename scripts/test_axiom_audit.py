import unittest
import hashlib
import json
import uuid
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

from audit_axioms import classify, parse_axioms, fingerprint
from audit_formal_scope import load_statuses
from generate_graph_artifacts import DeclarationTrace, result_status, load_alignment_findings

TEST_TEMP_ROOT = Path(__file__).resolve().parents[1] / ".lake"


@contextmanager
def scratch_files(*suffixes):
    # Use ordinary files: Python's private-directory ACLs are not writable by
    # the Windows restricted token used by the desktop runtime.
    prefix = f"axiom-test-{uuid.uuid4().hex}"
    paths = [TEST_TEMP_ROOT / f"{prefix}-{suffix}" for suffix in suffixes]
    try:
        yield paths
    finally:
        for path in paths:
            assert path.resolve().parent == TEST_TEMP_ROOT.resolve()
            path.unlink(missing_ok=True)


class AxiomAuditTests(unittest.TestCase):
    def test_checkout_line_endings_do_not_invalidate_identical_lean_content(self):
        with scratch_files("LF.lean", "CRLF.lean") as (lf, crlf):
            lf.write_bytes(b"theorem result : True := True.intro\n")
            crlf.write_bytes(b"theorem result : True := True.intro\r\n")
            self.assertEqual(fingerprint(lf), fingerprint(crlf))

    def test_graph_status_requires_fresh_transitive_evidence(self):
        trace = DeclarationTrace("result", "theorem", "Example", "Example.lean", 1,
                                 full_name="Example.result")
        self.assertEqual(result_status("thm:spectral-thm", [trace], {}), "unknown")
        self.assertEqual(result_status("thm:spectral-thm", [trace],
                         {"Example.result": "kernel-checked"}), "verified")
        self.assertEqual(result_status("thm:wrapper", [trace],
                         {"Example.result": "external"}), "external")
        self.assertEqual(result_status("thm:wrapper", [trace],
                         {"Example.result": "unproved"}), "unknown")

    def test_graph_finding_requires_matching_source_fingerprint(self):
        finding = {"issue": "TEST", "status": "incorrect-statement", "summary": "Test finding",
                   "statementSha256": "original-statement", "proofSha256": "original-proof"}
        record = {"id": "thm:regression-theorem", "statementSha256": finding["statementSha256"],
                  "proofSha256": finding["proofSha256"]}
        payload = json.dumps({"byLabel": {record["id"]: finding}})
        with patch.object(Path, "read_text", return_value=payload):
            self.assertEqual(load_alignment_findings({"results": [record]})[record["id"]]["status"],
                             "incorrect-statement")
            record["statementSha256"] = "changed"
            self.assertEqual(load_alignment_findings({"results": [record]})[record["id"]]["status"],
                             "needs-review")

    def test_transitive_local_axiom_is_external(self):
        parsed = parse_axioms("'wrapper' depends on axioms: [propext,\n Thesis.External.result]")
        self.assertEqual(classify(parsed["wrapper"]), "external")

    def test_missing_diagnostic_is_not_a_proof(self):
        self.assertEqual(classify(None), "unverified")
        self.assertEqual(classify(["sorryAx"]), "unproved")

    def test_standard_axioms_and_constructive_proofs(self):
        parsed = parse_axioms("'a' does not depend on any axioms\n"
                              "'b' depends on axioms: [propext, Classical.choice, Quot.sound]")
        self.assertEqual(classify(parsed["a"]), "kernel-checked")
        self.assertEqual(classify(parsed["b"]), "kernel-checked")

    def test_stale_source_invalidates_kernel_evidence(self):
        with scratch_files("Result.lean", "audit.json") as (source, audit):
            root = TEST_TEMP_ROOT
            source.write_text("theorem result : True := True.intro\n", encoding="utf-8")
            audit.write_text(json.dumps({
                "querySucceeded": True,
                "sourceHashes": {source.name: fingerprint(source)},
                "byDeclaration": {"result": {"status": "kernel-checked"}},
            }), encoding="utf-8")
            with patch("audit_formal_scope.project_lean_files", return_value=[source]):
                self.assertEqual(load_statuses(audit, root), {"result": "kernel-checked"})
                source.write_text("axiom result : True\n", encoding="utf-8")
                self.assertEqual(load_statuses(audit, root), {})

    def test_new_source_invalidates_kernel_evidence(self):
        with scratch_files("Result.lean", "Added.lean", "audit.json") as (source, added, audit):
            root = TEST_TEMP_ROOT
            source.write_text("theorem result : True := True.intro\n", encoding="utf-8")
            audit.write_text(json.dumps({
                "querySucceeded": True,
                "sourceHashes": {source.name: fingerprint(source)},
                "byDeclaration": {"result": {"status": "kernel-checked"}},
            }), encoding="utf-8")
            # A new file may introduce a conflicting declaration with an old name.
            # Even unchanged old files cannot certify the new source inventory.
            added.write_text("axiom result : True\n", encoding="utf-8")
            with patch("audit_formal_scope.project_lean_files", return_value=[source, added]):
                self.assertEqual(load_statuses(audit, root), {})

    def test_graph_color_is_not_kernel_evidence(self):
        with scratch_files("colors.json") as (audit,):
            root = TEST_TEMP_ROOT
            audit.write_text(json.dumps({"byLabel": {"thm:result": {"status": "verified"}}}),
                             encoding="utf-8")
            self.assertEqual(load_statuses(audit, root), {})


if __name__ == "__main__":
    unittest.main()
