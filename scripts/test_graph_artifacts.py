"""Current-source graph integrity, without asserting that partial proofs are complete.

Source-specific tests for the previous338-block thesis are preserved under the
dated audit's before/ directory. Mathematical completion has a separate strict
gate in audit_formal_scope.py.
"""
from __future__ import annotations

import json
from pathlib import Path
import unittest

from thesis_config import review_inputs, stored_path_name

ROOT = Path(__file__).resolve().parents[1]


class GraphArtifactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = json.loads((ROOT / "graph-artifacts/lean-bridge-data.json").read_text(encoding="utf-8"))
        cls.metadata = json.loads((ROOT / "bridge-data/thesis-results.json").read_text(encoding="utf-8"))
        cls.coverage = json.loads((ROOT / "bridge-data/current-formal-coverage.json").read_text(encoding="utf-8"))
        cls.findings = json.loads((review_inputs(ROOT) / "findings.json").read_text(encoding="utf-8"))
        cls.snapshot = json.loads((review_inputs(ROOT) / "snapshot.json").read_text(encoding="utf-8"))
        cls.nodes = {r["id"]: r for r in cls.graph["nodes"]}
        cls.formal = {r["id"] for r in cls.metadata["results"]}

    def test_exact_current_master_scope(self):
        self.assertEqual(self.graph["schemaVersion"], 3)
        self.assertEqual(self.metadata["summary"]["environmentCount"], len(self.snapshot["blocks"]))
        self.assertEqual({n["id"] for n in self.graph["nodes"] if n.get("thesisRefs")}, self.formal)
        self.assertEqual({n["id"] for n in self.graph["nodes"] if not n.get("graphHidden")}, self.formal)
        self.assertEqual(self.metadata["sourceRoot"], stored_path_name(self.snapshot["sourceRoot"]))
        self.assertNotIn("prin:finitism", self.formal)
        self.assertIn("defn:state-dependent-selection-probabilities", self.formal)

    def test_edges_and_proof_moves_resolve(self):
        for edge in self.graph["edges"]:
            self.assertIn(edge["source"], self.nodes)
            self.assertIn(edge["target"], self.nodes)
        for node in self.graph["nodes"]:
            for move in node.get("bridge", {}).get("proofMoves", []):
                for match in move.get("leanMatches", []):
                    self.assertIn(match["nodeId"], self.nodes)
                    self.assertIn(match["declaration"],
                                  {r["declaration"] for r in self.nodes[match["nodeId"]].get("lean", [])})

    def test_graph_cannot_promote_partial_or_stale_evidence(self):
        for block in self.coverage["blocks"]:
            node = self.nodes[block["key"]]
            if block["alignmentStatus"] == "partial":
                self.assertEqual(node["status"], "needs-alignment", block["key"])
            if not block["clauseReview"]["fresh"]:
                self.assertNotEqual(node["status"], "verified", block["key"])
            if node["status"] == "verified":
                self.assertEqual(block["verificationStatus"], "kernel-checked", block["key"])
                self.assertIn(block["alignmentStatus"], {"aligned", "model-assumptions-aligned"})

    def test_counterexample_never_certifies_false_source(self):
        for key in self.findings["byLabel"]:
            self.assertEqual(self.nodes[key]["status"], "incorrect-statement", key)
            self.assertTrue(self.nodes[key]["thesisIssue"], key)

    def test_full_thesis_findings_and_concurrent_resolutions_are_current(self):
        audit = self.graph["audit"]
        self.assertTrue(audit["findingsSourceMatches"])
        self.assertEqual({f["id"] for f in audit["findings"]}, {f["id"] for f in self.findings["issues"]})
        self.assertEqual({f["id"] for f in audit["resolvedFindings"]},
                         {f["id"] for f in self.findings["resolvedIssues"]})
        self.assertFalse(any(f["id"].startswith("UV") for f in audit["findings"]))
        if any(b["alignmentStatus"] == "partial" for b in self.coverage["blocks"]):
            self.assertNotEqual(audit["status"], "formal-review-complete")

    def test_every_visible_node_has_readable_text(self):
        for key in self.formal:
            node = self.nodes[key]
            self.assertTrue(node["title"].strip(), key)
            self.assertTrue(str(node["bridge"]["explanation"]).strip(), key)
            self.assertTrue(str(node["bridge"]["strategy"]).strip(), key)

    def test_rendered_fragments_require_exact_source_hashes(self):
        manifest = json.loads((ROOT / "graph-artifacts/thesis-svg/manifest.json").read_text(encoding="utf-8"))
        for record in self.metadata["results"]:
            for field, digest in (
                (record.get("svg"), "statementSha256"),
                (record.get("proofSvg"), "proofSha256"),
            ):
                if field:
                    self.assertEqual(manifest[record["id"]][digest], record[digest])

    def test_retired_simulator_modules_are_not_active(self):
        retired = json.loads((review_inputs(ROOT) / "archived-intraday.json").read_text(encoding="utf-8"))
        for name in retired:
            self.assertFalse(list((ROOT / "Thesis" / "Intraday").rglob(name)), name)
            self.assertTrue((review_inputs(ROOT) / "legacy-intraday" / (name + ".txt")).exists(), name)
        for name in ("GridAverages.lean", "GridDecoder.lean", "GridPipeline.lean"):
            self.assertFalse(list((ROOT / "Thesis" / "DayAhead").rglob(name)), name)


if __name__ == "__main__":
    unittest.main()
