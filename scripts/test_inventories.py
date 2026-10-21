from __future__ import annotations

import json
import hashlib
import unittest
from pathlib import Path

from build_thesis_fixes import _audit_fix_sources
from scrape_thesis_environments import CHAPTER_COMMAND_RE, HEADING_RE
from inventory_common import latex_plain_text
from thesis_config import AUDIT_RELATIVE, REVIEW_INPUTS, REVIEW_RELATIVE, review_inputs, stored_path_name


ROOT = Path(__file__).resolve().parents[1]
LEAN_PATH = ROOT / "bridge-data" / "lean-inventory.json"
THESIS_PATH = ROOT / "bridge-data" / "thesis-environments.json"
BRIDGE_PATH = ROOT / "bridge-data" / "bridge-inventory.json"
FIXES_PATH = ROOT / "bridge-data" / "thesis-fixes.json"
FORMAL_COVERAGE_PATH = ROOT / "bridge-data" / "current-formal-coverage.json"


class InventoryTests(unittest.TestCase):
    def test_revised_chapter_titles_retain_numbering(self) -> None:
        text = r"\chapter[Short title]{\modifiedtext{Long title}}"
        chapters = list(CHAPTER_COMMAND_RE.finditer(text))
        self.assertEqual(len(chapters), 1)
        self.assertIsNone(chapters[0].group(1))
        self.assertEqual(HEADING_RE.search(text).group(1), "chapter")
        self.assertEqual(latex_plain_text(r"\modifiedtext{Hilbert-Valued Curve\\Processes}"),
                         "Hilbert-Valued Curve Processes")

    @classmethod
    def setUpClass(cls) -> None:
        cls.lean = json.loads(LEAN_PATH.read_text(encoding="utf-8"))
        cls.thesis = json.loads(THESIS_PATH.read_text(encoding="utf-8"))
        cls.bridge = json.loads(BRIDGE_PATH.read_text(encoding="utf-8"))
        cls.fixes = json.loads(FIXES_PATH.read_text(encoding="utf-8"))
        cls.coverage = json.loads(FORMAL_COVERAGE_PATH.read_text(encoding="utf-8"))
        cls.snapshot = json.loads((review_inputs(ROOT) / "snapshot.json").read_text(encoding="utf-8"))

    def test_full_lean_inventory(self) -> None:
        self.assertGreater(self.lean["summary"]["declarationCount"], 1000)
        self.assertGreater(self.lean["summary"]["moduleCount"], 30)
        ids = [record["id"] for record in self.lean["declarations"]]
        self.assertEqual(len(ids), len(set(ids)))
        for record in self.lean["declarations"]:
            self.assertTrue(record["name"])
            self.assertTrue(record["fullName"])
            self.assertFalse(Path(record["source"]).is_absolute())

    def test_thesis_inventory_uses_master_sources(self) -> None:
        self.assertEqual(self.thesis["scope"], "sources included by master.tex")
        self.assertEqual(self.thesis["summary"]["environmentCount"], len(self.snapshot["blocks"]))
        self.assertEqual(self.thesis["summary"]["labeledEnvironmentCount"] +
                         self.thesis["summary"]["unlabeledEnvironmentCount"], len(self.snapshot["blocks"]))
        self.assertGreaterEqual(self.thesis["summary"]["environmentKinds"]["defn"], 112)
        ids = [record["id"] for record in self.thesis["environments"]]
        self.assertEqual(len(ids), len(set(ids)))
        for record in self.thesis["environments"]:
            if record["label"]:
                self.assertTrue(record["label"].startswith(f"{record['environment']}:"))

        sources = {record["source"] for record in self.thesis["sources"]}
        self.assertIn("3 - intraday/4_simulation_of_the_lob.tex", sources)
        self.assertNotIn("3 - intraday/3_inference_replacement.tex", sources)

    def test_titles_and_svg_links(self) -> None:
        disjoint = next(record for record in self.thesis["environments"]
                        if record["label"] == "defn:disjoint-union")
        self.assertTrue(disjoint["title"])
        for record in self.thesis["environments"]:
            if not record.get("svg"):
                continue
            self.assertTrue((ROOT / "graph-artifacts" / record["svg"]["path"]).is_file())

    def test_rendered_fragments_require_matching_fingerprints(self) -> None:
        manifest = json.loads((ROOT / "graph-artifacts/thesis-svg/manifest.json").read_text(
            encoding="utf-8"))
        for record in self.thesis["environments"]:
            key = record["label"] or record["id"]
            for field, content, hash_field in (
                (record.get("svg"), record["rawEnvironment"], "statementSha256"),
                ((record.get("proof") or {}).get("svg"),
                 (record.get("proof") or {}).get("rawEnvironment", ""), "proofSha256"),
            ):
                if field:
                    self.assertEqual(manifest[key][hash_field], hashlib.sha256(content.encode()).hexdigest())

    def test_svg_render_context_matches_the_compiled_thesis(self) -> None:
        connected_segments = next(record for record in self.thesis["environments"]
                                  if record["label"] == "defn:disjoint-union")
        self.assertRegex(connected_segments["renderContext"]["number"], r"^\d+\.\d+$")

    def test_svg_assets_use_browser_safe_glyph_outlines(self) -> None:
        svg_paths: set[Path] = set()
        for record in self.thesis["environments"]:
            if record.get("svg"):
                svg_paths.add(ROOT / "graph-artifacts" / record["svg"]["path"])
            proof_svg = (record.get("proof") or {}).get("svg")
            if proof_svg:
                svg_paths.add(ROOT / "graph-artifacts" / proof_svg)
        for path in svg_paths:
            svg = path.read_text(encoding="utf-8")
            self.assertNotIn("<font", svg, path.name)
            self.assertNotIn("<text", svg, path.name)
            self.assertIn("<path", svg, path.name)

    def test_exact_label_bridge_resolves(self) -> None:
        declaration_ids = {record["id"] for record in self.lean["declarations"]}
        environment_ids = {record["id"] for record in self.thesis["environments"]}
        linked = self.bridge["byLabel"]["defn:disjoint-union"]
        self.assertEqual(linked["status"], "linked")
        for link in self.bridge["links"]:
            self.assertTrue(set(link["leanDeclarationIds"]) <= declaration_ids)
            self.assertTrue(set(link["thesisEnvironmentIds"]) <= environment_ids)

    def test_outputs_have_portable_roots(self) -> None:
        self.assertEqual(self.lean["sourceRoot"], "thesis-lean-verification")
        self.assertEqual(self.thesis["sourceRoot"], stored_path_name(self.snapshot["sourceRoot"]))

    def test_published_review_inputs_match_the_dated_audit(self) -> None:
        dated = ROOT / AUDIT_RELATIVE
        if not (dated / "snapshot.json").is_file():
            self.skipTest("the dated audit directory is kept locally only")
        published = ROOT / REVIEW_RELATIVE
        for name in REVIEW_INPUTS:
            sources = (sorted(p for p in (dated / name).rglob("*") if p.is_file())
                       if (dated / name).is_dir() else [dated / name])
            self.assertTrue(sources, name)
            for source in sources:
                target = published / source.relative_to(dated)
                self.assertTrue(target.is_file(), str(target))
                self.assertEqual(target.read_bytes(), source.read_bytes(), str(target))

    def test_same_line_attributed_declarations_are_inventoried(self) -> None:
        names = {record["fullName"] for record in self.lean["declarations"]}
        self.assertIn("Thesis.DayAhead.SidedParametrisation.clampUnit_of_nonpos", names)

    def test_current_coverage_matches_source_and_does_not_hide_gaps(self) -> None:
        summary = self.coverage["summary"]
        self.assertEqual(summary["blockCount"], len(self.snapshot["blocks"]))
        self.assertEqual(summary["unmappedBlockCount"],
                         sum(not b["leanDeclarations"] for b in self.coverage["blocks"]))
        for block in self.coverage["blocks"]:
            self.assertTrue(block["clauseReview"]["fresh"], block["key"])
            if block["leanDeclarations"]:
                self.assertEqual(block["verificationStatus"], "kernel-checked", block["key"])
            if block["alignmentStatus"] == "partial":
                self.assertTrue(block["clauseReview"]["notes"].strip(), block["key"])
        self.assertNotIn("prop:market-state-hilbert-curve", {b["key"] for b in self.coverage["blocks"]})

    def test_historical_fixes_are_not_certification_of_current_source(self) -> None:
        self.assertEqual(self.fixes["summary"]["issueCount"], 0)
        self.assertEqual(self.fixes["byLabel"], {})
        findings = json.loads((review_inputs(ROOT) / "findings.json").read_text(encoding="utf-8"))
        self.assertEqual(findings["authoritativeSource"], self.snapshot["sourceRoot"])
        self.assertFalse(any(f["id"].startswith("UV") for f in findings["issues"]))
        regression = next(r for r in self.coverage["blocks"] if r["key"] == "thm:regression-theorem")
        self.assertEqual(regression["verificationStatus"], "kernel-checked")
        self.assertEqual(regression["alignmentStatus"], "aligned")
        truncation = next(r for r in self.coverage["blocks"]
                          if r["key"] == "rem:extended-metric-convention")
        self.assertEqual(truncation["alignmentStatus"], "aligned")
        void = next(row for row in self.coverage["blocks"] if row["label"] == "rem:void-modification")
        self.assertEqual(void["alignmentStatus"], "aligned")

    def test_fix_source_audit_rejects_wrong_replacement_base(self) -> None:
        with self.assertRaisesRegex(ValueError, "same-stem replacement base"):
            _audit_fix_sources(
                ["chapter_fix.tex"],
                ["chapter_replacement.tex"],
                [
                    {
                        "fixSource": "chapter_fix.tex",
                        "originalSource": "chapter.tex",
                    }
                ],
            )

    def test_fix_source_audit_rejects_non_original_fallback(self) -> None:
        with self.assertRaisesRegex(ValueError, "must use its original source"):
            _audit_fix_sources(
                ["chapter_fix.tex"],
                [],
                [
                    {
                        "fixSource": "chapter_fix.tex",
                        "originalSource": "chapter.tex",
                        "baseSource": "another.tex",
                    }
                ],
            )

    def test_fix_source_audit_rejects_missing_registered_fix(self) -> None:
        with self.assertRaisesRegex(ValueError, "registered fix sources are missing"):
            _audit_fix_sources(
                [],
                [],
                [
                    {
                        "fixSource": "chapter_fix.tex",
                        "originalSource": "chapter.tex",
                    }
                ],
            )


if __name__ == "__main__":
    unittest.main()
