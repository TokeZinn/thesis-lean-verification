"""Each section workflow builds exactly the Lean modules of the thesis part or chapter it is named for.

The README's badge table is only honest if the workflow behind a badge builds
the whole directory shown next to it, so this test fails as soon as a module
is added without being listed in the matching workflow.
"""
from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"
README = ROOT / "README.md"

SECTION_DIRECTORIES = {
    "lean-foundations.yml": "Thesis/Foundations",
    "lean-market-representation.yml": "Thesis/Foundations/MarketRepresentation",
    "lean-market-actions.yml": "Thesis/Foundations/MarketActions",
    "lean-market-clearing.yml": "Thesis/Foundations/MarketClearing",
    "lean-stochastic.yml": "Thesis/Foundations/Stochastic",
    "lean-day-ahead.yml": "Thesis/DayAhead",
    "lean-day-ahead-price-curves.yml": "Thesis/DayAhead/ClearingOperatorPriceCurves",
    "lean-day-ahead-fda.yml": "Thesis/DayAhead/FunctionalDataAnalysis",
    "lean-day-ahead-price-curve-analysis.yml": "Thesis/DayAhead/PriceCurveAnalysis",
    "lean-day-ahead-forecasting.yml": "Thesis/DayAhead/ForecastingImpact",
    "lean-day-ahead-applications.yml": "Thesis/DayAhead/Applications",
    "lean-intraday.yml": "Thesis/Intraday",
    "lean-intraday-lobs.yml": "Thesis/Intraday/LOBsAndTuples",
    "lean-intraday-inference.yml": "Thesis/Intraday/InferencePointProcesses",
    "lean-intraday-simulation.yml": "Thesis/Intraday/Simulation",
    "lean-intraday-applications.yml": "Thesis/Intraday/Applications",
    "lean-appendices.yml": "Thesis/Appendices",
}
GLOBAL_WORKFLOW = "lean-global.yml"
BADGE_RE = re.compile(r"actions/workflows/([A-Za-z0-9._-]+)/badge\.svg")


def build_args(path: Path) -> list[str]:
    """Tokens of the `build-args:` value, written inline or as a `>-` folded block."""
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip().startswith("build-args:"))
    inline = lines[start].split("build-args:", 1)[1].strip()
    if inline != ">-":
        return inline.split()
    indent = len(lines[start]) - len(lines[start].lstrip())
    tokens: list[str] = []
    for line in lines[start + 1:]:
        if not line.strip() or len(line) - len(line.lstrip()) <= indent:
            break
        tokens.extend(line.split())
    return tokens


def directory_modules(directory: str) -> list[str]:
    return sorted(".".join(path.relative_to(ROOT).with_suffix("").parts)
                  for path in (ROOT / directory).rglob("*.lean"))


class WorkflowTests(unittest.TestCase):
    def test_section_workflows_build_their_whole_directory(self) -> None:
        for workflow, directory in SECTION_DIRECTORIES.items():
            with self.subTest(workflow=workflow):
                args = build_args(WORKFLOWS / workflow)
                self.assertIn("--wfail", args)
                modules = [arg for arg in args if not arg.startswith("--")]
                self.assertEqual(len(modules), len(set(modules)))
                self.assertEqual(sorted(modules), directory_modules(directory))
                self.assertTrue(modules, directory)

    def test_global_workflow_builds_everything(self) -> None:
        self.assertEqual(build_args(WORKFLOWS / GLOBAL_WORKFLOW), ["--wfail", "Formalization"])

    def test_no_unexpected_workflows(self) -> None:
        present = {path.name for path in WORKFLOWS.glob("*.yml")}
        self.assertEqual(present, set(SECTION_DIRECTORIES) | {GLOBAL_WORKFLOW})

    def test_readme_badges_cover_every_workflow(self) -> None:
        badged = set(BADGE_RE.findall(README.read_text(encoding="utf-8")))
        self.assertEqual(badged, set(SECTION_DIRECTORIES) | {GLOBAL_WORKFLOW})


if __name__ == "__main__":
    unittest.main()
