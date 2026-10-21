from __future__ import annotations

import argparse
import json
import hashlib
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from build_bridge_inventory import link_inventories
from build_lean_inventory import build_inventory as build_lean_inventory, project_lean_files
from inventory_common import write_json, implementation_fingerprint
from current_alignment import load_clause_reviews
from scrape_thesis_environments import (
    DEFAULT_SVG_ROOT,
    DEFAULT_THESIS_ROOT,
    build_inventory as build_thesis_inventory,
    uncommented_latex,
)


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RESULT_STATUS = PROJECT_ROOT / "bridge-data" / "axiom-audit.json"
DEFAULT_JSON_REPORT = PROJECT_ROOT / "bridge-data" / "current-formal-coverage.json"
DEFAULT_MARKDOWN_REPORT = PROJECT_ROOT / "docs" / "audit-history" / "CURRENT_FORMAL_COVERAGE.md"

CORE_ENVIRONMENTS = {"defn", "lem", "prop", "thm", "cor"}


def load_statuses(path: Path, lean_root: Path) -> dict[str, str]:
    """Use kernel evidence only when every audited input still matches.

    Historical graph colors were assigned by source annotations and a manual
    external-label list. They are not proof evidence for the current checkout.
    """
    if not path.is_file():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not payload.get("querySucceeded") or not payload.get("sourceHashes"):
        return {}
    audited_sources = {source for source in payload["sourceHashes"] if source.endswith(".lean")}
    current_sources = {source.relative_to(lean_root).as_posix()
                       for source in project_lean_files(lean_root)}
    if audited_sources != current_sources:
        return {}
    for source, expected in payload["sourceHashes"].items():
        file = lean_root / source
        if not file.is_file() or implementation_fingerprint(file) != expected:
            return {}
    return {
        str(name): str(record.get("status", "unverified"))
        for name, record in payload.get("byDeclaration", {}).items()
    }


def environment_key(record: dict[str, Any]) -> str:
    return str(record.get("label") or record["id"])


def classify_unmatched_keys(
    keys: list[str], thesis_root: Path, active_sources: list[str]
) -> list[dict[str, Any]]:
    """Distinguish absent references from current equation/item/secondary labels.

    Presence is source traceability only, never proof or clause-alignment evidence.
    Read the selected source files, excluding commented historical copies.
    """
    locations: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for source in active_sources:
        text = uncommented_latex((thesis_root / source).read_text(encoding="utf-8"))
        for match in re.finditer(r"\\label\s*\{([^{}]+)\}", text):
            locations[match[1]].append({"source": source,
                                       "line": text.count("\n", 0, match.start()) + 1})
    return [{"key": key,
             "status": "present-outside-primary-block-keys" if key in locations else "absent",
             "locations": locations.get(key, [])}
            for key in sorted(keys)]


def build_coverage(
    lean_root: Path,
    thesis_root: Path,
    svg_root: Path,
    result_status_path: Path,
) -> dict[str, Any]:
    lean = build_lean_inventory(lean_root)
    thesis = build_thesis_inventory(thesis_root, svg_root)
    bridge = link_inventories(lean, thesis)
    statuses = load_statuses(result_status_path, lean_root)
    reviews = load_clause_reviews(lean_root, thesis.get("environments", []))
    declarations = {
        str(record["id"]): record for record in lean.get("declarations", [])
    }

    rows: list[dict[str, Any]] = []
    for record in thesis.get("environments", []):
        key = environment_key(record)
        link = bridge["byKey"].get(key, {})
        declaration_ids = list(link.get("leanDeclarationIds", []))
        linked_declarations = [declarations[identifier] for identifier in declaration_ids]
        bridge_status = str(link.get("status", "thesis-only"))
        declaration_statuses = [statuses.get(d["fullName"], "unverified")
                                for d in linked_declarations]
        verification_status = "thesis-only"
        if declaration_statuses:
            verification_status = next(
                (status for status in ("unproved", "unverified", "external")
                 if status in declaration_statuses), "kernel-checked")
        rows.append(
            {
                "id": str(record["id"]),
                "key": key,
                "label": record.get("label"),
                "environment": str(record["environment"]),
                "kind": str(record["kind"]),
                "core": str(record["environment"]) in CORE_ENVIRONMENTS,
                "title": str(record["title"]),
                "part": str(record.get("part", "")),
                "chapter": str(record.get("chapter", "")),
                "section": str(record.get("section", "")),
                "source": str(record["source"]),
                "line": int(record["line"]),
                "hasProof": bool(record.get("proof")),
                "statementSvg": (record.get("svg") or {}).get("path"),
                "proofSvg": (record.get("proof") or {}).get("svg"),
                "bridgeStatus": bridge_status,
                "verificationStatus": verification_status,
                "alignmentStatus": reviews[key]["status"],
                "clauseReview": reviews[key],
                "leanDeclarations": [
                    {
                        "fullName": item["fullName"],
                        "kind": item["kind"],
                        "source": item["source"],
                        "line": item["line"],
                    }
                    for item in linked_declarations
                ],
            }
        )

    by_kind: dict[str, dict[str, int]] = {}
    for kind in sorted({str(row["environment"]) for row in rows}):
        selected = [row for row in rows if row["environment"] == kind]
        by_kind[kind] = {
            "blocks": len(selected),
            "labeled": sum(bool(row["label"]) for row in selected),
            "proofs": sum(bool(row["hasProof"]) for row in selected),
            "linked": sum(row["bridgeStatus"] == "linked" for row in selected),
            "unmapped": sum(row["bridgeStatus"] != "linked" for row in selected),
        }

    by_source: dict[str, dict[str, int]] = {}
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["source"])].append(row)
    for source, selected in sorted(grouped.items()):
        by_source[source] = {
            "blocks": len(selected),
            "coreBlocks": sum(bool(row["core"]) for row in selected),
            "linked": sum(row["bridgeStatus"] == "linked" for row in selected),
            "unmapped": sum(row["bridgeStatus"] != "linked" for row in selected),
        }

    active_sources = [str(record["source"]) for record in thesis.get("sources", [])]
    source_key_review = classify_unmatched_keys(
        list(bridge["unmatched"]["lean"]), thesis_root, active_sources)
    verification_counts = Counter(str(row["verificationStatus"]) for row in rows)
    summary = {
        "activeSourceCount": len(active_sources),
        "blockCount": len(rows),
        "coreBlockCount": sum(bool(row["core"]) for row in rows),
        "labeledBlockCount": sum(bool(row["label"]) for row in rows),
        "unlabeledBlockCount": sum(not row["label"] for row in rows),
        "proofCount": sum(bool(row["hasProof"]) for row in rows),
        "linkedBlockCount": sum(row["bridgeStatus"] == "linked" for row in rows),
        "unmappedBlockCount": sum(row["bridgeStatus"] != "linked" for row in rows),
        "linkedCoreBlockCount": sum(
            bool(row["core"]) and row["bridgeStatus"] == "linked" for row in rows
        ),
        "unmappedCoreBlockCount": sum(
            bool(row["core"]) and row["bridgeStatus"] != "linked" for row in rows
        ),
        "distinctActiveLabels": len({str(row["label"]) for row in rows if row["label"]}),
        "leanOnlyKeyCount": len(bridge["unmatched"]["lean"]),
        "unmatchedButPresentKeyCount": sum(r["status"] != "absent" for r in source_key_review),
        "absentSourceKeyCount": sum(r["status"] == "absent" for r in source_key_review),
        "verificationStatuses": dict(sorted(verification_counts.items())),
        "alignmentStatuses": dict(sorted(Counter(row["alignmentStatus"] for row in rows).items())),
    }
    return {
        "schemaVersion": 4,
        "sourceRoot": thesis["sourceRoot"],
        "scope": "all custom theorem-style environments in sources selected by master.tex",
        "selection": {
            "master": "master.tex",
            "activeSources": active_sources,
            "part3Sources": [source for source in active_sources if source.startswith("3 - intraday/")],
        },
        "summary": summary,
        "byEnvironmentKind": by_kind,
        "bySource": by_source,
        "blocks": rows,
        "unmatchedLeanKeys": list(bridge["unmatched"]["lean"]),
        "unmatchedSourceKeyReview": source_key_review,
    }


def markdown_cell(value: object) -> str:
    return str(value or "—").replace("|", "\\|").replace("\n", " ")


def markdown_report(payload: dict[str, Any]) -> str:
    summary = payload["summary"]
    lines = [
        "# Active Thesis Formal-Coverage Audit",
        "",
        "This report is generated from the sources selected by `master.tex`. It includes every custom theorem-style block and deliberately excludes standalone equations outside those blocks.",
        "",
        "`kernel-checked` means that the linked Lean declarations compile without project-specific axioms or placeholders. Definitions and modelling records are not theorems. Kernel validity and manual clause alignment are reported separately. A checked counterexample does not prove the source claim. Clause reviews are invalidated when the source statement, proof, or recorded implementation evidence changes.",
        "",
        "Authoritative source: `" + payload['sourceRoot'] + "`. See [the dated audit](audit/doctoral-2026-10-20/README.md) for the reviewed snapshot, findings and limitations. Source links, kernel checks and mathematical clause alignment are separate evidence. This table does not certify surrounding prose or empirical results.",
        "",
        "## Summary",
        "",
        "| Measure | Count |",
        "|---|---:|",
        f"| Active source files | {summary['activeSourceCount']} |",
        f"| Custom formal blocks | {summary['blockCount']} |",
        f"| Core definition/lemma/proposition/theorem/corollary blocks | {summary['coreBlockCount']} |",
        f"| Blocks with labels | {summary['labeledBlockCount']} |",
        f"| Blocks without labels | {summary['unlabeledBlockCount']} |",
        f"| Blocks with an attached thesis proof | {summary['proofCount']} |",
        f"| Blocks linked to Lean | {summary['linkedBlockCount']} |",
        f"| Blocks not yet linked to Lean | {summary['unmappedBlockCount']} |",
        f"| Core blocks linked to Lean | {summary['linkedCoreBlockCount']} |",
        f"| Core blocks not yet linked to Lean | {summary['unmappedCoreBlockCount']} |",
        "",
        "## Current declaration evidence",
        "",
        *[f"- {status}: {count}" for status, count in summary["verificationStatuses"].items()],
        "",
        "## Current manual clause review",
        "",
        *[f"- {status}: {count}" for status, count in summary["alignmentStatuses"].items()],
        "",
        "## References outside primary formal-block keys",
        "",
        f"{summary['unmatchedButPresentKeyCount']} Lean reference keys are current equation, item, or secondary labels. They are present in the selected, uncommented thesis source but are not primary formal-block keys. Their presence is not additional proof evidence.",
        "",
        f"{summary['absentSourceKeyCount']} Lean reference keys are absent from the selected source. Exact locations for the present labels are recorded in `unmatchedSourceKeyReview` in the JSON report.",
        "",
        "## Active Part 3 selection",
        "",
    ]
    lines.extend(f"- `{source}`" for source in payload["selection"]["part3Sources"])
    lines.extend(
        [
            "",
            "## Coverage by environment kind",
            "",
            "| Environment | Blocks | Labeled | Proofs | Linked | Unmapped |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for kind, counts in payload["byEnvironmentKind"].items():
        lines.append(
            f"| {kind} | {counts['blocks']} | {counts['labeled']} | {counts['proofs']} | "
            f"{counts['linked']} | {counts['unmapped']} |"
        )
    lines.extend(
        [
            "",
            "## Block-by-block traceability",
            "",
            "| Key | Kind | Title | Thesis source | Proof | Lean status | Clause review | Lean declarations |",
            "|---|---|---|---|---:|---|---|---|",
        ]
    )
    for row in payload["blocks"]:
        declarations = ", ".join(
            f"`{item['fullName']}`" for item in row["leanDeclarations"]
        )
        lines.append(
            "| "
            + " | ".join(
                [
                    f"`{markdown_cell(row['key'])}`",
                    markdown_cell(row["kind"]),
                    markdown_cell(row["title"]),
                    f"`{markdown_cell(row['source'])}:{row['line']}`",
                    "yes" if row["hasProof"] else "no",
                    markdown_cell(row["verificationStatus"]),
                    markdown_cell(row["alignmentStatus"]),
                    declarations or "—",
                ]
            )
            + " |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit every active thesis formal block against the Lean bridge."
    )
    parser.add_argument("--lean-root", type=Path, default=PROJECT_ROOT)
    parser.add_argument("--thesis-root", type=Path, default=DEFAULT_THESIS_ROOT)
    parser.add_argument("--svg-root", type=Path, default=DEFAULT_SVG_ROOT)
    parser.add_argument("--result-status", type=Path, default=DEFAULT_RESULT_STATUS)
    parser.add_argument("--json-report", type=Path, default=DEFAULT_JSON_REPORT)
    parser.add_argument("--markdown-report", type=Path, default=DEFAULT_MARKDOWN_REPORT)
    parser.add_argument("--no-write-report", action="store_true")
    parser.add_argument(
        "--fail-on-scope-mismatch",
        action="store_true",
        help="Fail when any active core formal block lacks a Lean link.",
    )
    parser.add_argument(
        "--fail-on-unmapped-blocks",
        action="store_true",
        help="Fail when any active custom theorem-style block lacks a Lean link.",
    )
    parser.add_argument(
        "--fail-on-incomplete-alignment", action="store_true",
        help="Fail unless every block has fresh complete clause evidence and a checked Lean link.",
    )
    args = parser.parse_args()

    payload = build_coverage(
        args.lean_root.resolve(),
        args.thesis_root.resolve(),
        args.svg_root.resolve(),
        args.result_status.resolve(),
    )
    if not args.no_write_report:
        write_json(args.json_report.resolve(), payload)
        if args.json_report.resolve() == DEFAULT_JSON_REPORT.resolve():
            # Keep the original machine-readable entry point current. Its July
            # contents are preserved under bridge-data/history/2026-07/.
            write_json(PROJECT_ROOT / "bridge-data" / "formal-coverage.json", payload)
        args.markdown_report.resolve().write_text(
            markdown_report(payload), encoding="utf-8", newline="\n"
        )

    summary = payload["summary"]
    print(f"active formal blocks: {summary['blockCount']}")
    print(f"core formal blocks: {summary['coreBlockCount']}")
    print(f"linked formal blocks: {summary['linkedBlockCount']}")
    print(f"unmapped formal blocks: {summary['unmappedBlockCount']}")
    print(f"unmapped core blocks: {summary['unmappedCoreBlockCount']}")
    print(f"active Part 3 sources: {', '.join(payload['selection']['part3Sources'])}")

    if args.fail_on_scope_mismatch and summary["unmappedCoreBlockCount"]:
        raise SystemExit(1)
    if args.fail_on_unmapped_blocks and summary["unmappedBlockCount"]:
        raise SystemExit(1)
    if args.fail_on_incomplete_alignment:
        accepted = {"aligned", "model-assumptions-aligned", "source-counterexample"}
        incomplete = [b["key"] for b in payload["blocks"] if
                      b["verificationStatus"] != "kernel-checked" or
                      b["alignmentStatus"] not in accepted or not b["clauseReview"]["fresh"]]
        print(f"blocks failing complete alignment: {len(incomplete)}")
        if incomplete:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
