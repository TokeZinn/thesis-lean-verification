from __future__ import annotations

import argparse
import copy
import hashlib
import json
from collections import defaultdict
from pathlib import Path

from build_lean_inventory import build_inventory as build_lean_inventory
from inventory_common import write_json
from scrape_thesis_environments import (
    DEFAULT_SVG_ROOT,
    attach_existing_svgs,
    build_inventory as build_thesis_inventory,
    rebuild_all_svgs,
    scrape_source,
)


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_THESIS_ROOT = PROJECT_ROOT.parent / "VibePhDThesis"
DEFAULT_REGISTRY = PROJECT_ROOT / "bridge-data" / "thesis-fix-registry.json"
DEFAULT_OUTPUT = PROJECT_ROOT / "bridge-data" / "thesis-fixes.json"
DEFAULT_FIX_SVG_ROOT = PROJECT_ROOT / "graph-artifacts" / "thesis-fix-svg"


def _formal_remainder(
    text: str,
    regions: list[tuple[str, dict[str, object]]],
) -> str:
    """Replace the authorised formal regions, leaving every other byte visible."""
    for marker, record in regions:
        label = str(record["label"])
        statement = str(record["rawEnvironment"])
        proof = str((record.get("proof") or {}).get("rawEnvironment", ""))
        if statement not in text:
            raise ValueError(f"could not locate {label} statement while checking formal-only edits")
        text = text.replace(statement, f"<FORMAL-STATEMENT:{marker}>", 1)
        if proof:
            if proof not in text:
                raise ValueError(f"could not locate {label} proof while checking formal-only edits")
            text = text.replace(proof, f"<FORMAL-PROOF:{marker}>", 1)
    return text


def _relative_tex_sources(thesis_root: Path, pattern: str) -> list[str]:
    return sorted(
        path.relative_to(thesis_root).as_posix()
        for path in thesis_root.rglob(pattern)
        if path.is_file()
    )


def _replacement_for_fix(fix_source: str) -> str:
    path = Path(fix_source)
    if not path.name.endswith("_fix.tex"):
        raise ValueError(f"registered fix source does not end in _fix.tex: {fix_source}")
    return (path.parent / path.name.removesuffix("_fix.tex")).as_posix() + "_replacement.tex"


def _audit_fix_sources(
    fix_sources: list[str],
    replacement_sources: list[str],
    issues: list[dict[str, object]],
) -> dict[str, object]:
    discovered_fix_sources = set(fix_sources)
    replacement_source_set = set(replacement_sources)
    issues_by_fix: dict[str, list[dict[str, object]]] = defaultdict(list)
    for issue in issues:
        fix_source = str(issue["fixSource"])
        _replacement_for_fix(fix_source)
        issues_by_fix[fix_source].append(issue)

    registered_fix_sources = set(issues_by_fix)
    unregistered_fix_sources = sorted(discovered_fix_sources - registered_fix_sources)
    missing_fix_sources = sorted(registered_fix_sources - discovered_fix_sources)
    if unregistered_fix_sources:
        raise ValueError(
            "unregistered full-file fixes: " + ", ".join(unregistered_fix_sources)
        )
    if missing_fix_sources:
        raise ValueError(
            "registered fix sources are missing or do not end in _fix.tex: "
            + ", ".join(missing_fix_sources)
        )

    paired_sources: list[dict[str, str]] = []
    for fix_source in fix_sources:
        replacement_source = _replacement_for_fix(fix_source)
        if replacement_source not in replacement_source_set:
            continue
        paired_sources.append(
            {
                "fixSource": fix_source,
                "replacementSource": replacement_source,
            }
        )
        for issue in issues_by_fix[fix_source]:
            base_source = str(issue.get("baseSource", issue["originalSource"]))
            if base_source != replacement_source:
                raise ValueError(
                    f"{fix_source} must use its same-stem replacement base "
                    f"{replacement_source}, not {base_source}"
                )

    paired_fix_sources = {pair["fixSource"] for pair in paired_sources}
    paired_replacement_sources = {pair["replacementSource"] for pair in paired_sources}
    unmatched_fix_sources = sorted(discovered_fix_sources - paired_fix_sources)
    for fix_source in unmatched_fix_sources:
        for issue in issues_by_fix[fix_source]:
            original_source = str(issue["originalSource"])
            base_source = str(issue.get("baseSource", original_source))
            if base_source != original_source:
                raise ValueError(
                    f"{fix_source} has no same-stem replacement and must use its "
                    f"original source {original_source}, not {base_source}"
                )

    return {
        "fixSources": fix_sources,
        "replacementSources": replacement_sources,
        "sameStemPairs": paired_sources,
        "unmatchedFixSources": unmatched_fix_sources,
        "unmatchedReplacementSources": sorted(
            replacement_source_set - paired_replacement_sources
        ),
        "allFixSourcesRegistered": True,
        "sameStemPairsUseReplacementBase": True,
        "unmatchedFixesUseOriginalBase": True,
    }


def build_payload(
    thesis_root: Path,
    registry_path: Path = DEFAULT_REGISTRY,
    fix_svg_root: Path = DEFAULT_FIX_SVG_ROOT,
    rebuild_svg: bool = False,
) -> dict[str, object]:
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    issues = list(registry.get("issues", []))
    retired = list(registry.get("retiredIssues", []))
    if not issues and not retired:
        raise ValueError(f"no thesis issues registered in {registry_path}")

    discovered_fixes = _relative_tex_sources(thesis_root, "*_fix.tex")
    discovered_replacements = _relative_tex_sources(thesis_root, "*_replacement.tex")
    registered_fixes = {str(issue["fixSource"]) for issue in issues}
    registered_replacements = {_replacement_for_fix(source) for source in registered_fixes}
    registered_replacements.update(registry.get("archivedReplacementSources", []))
    fix_sources = sorted(set(discovered_fixes) & registered_fixes)
    replacement_sources = sorted(set(discovered_replacements) & registered_replacements)
    source_audit = _audit_fix_sources(fix_sources, replacement_sources, issues)
    source_audit["scope"] = "registered formal correction copies; other copies are listed without verification"
    source_audit["unregisteredFixSources"] = sorted(set(discovered_fixes) - registered_fixes)
    source_audit["unregisteredReplacementSources"] = sorted(
        set(discovered_replacements) - registered_replacements)
    source_audit["retiredCorrectionSources"] = [
        {"source": source, "exists": (thesis_root / source).is_file()}
        for source in sorted({str(issue["fixSource"]) for issue in retired})
    ]

    thesis = build_thesis_inventory(thesis_root, DEFAULT_SVG_ROOT)
    original_by_label = {
        str(record["label"]): record
        for record in thesis["environments"]
        if record.get("label")
    }
    source_by_name = {str(record["source"]): record for record in thesis["sources"]}
    active_source_names = set(source_by_name)
    for issue in retired:
        label = str(issue["currentLabel"])
        record = original_by_label.get(label)
        if record is None or record["source"] != issue["originalSource"]:
            raise ValueError(f"retired correction {issue['id']} has no current source: {label}")
        for key, content in (
            ("currentStatementSha256", record["rawEnvironment"]),
            ("currentProofSha256", (record.get("proof") or {}).get("rawEnvironment", "")),
        ):
            if hashlib.sha256(content.encode("utf-8")).hexdigest() != issue[key]:
                raise ValueError(f"retired correction {issue['id']} needs source review ({key})")
    archived_replacements = set(registry.get("archivedReplacementSources", []))
    if archived_replacements & active_source_names:
        raise ValueError("an archived replacement is selected by master.tex; review its classification")
    unmatched_replacement_sources = list(source_audit["unmatchedReplacementSources"])
    unclassified_replacement_sources = sorted(
        set(unmatched_replacement_sources) - active_source_names - archived_replacements
    )
    if unclassified_replacement_sources:
        raise ValueError(
            "replacement sources have neither a same-stem fix nor an active master.tex "
            "selection: " + ", ".join(unclassified_replacement_sources)
        )
    formal_block_count_by_source: dict[str, int] = defaultdict(int)
    for record in thesis["environments"]:
        formal_block_count_by_source[str(record["source"])] += 1
    source_audit["unmatchedReplacementDetails"] = [
        {
            "replacementSource": source,
            "classification": ("archived-replacement" if source in archived_replacements
                               else "active-master-source-without-fix"),
            "formalBlockCount": formal_block_count_by_source[source],
        }
        for source in unmatched_replacement_sources
    ]
    source_audit["allUnmatchedReplacementsClassified"] = True
    lean = build_lean_inventory(PROJECT_ROOT)
    lean_by_name = {str(record["fullName"]): record for record in lean["declarations"]}

    grouped: dict[tuple[str, str, str], list[dict[str, object]]] = defaultdict(list)
    for issue in issues:
        original_source = str(issue["originalSource"])
        base_source = str(issue.get("baseSource", original_source))
        grouped[(original_source, base_source, str(issue["fixSource"]))].append(issue)

    fixed_by_label: dict[str, dict[str, object]] = {}
    base_by_issue_id: dict[str, dict[str, object]] = {}
    formal_only_by_pair: dict[tuple[str, str, str], bool] = {}
    for (original_source, base_source, fix_source), source_issues in grouped.items():
        if original_source not in source_by_name:
            raise ValueError(f"registered original is not active in master.tex: {original_source}")
        source_record = copy.deepcopy(source_by_name[original_source])
        base_record = copy.deepcopy(source_record)
        base_record["source"] = base_source
        if not (thesis_root / base_source).is_file():
            raise FileNotFoundError(thesis_root / base_source)
        base_records = scrape_source(thesis_root, base_record)
        base_source_by_label = {
            str(record["label"]): record for record in base_records if record.get("label")
        }

        source_record["source"] = fix_source
        if not (thesis_root / fix_source).is_file():
            raise FileNotFoundError(thesis_root / fix_source)
        fixed_records = scrape_source(thesis_root, source_record)
        fixed_source_by_label = {
            str(record["label"]): record for record in fixed_records if record.get("label")
        }
        for issue in source_issues:
            label = str(issue["label"])
            base_label = str(issue.get("baseLabel", label))
            fix_label = str(issue.get("fixLabel", label))
            if label not in original_by_label:
                raise ValueError(f"registered label is not active in master.tex: {label}")
            if str(original_by_label[label]["source"]) != original_source:
                raise ValueError(f"{label} is not in registered source {original_source}")
            if base_label not in base_source_by_label:
                raise ValueError(f"{base_label} is missing from copy base {base_source}")
            if fix_label not in fixed_source_by_label:
                raise ValueError(f"{fix_label} is missing from fix copy {fix_source}")
            base = base_source_by_label[base_label]
            fixed = fixed_source_by_label[fix_label]
            fixed["renderContext"] = copy.deepcopy(
                base.get("renderContext") or original_by_label[label].get("renderContext")
            )
            base_by_issue_id[str(issue["id"])] = base
            fixed_by_label[label] = fixed

        base_text = (thesis_root / base_source).read_text(encoding="utf-8-sig")
        fixed_text = (thesis_root / fix_source).read_text(encoding="utf-8-sig")
        base_regions = [
            (
                str(issue["id"]),
                base_source_by_label[str(issue.get("baseLabel", issue["label"]))],
            )
            for issue in source_issues
        ]
        fix_regions = [
            (
                str(issue["id"]),
                fixed_source_by_label[str(issue.get("fixLabel", issue["label"]))],
            )
            for issue in source_issues
        ]
        pair = (original_source, base_source, fix_source)
        formal_only_by_pair[pair] = (
            _formal_remainder(base_text, base_regions)
            == _formal_remainder(fixed_text, fix_regions)
        )
        if not formal_only_by_pair[pair]:
            raise ValueError(
                f"{fix_source} differs from {base_source} outside the registered formal results"
            )

    fixed_records_ordered = [
        fixed_by_label[str(record["label"])]
        for record in thesis["environments"]
        if record.get("label") and str(record["label"]) in fixed_by_label
    ]
    if rebuild_svg:
        rebuild_all_svgs(thesis_root, fix_svg_root, fixed_records_ordered)
    attach_existing_svgs(fixed_records_ordered, fix_svg_root)

    output_issues: list[dict[str, object]] = []
    for issue in issues:
        label = str(issue["label"])
        linked_labels = {
            label,
            str(issue.get("baseLabel", label)),
            str(issue.get("fixLabel", label)),
        }
        original = original_by_label[label]
        base = base_by_issue_id[str(issue["id"])]
        fixed = fixed_by_label[label]
        declarations = []
        for full_name in issue.get("leanDeclarations", []):
            declaration = lean_by_name.get(str(full_name))
            if declaration is None:
                raise ValueError(f"registered Lean declaration does not exist: {full_name}")
            declarations.append(
                {
                    "fullName": declaration["fullName"],
                    "kind": declaration["kind"],
                    "module": declaration["module"],
                    "source": declaration["source"],
                    "line": declaration["line"],
                    "linkedToLabel": bool(
                        linked_labels.intersection(declaration.get("thesisLabels", []))
                    ),
                }
            )
        if not any(item["linkedToLabel"] for item in declarations):
            raise ValueError(f"no registered Lean correction is linked to {label}")
        original_source = str(issue["originalSource"])
        pair = (
            original_source,
            str(issue.get("baseSource", original_source)),
            str(issue["fixSource"]),
        )
        output_issues.append(
            {
                **issue,
                "leanVerified": True,
                "formalOnlyDiffVerified": formal_only_by_pair[pair],
                "leanDeclarations": declarations,
                "original": {
                    "label": original.get("label"),
                    "source": original["source"],
                    "line": original["line"],
                    "statement": original["statement"],
                    "proof": original.get("proof"),
                    "svg": (original.get("svg") or {}).get("path"),
                },
                "base": {
                    "label": base.get("label"),
                    "source": base["source"],
                    "line": base["line"],
                    "statement": base["statement"],
                    "proof": base.get("proof"),
                },
                "fix": {
                    "label": fixed.get("label"),
                    "source": fixed["source"],
                    "line": fixed["line"],
                    "statement": fixed["statement"],
                    "proof": fixed.get("proof"),
                    "svg": (fixed.get("svg") or {}).get("path"),
                },
            }
        )

    return {
        "schemaVersion": 2,
        "scope": "active correction copies and source-fingerprinted integration history",
        "summary": {
            "issueCount": len(output_issues),
            "integratedIssueCount": len(retired),
            "fixSourceCount": len(fix_sources),
            "replacementSourceCount": len(replacement_sources),
            "sameStemPairCount": len(source_audit["sameStemPairs"]),
            "incorrectStatementCount": sum(
                str(issue["kind"]).startswith("incorrect-statement")
                for issue in output_issues
            ),
            "proofGapCount": sum(issue["kind"] == "proof-gap" for issue in output_issues),
            "formalOnlyCopiesVerified": all(
                issue["formalOnlyDiffVerified"] for issue in output_issues
            ),
            "leanVerified": all(issue["leanVerified"] for issue in output_issues),
        },
        "sourceAudit": source_audit,
        "issues": output_issues,
        "retiredIssues": retired,
        "byLabel": {str(issue["label"]): issue for issue in output_issues},
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Validate and inventory Lean-backed thesis correction copies."
    )
    parser.add_argument("--thesis-root", type=Path, default=DEFAULT_THESIS_ROOT)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--fix-svg-root", type=Path, default=DEFAULT_FIX_SVG_ROOT)
    parser.add_argument("--rebuild-svg", action="store_true")
    args = parser.parse_args()
    payload = build_payload(
        args.thesis_root.resolve(),
        args.registry.resolve(),
        args.fix_svg_root.resolve(),
        args.rebuild_svg,
    )
    write_json(args.output.resolve(), payload)
    print(
        f"Thesis fixes: {payload['summary']['issueCount']} active correction copies; "
        f"{payload['summary']['integratedIssueCount']} integrated corrections preserved in history."
    )
    print(args.output.resolve())


if __name__ == "__main__":
    main()
