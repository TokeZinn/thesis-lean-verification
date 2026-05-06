from __future__ import annotations

import json
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = PROJECT_ROOT / "graph-artifacts"
FOUNDATIONS_ROOT = PROJECT_ROOT / "Foundations"

RESULT_PREFIXES = ("cor", "defn", "eq", "exmp", "lem", "prin", "prop", "rem", "thm")
LABEL_RE = re.compile(r"\b(?:" + "|".join(RESULT_PREFIXES) + r"):[A-Za-z0-9_.-]+")
DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|protected|private|local|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|axiom|structure|class|inductive)\s+"
    r"([A-Za-z0-9_'.]+)"
)

STATUS_PALETTE = {
    "verified": {
        "color": "#2da44e",
        "label": "verified",
        "description": "Backed by compiled Lean declarations without external axioms.",
    },
    "external": {
        "color": "#8250df",
        "label": "external",
        "description": "Represented by an intentional cited axiom or by a wrapper depending on one.",
    },
    "commentary": {
        "color": "#6e7781",
        "label": "commentary",
        "description": "Recorded as thesis/framework narrative rather than a compiled theorem.",
    },
    "unknown": {
        "color": "#d1242f",
        "label": "unknown",
        "description": "No reliable Lean trace was found.",
    },
}

SECTION_PALETTE = {
    "foundations": "#0969da",
    "market-representation": "#1a7f37",
    "market-actions": "#bf8700",
    "market-clearing": "#cf222e",
    "stochastic": "#8250df",
    "other": "#6e7781",
}

SECTION_WORKFLOWS = {
    "foundations": "lean-foundations.yml",
    "market-representation": "lean-market-representation.yml",
    "market-actions": "lean-market-actions.yml",
    "market-clearing": "lean-market-clearing.yml",
    "stochastic": "lean-stochastic.yml",
    "other": "lean-global.yml",
}


@dataclass
class DeclarationTrace:
    declaration: str | None
    kind: str | None
    module: str
    file: str
    line: int


@dataclass
class ResultTrace:
    label: str
    traces: list[DeclarationTrace] = field(default_factory=list)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(PROJECT_ROOT).with_suffix("").parts)


def section_for_module(module: str) -> str:
    if module in {"Basic", "Foundations.Economics", "Foundations.External"}:
        return "foundations"
    if module == "MarketRepresentation" or module.startswith("Foundations.MarketRepresentation."):
        return "market-representation"
    if module.startswith("Foundations.MarketActions."):
        return "market-actions"
    if module.startswith("Foundations.MarketClearing."):
        return "market-clearing"
    if module.startswith("Foundations.Stochastic."):
        return "stochastic"
    return "other"


def lean_files() -> list[Path]:
    roots = [
        PROJECT_ROOT / "Basic.lean",
        PROJECT_ROOT / "MarketRepresentation.lean",
        PROJECT_ROOT / "Formalization.lean",
    ]
    files = [path for path in roots if path.exists()]
    if FOUNDATIONS_ROOT.exists():
        files.extend(sorted(FOUNDATIONS_ROOT.rglob("*.lean")))
    return files


def find_next_declaration(lines: list[str], start_index: int) -> tuple[int, str, str] | None:
    for index in range(start_index, min(len(lines), start_index + 120)):
        match = DECL_RE.match(lines[index])
        if match:
            kind, declaration = match.groups()
            return index + 1, kind, declaration
    return None


def comment_blocks(lines: list[str]) -> list[tuple[int, int, str, str]]:
    blocks: list[tuple[int, int, str, str]] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        marker = None
        if "/--" in line:
            marker = "/--"
        elif "/-!" in line:
            marker = "/-!"
        if marker is None:
            index += 1
            continue

        start = index
        while index < len(lines) and "-/" not in lines[index]:
            index += 1
        end = min(index, len(lines) - 1)
        text = "\n".join(lines[start : end + 1])
        blocks.append((start + 1, end + 1, marker, text))
        index = end + 1
    return blocks


def labels_from_original_label_clause(comment: str) -> list[str]:
    lines = comment.splitlines()
    labels: list[str] = []
    for index, line in enumerate(lines):
        if "Original label" not in line:
            continue
        clause_lines = [line]
        for follow in lines[index + 1 : index + 6]:
            stripped = follow.strip()
            if not stripped:
                break
            if stripped.startswith(("Informal statement", "Lean strategy", "External reference", "Thesis source")):
                break
            clause_lines.append(follow)
        labels.extend(LABEL_RE.findall("\n".join(clause_lines)))
    return sorted(dict.fromkeys(labels))


def labels_for_comment(comment: str) -> list[str]:
    original_labels = labels_from_original_label_clause(comment)
    if original_labels:
        return original_labels
    return sorted(dict.fromkeys(LABEL_RE.findall(comment)))


def result_status(traces: list[DeclarationTrace]) -> str:
    if not traces:
        return "unknown"
    if all(trace.declaration is None for trace in traces):
        return "commentary"
    if any(trace.kind == "axiom" for trace in traces):
        return "external"
    return "verified"


def declaration_payload(trace: DeclarationTrace) -> dict[str, object]:
    return {
        "name": trace.declaration,
        "kind": trace.kind,
        "module": trace.module,
        "file": trace.file,
        "line": trace.line,
    }


def build_results() -> dict[str, ResultTrace]:
    results: dict[str, ResultTrace] = defaultdict(lambda: ResultTrace(label=""))

    for path in lean_files():
        lines = path.read_text(encoding="utf-8").splitlines()
        module = module_name(path)
        relative_file = path.relative_to(PROJECT_ROOT).as_posix()

        for start, end, marker, comment in comment_blocks(lines):
            labels = labels_for_comment(comment)
            if not labels:
                continue

            declaration = find_next_declaration(lines, end)
            if declaration is None or marker == "/-!":
                trace = DeclarationTrace(
                    declaration=None,
                    kind=None,
                    module=module,
                    file=relative_file,
                    line=start,
                )
            else:
                line_number, kind, name = declaration
                trace = DeclarationTrace(
                    declaration=name,
                    kind=kind,
                    module=module,
                    file=relative_file,
                    line=line_number,
                )

            for label in labels:
                if not results[label].label:
                    results[label].label = label
                duplicate_key = (trace.declaration, trace.kind, trace.module, trace.file, trace.line)
                existing_keys = {
                    (item.declaration, item.kind, item.module, item.file, item.line)
                    for item in results[label].traces
                }
                if duplicate_key not in existing_keys:
                    results[label].traces.append(trace)

    return dict(sorted(results.items()))


def primary_section(traces: list[DeclarationTrace]) -> str:
    for trace in traces:
        section = section_for_module(trace.module)
        if section != "other":
            return section
    return "other"


def write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    results = build_results()

    result_records: list[dict[str, object]] = []
    status_counts: dict[str, int] = defaultdict(int)
    section_counts: dict[str, int] = defaultdict(int)

    for label, result in results.items():
        status = result_status(result.traces)
        section = primary_section(result.traces)
        status_counts[status] += 1
        section_counts[section] += 1
        result_records.append(
            {
                "label": label,
                "status": status,
                "color": STATUS_PALETTE[status]["color"],
                "section": section,
                "sectionColor": SECTION_PALETTE[section],
                "workflow": SECTION_WORKFLOWS[section],
                "modules": sorted({trace.module for trace in result.traces}),
                "declarations": [declaration_payload(trace) for trace in result.traces],
            }
        )

    payload = {
        "schemaVersion": 1,
        "description": "Result-level coloring metadata for the thesis Lean verification graph website.",
        "statusPalette": STATUS_PALETTE,
        "sectionPalette": SECTION_PALETTE,
        "sectionWorkflows": SECTION_WORKFLOWS,
        "summary": {
            "resultCount": len(result_records),
            "statusCounts": dict(sorted(status_counts.items())),
            "sectionCounts": dict(sorted(section_counts.items())),
        },
        "results": result_records,
        "byLabel": {record["label"]: record for record in result_records},
    }

    write_json(OUTPUT_ROOT / "result-colors.json", payload)
    write_json(
        OUTPUT_ROOT / "palette.json",
        {
            "schemaVersion": 1,
            "statusPalette": STATUS_PALETTE,
            "sectionPalette": SECTION_PALETTE,
            "sectionWorkflows": SECTION_WORKFLOWS,
        },
    )

    tsv_lines = [
        "label\tstatus\tcolor\tsection\tsectionColor\tworkflow\tmodules\tdeclarations"
    ]
    for record in result_records:
        declarations = ";".join(
            str(item["name"] or "module-comment") for item in record["declarations"]
        )
        tsv_lines.append(
            "\t".join(
                [
                    str(record["label"]),
                    str(record["status"]),
                    str(record["color"]),
                    str(record["section"]),
                    str(record["sectionColor"]),
                    str(record["workflow"]),
                    ";".join(record["modules"]),
                    declarations,
                ]
            )
        )
    (OUTPUT_ROOT / "result-colors.tsv").write_text("\n".join(tsv_lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
