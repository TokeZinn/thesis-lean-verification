from __future__ import annotations

import argparse
import re
from collections import Counter, defaultdict
from pathlib import Path

from inventory_common import audit_labels_in, unique, write_json


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = PROJECT_ROOT / "bridge-data" / "lean-inventory.json"

# Lean names may contain Unicode letters, subscript digits, primes, and
# guillemet-escaped components. ASCII-only matching silently truncated sd₀
# and merged distinct declarations in the transitive axiom-audit query.
NAME_COMPONENT = r"(?:[^\W\d][\w'′]*|«[^»]+»)"
NAME_PATTERN = rf"{NAME_COMPONENT}(?:\.{NAME_COMPONENT})*"
DECLARATION_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected|private|local|scoped|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|axiom|opaque|structure|class|inductive)\s+"
    rf"(?:\{{[^}}]*\}}\s*)?({NAME_PATTERN})"
)
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
SCOPE_RE = re.compile(rf"^\s*(?:noncomputable\s+)?(namespace|section)\s*({NAME_PATTERN})?\s*(?:--.*)?$")
END_RE = re.compile(rf"^\s*end(?:\s+({NAME_PATTERN}))?\s*(?:--.*)?$")
BLOCK_ID_RE = re.compile(r"(?mi)^\s*Original block id:\s*`?([^`\r\n]+?)`?[.,;:]?\s*$")


def project_lean_files(root: Path) -> list[Path]:
    ignored = {".git", ".lake", "build", "graph-artifacts", "bridge-data", "audit"}
    # Sort on the POSIX string so Windows (case-insensitive Path ordering) and
    # the Linux CI runner inventory the modules in the same order.
    return sorted(
        (
            path
            for path in root.rglob("*.lean")
            if not any(part in ignored for part in path.relative_to(root).parts)
        ),
        key=Path.as_posix,
    )


def module_name(root: Path, path: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def doc_blocks(lines: list[str]) -> list[tuple[int, int, str]]:
    blocks: list[tuple[int, int, str]] = []
    index = 0
    while index < len(lines):
        start_marker = lines[index].find("/--")
        if start_marker < 0:
            index += 1
            continue
        start = index
        while index < len(lines) and "-/" not in lines[index]:
            index += 1
        end = min(index, len(lines) - 1)
        blocks.append((start, end, "\n".join(lines[start : end + 1])))
        index = end + 1
    return blocks


def block_comment_lines(lines: list[str]) -> set[int]:
    """Return lines that intersect a Lean block comment.

    Declaration-looking prose inside `/-- ... -/` used to be counted as Lean
    code.  Lean block comments may nest, so a small depth scanner is more
    reliable than testing only the first two characters of a line.
    """
    depth = 0
    commented: set[int] = set()
    for index, line in enumerate(lines):
        if depth:
            commented.add(index)
        cursor = 0
        while cursor + 1 < len(line):
            token = line[cursor : cursor + 2]
            if token == "/-":
                depth += 1
                commented.add(index)
                cursor += 2
                continue
            if token == "-/" and depth:
                depth -= 1
                commented.add(index)
                cursor += 2
                continue
            cursor += 1
    return commented


def clean_doc_comment(comment: str) -> str:
    text = comment.replace("/--", "").replace("-/", "")
    lines = [line.strip().lstrip("*").strip() for line in text.splitlines()]
    return "\n".join(lines).strip()


def declaration_header(lines: list[str], start: int) -> str:
    pieces: list[str] = []
    balance = 0
    for index in range(start, min(len(lines), start + 80)):
        line = lines[index]
        pieces.append(line.rstrip())
        balance += sum(line.count(character) for character in "({[")
        balance -= sum(line.count(character) for character in ")}]")
        joined = "\n".join(pieces)
        if balance <= 0 and (
            re.search(r"\s:=\s*", line)
            or re.search(r"\sby\s*(?:--.*)?$", line)
            or re.search(r"\swhere\s*(?:--.*)?$", line)
        ):
            break
        if balance <= 0 and index > start and line.rstrip().endswith((":=", "where", "by")):
            break
    header = re.split(r"\s(?::=|by|where)\b", joined, maxsplit=1)[0]
    return re.sub(r"\s+", " ", header).strip()


def preceding_doc_comment(
    lines: list[str], declaration_index: int, blocks_by_end: dict[int, tuple[int, int, str]]
) -> tuple[int, str] | None:
    cursor = declaration_index - 1
    while cursor >= 0 and (not lines[cursor].strip() or lines[cursor].lstrip().startswith("@[")):
        cursor -= 1
    block = blocks_by_end.get(cursor)
    if block is None:
        return None
    start, _end, text = block
    return start + 1, clean_doc_comment(text)


def qualified_name(name: str, namespaces: list[str]) -> str:
    if name.startswith("_root_."):
        return name.removeprefix("_root_.")
    prefix = ".".join(namespaces)
    return f"{prefix}.{name}" if prefix else name


def parse_file(root: Path, path: Path) -> tuple[dict[str, object], list[dict[str, object]]]:
    lines = path.read_text(encoding="utf-8-sig").splitlines()
    module = module_name(root, path)
    relative = path.relative_to(root).as_posix()
    imports: list[str] = []
    declarations: list[dict[str, object]] = []
    scopes: list[tuple[str, str | None]] = []
    blocks = doc_blocks(lines)
    blocks_by_end = {end: block for block in blocks for end in [block[1]]}
    commented_lines = block_comment_lines(lines)

    for index, line in enumerate(lines):
        if index in commented_lines:
            continue
        import_match = IMPORT_RE.match(line)
        if import_match:
            imports.extend(import_match.group(1).split())

        scope_match = SCOPE_RE.match(line)
        if scope_match:
            scopes.append((scope_match.group(1), scope_match.group(2)))
            continue
        end_match = END_RE.match(line)
        if end_match and scopes:
            requested = end_match.group(1)
            if not requested:
                scopes.pop()
            else:
                match_index = next(
                    (position for position in range(len(scopes) - 1, -1, -1) if scopes[position][1] == requested),
                    len(scopes) - 1,
                )
                del scopes[match_index:]
            continue

        declaration_match = DECLARATION_RE.match(line)
        if not declaration_match:
            continue
        kind, name = declaration_match.groups()
        namespace = [name for scope_kind, name in scopes if scope_kind == "namespace" and name]
        doc = preceding_doc_comment(lines, index, blocks_by_end)
        doc_line, doc_text = doc if doc else (None, "")
        labels = audit_labels_in(doc_text)
        block_ids = unique(BLOCK_ID_RE.findall(doc_text))
        declarations.append(
            {
                "id": f"{module}:{index + 1}:{name}",
                "name": name,
                "fullName": qualified_name(name, namespace),
                "kind": kind,
                "module": module,
                "source": relative,
                "line": index + 1,
                "namespace": ".".join(namespace),
                "header": declaration_header(lines, index),
                "docComment": doc_text,
                "docLine": doc_line,
                "thesisLabels": labels,
                "thesisEnvironmentIds": block_ids,
            }
        )

    return (
        {
            "module": module,
            "source": relative,
            "imports": unique(imports),
            "declarationCount": len(declarations),
        },
        declarations,
    )


def build_inventory(root: Path) -> dict[str, object]:
    modules: list[dict[str, object]] = []
    declarations: list[dict[str, object]] = []
    for path in project_lean_files(root):
        module, records = parse_file(root, path)
        modules.append(module)
        declarations.extend(records)

    by_label: dict[str, list[str]] = defaultdict(list)
    by_environment_id: dict[str, list[str]] = defaultdict(list)
    for declaration in declarations:
        for label in declaration["thesisLabels"]:
            by_label[str(label)].append(str(declaration["id"]))
        for environment_id in declaration["thesisEnvironmentIds"]:
            by_environment_id[str(environment_id)].append(str(declaration["id"]))

    kinds = Counter(str(declaration["kind"]) for declaration in declarations)
    labeled = sum(bool(declaration["thesisLabels"]) for declaration in declarations)
    return {
        "schemaVersion": 1,
        "sourceRoot": root.name,
        "summary": {
            "moduleCount": len(modules),
            "declarationCount": len(declarations),
            "labeledDeclarationCount": labeled,
            "unlabeledDeclarationCount": len(declarations) - labeled,
            "distinctThesisLabelCount": len(by_label),
            "distinctThesisEnvironmentIdCount": len(by_environment_id),
            "declarationKinds": dict(sorted(kinds.items())),
        },
        "modules": modules,
        "declarations": declarations,
        "byThesisLabel": dict(sorted(by_label.items())),
        "byThesisEnvironmentId": dict(sorted(by_environment_id.items())),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Inventory every declaration in a local Lean project.")
    parser.add_argument("--lean-root", type=Path, default=PROJECT_ROOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    root = args.lean_root.resolve()
    if not (root / "lakefile.toml").is_file():
        parser.error(f"not a Lean project (lakefile.toml missing): {root}")
    payload = build_inventory(root)
    write_json(args.output.resolve(), payload)
    summary = payload["summary"]
    print(
        f"Lean inventory: {summary['declarationCount']} declarations in "
        f"{summary['moduleCount']} modules; {summary['distinctThesisLabelCount']} thesis labels."
    )
    print(args.output.resolve())


if __name__ == "__main__":
    main()
