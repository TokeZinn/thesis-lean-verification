from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import uuid
from contextlib import contextmanager
from concurrent.futures import ThreadPoolExecutor
from collections import Counter
from pathlib import Path
from thesis_config import THESIS_ROOT, source_name

from inventory_common import (
    humanize_label,
    latex_plain_text,
    references_in,
    slug_for_label,
    unique,
    write_json,
)


PROJECT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_THESIS_ROOT = THESIS_ROOT
DEFAULT_OUTPUT = PROJECT_ROOT / "bridge-data" / "thesis-environments.json"
DEFAULT_SVG_ROOT = PROJECT_ROOT / "graph-artifacts" / "thesis-svg"

ENVIRONMENT_KINDS = {
    "axiom": "Axiom",
    "prin": "Principle",
    "conc": "Conclusion",
    "thm": "Theorem",
    "lem": "Lemma",
    "prop": "Proposition",
    "cor": "Corollary",
    "defn": "Definition",
    "exmp": "Example",
    "rem": "Remark",
    "assum": "Assumption",
    "qst": "Question",
}
BEGIN_RE = re.compile(
    r"\\begin\{(" + "|".join(map(re.escape, ENVIRONMENT_KINDS)) + r")\}"
    r"(?:\[([^\]]*)\])?"
)
LABEL_COMMAND_RE = re.compile(r"\\label\{([^}]+)\}")
HEADING_RE = re.compile(r"\\(chapter|section|subsection|subsubsection)\*?(?:\[[^\]]*\])?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}")
CHAPTER_COMMAND_RE = re.compile(r"\\chapter(\*)?(?:\[[^\]]*\])?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}")
INCLUDE_RE = re.compile(r"\\(?:subfile|include|input)\{([^}]+)\}")
PART_RE = re.compile(r"\\part\*?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}")
APPENDIX_RE = re.compile(r"\\appendix\b")
MATTER_RE = re.compile(r"\\(frontmatter|mainmatter|backmatter)\b")
PROOF_START_RE = re.compile(r"(?:\s|%[^\n]*\n)*\\begin\{proof\}(?:\[[^\]]*\])?")
PROOF_ANY_RE = re.compile(r"\\begin\{proof\}(?:\[([^\]]*)\])?")
SHARED_THEOREM_ENVIRONMENTS = {"thm", "lem", "prop", "cor", "defn"}


def resolve_source(thesis_root: Path, value: str) -> Path | None:
    candidate = (thesis_root / value).with_suffix(".tex") if not Path(value).suffix else thesis_root / value
    return candidate.resolve() if candidate.is_file() else None


def uncommented_latex(text: str) -> str:
    """Mask comments while preserving offsets used by source matches."""
    return re.sub(
        r"(?<!\\)%[^\n]*",
        lambda match: " " * len(match.group(0)),
        text,
    )


def master_sources(thesis_root: Path) -> list[dict[str, object]]:
    """Follow the full input tree, retaining the order at each inclusion site.

    A direct-master-only scan silently omitted the four intraday appendices.
    Per-block context also handles a child inserted between two parent blocks.
    """
    records: list[dict[str, object]] = []
    current_part = "Front matter"
    current_master_chapter = ""
    chapter_counter = 0
    appendix = False
    mainmatter = True
    order = 0
    stack: list[Path] = []

    def visit(source: Path, is_master: bool = False) -> None:
        nonlocal current_part, current_master_chapter, chapter_counter, appendix, mainmatter, order
        source = source.resolve()
        if source in stack:
            raise ValueError("Cyclic thesis input: " + " -> ".join(map(str, [*stack, source])))
        stack.append(source)
        scan_text = uncommented_latex(source.read_text(encoding="utf-8-sig"))
        record = {
            "source": source.relative_to(thesis_root.resolve()).as_posix(),
            "part": current_part, "chapterStart": chapter_counter,
            "masterChapter": current_master_chapter, "appendix": appendix,
            "numberedChapters": mainmatter, "blockContexts": {},
        }
        if not is_master:
            records.append(record)
        events = sorted(
            [(m.start(), "part", m) for m in PART_RE.finditer(scan_text)]
            + [(m.start(), "chapter", m) for m in CHAPTER_COMMAND_RE.finditer(scan_text)]
            + [(m.start(), "appendix", m) for m in APPENDIX_RE.finditer(scan_text)]
            + [(m.start(), "matter", m) for m in MATTER_RE.finditer(scan_text)]
            + [(m.start(), "source", m) for m in INCLUDE_RE.finditer(scan_text)]
            + [(m.start(), "block", m) for m in BEGIN_RE.finditer(scan_text)],
            key=lambda item: item[0],
        )
        for offset, event_type, match in events:
            if event_type == "part":
                current_part = latex_plain_text(match.group(1)) or current_part
                current_master_chapter = ""
            elif event_type == "appendix":
                appendix, chapter_counter = True, 0
            elif event_type == "matter":
                mainmatter = match.group(1) == "mainmatter"
            elif event_type == "chapter":
                if mainmatter and not match.group(1):
                    chapter_counter += 1
                current_master_chapter = latex_plain_text(match.group(2))
            elif event_type == "block":
                record["blockContexts"][offset] = {
                    "expansionOrder": order, "chapterCounter": chapter_counter,
                    "chapter": current_master_chapter, "part": current_part,
                    "appendix": appendix,
                }
                order += 1
                if is_master and record not in records:
                    records.append(record)
            else:
                value = match.group(1).strip()
                child = resolve_source(thesis_root, value) or resolve_source(source.parent, value)
                if child is not None:
                    visit(child)
        stack.pop()

    visit(thesis_root / "master.tex", is_master=True)
    return records


def find_environment_end(text: str, env: str, start: int) -> int:
    token_re = re.compile(rf"\\(begin|end)\{{{re.escape(env)}\}}")
    depth = 1
    for match in token_re.finditer(text, start):
        depth += 1 if match.group(1) == "begin" else -1
        if depth == 0:
            return match.end()
    return -1


def clean_body(raw: str, env: str) -> str:
    body = re.sub(rf"^\\begin\{{{re.escape(env)}\}}(?:\[[^\]]*\])?", "", raw.strip())
    body = re.sub(rf"\\end\{{{re.escape(env)}\}}\s*$", "", body)
    return body.strip()


def heading_at(text: str, offset: int, level: str) -> str:
    headings = [match for match in HEADING_RE.finditer(text, 0, offset) if match.group(1) == level]
    return latex_plain_text(headings[-1].group(2)) if headings else ""


def following_proof(text: str, environment_end: int) -> tuple[int | None, str, str]:
    scan_text = uncommented_latex(text)
    match = PROOF_START_RE.match(scan_text, environment_end)
    if not match:
        return None, "", ""
    proof_end = find_environment_end(scan_text, "proof", match.end())
    if proof_end < 0:
        return None, "", ""
    raw_end = proof_end
    proof_end -= len(r"\end{proof}")
    return (
        text.count("\n", 0, match.start()) + 1,
        text[match.end() : proof_end].strip(),
        text[match.start() : raw_end].strip(),
    )


def primary_label(env: str, labels: list[str]) -> str | None:
    expected = [label for label in labels if label.startswith(f"{env}:")]
    return expected[0] if expected else None


def scrape_source(thesis_root: Path, source_record: dict[str, object]) -> list[dict[str, object]]:
    relative = str(source_record["source"])
    path = thesis_root / relative
    text = path.read_text(encoding="utf-8-sig")
    scan_text = uncommented_latex(text)
    records: list[dict[str, object]] = []
    # The masked source preserves offsets but removes commented-out LaTeX.
    # Slice the original text at those offsets so the inventory contains only
    # environments that are active in the compiled thesis.
    for ordinal, match in enumerate(BEGIN_RE.finditer(scan_text), start=1):
        env = match.group(1)
        end = find_environment_end(scan_text, env, match.end())
        if end < 0:
            line = text.count("\n", 0, match.start()) + 1
            raise ValueError(f"unclosed {env} environment at {relative}:{line}")
        raw = text[match.start() : end]
        body = clean_body(raw, env)
        labels = unique(LABEL_COMMAND_RE.findall(scan_text[match.start() : end]))
        label = primary_label(env, labels)
        line = text.count("\n", 0, match.start()) + 1
        stable_id = label or f"source:{relative}:{line}:{env}:{ordinal}"
        optional_title = latex_plain_text(match.group(2) or "")
        title = optional_title or (humanize_label(label) if label else f"{ENVIRONMENT_KINDS[env]} at line {line}")
        proof_line, proof, raw_proof = following_proof(text, end)
        chapter_counter = int(source_record.get("chapterStart", 0))
        if source_record.get("numberedChapters", True):
            chapter_counter += sum(
                not chapter_match.group(1)
                for chapter_match in CHAPTER_COMMAND_RE.finditer(scan_text, 0, match.start())
            )
        records.append(
            {
                "id": stable_id,
                "label": label,
                "labels": labels,
                "environment": env,
                "kind": ENVIRONMENT_KINDS[env],
                "title": title,
                "optionalTitle": optional_title or None,
                "part": source_record["part"],
                "appendix": bool(source_record.get("appendix", False)),
                "chapterCounter": chapter_counter,
                "chapter": heading_at(scan_text, match.start(), "chapter")
                or str(source_record.get("masterChapter", "")),
                "section": heading_at(scan_text, match.start(), "section"),
                "subsection": heading_at(scan_text, match.start(), "subsection"),
                "source": relative,
                "line": line,
                "statement": body,
                "rawEnvironment": raw,
                "references": references_in(body),
                "proof": {
                    "line": proof_line,
                    "text": proof,
                    "rawEnvironment": raw_proof,
                    "references": references_in(proof),
                }
                if proof
                else None,
                "svg": None,
            }
        )
        records[-1].update(source_record.get("blockContexts", {}).get(match.start(), {}))
    # A few long thesis arguments place auxiliary lemmas between a theorem and
    # a later `Proof of Theorem~\ref{...}` block.  Associate those explicitly
    # titled proofs by their reference instead of silently dropping them.
    records_by_label = {
        str(record["label"]): record for record in records if record.get("label")
    }
    for proof_match in PROOF_ANY_RE.finditer(scan_text):
        title = proof_match.group(1) or ""
        targets = [label for label in references_in(title) if label in records_by_label]
        if len(targets) != 1:
            continue
        target = records_by_label[targets[0]]
        if target.get("proof"):
            continue
        proof_end = find_environment_end(scan_text, "proof", proof_match.end())
        if proof_end < 0:
            continue
        raw_end = proof_end
        proof_end -= len(r"\end{proof}")
        proof_text = text[proof_match.end() : proof_end].strip()
        target["proof"] = {
            "line": text.count("\n", 0, proof_match.start()) + 1,
            "text": proof_text,
            "rawEnvironment": text[proof_match.start() : raw_end].strip(),
            "references": references_in(proof_text),
        }
    return records


def attach_render_counters(records: list[dict[str, object]], thesis_root: Path | None = None) -> None:
    shared = SHARED_THEOREM_ENVIRONMENTS
    if thesis_root and (thesis_root / "incl/pre/cmds.tex").is_file():
        commands = uncommented_latex((thesis_root / "incl/pre/cmds.tex").read_text(encoding="utf-8-sig"))
        shared = {"thm"} | set(re.findall(r"\\newtheorem\{([^}]+)\}\[thm\]", commands))
    shared_counter = 0
    independent_counters: Counter[str] = Counter()
    current_chapter: tuple[bool, int] | None = None
    for record in records:
        chapter = (bool(record.get("appendix", False)), int(record.get("chapterCounter", 0)))
        if chapter != current_chapter:
            shared_counter = 0
            current_chapter = chapter
        environment = str(record["environment"])
        if environment in shared:
            counter_name = "thm"
            counter_before = shared_counter
            shared_counter += 1
            chapter_name = (
                chr(ord("A") + chapter[1] - 1)
                if chapter[0] and chapter[1]
                else str(chapter[1])
            )
            number = f"{chapter_name}.{counter_before + 1}"
        else:
            counter_name = environment
            counter_before = independent_counters[environment]
            independent_counters[environment] += 1
            number = str(counter_before + 1)
        record["renderContext"] = {
            "appendix": chapter[0],
            "chapter": chapter[1],
            "counter": counter_name,
            "counterBefore": counter_before,
            "number": number,
        }


def load_manifest(svg_root: Path) -> dict[str, dict[str, object]]:
    path = svg_root / "manifest.json"
    if not path.is_file():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    return {str(key): value for key, value in payload.items() if isinstance(value, dict)}


def attach_existing_svgs(records: list[dict[str, object]], svg_root: Path) -> None:
    manifest = load_manifest(svg_root)
    for record in records:
        key = str(record.get("label") or record["id"])
        entry = manifest.get(key)
        if not entry or not entry.get("svg"):
            continue
        # A label can survive a changed statement. Historical un-fingerprinted
        # renders must not replace the actual current LaTeX text in the viewer.
        if entry.get("statementSha256") != hashlib.sha256(record["rawEnvironment"].encode()).hexdigest():
            continue
        if entry.get("number") != (record.get("renderContext") or {}).get("number"):
            continue
        svg_path = svg_root.parent / str(entry["svg"])
        if svg_path.is_file():
            record["svg"] = {
                "path": str(entry["svg"]),
                "repoPath": entry.get("repoPath"),
                "rendered": True,
            }
        if (record.get("proof") and entry.get("proofSvg") and
            entry.get("proofSha256") == hashlib.sha256(record["proof"]["rawEnvironment"].encode()).hexdigest()):
            proof_path = svg_root.parent / str(entry["proofSvg"])
            if proof_path.is_file():
                record["proof"]["svg"] = str(entry["proofSvg"])


def current_thesis_preamble(thesis_root: Path) -> str:
    """Return the literal pre-document portion of the current thesis master."""
    text = (thesis_root / "master.tex").read_text(encoding="utf-8-sig")
    marker = r"\begin{document}"
    position = text.find(marker)
    if position < 0:
        raise ValueError(f"{marker} missing from {thesis_root / 'master.tex'}")
    return text[:position].rstrip()


def latex_source_for_fragments(
    thesis_root: Path,
    fragments: list[dict[str, object]],
) -> str:
    preview_environments = sorted({str(fragment["environment"]) for fragment in fragments})
    # Reuse references only from a successful build of these exact sources.
    reference_lines = []
    build_path = PROJECT_ROOT / "audit/ultravibe/pdf-build.json"
    if build_path.is_file():
        build = json.loads(build_path.read_text(encoding="utf-8"))
        if all((thesis_root / p).is_file() and
               hashlib.sha256((thesis_root / p).read_bytes()).hexdigest() == h
               for p, h in build.get("sourceHashes", {}).items()):
            output = (PROJECT_ROOT / build["output"]).parent
            for aux in sorted(output.rglob("*.aux")):
                reference_lines += [line for line in aux.read_text(encoding="utf-8").splitlines()
                                    if line.startswith((r"\newlabel{", r"\bibcite{"))]
    lines = [
        current_thesis_preamble(thesis_root),
        r"\usepackage[active,tightpage]{preview}",
        *[rf"\PreviewEnvironment{{{environment}}}" for environment in preview_environments],
        r"\makeatletter",
        *reference_lines,
        r"\makeatother",
        r"\begin{document}",
    ]
    appendix_active = False
    for index, fragment in enumerate(fragments, start=1):
        record = fragment.get("record")
        if fragment["fragmentKind"] == "statement" and isinstance(record, dict):
            context = record.get("renderContext") or {}
            if context.get("appendix") and not appendix_active:
                lines.append(r"\appendix")
                appendix_active = True
            lines.extend(
                [
                    rf"\setcounter{{chapter}}{{{int(context.get('chapter', 0))}}}",
                    rf"\setcounter{{{context.get('counter', record['environment'])}}}"
                    rf"{{{int(context.get('counterBefore', 0))}}}",
                ]
            )
        lines.extend(
            [
                f"% Lean explorer SVG fragment {index}: {fragment['label']} ({fragment['fragmentKind']})",
                rf"\typeout{{LEAN-SVG-FRAGMENT:{index}:{fragment['label']}:{fragment['fragmentKind']}}}",
                str(fragment["body"]),
            ]
        )
    lines.extend([r"\end{document}", ""])
    return "\n".join(lines)


def batch_fragments(
    records: list[dict[str, object]],
    kinds: set[str],
    labels: set[str] | None = None,
) -> list[dict[str, object]]:
    fragments: list[dict[str, object]] = []
    for record in records:
        label = str(record.get("label") or record["id"])
        if record["environment"] not in kinds:
            continue
        if labels is not None and label not in labels:
            continue
        slug = slug_for_label(str(label))
        fragments.append(
            {
                "record": record,
                "label": label,
                "fragmentKind": "statement",
                "environment": record["environment"],
                "body": record["rawEnvironment"],
                "filename": f"{slug}.svg",
            }
        )
        proof = record.get("proof")
        if proof and proof.get("rawEnvironment"):
            fragments.append(
                {
                    "record": record,
                    "label": label,
                    "fragmentKind": "proof",
                    "environment": "proof",
                    "body": proof["rawEnvironment"],
                    "filename": f"{slug}__proof.svg",
                }
            )
    return fragments


def page_number(path: Path) -> int:
    match = re.search(r"-(\d+)\.svg$", path.name)
    if not match:
        raise ValueError(f"Could not read rendered page number from {path.name}")
    return int(match.group(1))


def run_latex(
    latex: str,
    thesis_root: Path,
    temporary_path: Path,
    tex_path: Path,
) -> None:
    command = [
        latex,
        "-interaction=nonstopmode",
        "-halt-on-error",
        f"-output-directory={temporary_path}",
        str(tex_path),
    ]
    for pass_number in (1, 2):
        result = subprocess.run(
            command,
            cwd=thesis_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if result.returncode:
            markers = [line for line in result.stdout.splitlines() if "LEAN-SVG-FRAGMENT:" in line]
            location = f" after {markers[-1]}" if markers else ""
            tail = "\n".join(result.stdout.splitlines()[-40:])
            raise RuntimeError(f"LaTeX pass {pass_number} failed{location}:\n{tail}")


@contextmanager
def render_workspace(prefix: str):
    # TemporaryDirectory uses private ACLs that the Windows restricted token
    # cannot access. A normal project-local directory inherits usable ACLs.
    parent = (PROJECT_ROOT / ".lake").resolve()
    parent.mkdir(exist_ok=True)
    directory = parent / f"{prefix}{uuid.uuid4().hex}"
    directory.mkdir()
    try:
        yield directory
    finally:
        resolved = directory.resolve()
        if resolved.parent != parent or not resolved.name.startswith(prefix):
            raise RuntimeError("refusing cleanup outside the render workspace")
        shutil.rmtree(resolved)


def rebuild_all_svgs(
    thesis_root: Path,
    svg_root: Path,
    records: list[dict[str, object]],
) -> tuple[int, int]:
    """Rebuild every active formal statement and proof from the current master preamble."""
    latex = shutil.which("pdflatex")
    dvisvgm = shutil.which("dvisvgm")
    if not latex or not dvisvgm:
        raise RuntimeError("pdflatex and dvisvgm must both be available on PATH to render SVGs")
    fragments = batch_fragments(records, set(ENVIRONMENT_KINDS))
    if not fragments:
        raise RuntimeError("No active thesis environments were found to render")
    filenames = [str(fragment["filename"]) for fragment in fragments]
    if len(filenames) != len(set(filenames)):
        duplicates = sorted(name for name, count in Counter(filenames).items() if count > 1)
        raise RuntimeError(f"Duplicate SVG filenames: {', '.join(duplicates)}")

    try:
        svg_root_relative = svg_root.relative_to(PROJECT_ROOT).as_posix()
    except ValueError:
        svg_root_relative = svg_root.name

    with render_workspace("thesis-svg-rebuild-") as temporary:
        temporary_path = Path(temporary)
        tex_path = temporary_path / "fragments.tex"
        tex_path.write_text(
            latex_source_for_fragments(thesis_root, fragments),
            encoding="utf-8",
            newline="\n",
        )
        run_latex(latex, thesis_root, temporary_path, tex_path)
        dvi_path = temporary_path / "fragments.pdf"
        # Retain the intermediate PDF and log for visual audit of the extraction.
        shutil.copy2(dvi_path, PROJECT_ROOT / ".lake/current-thesis-fragments.pdf")
        shutil.copy2(temporary_path / "fragments.log", PROJECT_ROOT / ".lake/current-thesis-fragments.log")
        output_pattern = temporary_path / "fragment-%p.svg"
        convert_result = subprocess.run(
            [
                dvisvgm,
                "--pdf",
                "--page=1-",
                "--bbox=min",
                "--no-fonts",
                f"--output={output_pattern}",
                str(dvi_path),
            ],
            cwd=thesis_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if convert_result.returncode:
            cairo = shutil.which("pdftocairo")
            if not cairo:
                tail = "\n".join(convert_result.stdout.splitlines()[-40:])
                raise RuntimeError(f"dvisvgm failed and pdftocairo is unavailable:\n{tail}")
            # Modern Ghostscript versions cannot be used by dvisvgm's PDF
            # backend. Poppler also exports the actual PDF glyph outlines.
            def export_page(page):
                result = subprocess.run([cairo, "-svg", "-f", str(page), "-l", str(page),
                                         str(dvi_path), str(temporary_path / f"fragment-{page}.svg")],
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        text=True, check=False)
                if result.returncode:
                    raise RuntimeError(f"pdftocairo page {page}: {result.stdout}")
            with ThreadPoolExecutor(max_workers=4) as pool:
                list(pool.map(export_page, range(1, len(fragments) + 1)))
        rendered_pages = sorted(temporary_path.glob("fragment-*.svg"), key=page_number)
        if len(rendered_pages) != len(fragments):
            raise RuntimeError(
                f"Expected {len(fragments)} SVG pages, but dvisvgm produced {len(rendered_pages)}"
            )

        resolved_svg_root = svg_root.resolve()
        if not resolved_svg_root.is_relative_to(PROJECT_ROOT.resolve()) or resolved_svg_root == PROJECT_ROOT.resolve():
            raise RuntimeError("refusing to replace SVGs outside the verification project")
        svg_root.mkdir(parents=True, exist_ok=True)
        for existing in svg_root.glob("*.svg"):
            existing.unlink()
        for rendered_page, fragment in zip(rendered_pages, fragments, strict=True):
            shutil.copy2(rendered_page, svg_root / str(fragment["filename"]))

    manifest: dict[str, dict[str, object]] = {}
    for fragment in fragments:
        record = fragment["record"]
        label = str(fragment["label"])
        filename = str(fragment["filename"])
        relative_svg = f"{svg_root.name}/{filename}"
        repo_path = f"{svg_root_relative}/{filename}"
        entry = manifest.setdefault(
            label,
            {
                "env": record["environment"],
                "line": record["line"],
                "repoPath": f"{svg_root_relative}/{slug_for_label(label)}.svg",
                "source": record["source"],
                "svg": f"{svg_root.name}/{slug_for_label(label)}.svg",
                "number": (record.get("renderContext") or {}).get("number"),
                "statementSha256": hashlib.sha256(record["rawEnvironment"].encode()).hexdigest(),
            },
        )
        if fragment["fragmentKind"] == "statement":
            record["svg"] = {
                "path": relative_svg,
                "repoPath": repo_path,
                "rendered": True,
            }
        else:
            proof = record["proof"]
            proof["svg"] = relative_svg
            entry.update(
                {
                    "proofLine": proof["line"],
                    "proofRepoPath": repo_path,
                    "proofSvg": relative_svg,
                    "proofSha256": hashlib.sha256(proof["rawEnvironment"].encode()).hexdigest(),
                }
            )
    write_json(svg_root / "manifest.json", manifest)
    statement_count = sum(fragment["fragmentKind"] == "statement" for fragment in fragments)
    proof_count = sum(fragment["fragmentKind"] == "proof" for fragment in fragments)
    return statement_count, proof_count


def render_svg(
    thesis_root: Path,
    svg_root: Path,
    record: dict[str, object],
    latex: str,
    dvisvgm: str,
) -> str:
    env = str(record["environment"])
    label = str(record.get("label") or record["id"])
    filename = slug_for_label(label) + ".svg"
    destination = svg_root / filename
    source = latex_source_for_fragments(
        thesis_root,
        [
            {
                "record": record,
                "label": label,
                "fragmentKind": "statement",
                "environment": env,
                "body": record["rawEnvironment"],
            }
        ],
    )
    with render_workspace("thesis-svg-") as temporary:
        temporary_path = Path(temporary)
        tex_path = temporary_path / "environment.tex"
        tex_path.write_text(source, encoding="utf-8", newline="\n")
        run_latex(latex, thesis_root, temporary_path, tex_path)
        dvi_path = temporary_path / "environment.pdf"
        svg_root.mkdir(parents=True, exist_ok=True)
        convert_result = subprocess.run(
            [
                dvisvgm,
                "--pdf",
                "--page=1",
                "--bbox=min",
                "--no-fonts",
                f"--output={destination}",
                str(dvi_path),
            ],
            cwd=thesis_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if convert_result.returncode or not destination.is_file():
            cairo = shutil.which("pdftocairo")
            if not cairo:
                raise RuntimeError(f"dvisvgm failed for {label}:\n{convert_result.stdout}")
            fallback = subprocess.run([cairo, "-svg", "-f", "1", "-l", "1",
                                       str(dvi_path), str(destination)],
                                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                      text=True, check=False)
            if fallback.returncode:
                raise RuntimeError(f"pdftocairo failed for {label}:\n{fallback.stdout}")
    return filename


def render_missing(
    thesis_root: Path,
    svg_root: Path,
    records: list[dict[str, object]],
    kinds: set[str],
    overwrite: bool,
    labels: set[str] | None = None,
) -> tuple[int, list[dict[str, str]]]:
    latex = shutil.which("pdflatex")
    dvisvgm = shutil.which("dvisvgm")
    if not latex or not dvisvgm:
        raise RuntimeError("pdflatex and dvisvgm must both be available on PATH to render SVGs")
    rendered = 0
    failures: list[dict[str, str]] = []
    manifest = load_manifest(svg_root)
    try:
        svg_root_relative = svg_root.relative_to(PROJECT_ROOT).as_posix()
    except ValueError:
        svg_root_relative = svg_root.name
    for record in records:
        key = str(record.get("label") or record["id"])
        if record["environment"] not in kinds:
            continue
        if labels is not None and key not in labels:
            continue
        current = record.get("svg")
        if current and not overwrite:
            continue
        try:
            filename = render_svg(thesis_root, svg_root, record, latex, dvisvgm)
            relative_svg = f"{svg_root.name}/{filename}"
            repo_path = f"{svg_root_relative}/{filename}"
            record["svg"] = {
                "path": relative_svg,
                "repoPath": repo_path,
                "rendered": True,
            }
            entry = dict(manifest.get(key, {}))
            entry.update({
                "env": record["environment"],
                "line": record["line"],
                "repoPath": repo_path,
                "source": record["source"],
                "svg": relative_svg,
                "number": (record.get("renderContext") or {}).get("number"),
                "statementSha256": hashlib.sha256(record["rawEnvironment"].encode()).hexdigest(),
            })
            manifest[key] = entry
            rendered += 1
        except RuntimeError as error:
            failures.append({"id": str(record["id"]), "error": str(error)})
    if rendered:
        write_json(svg_root / "manifest.json", manifest)
    return rendered, failures


def build_inventory(thesis_root: Path, svg_root: Path) -> dict[str, object]:
    sources = master_sources(thesis_root)
    records = [record for source in sources for record in scrape_source(thesis_root, source)]
    hashes = {row["source"]: hashlib.sha256((thesis_root / row["source"]).read_bytes()).hexdigest()
              for row in sources}
    for record in records:
        record["sourceFileSha256"] = hashes[record["source"]]
    records.sort(key=lambda record: record.get("expansionOrder", 0))
    attach_render_counters(records, thesis_root)
    attach_existing_svgs(records, svg_root)
    label_counts = Counter(str(record["label"]) for record in records if record.get("label"))
    duplicate_labels = {label: count for label, count in label_counts.items() if count > 1}
    kinds = Counter(str(record["environment"]) for record in records)
    return {
        "schemaVersion": 1,
        "sourceRoot": source_name(thesis_root),
        "scope": "sources included by master.tex",
        "summary": {
            "sourceCount": len(sources),
            "environmentCount": len(records),
            "labeledEnvironmentCount": sum(bool(record["label"]) for record in records),
            "unlabeledEnvironmentCount": sum(not record["label"] for record in records),
            "environmentKinds": dict(sorted(kinds.items())),
            "svgCount": sum(bool(record["svg"]) for record in records),
            "proofSvgCount": sum(
                bool((record.get("proof") or {}).get("svg")) for record in records
            ),
            "duplicateLabels": duplicate_labels,
        },
        "sources": sources,
        "environments": records,
        "byId": {str(record["id"]): index for index, record in enumerate(records)},
        "byLabel": {
            str(record["label"]): str(record["id"])
            for record in records
            if record.get("label")
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Scrape theorem-like thesis environments and optionally render them as SVG."
    )
    parser.add_argument("--thesis-root", type=Path, default=DEFAULT_THESIS_ROOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--svg-root", type=Path, default=DEFAULT_SVG_ROOT)
    parser.add_argument("--render-svg", action="store_true", help="render missing environments")
    parser.add_argument(
        "--kinds",
        default="defn",
        help="comma-separated LaTeX environment names to render (default: defn)",
    )
    parser.add_argument("--overwrite-svg", action="store_true")
    parser.add_argument(
        "--rebuild-all-svg",
        action="store_true",
        help=(
            "replace the SVG artifact directory with every active thesis statement and proof, "
            "compiled from the current master.tex preamble"
        ),
    )
    parser.add_argument(
        "--labels",
        help="optional comma-separated exact labels to render",
    )
    args = parser.parse_args()
    thesis_root = args.thesis_root.resolve()
    if not (thesis_root / "master.tex").is_file():
        parser.error(f"master.tex missing: {thesis_root}")
    svg_root = args.svg_root.resolve()
    payload = build_inventory(thesis_root, svg_root)
    failures: list[dict[str, str]] = []
    if args.rebuild_all_svg:
        statement_count, proof_count = rebuild_all_svgs(
            thesis_root,
            svg_root,
            payload["environments"],
        )
        payload["summary"]["newSvgCount"] = statement_count
        payload["summary"]["newProofSvgCount"] = proof_count
        payload["summary"]["svgFailures"] = []
        payload["summary"]["svgCount"] = statement_count
        payload["summary"]["proofSvgCount"] = proof_count
    elif args.render_svg:
        kinds = {kind.strip() for kind in args.kinds.split(",") if kind.strip()}
        unknown = kinds - set(ENVIRONMENT_KINDS)
        if unknown:
            parser.error(f"unknown environment kinds: {', '.join(sorted(unknown))}")
        rendered, failures = render_missing(
            thesis_root,
            svg_root,
            payload["environments"],
            kinds,
            args.overwrite_svg,
            {label.strip() for label in args.labels.split(",") if label.strip()}
            if args.labels
            else None,
        )
        payload["summary"]["newSvgCount"] = rendered
        payload["summary"]["svgFailures"] = failures
        payload["summary"]["svgCount"] = sum(
            bool(record["svg"]) for record in payload["environments"]
        )
    write_json(args.output.resolve(), payload)
    summary = payload["summary"]
    print(
        f"Thesis inventory: {summary['environmentCount']} environments in "
        f"{summary['sourceCount']} master sources; {summary['svgCount']} SVGs linked."
    )
    if failures:
        print(f"SVG rendering failures: {len(failures)} (recorded in the inventory)")
    print(args.output.resolve())


if __name__ == "__main__":
    main()
