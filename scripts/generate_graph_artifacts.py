from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

from build_lean_inventory import build_inventory as build_lean_inventory
from audit_formal_scope import load_statuses
from current_alignment import load_clause_reviews, display_status, current_finding_payload
from inventory_common import audit_labels_in
from scrape_thesis_environments import build_inventory as build_thesis_inventory
from thesis_config import THESIS_ROOT, publish_review_inputs, source_name


PROJECT_ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = PROJECT_ROOT / "graph-artifacts"
BRIDGE_DATA_ROOT = PROJECT_ROOT / "bridge-data"
THESIS_LEAN_ROOT = PROJECT_ROOT / "Thesis"
FOUNDATIONS_ROOT = THESIS_LEAN_ROOT / "Foundations"
DAY_AHEAD_ROOT = THESIS_LEAN_ROOT / "DayAhead"
DEFAULT_THESIS_ROOT = THESIS_ROOT
THESIS_METADATA_PATH = BRIDGE_DATA_ROOT / "thesis-results.json"
THESIS_FIXES_PATH = BRIDGE_DATA_ROOT / "thesis-fixes.json"
PROOF_OVERRIDES_PATH = BRIDGE_DATA_ROOT / "proof-mapping-overrides.json"

RESULT_PREFIXES = (
    "assum",
    "axiom",
    "conc",
    "cor",
    "defn",
    "exmp",
    "lem",
    "prin",
    "prop",
    "qst",
    "rem",
    "thm",
)
CONTEXT_PREFIXES = RESULT_PREFIXES
LABEL_RE = re.compile(r"\b(?:" + "|".join(CONTEXT_PREFIXES) + r"):[A-Za-z0-9_.-]+")
BLOCK_ID_RE = re.compile(r"(?mi)^\s*Original block id:\s*`?([^`\r\n]+?)`?[.,;:]?\s*$")
REFERENCE_RE = re.compile(r"\\(?:eqref|ref|autoref|cref|Cref|nameref)\{([^}]+)\}")
DECL_RE = re.compile(
    r"^\s*(?:(?:noncomputable|protected|private|local|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|axiom|structure|class|inductive)\s+"
    r"([A-Za-z0-9_'.]+)"
)

PART_I_SOURCES = (
    "1 - theoretical foundations/1_economics.tex",
    "1 - theoretical foundations/2_chapter_market_representations.tex",
    "1 - theoretical foundations/3_market_actions.tex",
    "1 - theoretical foundations/4_market_clearing.tex",
    "1 - theoretical foundations/5_stochastic_markets.tex",
)

CHAPTER_TITLES = {
    PART_I_SOURCES[0]: "Chapter 1 — Economics and Mathematical Formalism",
    PART_I_SOURCES[1]: "Chapter 2 — Market Representation",
    PART_I_SOURCES[2]: "Chapter 3 — Market Actions",
    PART_I_SOURCES[3]: "Chapter 4 — Market Clearing",
    PART_I_SOURCES[4]: "Chapter 5 — Stochastic Markets",
}

ENVIRONMENT_KINDS = {
    "assum": "assum",
    "assumption": "assum",
    "axiom": "axiom",
    "conc": "conc",
    "conclusion": "conc",
    "defn": "defn",
    "definition": "defn",
    "lem": "lem",
    "lemma": "lem",
    "prop": "prop",
    "proposition": "prop",
    "thm": "thm",
    "theorem": "thm",
    "cor": "cor",
    "corollary": "cor",
    "prin": "prin",
    "principle": "prin",
    "exmp": "exmp",
    "example": "exmp",
    "rem": "rem",
    "remark": "rem",
    "qst": "qst",
    "question": "qst",
}
BEGIN_ENV_RE = re.compile(
    r"\\begin\{(" + "|".join(map(re.escape, ENVIRONMENT_KINDS)) + r")\}"
    r"(?:\[([^\]]*)\])?"
)
HEADING_RE = re.compile(r"\\(section|subsection|subsubsection)\*?\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}")
PROOF_BEGIN_RE = re.compile(r"\s*(?:%[^\n]*\n\s*)*\\begin\{proof\}(?:\[[^\]]*\])?")

OBSOLETE_OR_OUT_OF_SCOPE_LABELS = {
    "cor:action-metrization",
    "cor:tuple-metrization",
    "prop:hausdorff-distance",
    "prop:index-augmented-hausdorff",
    "thm:tuple-space-metrization",
}

STATUS_PALETTE = {
    "verified": {
        "color": "#2f6f59",
        "label": "kernel checked",
        "description": "Every linked declaration has fresh transitive Lean kernel evidence, with no project-specific axioms or unfinished proofs. Statement alignment requires separate review.",
    },
    "external": {
        "color": "#74558d",
        "label": "external",
        "description": "A linked declaration depends transitively on a project-specific axiom.",
    },
    "commentary": {
        "color": "#6e6670",
        "label": "commentary",
        "description": "Recorded as framework commentary rather than a compiled declaration.",
    },
    "unknown": {
        "color": "#a34b52",
        "label": "unverified",
        "description": "Kernel evidence is missing, stale, unresolved, or contains an unfinished proof.",
    },
    "thesis-only": {
        "color": "#817676",
        "label": "thesis only",
        "description": "The thesis block is present in the explorer but has no linked Lean declaration yet.",
    },
    "incorrect-statement": {
        "color": "#a34b52", "label": "incorrect statement",
        "description": "A current-source mistake is documented; the linked valid lemmas do not prove the false clause.",
    },
    "needs-alignment": {
        "color": "#9b6428", "label": "needs alignment",
        "description": "A documented gap remains between the manuscript and its linked Lean statements.",
    },
    "needs-review": {
        "color": "#9b6428", "label": "needs review",
        "description": "The source changed after a recorded finding; its diagnosis needs review.",
    },
}

SECTION_PALETTE = {
    "foundations": "#8f1d2c",
    "market-representation": "#394f62",
    "market-actions": "#775f32",
    "market-clearing": "#7e3d45",
    "stochastic": "#65517a",
    "day-ahead": "#9b6428",
    "intraday": "#2f6b5e",
    "preliminary": "#4f5963",
    "other": "#6e6670",
}

SECTION_WORKFLOWS = {
    "foundations": "lean-foundations.yml",
    "market-representation": "lean-market-representation.yml",
    "market-actions": "lean-market-actions.yml",
    "market-clearing": "lean-market-clearing.yml",
    "stochastic": "lean-stochastic.yml",
    "day-ahead": "lean-day-ahead.yml",
    "intraday": "lean-intraday.yml",
    "preliminary": "lean-appendices.yml",
    "other": "lean-global.yml",
}


@dataclass
class DeclarationTrace:
    declaration: str | None
    kind: str | None
    module: str
    file: str
    line: int
    comment: str = ""
    full_name: str = ""


@dataclass
class ResultTrace:
    label: str
    traces: list[DeclarationTrace] = field(default_factory=list)


def write_json(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    content = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if path.is_file() and path.read_text(encoding="utf-8") == content:
        return
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(content)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(PROJECT_ROOT).with_suffix("").parts)


def section_for_module(module: str) -> str:
    # Module paths mirror the thesis since the 2026-10-21 reorganisation
    # (Thesis/{Foundations,DayAhead,Intraday,Appendices,Context}).
    if module.startswith("Thesis.Context."):
        return "foundations"
    if module.startswith("Thesis.Foundations.MarketRepresentation."):
        return "market-representation"
    if module.startswith("Thesis.Foundations.MarketActions."):
        return "market-actions"
    if module.startswith("Thesis.Foundations.MarketClearing."):
        return "market-clearing"
    if module.startswith("Thesis.Foundations.Stochastic."):
        return "stochastic"
    if module.startswith("Thesis.DayAhead."):
        return "day-ahead"
    if module.startswith("Thesis.Intraday."):
        return "intraday"
    if module.startswith("Thesis.Appendices."):
        return "preliminary"
    return "other"


def lean_files() -> list[Path]:
    files = [path for path in [PROJECT_ROOT / "Formalization.lean"] if path.exists()]
    for root in (THESIS_LEAN_ROOT,):
        if root.exists():
            # Sort on the POSIX string, not the Path: WindowsPath orders
            # case-insensitively, so a plain sorted() would emit declaration
            # lists in a different order on the author's machine and on CI.
            files.extend(sorted(root.rglob("*.lean"), key=Path.as_posix))
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
        marker = "/--" if "/--" in lines[index] else "/-!" if "/-!" in lines[index] else None
        if marker is None:
            index += 1
            continue
        start = index
        while index < len(lines) and "-/" not in lines[index]:
            index += 1
        end = min(index, len(lines) - 1)
        blocks.append((start + 1, end + 1, marker, "\n".join(lines[start : end + 1])))
        index = end + 1
    return blocks


def labels_from_original_label_clause(comment: str) -> list[str]:
    lines = comment.splitlines()
    labels: list[str] = []
    for index, line in enumerate(lines):
        if "Original label" not in line:
            continue
        clause = [line]
        for follow in lines[index + 1 : index + 6]:
            stripped = follow.strip()
            if not stripped or stripped.startswith(
                ("Informal statement", "Lean strategy", "External reference", "Thesis source")
            ):
                break
            clause.append(follow)
        labels.extend(LABEL_RE.findall("\n".join(clause)))
    return sorted(dict.fromkeys(labels))


def labels_for_comment(comment: str) -> list[str]:
    # Only an explicit audit annotation creates a bridge edge. Incidental
    # cross-references in explanatory prose must not masquerade as coverage.
    labels = audit_labels_in(comment)
    keys = [
        label
        for label in labels
        if label.split(":", 1)[0] in RESULT_PREFIXES and label not in OBSOLETE_OR_OUT_OF_SCOPE_LABELS
    ]
    keys.extend(BLOCK_ID_RE.findall(comment))
    return sorted(dict.fromkeys(keys))


def build_results() -> dict[str, ResultTrace]:
    results: dict[str, ResultTrace] = defaultdict(lambda: ResultTrace(label=""))
    inventory = build_lean_inventory(PROJECT_ROOT)
    for declaration in inventory.get("declarations", []):
        keys = list(declaration.get("thesisLabels", [])) + list(
            declaration.get("thesisEnvironmentIds", [])
        )
        keys = [
            str(key)
            for key in keys
            if str(key).startswith("source:")
            or str(key).split(":", 1)[0] in RESULT_PREFIXES
        ]
        if not keys:
            continue
        trace = DeclarationTrace(
            str(declaration["name"]),
            str(declaration["kind"]),
            str(declaration["module"]),
            str(declaration["source"]),
            int(declaration["line"]),
            str(declaration.get("docComment", "")),
            str(declaration["fullName"]),
        )
        for key_name in keys:
            if not results[key_name].label:
                results[key_name].label = key_name
            trace_key = (
                trace.declaration,
                trace.kind,
                trace.module,
                trace.file,
                trace.line,
            )
            existing = {
                (item.declaration, item.kind, item.module, item.file, item.line)
                for item in results[key_name].traces
            }
            if trace_key not in existing:
                results[key_name].traces.append(trace)
    return dict(sorted(results.items()))


def result_status(label: str, traces: list[DeclarationTrace],
                  statuses: dict[str, str] | None = None) -> str:
    if not traces:
        return "unknown"
    if all(trace.declaration is None for trace in traces):
        return "commentary"
    evidence = [(statuses or {}).get(trace.full_name, "unverified")
                for trace in traces if trace.declaration]
    if any(status in {"unverified", "unproved"} for status in evidence):
        return "unknown"
    if "external" in evidence:
        return "external"
    return "verified" if all(status == "kernel-checked" for status in evidence) else "unknown"


def primary_section(traces: list[DeclarationTrace]) -> str:
    for trace in traces:
        section = section_for_module(trace.module)
        if section != "other":
            return section
    return "other"


def latex_plain_text(value: str) -> str:
    text = re.sub(r"\\begin\{[^}]+\}(?:\[[^\]]*\])?|\\end\{[^}]+\}", " ", value)
    text = text.replace("\\\\", "; ").replace("&", " ")
    text = re.sub(r"\\(?:cite|citep|citet|index|label)\{[^}]*\}", "", text)
    symbol_commands = {
        r"\mathbb{R}": "ℝ",
        r"\mathbb{N}": "ℕ",
        r"\bigsqcup": "disjoint union",
        r"\bigcup": "union",
        r"\longrightarrow": "→",
        r"\mapsto": "↦",
        r"\rightarrow": "→",
        r"\to": "→",
        r"\leq": "≤",
        r"\geq": "≥",
        r"\neq": "≠",
        r"\preceq": "≤",
        r"\prec": "<",
        r"\subseteq": "⊆",
        r"\subset": "⊂",
        r"\setminus": "∖",
        r"\cap": "∩",
        r"\cup": "∪",
        r"\times": "×",
        r"\oplus": "⊕",
        r"\simeq": "≃",
        r"\sum": "∑",
        r"\infty": "∞",
        r"\in": "∈",
        r"\backslash": "∖",
        r"\Pi": "Π",
        r"\Gamma": "Γ",
        r"\Omega": "Ω",
        r"\Sigma": "Σ",
        r"\alpha": "α",
        r"\beta": "β",
        r"\chi": "χ",
        r"\delta": "δ",
        r"\eta": "η",
        r"\kappa": "κ",
        r"\lambda": "λ",
        r"\pi": "π",
        r"\tau": "τ",
        r"\varphi": "φ",
        r"\varsigma": "ς",
        r"\dots": "…",
    }
    for command, replacement in sorted(
        symbol_commands.items(), key=lambda item: len(item[0]), reverse=True
    ):
        text = re.sub(re.escape(command) + r"(?![A-Za-z])", replacement, text)
    text = re.sub(
        r"\\(?:emph|textbf|textit|text|nameref|mathscr|mathcal|mathsf|mathrm|mathbf|bm|operatorname)\{([^{}]*)\}",
        r"\1",
        text,
    )
    text = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?", "", text)
    text = text.replace("~", " ").replace("{", "").replace("}", "").replace("$", "")
    text = text.replace("\\", "")
    return re.sub(r"\s+", " ", text).strip(" ,.;:-")


def humanize_label(label: str) -> str:
    if label.startswith("source:"):
        source, line, kind, _ = label.removeprefix("source:").rsplit(":", 3)
        return f"{ENVIRONMENT_KINDS.get(kind, kind).capitalize()} in {Path(source).stem.replace('_', ' ')} (line {line})"
    slug = label.split(":", 1)[-1]
    words = re.split(r"[-_]+", slug)
    small = {"and", "as", "by", "for", "from", "in", "is", "of", "on", "to", "with"}
    output: list[str] = []
    for index, word in enumerate(words):
        if not word:
            continue
        if any(char.isupper() for char in word[1:]) or word.isupper():
            output.append(word)
        elif index and word.lower() in small:
            output.append(word.lower())
        else:
            output.append(word[0].upper() + word[1:])
    return " ".join(output) or label


def clean_environment_body(raw: str) -> str:
    body = re.sub(r"^\\begin\{[^}]+\}(?:\[[^\]]*\])?", "", raw.strip())
    body = re.sub(r"\\end\{[^}]+\}\s*$", "", body)
    body = re.sub(r"\\label\{[^}]+\}", "", body)
    body = re.sub(r"\\index\{[^}]+\}", "", body)
    return body.strip()


def references_in(text: str) -> list[str]:
    return list(dict.fromkeys(REFERENCE_RE.findall(text)))


def proof_steps(proof: str) -> list[dict[str, object]]:
    normalized = proof.strip()
    if not normalized:
        return []
    paragraphs = [part.strip() for part in re.split(r"\n\s*\n+", normalized) if part.strip()]
    chunks: list[str] = []
    for paragraph in paragraphs:
        if len(paragraph) <= 520 or "\\begin{" in paragraph:
            chunks.append(paragraph)
            continue
        sentences = [part.strip() for part in re.split(r"(?<=[.!?])\s+(?=[A-Z\\])", paragraph) if part.strip()]
        current = ""
        for sentence in sentences:
            candidate = f"{current} {sentence}".strip()
            if current and len(candidate) > 420:
                chunks.append(current)
                current = sentence
            else:
                current = candidate
        if current:
            chunks.append(current)
    merged: list[str] = []
    for chunk in chunks:
        if merged and len(chunk) < 90:
            merged[-1] = f"{merged[-1]} {chunk}"
        else:
            merged.append(chunk)
    return [
        {
            "id": f"step-{index}",
            "index": index,
            "title": f"Proof step {index}",
            "text": chunk,
            "references": references_in(chunk),
        }
        for index, chunk in enumerate(merged, start=1)
    ]


def last_heading(text: str, end: int) -> str:
    headings = list(HEADING_RE.finditer(text, 0, end))
    if not headings:
        return "Introduction"
    return latex_plain_text(headings[-1].group(2)) or "Introduction"


def extract_thesis_metadata(thesis_root: Path) -> dict[str, object]:
    inventory = build_thesis_inventory(thesis_root, OUTPUT_ROOT / "thesis-svg")
    results: list[dict[str, object]] = []
    for record in inventory.get("environments", []):
        identifier = str(record.get("label") or record["id"])
        proof_record = record.get("proof") or None
        proof_text = str((proof_record or {}).get("text", ""))
        chapter = str(record.get("chapter") or record.get("part") or "Thesis")
        section = str(
            record.get("subsubsection")
            or record.get("subsection")
            or record.get("section")
            or chapter
        )
        results.append(
            {
                "id": identifier,
                "label": record.get("label"),
                "kind": str(record["environment"]),
                "displayKind": str(record["kind"]),
                "title": str(record["title"]),
                "part": str(record.get("part", "")),
                "appendix": bool(record.get("appendix", False)),
                "chapter": chapter,
                "section": section,
                "source": str(record["source"]),
                "line": int(record["line"]),
                "statement": str(record.get("statement", "")),
                "statementSha256": hashlib.sha256(record["rawEnvironment"].encode("utf-8")).hexdigest(),
                "proofSha256": hashlib.sha256((proof_record or {}).get("rawEnvironment", "").encode("utf-8")).hexdigest(),
                "sourceFileSha256": record["sourceFileSha256"],
                "references": list(record.get("references", [])),
                "proof": {
                    "line": (proof_record or {}).get("line"),
                    "text": proof_text,
                    "references": list((proof_record or {}).get("references", [])),
                    "steps": proof_steps(proof_text),
                }
                if proof_record
                else None,
                "svg": record.get("svg"),
                "proofSvg": (proof_record or {}).get("svg"),
            }
        )
    return {
        "schemaVersion": 2,
        "sourceRoot": inventory["sourceRoot"],
        "sourceHashes": {source: hashlib.sha256((thesis_root / source).read_bytes()).hexdigest()
                         for source in ["master.tex"] + [r["source"] for r in inventory["sources"]]},
        "scope": "all custom theorem-style environments in sources selected by master.tex",
        "summary": inventory.get("summary", {}),
        "sources": inventory.get("sources", []),
        "results": results,
    }


def load_alignment_findings(metadata: dict[str, object]) -> dict[str, dict[str, object]]:
    path = BRIDGE_DATA_ROOT / "alignment-findings.json"
    if not path.is_file():
        return {}
    by_id = {str(record["id"]): record for record in metadata.get("results", [])}
    findings = json.loads(path.read_text(encoding="utf-8")).get("byLabel", {})
    result = {}
    for label, finding in findings.items():
        record = by_id.get(label)
        if record is None:
            continue
        matches = (record.get("statementSha256") == finding["statementSha256"] and
                   record.get("proofSha256") == finding.get("proofSha256"))
        result[label] = {
            **finding, "id": finding["issue"], "label": label,
            "status": finding["status"] if matches else "needs-review",
            "kind": finding.get("kind", finding["status"]) if matches else "needs-review",
            "problem": finding["summary"], "leanVerified": False,
            "fix": None,
        }
    return result


def load_manifest() -> dict[str, dict[str, object]]:
    path = OUTPUT_ROOT / "thesis-svg" / "manifest.json"
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    return {str(key): value for key, value in payload.items() if isinstance(value, dict)}


def clean_comment(comment: str) -> str:
    text = comment.replace("/--", "").replace("/-!", "").replace("-/", "")
    lines = []
    for line in text.splitlines():
        stripped = line.strip().lstrip("*").strip()
        if not stripped or stripped.startswith(
            ("Thesis source:", "Original label:", "Original labels:", "Original block id:")
        ):
            continue
        lines.append(stripped.replace("`", ""))
    return re.sub(r"\s+", " ", " ".join(lines)).strip()


def comment_clause(comment: str, heading: str, stop_headings: tuple[str, ...]) -> str:
    text = clean_comment(comment)
    stop = "|".join(re.escape(value) for value in stop_headings)
    match = re.search(
        rf"{heading}\s*:\s*(.*?)(?=(?:{stop})\s*:|$)",
        text,
        flags=re.IGNORECASE,
    )
    return re.sub(r"\s+", " ", match.group(1)).strip() if match else ""


def comment_explanation(comment: str) -> str:
    return comment_clause(
        comment,
        r"Informal statement",
        (
            "Lean strategy / thesis relation note",
            "Lean strategy / thesis strategy note",
            "Lean strategy",
            "External reference",
        ),
    )


def comment_strategy(comment: str) -> str:
    return comment_clause(
        comment,
        r"Lean strategy(?:\s*/\s*thesis (?:relation|strategy) note)?",
        ("Informal statement", "External reference"),
    )


def declaration_payload(trace: DeclarationTrace) -> dict[str, object]:
    summary = clean_comment(trace.comment)
    explanation = latex_plain_text(comment_explanation(trace.comment))
    strategy = latex_plain_text(comment_strategy(trace.comment))
    if not explanation:
        explanation = latex_plain_text(summary[:700])
    if not strategy and trace.declaration:
        strategy = (
            f"The compiled {trace.kind or 'declaration'} `{trace.module}.{trace.declaration}` "
            "is the Lean representation of this thesis block; its source records the proof term "
            "and any hypotheses made explicit by elaboration."
        )
    return {
        "declaration": trace.declaration,
        "fullName": trace.full_name,
        "declarationKind": trace.kind,
        "name": trace.declaration,
        "kind": trace.kind,
        "module": trace.module,
        "file": trace.file,
        "source": trace.file,
        "line": trace.line,
        "informal": latex_plain_text(summary[:700]),
        "explanation": explanation[:1200],
        "strategy": strategy[:1600],
    }


def identifier_tokens(value: str) -> set[str]:
    split_camel = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", value)
    aliases = {
        "minimal": "minimum",
        "sorting": "sort",
        "sorted": "sort",
        "measurability": "measurable",
        "metrisation": "metric",
        "metrization": "metric",
    }
    return {
        aliases.get(token, token)
        for token in re.split(r"[^A-Za-z0-9]+", split_camel.lower())
        if token and token not in {"a", "an", "and", "by", "for", "is", "of", "on", "the", "to"}
    }


REPRESENTATIVE_DECLARATION_OVERRIDES = {
    "lem:disintegration-lemma": "atomicDecomposition_disintegration_full",
    "thm:integer-measures-tuples-homeomorphic": "matchingIntegerMeasuresHomeomorph",
    "lem:measurable-enumeration": "measurableEnumeration_prokhorovBorel",
    "rem:uniform-permutation-sampling": "uniformPermutationMeasure_singleton_eq_inv_ncard",
    "prop:separation-continuous": "continuous_separationOperator_supMetric",
    "thm:equilibrium-quantity-measurable": "measurable_equilibriumQuantity_cumulativeDomain",
    "cor:sorted-operations-measurable": "measurable_sortedAdd_productBorel",
    "rem:void-modification": "sortedModify_void_eq_sort",
    "thm:tuple-space-properties": "fixedLength_edist_eq_coordinateEDistSup_of_lt_one",
    "exmp:sort-discont": "euclidean_sortingRule_not_continuous",
    "thm:minimal-sorting-measurable": "measurable_minimumSortingRule_toSortedTuple",
    "prop:truncated-metric-equivalent-topology": "extended_truncation_same_topology",
    "prop:transitive-closure-finite": "finite_closure_eq_diagonal_union_powers",
    "cor:connected-segments-totally-ordered-by-arrival-index": "segmentArrivalLE_isLinearOrder",
    "exmp:partial-order-static-market": "taggedStaticPriority_isPartialOrder",
    "exmp:total-order-static-market": "staticTotalPriority_isLinearOrder",
    "exmp:total-order-dynamic-market": "dynamicTotalPriority_isLinearOrder",
    "exmp:completing-order-agent-based-static-market": "restrictedAgentOrderQuotientEquiv",
    "lem:rectangular-simple-dense-finite": "finite_rectangle_expansion_dense_simple_finite",
    "thm:rectangular-simple-dense-lebesgue": "finite_rectangle_expansion_dense_simple_volume",
    "defn:actions": "MarketAction",
    "prop:sim-equivalence": "connectivitySetoid",
    "source:2 - day-ahead/3_functional_data_analysis.tex:104:rem:5":
        "compact_selfAdjoint_ordered_rankOne_expansion",
}

NODE_NARRATIVE_OVERRIDES = {
    "cor:grothendieck-vectorization-inner-product-space": {
        "strategy": "Construct the actual quotient inner product and its linear isometry to the span. Extend that map to both completions and prove the extension agrees with T on embedded points. Prove the cone embedding injective, identify its closure isometrically in the completion, and apply the unique projection theorem to the resulting nonempty closed cone. FA-014 records these explicit map-level bridges.",
    },
    "prop:finite-hausdorff-isolative-iff-isolative": {
        "strategy": "Use singleton sets to recover exactly the base isolation property. The separate following prose claim is proved by ShrinkingPairs: pair distances are 1/(n+1), distinct components remain separated, and the complete discrete base has an actual Hausdorff isometry between finite and compact subsets. Thus finite-subset completeness need not imply uniform isolation (FA-015).",
    },
    "lem:disintegration-lemma": {
        "strategy": (
            "Integer rounding removes the Prokhorov additive error below radius one. "
            "Separated atom balls preserve each block's mass and are disjoint. Positive "
            "multiplicities make each block nonempty; a finite supremum gives its strict "
            "maximum-distance bound. Equal total mass proves exact coverage of all "
            "nearby atoms. The full theorem includes all four source clauses."
        ),
    },
    "thm:integer-measures-tuples-homeomorphic": {
        "strategy": (
            "The counting-measure bijection and its inverse continuity estimates form "
            "an actual Homeomorph between the current bounded matching-metric quotient "
            "and the Prokhorov finite-integer-measure carrier. The matching metric shares "
            "the proved orbit metric's uniformity, so both epsilon arguments apply."
        ),
    },
    "lem:measurable-enumeration": {
        "strategy": (
            "Sort using a measurable real embedding of the standard Borel base. "
            "The sorted fixed-length layers inject measurably into counting measures, "
            "yielding a measurable selection. The explicit Prokhorov Borel bridge "
            "gives exactly the metric-domain statement and preserves the counting measure."
        ),
    },
    "rem:uniform-permutation-sampling": {
        "strategy": (
            "Reindexing the finite permutation sum proves equal singleton masses on "
            "the actual tuple orbit. All mass lies in that finite class; summing its "
            "singleton masses gives probability exactly 1 / class size. Repeated entries "
            "and the empty tuple are included, and the counting measure is preserved."
        ),
    },
    "thm:point-process-tuple": {
        "strategy": (
            "Measurable permutation averaging constructs the stated Markov kernel. "
            "Its evaluation formula has the factorial normalization, and an enumeration's "
            "length equals the point measure's total mass. DA-048 is a minor proof-wording "
            "error: at most one length-layer term is nonzero, since for the empty event "
            "every term is zero. The kernel theorem itself remains valid."
        ),
    },
    "prop:separation-continuous": {
        "explanation": "Each component separation is continuous, and the full separation map is continuous for the unweighted supremum metric on all component tuple spaces.",
        "strategy": (
            "Below radius one, tuple length and every entry's component tag stabilize. "
            "The same radius bounds every separated component. Choosing a smaller "
            "radius then bounds their supremum strictly below the requested tolerance. "
            "This proves the exact supremum topology even for arbitrary index families; "
            "ordinary product continuity alone would not establish it."
        ),
    },
    "thm:equilibrium-quantity-measurable": {
        "explanation": "The maximum price-compatible volume is a Borel-measurable scalar on the stated domain of sorted cumulative quantities and sorted prices of matching lengths.",
        "strategy": (
            "Feasible index sets give a countable measurable partition. On each cell, "
            "continuous coordinate evaluations and finite minima/maxima give the volume. "
            "The empty case equals zero; every nonempty case attains the maximum of "
            "exactly its candidate volumes. The final restriction includes sorted "
            "quantity tuples and the Borel sigma-algebra of the product/subspace metric. "
            "This scalar result supplies no allocation, settlement price, or residual-state map."
        ),
    },
    "rem:void-modification": {
        "explanation": "A modification whose indices miss the input domain leaves the unsorted tuple unchanged. Sorting that output returns the chosen sorting of the input.",
        "strategy": (
            "The general proof allows nonempty payloads with out-of-domain indices. "
            "DA-047 flags the final sentence: global idempotence alone does not fix "
            "every sorted input under a partial order. A checked equality-order "
            "Boolean example disproves it even for an empty payload. The corrected "
            "fixed-input and sorting-image versions are proved separately."
        ),
    },
    "cor:sorted-operations-measurable": {
        "strategy": (
            "Compose each continuous primitive operation with the assumed measurable "
            "sorting rule. Separability of tuple space identifies the product of "
            "the factor Borel sigma-algebras with the product topology's Borel "
            "sigma-algebra. All three conclusions retain the sorted-subspace codomain."
        ),
    },
    "defn:pairing": {
        "strategy": "The increasing finite-set enumeration has the exact cardinality and range. Each entry is proved to be the least member left after removing all earlier entries, so it satisfies the source's repeated-minimum recursion.",
    },
    "thm:tuple-space-properties": {
        "strategy": (
            "Below radius one, matching graph points must have the same index. "
            "This fixes the length and gives the maximum coordinate distance. "
            "Cauchy sequences eventually stay in one length layer; coordinate limits "
            "prove completeness. Graph embedding and metric subspaces give separability. "
            "DA-046 flags the proof's false assertion that the entry value determines "
            "the indexed graph point: repeated values give a checked counterexample. "
            "The valid proof uses uniqueness at a fixed index instead."
        ),
    },
    "exmp:sort-discont": {
        "explanation": "Lexicographic sorting on tuples over the Euclidean plane is discontinuous, and the sorted subspace is incomplete.",
        "strategy": (
            "Embed the displayed reciprocal sequence in the actual tuple Hausdorff "
            "space over the Euclidean plane. Every term is sorted, its limit is not, "
            "and the sorted limit is explicitly the reversed pair. Every sorting rule "
            "fixes the sequence, so uniqueness of limits contradicts continuity. "
            "The same sequence proves non-closedness and incompleteness of the sorted subspace."
        ),
    },
    "thm:minimal-sorting-measurable": {
        "strategy": (
            "On each finite length layer, Borel order tests give measurable connectivity "
            "and greedy-choice cells. Finitely many realized branch codes cover that "
            "layer, and the actual minimum rule equals a fixed continuous permutation "
            "on each cell. Measurable pasting over cells and then length layers proves "
            "the result. The final bridge uses the sorted subtype's subspace Borel sigma-algebra."
        ),
    },
    "prop:transitive-closure-finite": {
        "explanation": "For any relation on a finite set, its reflexive transitive closure equals the diagonal union the relation powers from one to the cardinality minus one.",
        "strategy": (
            "Delete repeated vertices from a forward relation chain. The resulting "
            "chain has distinct vertices, so its edge count is at most |X|-1. "
            "Relation powers use the manuscript's composition convention, and Lean "
            "proves the literal set equality. No symmetry or comparability hypothesis "
            "is assumed; the older tuple-comparability theorem remains a special case."
        ),
    },
    "defn:reflexive-transitive-closure": {
        "strategy": "The inductive closure used in tuple connectivity is identified with the literal diagonal union of positive relation powers. Each successor power composes the previous power with one forward edge.",
    },
    "cor:connected-segments-totally-ordered-by-arrival-index": {
        "strategy": "The first-arrival index is injective. Pulling back the natural order proves reflexivity, transitivity, antisymmetry, and totality for exactly the displayed segment relation.",
    },
    "thm:distinct-properties": {
        "explanation": "The indexed finite-configuration space inherits separability and completeness independently from the base space, using the stated sum distance on indexed points.",
        "strategy": (
            "Separability uses finite configurations supported on a countable dense "
            "payload set. For completeness, Hausdorff distance below one fixes the "
            "finite index set. The stronger matching estimate at every smaller "
            "radius makes each coordinate sequence Cauchy; their limits give the "
            "finite configuration limit. Neither clause assumes the other base property."
        ),
    },
    "prop:finite-hausdorff-isolative": {
        "strategy": "Choose a point in the symmetric difference. Every point of the other set is at least the supplied isolation bound away, so its Hausdorff distance has that same lower bound. The proof retains the exact bound and includes empty sets.",
    },
    "rem:hausdorff-infinite-values": {
        "strategy": "Finite subsets are bounded. Their Hausdorff distance is finite when both are nonempty; the empty-set convention gives the other cases. Lean explicitly constructs the ordinary metric on the nonempty finite-subset carrier without changing its topology or uniformity.",
    },
    "exmp:partial-order-static-market": {
        "strategy": (
            "The displayed side-specific price and quantity comparisons satisfy every "
            "linear-order axiom. Requiring the same direction gives a partial order "
            "on tagged orders, and comparability is proved equivalent to matching sides."
        ),
    },
    "exmp:total-order-static-market": {
        "strategy": "Buy-before-sell comparison combines the side-specific priorities. Reflexivity, transitivity, antisymmetry, and totality are all proved for the exact displayed relation.",
    },
    "exmp:total-order-dynamic-market": {
        "strategy": "The exact price-time-quantity relation has all linear-order axioms, and ordering buys before sells preserves them. This completes the earlier comparability-only proof.",
    },
    "exmp:completing-order-agent-based-static-market": {
        "explanation": "Forgetting the agent identifies constrained orders precisely by their visible direction, price, and quantity. The quotient carries the inherited total priority.",
        "strategy": (
            "Use the actual agent-dependent price and quantity subtypes. The kernel "
            "quotient is equivalent to the union of each agent's admissible product, "
            "with the same agent witnessing both constraints. Injectivity of this "
            "equivalence transfers every linear-order axiom. Nearby prose claiming "
            "that non-atomic marginals alone exclude ties is separately flagged as DA-045."
        ),
    },
    "exmp:agent-adm-dyn": {
        "strategy": (
            "Membership at the actual submission time implies membership in the "
            "separate unions of price and quantity sets over all times. Both this "
            "intermediate inclusion and its embedding into unrestricted coordinates "
            "are injective, and their composition is the original coordinate map."
        ),
    },
    "lem:rectangular-simple-dense-finite": {
        "explanation": "Finite sums of interval-product indicators are dense among Hilbert-valued simple functions for every finite Borel measure.",
        "strategy": (
            "Approximate measurable cells in the algebra generated by rational boxes. "
            "A separate span induction expands every algebra-cell indicator into a "
            "finite sum of actual rectangle indicators, using intersections, complements, "
            "and inclusion-exclusion. The resulting approximation has the stated L2 error."
        ),
    },
    "thm:rectangular-simple-dense-lebesgue": {
        "explanation": "Every square-integrable Hilbert-valued simple function on Euclidean space can be approximated by literal finite rectangular sums.",
        "strategy": (
            "Choose a bounded box with small L2 tail, approximate for restricted finite "
            "Lebesgue measure, and cut the approximation off on the box. The triangle "
            "inequality controls the error. The proved finite rectangle expansion "
            "removes the remaining Boolean-algebra representation."
        ),
    },
    "prop:admissible-parametrisations-cone": {
        "explanation": "Graph-admissible actual functions form a convex cone and determine unique price curves on their volume ranges.",
        "strategy": (
            "Nonnegative monotone combinations preserve fiber constancy. The continuous "
            "volume range is the endpoint interval; the fiberwise decoder gives an "
            "admissible parametrisation and a unique actual graph. Measurability and "
            "boundedness prove Euclidean L2 membership, and the induced L2 classes "
            "also form a convex cone."
        ),
    },
    "defn:arborescence": {
        "strategy": (
            "The structure records looplessness and a unique positive-edge root path "
            "to every other vertex. Lean proves these conditions exclude all positive "
            "cycles by appending a hypothetical cycle to a root path."
        ),
    },
    "defn:decision-tree": {
        "strategy": (
            "Finite vertices, decisions choosing actual children, and leaf labels define "
            "the tree. Every edge increases root depth, so recursion reaches a leaf "
            "before exceeding the finite maximum depth. Reflexive reachability includes "
            "the zero-edge singleton case; the source's Visits formula still needs "
            "that convention, as recorded in DA-030."
        ),
    },
    "defn:frechet-derivative": {
        "strategy": (
            "The bounded-linear derivative is expressed by HasFDerivAt. Lean proves "
            "equivalence with the source's norm-quotient limit and proves uniqueness "
            "of the derivative, making the displayed derivative map well defined."
        ),
    },
    "source:2 - day-ahead/3_functional_data_analysis.tex:104:rem:5": {
        "explanation": (
            "The nonzero eigenvalues can be ordered by decreasing magnitude, and "
            "adjoining a kernel basis completes the closed-range eigenbasis. "
            "An infinite Hilbert basis has dense span, not necessarily full algebraic span."
        ),
        "strategy": (
            "Operator-norm convergence makes every positive eigenvalue superlevel "
            "set finite. Finite predecessor counts then give an ordered natural-number "
            "index set. A Hilbert-basis extension is proved to add exactly a dense "
            "orthonormal family in the kernel. A vector with coordinates 2 to the "
            "power minus n proves that algebraic span can be proper."
        ),
    },
    "defn:covariance-operator": {
        "strategy": (
            "The covariance is the Bochner integral of centered rank-one operators. "
            "Square integrability ensures this integral exists. Its symmetry, positivity, "
            "and compactness are proved; compactness uses the closed convex set of "
            "compact operators. Finite orthogonal projections also prove both directions "
            "of the finite-rank operator-norm approximation criterion."
        ),
    },
    "prop:graph-defines": {
        "explanation": "A set-coded function equals its graph of Kuratowski ordered pairs.",
        "strategy": (
            "Lean evaluates the unique output of each input in the function relation, "
            "constructs the graph inside Mathlib's ZFSet universe, and proves equality "
            "with the original relation by membership extensionality. The typed "
            "graph-injectivity theorem is also retained."
        ),
    },
    "prop:empty-domain-function": {
        "explanation": (
            "All set-coded functions with empty domain are the same empty set, "
            "including when their codomains differ."
        ),
        "strategy": (
            "Each function relation is contained in the empty Cartesian product, "
            "so it has no elements and equals the empty ZFC set. Transitivity gives "
            "literal equality across different codomains."
        ),
    },
    "prin:finitism": {
        "explanation": (
            "Every bounded time interval has finitely many acting agents and "
            "finitely many action occurrences for each agent."
        ),
        "strategy": (
            "An event history records each occurrence separately from its action "
            "payload. The model's two finiteness assumptions are quantified over "
            "every bounded interval and proved equivalent to finitely many total "
            "events in each such interval. Possible action types remain unrestricted."
        ),
    },
    "defn:actions": {
        "explanation": (
            "An action is a disjoint-union element consisting of a primitive "
            "operation label and a payload admissible for that operation."
        ),
        "strategy": (
            "Lean represents the thesis's finite dependent disjoint union over "
            "the three operation labels as an inductive type with one constructor "
            "per primitive action. Each payload is therefore paired with the "
            "correct operation by construction."
        ),
    },
    "prop:sim-equivalence": {
        "explanation": (
            "The connectivity relation on tuple indices is an equivalence relation."
        ),
        "strategy": (
            "Lean proves reflexivity, symmetry, and transitivity for connectivity "
            "by finite chains of immediately comparable indices, then packages "
            "those three results as a Setoid."
        ),
    },
    "thm:analytic-properties-actions": {
        "explanation": (
            "Lean verifies the thesis's three analytic claims: concatenation, "
            "cancellation, and modification are continuous for the explicit "
            "extended-metric topologies on tuple and action data."
        ),
        "strategy": (
            "The proofs follow the thesis's local-stabilisation argument. Below "
            "radius 1, tuple lengths and natural-index sets stabilise; fixed-layer "
            "coordinate estimates then make concatenation nonexpansive, cancellation "
            "a reindexing, and modification a modified-or-unmodified coordinate split."
        ),
    },
}

ZFC_STRATEGIES = {
    "axiom:existence": "The empty ZFC set witnesses existence in Mathlib's ZFSet universe.",
    "axiom:extensionality": "Extensional equality in ZFSet identifies sets with identical membership.",
    "axiom:scheme-of-comprehension": (
        "Separation constructs a ZFSet object with exactly the restricted membership "
        "predicate; formula parameters are absorbed in that predicate."
    ),
    "axiom:foundation": (
        "Mathlib constructs well-founded ZFSet membership and proves regularity. "
        "Lean then derives the source's exact disjoint-element condition."
    ),
    "axiom:pairing": "The pair is a ZFSet object containing exactly the two supplied sets.",
    "axiom:union": (
        "The union is a ZFSet object whose elements are exactly the elements of "
        "members of the supplied family."
    ),
    "axiom:replacement": (
        "Lean selects the uniquely specified outputs and constructs their range "
        "as a ZFSet in the same universe, proving the source's membership formula."
    ),
    "axiom:infinity": (
        "The von Neumann omega set contains the empty set and is closed under "
        "the literal set successor x union {x}."
    ),
    "axiom:power-set": (
        "Mathlib's ZFSet powerset is an object of the same set universe and "
        "contains exactly the subsets of the original set."
    ),
    "axiom:choice": (
        "Lean's standard classical choice constructs a set-coded function on "
        "the family with codomain its union, and proves that every selected "
        "value belongs to its argument set."
    ),
}
for _label, _strategy in ZFC_STRATEGIES.items():
    NODE_NARRATIVE_OVERRIDES.setdefault(_label, {})["strategy"] = _strategy


def representative_declaration(
    node_id: str, declarations: list[dict[str, object]]
) -> dict[str, object] | None:
    if not declarations:
        return None
    preferred_name = REPRESENTATIVE_DECLARATION_OVERRIDES.get(node_id)
    if preferred_name:
        preferred = next(
            (
                record
                for record in declarations
                if str(record.get("declaration", "")) == preferred_name
            ),
            None,
        )
        if preferred is not None:
            return preferred
    prefix = node_id.split(":", 1)[0]
    expected_kinds = {
        "defn": {"def", "abbrev", "structure", "class", "inductive"},
        "axiom": {"axiom", "theorem"},
        "prin": {"def", "structure", "theorem"},
        "rem": {"def", "theorem", "lemma"},
        "exmp": {"def", "theorem", "lemma"},
    }.get(prefix, {"theorem", "lemma"})
    label_tokens = identifier_tokens(node_id.split(":", 1)[-1])

    def score(
        index_and_record: tuple[int, dict[str, object]]
    ) -> tuple[int, int, int]:
        index, record = index_and_record
        name_tokens = identifier_tokens(str(record.get("declaration", "")))
        overlap = len(label_tokens & name_tokens)
        # Definition nodes should explain the construction itself even when a
        # nearby theorem happens to share one more label token.
        expected_kind_bonus = 20 if prefix == "defn" else 8
        kind_bonus = (
            expected_kind_bonus
            if str(record.get("kind", "")) in expected_kinds
            else 0
        )
        explanation_bonus = 3 if record.get("explanation") else 0
        strategy_bonus = 1 if record.get("strategy") else 0
        base = overlap * 10 + kind_bonus + explanation_bonus + strategy_bonus
        # Prefer the compact, primary declaration over a longer generated
        # helper when their semantic scores are otherwise tied; then preserve
        # source order for deterministic output.
        excess_tokens = len(name_tokens - label_tokens)
        return base, -excess_tokens, -index

    return max(enumerate(declarations), key=score)[1]


def concise_narrative(value: str, limit: int = 1000) -> str:
    text = re.sub(r"\s+", " ", value).strip()
    if len(text) <= limit:
        return text
    prefix = text[:limit]
    sentence_end = max(prefix.rfind(". "), prefix.rfind("; "), prefix.rfind(": "))
    if sentence_end >= limit // 2:
        prefix = prefix[: sentence_end + 1]
    return prefix.rstrip(" ,;:") + "..."


def bridge_matches(
    node_id: str,
    step: dict[str, object],
    nodes_by_id: dict[str, dict[str, object]],
    is_final: bool,
) -> list[dict[str, str]]:
    matches: list[dict[str, str]] = []
    for reference in step.get("references", []):
        target = nodes_by_id.get(str(reference))
        declaration = next((item for item in target.get("lean", []) if item.get("declaration")), None) if target else None
        if declaration:
            matches.append(
                {
                    "nodeId": str(reference),
                    "declaration": str(declaration["declaration"]),
                    "matchKind": "uses-reference",
                }
            )
    current = nodes_by_id.get(node_id, {})
    own = next((item for item in current.get("lean", []) if item.get("declaration")), None)
    if own and (not matches or is_final):
        matches.append(
            {
                "nodeId": node_id,
                "declaration": str(own["declaration"]),
                "matchKind": "implements-result",
            }
        )
    return matches


def load_overrides() -> dict[str, object]:
    if not PROOF_OVERRIDES_PATH.exists():
        return {}
    payload = json.loads(PROOF_OVERRIDES_PATH.read_text(encoding="utf-8"))
    mappings = payload.get("mappings", {})
    return mappings if isinstance(mappings, dict) else {}


def make_summary(nodes: list[dict[str, object]], edges: list[dict[str, str]]) -> dict[str, int]:
    summary = {
        "nodes": len(nodes),
        "edges": len(edges),
        "mappedToLean": sum(bool(node["mappedToLean"]) for node in nodes),
        "renderedThesisSvgs": sum(bool((node.get("thesisSvg") or {}).get("svg")) for node in nodes),
        "renderedThesisProofSvgs": sum(bool((node.get("thesisProof") or {}).get("svg")) for node in nodes),
        "thesisIssues": sum(bool(node.get("thesisIssue")) for node in nodes),
    }
    for status in STATUS_PALETTE:
        summary[status.replace("-", "_")] = sum(node["status"] == status for node in nodes)
    return summary


def build_bridge_payload(
    result_records: list[dict[str, object]],
    metadata: dict[str, object],
    fixes: dict[str, object],
) -> dict[str, object]:
    reviews = load_clause_reviews(PROJECT_ROOT, metadata.get("results", []))
    formal_by_id = {str(record["label"]): record for record in result_records}
    thesis_by_id = {str(record["id"]): record for record in metadata.get("results", [])}
    fixes_by_label = {
        str(label): issue
        for label, issue in (fixes.get("byLabel", {}) or {}).items()
        if isinstance(issue, dict)
    }
    fixes_by_label.update(load_alignment_findings(metadata))
    node_ids = sorted(set(formal_by_id) | set(thesis_by_id))
    nodes: list[dict[str, object]] = []

    for order, node_id in enumerate(node_ids):
        formal = formal_by_id.get(node_id)
        thesis = thesis_by_id.get(node_id)
        thesis_issue = fixes_by_label.get(node_id)
        # The scraper only attaches renders with matching source fingerprints.
        svg = (thesis or {}).get("svg") or {}
        declarations = list(formal["declarations"]) if formal else []
        title = str(thesis["title"]) if thesis else humanize_label(node_id)
        source = str(thesis["source"]) if thesis else str(svg.get("source", ""))
        chapter = (
            str(thesis["chapter"])
            if thesis
            else CHAPTER_TITLES.get(source, str(formal["section"] if formal else "Other"))
        )
        section = str(thesis["section"]) if thesis else chapter
        statement_svg = None
        if svg.get("path"):
            statement_svg = {
                "svg": svg["path"],
                "source": source or svg.get("source", ""),
                "line": thesis.get("line") if thesis else svg.get("line"),
                "repoPath": svg.get("repoPath"),
            }
        proof = thesis.get("proof") if thesis else None
        proof_svg = (thesis or {}).get("proofSvg")
        thesis_proof = None
        if proof or proof_svg:
            thesis_proof = {
                "svg": proof_svg,
                "source": source or svg.get("source", ""),
                "line": (proof or {}).get("line") or svg.get("proofLine"),
                "text": (proof or {}).get("text", ""),
                "references": (proof or {}).get("references", []),
            }
        representative = representative_declaration(node_id, declarations)
        narrative_override = NODE_NARRATIVE_OVERRIDES.get(node_id, {})
        explanation = str(
            narrative_override.get(
                "explanation", (representative or {}).get("explanation", "")
            )
        )
        if not explanation:
            explanation = next(
                (str(item.get("explanation", "")) for item in declarations if item.get("explanation")),
                "",
            )
        if not explanation and thesis:
            explanation = latex_plain_text(str(thesis.get("statement", "")))[:1200]
        if not explanation:
            explanation = "This node records a formal thesis block and its verification status."
        explanation = concise_narrative(explanation)
        strategy = str(
            narrative_override.get(
                "strategy", (representative or {}).get("strategy", "")
            )
        )
        if not strategy:
            strategy = next(
                (str(item.get("strategy", "")) for item in declarations if item.get("strategy")),
                "",
            )
        if not strategy and declarations:
            names = ", ".join(
                str(item["declaration"])
                for item in declarations[:4]
                if item.get("declaration")
            )
            strategy = f"Lean represents the block with the compiled declaration(s) {names}."
        if strategy and len(declarations) > 1:
            strategy = strategy.rstrip()
            if strategy and strategy[-1] not in ".!?":
                strategy += "."
            strategy = (
                f"{strategy} The Lean tab lists all {len(declarations)} linked declarations, "
                "including the supporting lemmas."
            )
        if not strategy:
            strategy = (
                "No direct Lean declaration is linked yet. The statement and any thesis proof "
                "remain visible so the missing verification boundary is explicit."
            )
        strategy = concise_narrative(strategy)
        bridge_notes = []
        review = reviews.get(node_id, {})
        proof_status = str((formal or {}).get("proofStatus", (formal or {}).get("status", "thesis-only")))
        status = display_status(proof_status, review) if thesis else proof_status
        if thesis_issue and thesis_issue["status"] != "verified":
            status = str(thesis_issue["status"])
        if thesis:
            bridge_notes.append("Manual clause review: " + review.get("status", "pending-review") +
                                ". " + review.get("notes", ""))
            bridge_notes.extend(review.get("invalidationReasons", []))
        if thesis_issue:
            bridge_notes.append(
                f"{thesis_issue['id']}: {thesis_issue['summary']} "
                + ("A Lean-verified replacement is available in the full-file fix copy."
                   if thesis_issue.get("fix") else str(thesis_issue.get("correction", "")))
            )
        bridge_summary = STATUS_PALETTE[
            status
        ]["description"]
        if thesis_issue:
            bridge_summary = (
                f"The original thesis block is marked {thesis_issue['kind']}. "
                "Lean verifies the replacement shown in the correction panel, not the "
                "uncorrected claim in isolation."
            ) if thesis_issue.get("fix") else (
                f"{thesis_issue['id']}: {thesis_issue['summary']} "
                f"Suggested correction: {thesis_issue.get('correction', '')}"
            )
        nodes.append(
            {
                "id": node_id,
                "title": title,
                "kind": str(thesis["kind"]) if thesis else node_id.split(":", 1)[0],
                "displayKind": str(thesis.get("displayKind", thesis["kind"]))
                if thesis
                else node_id.split(":", 1)[0],
                "chapter": chapter,
                "section": section,
                "status": status,
                "proofStatus": proof_status,
                "alignmentStatus": review.get("status", "not-a-thesis-block"),
                "clauseReview": review,
                "mappedToLean": bool(declarations),
                "order": order,
                "statement": str(thesis.get("statement", "")) if thesis else "",
                "titleReferences": list(thesis.get("references", [])) if thesis else [],
                "lean": declarations,
                "thesisSvg": statement_svg,
                "thesisProof": thesis_proof,
                "thesisIssue": thesis_issue,
                "thesisRefs": [{"source": source, "line": thesis.get("line"), "chapter": chapter, "section": section}]
                if thesis
                else [],
                # Lean-only compatibility/helper nodes remain addressable from
                # proof maps and deep links, but do not alter the thesis graph.
                "graphHidden": thesis is None,
                "bridge": {
                    "status": status,
                    "summary": bridge_summary,
                    "explanation": explanation,
                    "strategy": strategy,
                    "proofMoves": list((proof or {}).get("steps", [])),
                    "leanGroups": [
                        {
                            "role": "Mapped Lean declarations",
                            "declarations": [item["declaration"] for item in declarations if item.get("declaration")],
                        }
                    ]
                    if declarations
                    else [],
                    "notes": bridge_notes,
                },
            }
        )

    nodes_by_id = {str(node["id"]): node for node in nodes}
    overrides = load_overrides()
    for node in nodes:
        moves = node["bridge"]["proofMoves"]
        node_overrides = overrides.get(str(node["id"]), {})
        for index, move in enumerate(moves):
            automatic = bridge_matches(str(node["id"]), move, nodes_by_id, index == len(moves) - 1)
            override = node_overrides.get(str(move["id"])) if isinstance(node_overrides, dict) else None
            move["leanMatches"] = override if isinstance(override, list) else automatic
            if isinstance(override, list):
                for match in move["leanMatches"]:
                    match["matchKind"] = "curated"

    edges_by_key: dict[tuple[str, str], dict[str, str]] = {}
    for node in nodes:
        references = list(node.get("titleReferences", [])) + list((node.get("thesisProof") or {}).get("references", []))
        for reference in references:
            source = str(reference)
            target = str(node["id"])
            if source in nodes_by_id and source != target:
                edges_by_key[(source, target)] = {"source": source, "target": target, "kind": "dependency"}
    edges = [edges_by_key[key] for key in sorted(edges_by_key)]
    chapters = list(dict.fromkeys(str(node["chapter"]) for node in sorted(nodes, key=lambda item: int(item["order"]))))
    return {
        "schemaVersion": 3,
        "audit": {
            "sourceRoot": metadata.get("sourceRoot"),
            "status": ("formal-review-complete" if all(
                node.get("alignmentStatus") in {"aligned", "model-assumptions-aligned", "source-counterexample"}
                for node in nodes if node.get("thesisRefs")) else "needs-review"),
            "scope": "formal-statements-and-proofs",
            "findings": current_finding_payload(PROJECT_ROOT)["issues"],
            "resolvedFindings": current_finding_payload(PROJECT_ROOT)["resolvedIssues"],
            "findingsSourceMatches": metadata.get("sourceHashes") == current_finding_payload(PROJECT_ROOT)["sourceHashes"],
            "notice": "Inventories the formal blocks selected by the current master.tex. Kernel checks, source links and manual clause alignment are separate. See the dated audit for full-thesis findings, implementation gaps and empirical limits.",
        },
        "generatedAt": None,
        "source": {
            "resultStatus": "graph-artifacts/result-colors.json",
            "thesisMetadata": "bridge-data/thesis-results.json",
            "thesisSvgManifest": "graph-artifacts/thesis-svg/manifest.json",
            "thesisFixes": "bridge-data/thesis-fixes.json",
            "scope": {
                "id": "active-master-all-formal-blocks",
                "title": "All formal blocks in the active thesis master",
                "status": "mixed",
            },
        },
        "summary": make_summary(nodes, edges),
        "chapters": chapters,
        "nodes": nodes,
        "edges": edges,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate verification and explorer graph artifacts.")
    parser.add_argument("--thesis-root", type=Path, default=DEFAULT_THESIS_ROOT)
    parser.add_argument("--refresh-thesis-metadata", action="store_true")
    args = parser.parse_args()

    thesis_root = args.thesis_root.resolve()
    if (thesis_root / "master.tex").is_file():
        # A local thesis checkout is authoritative: follow its active
        # `master.tex` selection, including replacement files and unlabelled
        # formal blocks, rather than a hard-coded chapter list.
        metadata = extract_thesis_metadata(thesis_root)
        write_json(THESIS_METADATA_PATH, metadata)
        fixes = {"schemaVersion": 2, "sourceRoot": source_name(thesis_root),
                 "issues": [], "byLabel": {}, "retiredIssues": [],
                 "summary": {"issueCount": 0},
                 "note": "No correction copies were made for this audit. Current findings are recorded separately; historical fixes remain in bridge-data/history/pre-ultravibe-audit/."}
        write_json(THESIS_FIXES_PATH, fixes)
    else:
        # The public verification CI checkout does not contain the private
        # thesis source tree.  It regenerates Lean-side artifacts against the
        # committed, locally audited thesis/fix snapshots.
        if args.refresh_thesis_metadata:
            parser.error(f"master.tex missing: {thesis_root}")
        if not THESIS_METADATA_PATH.is_file() or not THESIS_FIXES_PATH.is_file():
            parser.error(
                "thesis checkout unavailable and committed thesis metadata/fix snapshots are missing"
            )
        metadata = json.loads(THESIS_METADATA_PATH.read_text(encoding="utf-8"))
        fixes = json.loads(THESIS_FIXES_PATH.read_text(encoding="utf-8"))

    # The dated audit directory is not published; refresh the copies of the
    # review inputs that this script, the axiom audit and the tests read.
    publish_review_inputs(PROJECT_ROOT)
    write_json(BRIDGE_DATA_ROOT / "alignment-findings.json", current_finding_payload(PROJECT_ROOT))
    results = build_results()
    statuses = load_statuses(BRIDGE_DATA_ROOT / "axiom-audit.json", PROJECT_ROOT)
    findings = load_alignment_findings(metadata)
    reviews = load_clause_reviews(PROJECT_ROOT, metadata.get("results", []))
    result_records: list[dict[str, object]] = []
    status_counts: dict[str, int] = defaultdict(int)
    section_counts: dict[str, int] = defaultdict(int)
    for label, result in results.items():
        proof_status = result_status(label, result.traces, statuses)
        status = display_status(proof_status, reviews[label]) if label in reviews else proof_status
        if label in findings and findings[label]["status"] != "verified":
            status = str(findings[label]["status"])
        section = primary_section(result.traces)
        status_counts[status] += 1
        section_counts[section] += 1
        result_records.append(
            {
                "label": label,
                "status": status,
                "proofStatus": proof_status,
                "color": STATUS_PALETTE[status]["color"],
                "section": section,
                "sectionColor": SECTION_PALETTE[section],
                "workflow": SECTION_WORKFLOWS[section],
                "modules": sorted({trace.module for trace in result.traces}),
                "declarations": [declaration_payload(trace) for trace in result.traces if trace.declaration],
            }
        )

    result_payload = {
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
    write_json(OUTPUT_ROOT / "result-colors.json", result_payload)
    write_json(
        OUTPUT_ROOT / "palette.json",
        {
            "schemaVersion": 1,
            "statusPalette": STATUS_PALETTE,
            "sectionPalette": SECTION_PALETTE,
            "sectionWorkflows": SECTION_WORKFLOWS,
        },
    )
    tsv_lines = ["label\tstatus\tcolor\tsection\tsectionColor\tworkflow\tmodules\tdeclarations"]
    for record in result_records:
        declarations = ";".join(str(item["declaration"]) for item in record["declarations"])
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
    with (OUTPUT_ROOT / "result-colors.tsv").open("w", encoding="utf-8", newline="\n") as handle:
        handle.write("\n".join(tsv_lines) + "\n")

    bridge_payload = build_bridge_payload(result_records, metadata, fixes)
    write_json(OUTPUT_ROOT / "lean-bridge-data.json", bridge_payload)
    with (OUTPUT_ROOT / "lean-bridge-data.js").open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(
            "window.LEAN_BRIDGE_DATA = "
            + json.dumps(bridge_payload, indent=2, sort_keys=True, ensure_ascii=False)
            + ";\n"
        )


if __name__ == "__main__":
    main()
