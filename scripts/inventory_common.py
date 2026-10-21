from __future__ import annotations

import json
import hashlib
import re
from pathlib import Path
from typing import Any


def implementation_fingerprint(path: Path) -> str:
    """Hash source content independently of Windows checkout line endings.

    Authoritative thesis/snapshot byte hashes deliberately use a separate path.
    """
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


LABEL_PREFIXES = (
    "alg",
    "assum",
    "axiom",
    "conc",
    "cor",
    "defn",
    "eq",
    "exmp",
    "lem",
    "prin",
    "prop",
    "property",
    "qst",
    "rem",
    "thm",
)
LABEL_RE = re.compile(
    r"\b(?:" + "|".join(map(re.escape, LABEL_PREFIXES)) + r"):[A-Za-z0-9_.-]+"
)
REFERENCE_RE = re.compile(
    r"\\(?:eqref|ref|autoref|cref|Cref|nameref|pageref)\{([^}]+)\}"
)


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def unique(values: list[str]) -> list[str]:
    return list(dict.fromkeys(value for value in values if value))


def references_in(text: str) -> list[str]:
    references: list[str] = []
    for clause in REFERENCE_RE.findall(text):
        references.extend(part.strip() for part in clause.split(","))
    return unique(references)


def labels_in(text: str) -> list[str]:
    return unique(LABEL_RE.findall(text))


def audit_labels_in(comment: str) -> list[str]:
    """Extract deliberate thesis join keys from a Lean documentation block.

    The project contains two historical annotation styles: an explicit
    `Original label:` clause, and a `Thesis source:` clause followed by a bare
    label.  Incidental references later in the explanation are deliberately
    ignored.
    """
    lines = comment.splitlines()
    labels: list[str] = []
    source_clause = False
    for index, line in enumerate(lines):
        stripped = line.strip().lstrip("*").strip()
        if "Original label" in stripped:
            clause = [stripped]
            for follow in lines[index + 1 : index + 6]:
                follow_stripped = follow.strip().lstrip("*").strip()
                if not follow_stripped or follow_stripped.startswith(
                    (
                        "Informal statement",
                        "Lean strategy",
                        "External reference",
                        "Thesis source",
                        "Original block id",
                    )
                ):
                    break
                clause.append(follow_stripped)
            labels.extend(labels_in("\n".join(clause)))
            source_clause = False
            continue
        if stripped.startswith("Thesis source:"):
            source_clause = True
            labels.extend(labels_in(stripped))
            continue
        if re.match(r"^Thesis\s+`?(?:" + "|".join(LABEL_PREFIXES) + r"):", stripped):
            labels.extend(labels_in(stripped))
            continue
        if source_clause:
            if not stripped:
                source_clause = False
                continue
            if stripped.startswith(("Informal statement", "Lean strategy", "External reference")):
                source_clause = False
                continue
            labels.extend(labels_in(stripped))
    return unique(labels)


def humanize_label(label: str) -> str:
    slug = label.split(":", 1)[-1]
    words = re.split(r"[-_]+", slug)
    small = {"and", "as", "by", "for", "from", "in", "is", "of", "on", "to", "with"}
    result: list[str] = []
    for index, word in enumerate(words):
        if not word:
            continue
        if any(character.isupper() for character in word[1:]) or word.isupper():
            result.append(word)
        elif index and word.lower() in small:
            result.append(word.lower())
        else:
            result.append(word[:1].upper() + word[1:])
    return " ".join(result) or label


def latex_plain_text(value: str) -> str:
    text = re.sub(r"%[^\n]*", " ", value)
    # A typesetting line break must not be parsed as a command whose name is
    # the first word of the next line (e.g. \\Historical).
    text = text.replace(r"\\", " ")
    text = re.sub(r"\\(?:cite|citep|citet|index|label)\{[^}]*\}", "", text)
    text = re.sub(
        r"\\(?:emph|textbf|textit|texttt|text|nameref|operatorname)\{([^{}]*)\}",
        r"\1",
        text,
    )
    text = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?", "", text)
    text = text.replace("~", " ").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", text).strip(" ,.;:-")


def slug_for_label(label: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "-", label.replace(":", "__"))
