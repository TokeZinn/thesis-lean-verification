"""Fresh manual clause evidence, independent of Lean kernel evidence."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from thesis_config import review_inputs
from inventory_common import implementation_fingerprint


def fingerprint(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_clause_reviews(root: Path, records: list[dict]) -> dict[str, dict]:
    audit = review_inputs(root)
    path = audit / "block-review.json"
    saved = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else {}
    by_key = {r["key"]: r for r in saved.get("blocks", [])}
    snapshot_path = audit / ("snapshot.json" if (audit / "snapshot.json").is_file() else "source-delta.json")
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8")) if snapshot_path.is_file() else {}
    file_hashes: dict[str, str | None] = {}
    result = {}
    for record in records:
        key = str(record.get("label") or record["id"])
        review = by_key.get(key, {}).get("implementationReview", {})
        status = review.get("status", "pending-review")
        if status == "pending-clause-audit":
            status = "pending-review"
        statement_hash = record.get("statementSha256") or fingerprint(record["rawEnvironment"])
        proof_hash = record.get("proofSha256") or fingerprint(
            (record.get("proof") or {}).get("rawEnvironment", ""))
        reasons = []
        if status != "pending-review":
            if (record.get("sourceFileSha256") and
                record["sourceFileSha256"] != snapshot.get("sourceHashes", {}).get(record.get("source"))):
                reasons.append("surrounding thesis source changed")
            if review.get("sourceStatementSha256") != statement_hash:
                reasons.append("thesis statement changed")
            if review.get("sourceProofSha256") != proof_hash:
                reasons.append("thesis proof changed")
            evidence = review.get("evidenceSha256", {})
            if not evidence:
                reasons.append("no recorded implementation evidence")
            for source, expected in evidence.items():
                if source not in file_hashes:
                    file = root / source
                    file_hashes[source] = (implementation_fingerprint(file)
                                           if file.is_file() else None)
                if file_hashes[source] != expected:
                    reasons.append(f"implementation evidence changed: {source}")
        result[key] = {
            **review,
            "status": "needs-review" if reasons else status,
            "fresh": bool(review) and not reasons and status != "pending-review",
            "invalidationReasons": reasons,
        }
    return result


def display_status(proof_status: str, review: dict) -> str:
    """Never turn a checked counterexample into a verified thesis claim."""
    status = review.get("status", "pending-review")
    if status == "source-counterexample":
        return "incorrect-statement"
    if status == "partial":
        return "needs-alignment"
    if status == "needs-review" or (status == "pending-review" and proof_status == "verified"):
        return "needs-review"
    return proof_status


def current_finding_payload(root: Path) -> dict:
    """Expose findings only from the currently selected source audit."""
    active = review_inputs(root)
    if (active / "snapshot.json").is_file():
        snapshot = json.loads((active / "snapshot.json").read_text(encoding="utf-8"))
        finding_path = active / "findings.json"
        payload = json.loads(finding_path.read_text(encoding="utf-8")) if finding_path.is_file() else {}
        return {"schemaVersion": 4, "sourceRoot": snapshot["sourceRoot"],
                "status": "review-in-progress", "scope": "full-thesis",
                "issues": [], "resolvedIssues": [], "byLabel": {},
                "sourceHashes": snapshot["sourceHashes"],
                "report": active.relative_to(root).as_posix() + "/THESIS_ERRORS.md", **payload}
    audit = root / "audit/ultravibe"
    text = (audit / "FORMAL_FINDINGS.md").read_text(encoding="utf-8")
    issues = []
    for match in re.finditer(r"^## (UV\d+) — ([^\n]+)\n(.*?)(?=^## |\Z)", text,
                             flags=re.MULTILINE | re.DOTALL):
        issues.append({"id": match[1], "title": match[2], "detail": match[3].strip()})
    blocks = {r["key"]: r for r in json.loads(
        (audit / "block-review.json").read_text(encoding="utf-8"))["blocks"]}
    resolution_path = audit / "patches/uv001-uv006/resolution.json"
    resolutions = (json.loads(resolution_path.read_text(encoding="utf-8")).get("byLabel", {})
                   if resolution_path.is_file() else {})
    resolved_issues = []
    by_label = {}
    for label, issue_id, status, summary, correction in (
        ("thm:regression-theorem", "UV001", "incorrect-statement",
         "The final sentence identifies minima for arbitrary G and sigma(Y).",
         "Set G = sigma(Y), or state the minimizations separately."),
        ("thm:point-process-tuple", "UV006", "verified",
         "The proof says exactly one nonzero summand; there may be none.",
         "Replace exactly one by at most one. The theorem remains valid."),
    ):
        block = blocks[label]
        resolution = resolutions.get(label)
        if resolution:
            matches = (resolution.get("status") == "resolved" and
                       resolution.get("statementSha256") == block["statementSha256"] and
                       resolution.get("proofSha256") == block["proofSha256"])
            if matches:
                resolved_issues.extend({**issue, "status": "resolved"}
                                       for issue in issues if issue["id"] == issue_id)
                issues = [issue for issue in issues if issue["id"] != issue_id]
                continue
            status = "needs-review"
            summary = "The source changed since this finding was corrected; review the new version."
        by_label[label] = {
            "issue": issue_id, "status": status,
            "kind": "proof-wording-error" if issue_id == "UV006" else status,
            "statementSha256": block["statementSha256"],
            "proofSha256": block["proofSha256"],
            "source": block["source"], "line": block["line"],
            "summary": summary, "correction": correction,
        }
    return {"schemaVersion": 3, "sourceRoot": "Ultravibe PhD Thesis",
            "status": "formal-review-complete", "scope": "formal-statements-and-proofs",
            "issues": issues, "resolvedIssues": resolved_issues, "byLabel": by_label,
            "sourceHashes": json.loads((audit / "source-delta.json").read_text(
                encoding="utf-8"))["sourceHashes"],
            "report": "audit/ultravibe/FORMAL_FINDINGS.md",
            "supplementaryReport": "audit/ultravibe/CURRENT_FINDINGS.md"}
