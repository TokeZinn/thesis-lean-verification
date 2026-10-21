"""Authoritative source and versioned audit locations. Never writes the thesis."""
from pathlib import Path
import json
import shutil

PROJECT_ROOT = Path(__file__).resolve().parents[1]
# Canonical thesis working copy since 2026-10-21 (git clone of TokeZinn/Doctoral-Thesis).
THESIS_ROOT = PROJECT_ROOT.parent / "Doctoral Thesis"
AUDIT_RELATIVE = Path("audit/doctoral-2026-10-20")
# The dated audit directory stays on the author's machine. The few files the
# CI steps read are published as copies here, next to the other bridge data.
REVIEW_RELATIVE = Path("bridge-data/review")
REVIEW_INPUTS = ("snapshot.json", "findings.json", "block-review.json", "archived-intraday.json",
                 "supplementary-lean-modules.json", "legacy-intraday")


def current_audit(root: Path) -> Path:
    dated = root / AUDIT_RELATIVE
    return dated if (dated / "snapshot.json").is_file() else root / "audit/ultravibe"


def review_inputs(root: Path) -> Path:
    """Where the review inputs are read from: the published copies when present, else the audit."""
    published = root / REVIEW_RELATIVE
    return published if (published / "snapshot.json").is_file() else current_audit(root)


def publish_review_inputs(root: Path) -> bool:
    """Refresh the published copies from the dated audit; a no-op where the audit is absent."""
    source = root / AUDIT_RELATIVE
    if not (source / "snapshot.json").is_file():
        return False
    target = root / REVIEW_RELATIVE
    target.mkdir(parents=True, exist_ok=True)
    for name in REVIEW_INPUTS:
        if (source / name).is_dir():
            if (target / name).exists():
                shutil.rmtree(target / name)
            shutil.copytree(source / name, target / name)
        else:
            shutil.copyfile(source / name, target / name)
    return True


def stored_path_name(stored: str) -> str:
    """Last component of a path string recorded on any OS.

    Snapshot manifests store the Windows path of the author's checkout; on a
    POSIX CI runner `Path(...).name` would return the whole string, so split on
    both separators explicitly.
    """
    return [part for part in stored.replace("\\", "/").split("/") if part][-1]


def source_name(thesis_root: Path) -> str:
    manifest = thesis_root.parent / "snapshot.json"
    if manifest.is_file():
        capture = json.loads(manifest.read_text(encoding="utf-8"))
        if Path(capture["snapshotRoot"]).resolve() == thesis_root.resolve():
            return stored_path_name(capture["sourceRoot"])
    return thesis_root.name
