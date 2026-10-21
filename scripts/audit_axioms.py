"""Check transitive axioms of thesis-linked declarations and registered prose modules.

The result certifies Lean declarations, not their semantic equivalence to prose.
Unlike the graph's historical hand-maintained list, a wrapper around a local
axiom cannot be classified as internally proved by this audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

from build_lean_inventory import build_inventory, project_lean_files
from inventory_common import write_json, implementation_fingerprint
from thesis_config import review_inputs

ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", re.DOTALL)
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def fingerprint(path: Path) -> str:
    return implementation_fingerprint(path)


def parse_axioms(output: str) -> dict[str, list[str]]:
    parsed = {
        name: sorted(a.strip() for a in dependencies.split(",") if a.strip())
        for name, dependencies in AXIOMS_RE.findall(output)
    }
    parsed.update({name: [] for name in NO_AXIOMS_RE.findall(output)})
    return parsed


def classify(dependencies: list[str] | None) -> str:
    if dependencies is None:
        return "unverified"
    if "sorryAx" in dependencies:
        return "unproved"
    if set(dependencies) - STANDARD_AXIOMS:
        return "external"
    return "kernel-checked"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true",
                        help="Use only immediately after a successful full build.")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH")
    if not args.skip_build:
        subprocess.run([lake, "build", "--wfail", "Formalization"], cwd=ROOT, check=True)
    inventory = build_inventory(ROOT)
    supplement_path = review_inputs(ROOT) / "supplementary-lean-modules.json"
    supplementary = set(json.loads(supplement_path.read_text(encoding="utf-8")))
    declarations = [r for r in inventory["declarations"]
                    if (r["thesisLabels"] or r["thesisEnvironmentIds"] or r["source"] in supplementary)
                    and not re.search(r"\bprivate\b", r["header"].split(":=", 1)[0])]
    names = sorted({r["fullName"] for r in declarations})
    sources = sorted({p.relative_to(ROOT).as_posix() for p in project_lean_files(ROOT)} |
                     {"lakefile.toml", "lake-manifest.json", "lean-toolchain",
                      supplement_path.relative_to(ROOT).as_posix()})
    source_hashes = {s: fingerprint(ROOT / s) for s in sources}
    query = ROOT / ".lake" / "ThesisAxiomAudit.lean"
    imports = sorted({"Formalization", *[m["module"] for m in inventory["modules"]
                                        if m["source"] in supplementary]})
    query.write_text("\n".join(f"import {name}" for name in imports) + "\n" +
                     "\n".join(f"#print axioms {name}" for name in names) + "\n",
                     encoding="utf-8")
    result = subprocess.run([lake, "env", "lean", str(query)], cwd=ROOT,
                            text=True, encoding="utf-8", capture_output=True)
    (ROOT / ".lake" / "axiom-audit-output.txt").write_text(
        result.stdout + result.stderr, encoding="utf-8")
    parsed = parse_axioms(result.stdout)
    stable = (set(s for s in sources if s.endswith(".lean")) ==
              {p.relative_to(ROOT).as_posix() for p in project_lean_files(ROOT)} and
              all((ROOT / s).is_file() and fingerprint(ROOT / s) == h
                  for s, h in source_hashes.items()))
    by_name = {}
    for name in names:
        dependencies = parsed.get(name)
        by_name[name] = {
            "status": classify(dependencies) if stable else "unverified",
            "axioms": dependencies,
            "projectAxioms": sorted(set(dependencies or []) - STANDARD_AXIOMS),
        }
    payload = {
        "schemaVersion": 1,
        "scope": "transitive Lean axiom dependencies; prose alignment requires separate review",
        "leanToolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "querySucceeded": result.returncode == 0 and stable,
        "sourceStableDuringQuery": stable,
        "implementationHashNormalization": "CRLF-to-LF",
        "sourceHashes": source_hashes,
        "supplementaryModules": sorted(supplementary),
        "byDeclaration": by_name,
        "summary": {status: sum(r["status"] == status for r in by_name.values())
                    for status in ("kernel-checked", "external", "unproved", "unverified")},
    }
    write_json(ROOT / "bridge-data" / "axiom-audit.json", payload)
    print(json.dumps(payload["summary"], sort_keys=True))
    if result.returncode or payload["summary"]["unproved"] or payload["summary"]["unverified"]:
        print("Incomplete audit; diagnostics: .lake/axiom-audit-output.txt")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
