# Graph Website Artifacts

This folder contains machine-readable graph metadata for the companion explorer
website and CI publishing job.

## Files

- `result-colors.json`: canonical artifact. It contains every traced thesis
  result label, its verification status, display color, section, section color,
  workflow name, module list, and linked Lean declarations.
- `result-colors.tsv`: audit-friendly tabular export of the same result-level
  metadata.
- `palette.json`: small palette-only file for UI code that wants colors before
  loading all result metadata.
- `lean-bridge-data.json`: schema-v3 explorer payload containing every custom
  formal block selected by the active thesis `master.tex`, human-readable
  titles, dependency edges, proof steps, explanations, strategies, and stable
  proof-to-Lean declaration matches.
- `lean-bridge-data.js`: browser fallback wrapper around the same bridge data.
- `thesis-svg/`: rendered thesis statement/proof excerpts referenced by the
  bridge data.
- `thesis-fix-svg/`: rendered excerpts from the Lean-verified `*_fix.tex`
  correction copies.
- `../bridge-data/thesis-results.json`: committed active-master metadata
  snapshot used in CI when the thesis checkout is unavailable.
- `../bridge-data/thesis-fixes.json`: validated issue/correction metadata,
  including the formal-only-copy and Lean-declaration checks.
- `../bridge-data/proof-mapping-overrides.json`: optional curated replacements
  for automatically generated proof-step matches.

## Status Colors

| Status | Meaning |
|---|---|
| `verified` | Backed by compiled Lean declarations without external axioms. |
| `external` | Represented by intentional cited external axioms, or wrappers depending on them. |
| `commentary` | Tracked as thesis/framework narrative rather than a compiled theorem. |
| `unknown` | No reliable Lean trace was found. |

`scripts/generate_graph_artifacts.py` is the canonical generator; the `.mjs`
entry point delegates to it for compatibility. To refresh the thesis snapshot
locally, run the generator with `--refresh-thesis-metadata --thesis-root` and
the path to `VibePhDThesis`. The generator never prunes contextual SVG files.

To replace the complete rendered active-thesis set, including unlabeled blocks
and proof excerpts, run:

```powershell
python scripts/scrape_thesis_environments.py `
  --thesis-root ..\VibePhDThesis `
  --rebuild-all-svg
```

The rebuild uses the literal pre-`\begin{document}` content of the current
thesis `master.tex`, performs two LaTeX passes, verifies a one-to-one mapping
between requested fragments and generated DVI pages, and then replaces the SVG
directory and manifest. It restores the thesis chapter/theorem counter context
for each fragment and converts glyphs to SVG paths so Chromium does not depend
on deprecated embedded SVG fonts. Run `scripts/generate_graph_artifacts.py
--refresh-thesis-metadata` afterwards to refresh the explorer payload.

Lean-backed correction excerpts are rebuilt separately with:

```powershell
python scripts/build_thesis_fixes.py `
  --thesis-root ..\VibePhDThesis `
  --rebuild-svg
```
