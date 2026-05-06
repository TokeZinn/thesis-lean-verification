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
- `lean-bridge-data.json`: rich graph payload for the explorer, including
  thesis labels, Lean declarations, statement/proof references, and graph edges.
- `lean-bridge-data.js`: browser fallback wrapper around the same bridge data.
- `thesis-svg/`: rendered thesis statement/proof excerpts referenced by the
  bridge data.

## Status Colors

| Status | Meaning |
|---|---|
| `verified` | Backed by compiled Lean declarations without external axioms. |
| `external` | Represented by intentional cited external axioms, or wrappers depending on them. |
| `commentary` | Tracked as thesis/framework narrative rather than a compiled theorem. |
| `unknown` | No reliable Lean trace was found. |

The status-color generator is `scripts/generate_graph_artifacts.py`. The bridge
data and rendered thesis SVGs are exported website artifacts and are published
from this folder for the explorer repository to consume.
