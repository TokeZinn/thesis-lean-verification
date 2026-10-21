from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from build_lean_inventory import PROJECT_ROOT, build_inventory as build_lean_inventory
from inventory_common import write_json
from scrape_thesis_environments import (
    DEFAULT_SVG_ROOT,
    DEFAULT_THESIS_ROOT,
    ENVIRONMENT_KINDS,
    build_inventory as build_thesis_inventory,
    render_missing,
)


BRIDGE_DATA_ROOT = PROJECT_ROOT / "bridge-data"
DEFAULT_LEAN_OUTPUT = BRIDGE_DATA_ROOT / "lean-inventory.json"
DEFAULT_THESIS_OUTPUT = BRIDGE_DATA_ROOT / "thesis-environments.json"
DEFAULT_BRIDGE_OUTPUT = BRIDGE_DATA_ROOT / "bridge-inventory.json"


def link_inventories(
    lean_inventory: dict[str, object], thesis_inventory: dict[str, object]
) -> dict[str, object]:
    declarations = {
        str(record["id"]): record for record in lean_inventory.get("declarations", [])
    }
    environments = {
        str(record["id"]): record for record in thesis_inventory.get("environments", [])
    }
    lean_by_label = {
        str(label): [str(identifier) for identifier in identifiers]
        for label, identifiers in lean_inventory.get("byThesisLabel", {}).items()
    }
    lean_by_environment_id = {
        str(identifier): [str(declaration_id) for declaration_id in declaration_ids]
        for identifier, declaration_ids in lean_inventory.get(
            "byThesisEnvironmentId", {}
        ).items()
    }
    lean_by_key = dict(lean_by_label)
    for key, identifiers in lean_by_environment_id.items():
        lean_by_key.setdefault(key, []).extend(identifiers)

    thesis_by_key: dict[str, list[str]] = {}
    for record in thesis_inventory.get("environments", []):
        key = str(record.get("label") or record["id"])
        thesis_by_key.setdefault(key, []).append(str(record["id"]))

    keys = sorted(set(lean_by_key) | set(thesis_by_key))
    links: list[dict[str, object]] = []
    for key in keys:
        declaration_ids = lean_by_key.get(key, [])
        environment_ids = thesis_by_key.get(key, [])
        if declaration_ids and environment_ids:
            status = "linked"
        elif environment_ids:
            status = "thesis-only"
        else:
            status = "lean-only"
        links.append(
            {
                "label": key,
                "joinKind": "label" if key in lean_by_label or ":" in key and not key.startswith("source:") else "environment-id",
                "status": status,
                "thesisEnvironmentIds": environment_ids,
                "leanDeclarationIds": declaration_ids,
                "thesis": [
                    {
                        "id": identifier,
                        "title": environments[identifier]["title"],
                        "kind": environments[identifier]["kind"],
                        "source": environments[identifier]["source"],
                        "line": environments[identifier]["line"],
                        "svg": environments[identifier].get("svg"),
                    }
                    for identifier in environment_ids
                ],
                "lean": [
                    {
                        "id": identifier,
                        "name": declarations[identifier]["name"],
                        "fullName": declarations[identifier]["fullName"],
                        "kind": declarations[identifier]["kind"],
                        "module": declarations[identifier]["module"],
                        "source": declarations[identifier]["source"],
                        "line": declarations[identifier]["line"],
                    }
                    for identifier in declaration_ids
                ],
            }
        )

    statuses = Counter(str(link["status"]) for link in links)
    return {
        "schemaVersion": 1,
        "joinKey": "exact thesis label, falling back to the stable environment id for unlabelled blocks",
        "summary": {
            "labelCount": len(links),
            "linkedLabelCount": statuses["linked"],
            "thesisOnlyLabelCount": statuses["thesis-only"],
            "leanOnlyLabelCount": statuses["lean-only"],
            "linkedDeclarationCount": sum(
                len(link["leanDeclarationIds"]) for link in links if link["status"] == "linked"
            ),
            "linkedEnvironmentCount": sum(
                len(link["thesisEnvironmentIds"]) for link in links if link["status"] == "linked"
            ),
        },
        "links": links,
        "byLabel": {str(link["label"]): link for link in links},
        "byKey": {str(link["label"]): link for link in links},
        "unmatched": {
            "thesis": [str(link["label"]) for link in links if link["status"] == "thesis-only"],
            "lean": [str(link["label"]) for link in links if link["status"] == "lean-only"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build and exactly join the local Lean and thesis environment inventories."
    )
    parser.add_argument("--lean-root", type=Path, default=PROJECT_ROOT)
    parser.add_argument("--thesis-root", type=Path, default=DEFAULT_THESIS_ROOT)
    parser.add_argument("--svg-root", type=Path, default=DEFAULT_SVG_ROOT)
    parser.add_argument("--lean-output", type=Path, default=DEFAULT_LEAN_OUTPUT)
    parser.add_argument("--thesis-output", type=Path, default=DEFAULT_THESIS_OUTPUT)
    parser.add_argument("--bridge-output", type=Path, default=DEFAULT_BRIDGE_OUTPUT)
    parser.add_argument("--render-svg", action="store_true")
    parser.add_argument("--kinds", default="defn")
    parser.add_argument("--overwrite-svg", action="store_true")
    parser.add_argument("--labels", help="optional comma-separated exact labels to render")
    args = parser.parse_args()

    lean_root = args.lean_root.resolve()
    thesis_root = args.thesis_root.resolve()
    svg_root = args.svg_root.resolve()
    lean_inventory = build_lean_inventory(lean_root)
    thesis_inventory = build_thesis_inventory(thesis_root, svg_root)

    if args.render_svg:
        kinds = {kind.strip() for kind in args.kinds.split(",") if kind.strip()}
        unknown = kinds - set(ENVIRONMENT_KINDS)
        if unknown:
            parser.error(f"unknown environment kinds: {', '.join(sorted(unknown))}")
        rendered, failures = render_missing(
            thesis_root,
            svg_root,
            thesis_inventory["environments"],
            kinds,
            args.overwrite_svg,
            {label.strip() for label in args.labels.split(",") if label.strip()}
            if args.labels
            else None,
        )
        thesis_inventory["summary"]["newSvgCount"] = rendered
        thesis_inventory["summary"]["svgFailures"] = failures
        thesis_inventory["summary"]["svgCount"] = sum(
            bool(record["svg"]) for record in thesis_inventory["environments"]
        )

    bridge = link_inventories(lean_inventory, thesis_inventory)
    write_json(args.lean_output.resolve(), lean_inventory)
    write_json(args.thesis_output.resolve(), thesis_inventory)
    write_json(args.bridge_output.resolve(), bridge)

    lean_summary = lean_inventory["summary"]
    thesis_summary = thesis_inventory["summary"]
    bridge_summary = bridge["summary"]
    print(
        f"Lean: {lean_summary['declarationCount']} declarations; thesis: "
        f"{thesis_summary['environmentCount']} environments; linked: "
        f"{bridge_summary['linkedLabelCount']} labels."
    )
    print(args.bridge_output.resolve())


if __name__ == "__main__":
    main()
