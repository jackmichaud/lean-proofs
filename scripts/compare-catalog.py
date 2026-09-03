#!/usr/bin/env python3
"""Compare two Frontier catalog exports on their structural content.

`make check` regenerates the catalog and compares it with the committed copy, so that the
web workspace can never silently drift from the Lean registry. A byte comparison is the wrong
test for that: pretty-printed Lean types depend on the toolchain and on mathlib's notation, so
a routine mathlib bump would fail the check on rendering churn rather than on substance.

This compares everything that is not a rendered type, and reports rendering differences
separately as informational output.
"""

from __future__ import annotations

import json
import sys

# Fields whose value is a pretty-printed Lean expression, and therefore toolchain-dependent.
RENDERED_FIELDS = {"statementType", "certificateType"}


def strip_rendered(node):
    """Recursively drop rendered-type fields so only structural content remains."""
    if isinstance(node, dict):
        return {
            key: ("<rendered>" if key == "type" else strip_rendered(value))
            for key, value in node.items()
            if key not in RENDERED_FIELDS
        }
    if isinstance(node, list):
        return [strip_rendered(item) for item in node]
    return node


def rendered_differences(fresh: dict, committed: dict) -> list[str]:
    """Rendered types that changed, keyed by entry id. Informational, never fatal."""
    committed_by_id = {entry["id"]: entry for entry in committed.get("entries", [])}
    differences = []
    for entry in fresh.get("entries", []):
        other = committed_by_id.get(entry["id"])
        if other is None:
            continue
        for field in sorted(RENDERED_FIELDS):
            if entry.get(field) != other.get(field):
                differences.append(f"{entry['id']}.{field}")
    return differences


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(f"usage: {argv[0]} <fresh.json> <committed.json>", file=sys.stderr)
        return 2

    fresh_path, committed_path = argv[1], argv[2]
    try:
        with open(fresh_path, encoding="utf-8") as handle:
            fresh = json.load(handle)
        with open(committed_path, encoding="utf-8") as handle:
            committed = json.load(handle)
    except FileNotFoundError as error:
        print(f"catalog comparison failed: {error}", file=sys.stderr)
        return 1
    except json.JSONDecodeError as error:
        print(f"catalog comparison failed: invalid JSON: {error}", file=sys.stderr)
        return 1

    if strip_rendered(fresh) != strip_rendered(committed):
        print(
            f"{committed_path} is out of date with the Lean registry.\n"
            f"Run `make catalog` and commit the result.",
            file=sys.stderr,
        )
        fresh_ids = [entry["id"] for entry in fresh.get("entries", [])]
        committed_ids = [entry["id"] for entry in committed.get("entries", [])]
        if fresh_ids != committed_ids:
            print(f"  registry ids: {fresh_ids}", file=sys.stderr)
            print(f"  committed ids: {committed_ids}", file=sys.stderr)
        return 1

    stale = rendered_differences(fresh, committed)
    if stale:
        print(
            f"catalog structure matches; {len(stale)} rendered type(s) differ "
            f"(likely a toolchain or mathlib change): {', '.join(stale)}\n"
            f"Run `make catalog` to refresh them."
        )
    else:
        print(f"{committed_path} matches the Lean registry.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
