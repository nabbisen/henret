#!/usr/bin/env python3
"""Parse and validate RFC 103 machine-readable explorer evidence."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from gate_registry import V3_EXPLORER_PARAMETERS, V3_EXPLORER_RESULT

PREFIX = "HENRET_EXPLORER_RESULT "


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def strict_json_loads(text: str) -> object:
    """Decode JSON while rejecting duplicate object keys at every depth."""
    try:
        return json.loads(text, object_pairs_hook=_unique_object)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid JSON: {exc}") from exc


def _require_exact_keys(value: object, expected: set[str], label: str) -> dict:
    if type(value) is not dict:
        raise ValueError(f"{label} must be a JSON object")
    observed = set(value)
    if observed != expected:
        raise ValueError(f"{label} keys must be exactly {sorted(expected)}; "
                         f"observed {sorted(observed)}")
    return value


def validate_result_object(result: object) -> dict:
    """Validate the RFC 103 result schema with strict JSON scalar types."""
    expected = V3_EXPLORER_RESULT
    result = _require_exact_keys(result, set(expected), "explorer result")
    world = _require_exact_keys(result["world"], set(expected["world"]),
                                "explorer result world")
    for key, canonical in expected["world"].items():
        if type(world[key]) is not int or world[key] != canonical:
            raise ValueError(f"explorer result world.{key} must be integer "
                             f"{canonical}")
    for key in ("schema", "depth", "program_count"):
        if type(result[key]) is not int or result[key] != expected[key]:
            raise ValueError(f"explorer result {key} must be integer {expected[key]}")
    boolean_keys = set(expected) - {"schema", "world", "depth", "program_count"}
    for key in sorted(boolean_keys):
        if type(result[key]) is not bool or result[key] is not expected[key]:
            raise ValueError(f"explorer result {key} must be boolean "
                             f"{str(expected[key]).lower()}")
    return result


def validate_manifest_evidence(parameters: object, result: object) -> None:
    """Validate canonical v3 parameters and result without Python coercions."""
    result = validate_result_object(result)
    parameters = _require_exact_keys(parameters, {"world", "depth"},
                                     "explorer parameters")
    world = _require_exact_keys(parameters["world"],
                                set(V3_EXPLORER_PARAMETERS["world"]),
                                "explorer parameters world")
    for key, canonical in V3_EXPLORER_PARAMETERS["world"].items():
        if type(world[key]) is not int or world[key] != canonical:
            raise ValueError(f"explorer parameters world.{key} must be integer "
                             f"{canonical}")
    if (type(parameters["depth"]) is not int or
            parameters["depth"] != V3_EXPLORER_PARAMETERS["depth"]):
        raise ValueError("explorer parameters depth must be integer "
                         f"{V3_EXPLORER_PARAMETERS['depth']}")
    if parameters["world"] != result["world"] or parameters["depth"] != result["depth"]:
        raise ValueError("explorer executed/recorded parameters disagree")


def parse_output(text: str) -> dict:
    lines = [line[len(PREFIX):] for line in text.splitlines()
             if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError(f"expected exactly one {PREFIX.strip()} line; found {len(lines)}")
    try:
        result = strict_json_loads(lines[0])
        validate_result_object(result)
    except ValueError as exc:
        raise ValueError(f"invalid explorer result JSON: {exc}") from exc
    return result


def manifest_evidence(text: str) -> dict:
    result = parse_output(text)
    return {
        "parameters": {"world": result["world"], "depth": result["depth"]},
        "result": result,
    }


def self_test() -> int:
    valid_line = PREFIX + json.dumps(V3_EXPLORER_RESULT, separators=(",", ":"))
    failures = int(manifest_evidence(valid_line)["parameters"] !=
                   V3_EXPLORER_PARAMETERS)
    invalid = [
        "no machine result",
        valid_line + "\n" + valid_line,
        PREFIX + json.dumps({**V3_EXPLORER_RESULT,
                             "counterexample_found": False}),
        PREFIX + json.dumps({**V3_EXPLORER_RESULT, "depth": 1}),
        PREFIX + json.dumps({**V3_EXPLORER_RESULT, "well_formed": 1}),
        PREFIX + json.dumps({**V3_EXPLORER_RESULT, "depth": True}),
        PREFIX + valid_line[len(PREFIX):].replace(
            '"counterexample_found":true',
            '"counterexample_found":false,"counterexample_found":true'),
        PREFIX + valid_line[len(PREFIX):].replace(
            '"maxMsg":1', '"maxMsg":2,"maxMsg":1'),
        PREFIX + "{not-json}",
    ]
    for fixture in invalid:
        try:
            manifest_evidence(fixture)
            failures += 1
        except ValueError:
            pass
    print(f"explorer-result-selftest: valid + {len(invalid)} invalid fixtures; "
          f"{failures} error(s)")
    return 1 if failures else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    if "--shell-args" in sys.argv:
        world = V3_EXPLORER_PARAMETERS["world"]
        print(world["maxTask"], world["maxActor"], world["maxMsg"],
              world["maxTime"], V3_EXPLORER_PARAMETERS["depth"])
        return 0
    if len(sys.argv) != 2:
        print("usage: explorer_result.py <explorer-stdout> | --shell-args | --self-test",
              file=sys.stderr)
        return 2
    try:
        evidence = manifest_evidence(Path(sys.argv[1]).read_text())
    except (OSError, ValueError) as exc:
        print(f"explorer-result: FAIL — {exc}", file=sys.stderr)
        return 1
    print(json.dumps(evidence, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
