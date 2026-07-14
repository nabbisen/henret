#!/usr/bin/env python3
"""Versioned release gate registries (RFC 102 / RFC 103).

Numeric IDs remain in manifests for compatibility and ordering. Evidence
ledger claims bind to stable semantic IDs, which must not be reused with a
different meaning inside a registry.
"""

V2_PROFILE = "release-core-v2"
V2_REGISTRY = "rfc102-release-core-v2"
V3_PROFILE = "release-core-v3"
V3_REGISTRY = "rfc103-release-core-v3"
ACTIVE_PROFILE = V3_PROFILE

V2_GATES = {
    0: "gate.selftest",
    1: "build.lean",
    2: "test.demo",
    3: "build.examples",
    4: "test.conformance",
    5: "docs.symbols",
    6: "proof.axiom-audit",
    7: "docs.consistency",
    8: "rfc.metadata",
    9: "lint.warning-budget",
    10: "docs.mdbook",
}

V3_GATES = {**V2_GATES, 11: "test.explorer"}

V3_EXPLORER_PARAMETERS = {
    "world": {"maxTask": 2, "maxActor": 2, "maxMsg": 1, "maxTime": 2},
    "depth": 3,
}

V3_EXPLORER_RESULT = {
    "schema": 1,
    **V3_EXPLORER_PARAMETERS,
    "program_count": 25260,
    "well_formed": True,
    "occurrence_unique": True,
    "bridge": True,
    "counterexample_found": True,
    "counterexample_fails": True,
    "counterexample_minimal": True,
}

EVIDENCE_CAPABILITIES = {
    "gate.selftest": "assurance-meta",
    "build.lean": "kernel-build",
    "test.demo": "executable-test",
    "build.examples": "executable-test",
    "test.conformance": "executable-test",
    "docs.symbols": "documentation-check",
    "proof.axiom-audit": "axiom-audit",
    "docs.consistency": "documentation-check",
    "rfc.metadata": "governance-check",
    "lint.warning-budget": "build-quality",
    "docs.mdbook": "documentation-check",
    "test.explorer": "executable-test",
}

PROFILES = {
    V2_PROFILE: {"registry": V2_REGISTRY, "gates": V2_GATES},
    V3_PROFILE: {"registry": V3_REGISTRY, "gates": V3_GATES},
}


def profile_contract(profile: str) -> dict | None:
    return PROFILES.get(profile)


def active_evidence_ids() -> set[str]:
    return set(V3_GATES.values())


def evidence_capability(evidence_id: str) -> str | None:
    return EVIDENCE_CAPABILITIES.get(evidence_id)
