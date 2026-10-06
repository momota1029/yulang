#!/usr/bin/env python3
"""Research-only successor gate inventory and nonimplication witnesses.

This checker does not parse source or implement inference. Its DAG edges name
proof obligations, not assertions that the target theorems have been proved.
Run with Python's standard library; no files, subprocesses, or network writes.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

BASELINE = "ac2864a48868b017a8b6fedc6a665f24d0c2daff"
STATUSES = {
    "CLOSED", "CONDITIONAL-CLOSED", "IMPLEMENTATION-ONLY", "OPEN-PROOF",
    "OPEN-SEMANTIC", "BLOCKED-BY-USER-DECISION",
}

# Stable leaf IDs are deliberately shared by every aggregate that needs them.
# R/G are interface leaves to the separately owned recursive producer lane.
LEAVES = {
    "SIG": ("OPEN-SEMANTIC", "independent complete signature/Slots/profile licensing"),
    "INIT": ("OPEN-SEMANTIC", "initial open-world environment/import/hole validity"),
    "HIST": ("OPEN-PROOF", "all admissible responses/future histories preserve original world"),
    "RAW": ("OPEN-PROOF", "raw source constructors emit exhaustive occurrence-indexed atoms"),
    "REC": ("OPEN-PROOF", "actual simultaneous recursive body/member discharge"),
    "GEN": ("OPEN-PROOF", "semantic generalized-view eligibility and binder placement"),
    "BOUND_ADAPT": ("OPEN-PROOF", "source boundary/path realization and adapter soundness/completeness"),
    "EBRIDGE": ("OPEN-SEMANTIC", "mixed abstract/concrete row component-to-occurrence interpretation"),
    "SUBIMAGE": ("OPEN-PROOF", "complete handler image and attachment-preserving targeted subtraction"),
    "RELEASE": ("OPEN-PROOF", "source attributed actual outward crossing and release lifetime"),
    "ORDINARY": ("OPEN-PROOF", "complete ordinary handler dispatch/OpCompat/arm/resumption theorem"),
    "CTX": ("OPEN-PROOF", "source derived-comparison context finite canonicalization"),
    "PHI": ("OPEN-SEMANTIC", "exhaustive guard/Phi/K,D primitive operand interpretation"),
    "JDEC": ("OPEN-PROOF", "complete effective joint residual decision/presentation"),
    "JPROJ": ("OPEN-PROOF", "effective principal public projection with scopes/evidence"),
    "DESC": ("OPEN-PROOF", "legal common descriptor at every original typed path"),
    "DIRECT": ("OPEN-PROOF", "independent valid-view lifting through actual common export"),
    "SAT_A": ("OPEN-SEMANTIC", "exhaustive production endpoint satisfaction incl Option 2 extras"),
    "ADM_A": ("OPEN-SEMANTIC", "independent punctured-context production admission"),
    "DOM": ("OPEN-PROOF", "D_C subset D_A in original joint fiber"),
    "OBS": ("OPEN-PROOF", "P_A(c) subset P_C(c) for every checked-admitted challenge"),
    "STATE_ID": ("OPEN-SEMANTIC", "dynamic State activation/location identity and captured access"),
    "STATE_RW": ("OPEN-SEMANTIC", "source local read/replacement/restart equations"),
    "STATE_RESUME": ("OPEN-SEMANTIC", "source resumed-store and multi-shot branch equations"),
    "REFWORLD": ("OPEN-PROOF", "first-class reference/import alias substitution and world validity"),
    "SELECT": ("OPEN-SEMANTIC", "visible implementation candidate/receiver/method selection judgments"),
    "ROLE_ASSOC": ("OPEN-SEMANTIC", "joint role conformance and associated-type equation judgments"),
    "RESOLVE_FP": ("OPEN-PROOF", "sound principal complete joint selection fixed point"),
    "IFACE": ("OPEN-SEMANTIC", "complete simultaneous canonical interface/equality contract"),
    "LIFE": ("OPEN-PROOF", "fresh/internal/import use correspondence and atomic publication"),
    "LIMIT": ("OPEN-SEMANTIC", "deterministic practical resource boundary with exact admitted result"),
    "HIR": ("IMPLEMENTATION-ONLY", "lower/emission/wiring after semantic contracts are reviewed/authorized"),
    "ORACLE": ("OPEN-PROOF", "successor final acceptance/observations across declared source envelope"),
}

CLOSED_SCOPES = {
    "PURE_FMP": ("CLOSED", "reviewed normalized pure structural regular-witness existence"),
    "PURE_DEC": ("CLOSED", "reviewed pure effective-input finite search, no joint Phi/effects"),
    "DIR": ("CLOSED", "reviewed source upper-output protection; no lower/provider backflow"),
    "REPLAY": ("CLOSED", "fixed source certificates replay independent of physical delivery order"),
    "DREL": ("CLOSED", "exact directional whole-relation rewrite at original scopes"),
    "SV": ("CONDITIONAL-CLOSED", "selected receipt/rebind/capture, independently typed original rows"),
    "K_PROVIDER": ("CLOSED", "selected constructor-guarded same-provider recursive graph"),
    "EXACT_IMAGE": ("CONDITIONAL-CLOSED", "candidate source machine to exact possibly infinite carrier"),
    "RES_FACT": ("CONDITIONAL-CLOSED", "residual normalization with stable finite contexts"),
    "AEXT": ("CONDITIONAL-CLOSED", "common extension in guarantee-only active-view envelope"),
    "AALLOC": ("CONDITIONAL-CLOSED", "actual-export V_alloc/V_alloc,H extension"),
    "REUSE": ("CONDITIONAL-CLOSED", "downstream reuse under complete boundary equality"),
}

AGGREGATES = {
    "SOURCE_J": ("OPEN-PROOF", ("SIG", "INIT", "HIST", "RAW", "REC", "GEN", "STATE_ID", "STATE_RW", "STATE_RESUME", "REFWORLD")),
    "COMPLETE": ("OPEN-PROOF", ("SOURCE_J",)),
    "RESIDUAL": ("OPEN-PROOF", ("SOURCE_J", "CTX", "PHI")),
    "EFFECTIVE": ("OPEN-PROOF", ("RESIDUAL", "JDEC", "JPROJ")),
    "COMMON": ("OPEN-PROOF", ("SOURCE_J", "DESC")),
    "ALLVIEW": ("OPEN-PROOF", ("COMMON", "DIRECT", "GEN")),
    "PROD_RULES": ("OPEN-SEMANTIC", ("SIG", "INIT", "HIST", "SAT_A", "ADM_A", "PHI")),
    "CONTAINMENT": ("OPEN-PROOF", ("PROD_RULES", "DOM", "OBS")),
    "EFFECT_HANDLERS": ("OPEN-PROOF", ("SIG", "RAW", "HIST", "BOUND_ADAPT", "EBRIDGE", "SUBIMAGE", "RELEASE", "ORDINARY")),
    "SELECTION": ("OPEN-PROOF", ("SELECT", "ROLE_ASSOC", "RESOLVE_FP")),
    "SOURCE_ADEQUACY": ("OPEN-PROOF", ("SOURCE_J", "COMPLETE", "EFFECT_HANDLERS", "CONTAINMENT", "SELECTION")),
    "SOUND": ("OPEN-PROOF", ("SOURCE_ADEQUACY", "EFFECTIVE")),
    "PRINCIPAL": ("OPEN-PROOF", ("SOURCE_ADEQUACY", "ALLVIEW", "EFFECTIVE")),
    "LIFECYCLE": ("OPEN-PROOF", ("IFACE", "LIFE", "GEN", "PRINCIPAL")),
    "PRODUCTION": ("OPEN-PROOF", ("SOUND", "PRINCIPAL", "CONTAINMENT", "LIFECYCLE", "LIMIT", "HIR", "ORACLE")),
    "CUTOVER": ("OPEN-PROOF", ("PRODUCTION",)),
}

DEPENDENCIES = (
    "AGENTS.md", "rules/research-lab.md", "rules/design-authority.md", "rules/git-concurrency.md",
    "tasks/current.md", "tasks/2026-10-06-current-before-directional-protection.md",
    "notes/theory/inference-theorem-dependencies.md", "notes/theory/inference-theory-map.md",
    "notes/design/2026-09-29-scc-intrusion-redesign-charter.md",
    "notes/design/2026-10-03-open-residual-factorization.md",
    "notes/design/2026-10-03-source-context-finite-closure.md",
    "notes/design/2026-10-04-common-allowance-context-preimage.md",
    "notes/design/2026-10-04-certified-callback-and-constrained-use.md",
    "notes/design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md",
    "notes/design/2026-10-02-source-interface-adequacy-theorem.md",
    "notes/design/2026-10-02-ordinary-computation-semantics-package.md",
    "notes/design/2026-10-02-typed-computation-core-elaboration.md",
    "notes/design/2026-10-02-typed-boundary-realization-draft.md",
    "notes/design/2026-10-03-concrete-compatibility-boundary.md",
    "notes/design/2026-10-05-source-contracts-and-common-allowance.md",
    "notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md",
    "notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md",
    "notes/progress/2026-10-06-erow-hinst-boundary-activation.md",
    "notes/progress/2026-10-06-directional-profile-completion-factorization.md",
    "notes/progress/2026-10-06-directional-source-view-instantiation-construction.md",
    "notes/progress/2026-10-06-source-profile-admission-construction.md",
    "notes/progress/2026-10-06-all-view-unequal-grammar-source-pair-audit.md",
    "notes/progress/2026-10-05-residual-admission-source-premise-audit.md",
    "notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md",
    "notes/progress/2026-10-05-inference-lifecycle-interface-conditional.md",
    "notes/progress/2026-10-04-local-state-capture-observation.md",
    "notes/progress/2026-10-05-local-state-multishot-playground.md",
    "notes/progress/2026-10-05-inequality-endpoint-dispatch-playground.md",
    "questions/2026-10-05-production-function-denotation/approved-answer.md",
    "questions/2026-10-05-production-function-bound-membership/approved-answer.md",
    "questions/2026-10-05-handler-protection-release-crossing/approved-answer.md",
    "crates/yu-hir/src/lib.rs", "crates/yu-solver/src/lib.rs",
)


def check_dag() -> tuple[int, int]:
    nodes = set(LEAVES) | set(CLOSED_SCOPES) | set(AGGREGATES)
    assert len(nodes) == len(LEAVES) + len(CLOSED_SCOPES) + len(AGGREGATES)
    for status, _ in (*LEAVES.values(), *CLOSED_SCOPES.values(), *AGGREGATES.values()):
        assert status in STATUSES
        assert status != "BLOCKED-BY-USER-DECISION"
    seen: set[str] = set()
    active: set[str] = set()

    def visit(node: str) -> None:
        assert node in nodes
        assert node not in active, f"cyclic gate dependency: {node}"
        if node in seen:
            return
        active.add(node)
        if node in AGGREGATES:
            dependencies = AGGREGATES[node][1]
            assert len(dependencies) == len(set(dependencies))
            for dependency in dependencies:
                visit(dependency)
        active.remove(node)
        seen.add(node)

    for node in sorted(nodes):
        visit(node)
    return len(nodes), sum(len(deps) for _, deps in AGGREGATES.values())


def check_cuts() -> None:
    # Compatible completion is a *shared* existential source coordinate.
    # Separate nonempty fragments do not construct a common completion.
    p0, p1 = {0}, {1}
    assert p0 and p1 and not (p0 & p1)
    # A complete shared fiber can instead be retained before projection;
    # its one source coordinate is used by every downstream query.
    joint = {("x", 0, "w0"), ("x", 1, "w1")}
    uses = {("x", 1, "w1", "v")}
    projected = {v for x, p, w, v in uses if (x, p, w) in joint}
    assert projected == {"v"}
    # Total common allowance does not imply all-view Direct evidence.
    sources, allowances = {"s"}, {"a"}
    q = {("s", "a")}
    valid_views = {"v"}
    direct: set[tuple[str, str, str]] = set()
    assert all(any((s, a) in q for a in allowances) for s in sources)
    assert valid_views and not any((s, a, "v") in direct for s, a in q)
    # Source-reference equality/inclusion does not account for a licensed
    # production-only observation. This is a relation-countermodel, not an
    # assertion that these predicates are actual admitted source rules.
    ref_actual, ref_checked = {"good"}, {"good"}
    production_actual, production_checked = {"good", "extra"}, {"good"}
    assert ref_actual <= ref_checked
    assert not production_actual <= production_checked
    # Approved endpoint-local discriminator; compressing an intermediate
    # source query invents a third local concrete success.
    empty, string, integer = "{}", "{foo?:string}", "{foo?:int}"
    concrete = {(empty, empty), (string, string), (integer, integer),
                (string, empty), (empty, string), (empty, integer)}
    assert (string, empty) in concrete and (empty, integer) in concrete
    assert (string, integer) not in concrete
    # Pure structural existence supplies no joint Phi witness by itself.
    structural = {0, 1}
    phi: set[int] = set()
    assert structural and not structural & phi


def main() -> None:
    counts = check_dag()
    check_cuts()
    print(f"PASS: {counts[0]} unique gate nodes, {counts[1]} acyclic dependency edges")
    print("PASS: shared-completion construction and five distinct nonimplication cuts")
    print("Scope: inventory/algebra only; zero parsed-source/production acceptance cases")
    root = Path(__file__).resolve().parents[1]
    for name in DEPENDENCIES:
        print(f"{hashlib.sha256((root / name).read_bytes()).hexdigest()}  {name}")


if __name__ == "__main__":
    main()
