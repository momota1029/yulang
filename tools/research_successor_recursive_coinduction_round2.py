#!/usr/bin/env python3
"""Bounded algebraic attacks on a conditional recursive certificate method.

This is not a Yulang interpreter or a descriptor/admission implementation.
The finite carrier has two distinguished obligation records. No subprocess,
randomness, source acceptance oracle, semantic search, or generated file is used.
"""

import hashlib
import itertools
import json
from pathlib import Path
import resource
import signal


DEPENDENCIES = (
    "AGENTS.md",
    "rules/research-lab.md",
    "rules/design-authority.md",
    "rules/git-concurrency.md",
    "notes/theory/successor-proof-obligations.md",
    "notes/design/2026-10-02-source-result-synthesis-choice.md",
    "notes/design/2026-10-02-typed-computation-core-elaboration.md",
    "notes/design/2026-10-02-ordinary-computation-semantics-package.md",
    "notes/design/2026-10-05-source-contracts-and-common-allowance.md",
    "notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md",
    "notes/progress/2026-10-06-recursive-source-validation-construction.md",
    "notes/progress/2026-10-07-successor-recursive-synthesis.md",
    "notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md",
    "notes/progress/2026-10-07-rec-desc-latent-function-clause-audit.md",
    "notes/progress/2026-10-07-rec-desc-captured-name-lookup-stop.md",
    "notes/progress/2026-10-08-rec-desc-finite-reflection-quantifier-attack.md",
    "notes/progress/2026-10-09-rec-init-boundary-attack.md",
    "questions/2026-10-05-production-function-denotation/approved-answer.md",
    "questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md",
)


def leq(a, b):
    return a & ~b == 0


def monotone(op):
    return all(not leq(a, b) or leq(op[a], op[b])
               for a in range(4) for b in range(4))


def swap(bits):
    return ((bits & 1) << 1) | ((bits & 2) >> 1)


def main():
    resource.setrlimit(resource.RLIMIT_AS, (1 << 30, 1 << 30))
    signal.alarm(60)
    counts = {"operators": 0, "monotone_operators": 0,
              "fixed_point_absorption_pairs": 0, "static_guard_masks": 4,
              "frozen_domain_cases": 2, "quantifier_matrices": 16}
    for op in itertools.product(range(4), repeat=4):
        counts["operators"] += 1
        if not monotone(op):
            continue
        counts["monotone_operators"] += 1
        postfixed = [z for z in range(4) if leq(z, op[z])]
        union = 0
        for z in postfixed:
            union |= z
        assert op[union] == union
        for actual in range(4):
            if op[actual] != actual:
                continue
            absorbs = all(leq(z, actual) for z in postfixed)
            assert absorbs == leq(union, actual)
            counts["fixed_point_absorption_pairs"] += 1

    knot_op = tuple(swap(z) for z in range(4))
    assert knot_op == (0, 2, 1, 3)
    assert monotone(knot_op)
    assert knot_op[0] == 0 and knot_op[3] == 3
    assert leq(3, knot_op[3]) and not leq(3, 0)
    # A missing independent local guard cannot be repaired by the latent cycle.
    for guards in range(4):
        op = tuple(guards & swap(z) for z in range(4))
        maximal = 0
        for z in range(4):
            if leq(z, op[z]):
                maximal |= z
        assert maximal == (3 if guards == 3 else 0)

    # Forall admitted h. Good(z,h): adding admitted challenges can invalidate.
    def all_admitted_good(candidate, domain):
        return not domain or bool(candidate & 1)

    assert all_admitted_good(0, False)
    assert not all_admitted_good(0, True)
    for domain in (False, True):
        assert all(not leq(a, b) or
                   not all_admitted_good(a, domain) or
                   all_admitted_good(b, domain)
                   for a in range(4) for b in range(4))

    # Pointwise existential projection is monotone; joint witness factoring fails.
    wf, wg = {0}, {1}
    assert bool(wf) and bool(wg) and not bool(wf & wg)
    diagonal = None
    for flat in itertools.product((False, True), repeat=4):
        matrix = (flat[:2], flat[2:])
        pointwise = all(any(row) for row in matrix)
        uniform = any(all(matrix[h][w] for h in range(2)) for w in range(2))
        reflected = any(not any(row) for row in matrix)
        assert reflected == (not pointwise)
        if flat == (True, False, False, True):
            assert pointwise and not uniform
            diagonal = flat

    # The exact returned handle is an operand, not an interchangeable annotation.
    actual_returns = {"v_f": "v_g", "v_g": "v_f"}
    for callee, actual in actual_returns.items():
        assert actual != callee
        assert actual_returns[callee] == actual
        assert actual_returns[callee] != "fresh_copy"

    root = Path(__file__).resolve().parents[1]
    hashes = {path: hashlib.sha256((root / path).read_bytes()).hexdigest()
              for path in DEPENDENCIES}
    print(json.dumps({
        "status": "PASS algebraic conditional-method checks only",
        "coverage": counts,
        "unfolding_without_absorption": {
            "operator": knot_op, "actual_fixed_point": 0,
            "postfixed_candidate": 3},
        "negative_domain_witness": {"candidate": 0,
                                    "empty_domain": True,
                                    "one_bad_challenge": False},
        "shared_witness_projection": {"f": [0], "g": [1], "joint": []},
        "uniform_witness_diagonal": diagonal,
        "actual_returns": actual_returns,
        "dependency_sha256_working_snapshot": hashes,
        "limits": {"processes": 1, "wall_alarm_seconds": 60,
                   "address_space_bytes": 1 << 30},
    }, indent=2))
    signal.alarm(0)


if __name__ == "__main__":
    main()
