#!/usr/bin/env python3
"""Finite check of transitive admission-dependency closure.

Theorem 4 in callback-coverage-and-source-joins.md says safe hiding must close
admission operands through the source evidence that an exposed request was
produced and retained. This checker represents that proof dependency as a
small graph, exhausts all Boolean inputs, and shrinks a mutant that omits the
edge to the request producer.

It is an incidence/data-dependency model, not an operational Yulang evaluator
or a production source certificate.

Run: python3 tools/research_callback_dependency_closure.py
"""

from __future__ import annotations

from itertools import product


INPUTS = (
    "challenge_ok",
    "provider_lookup",
    "call_executed",
    "continuation_retained",
    "owner_valid",
    "private_body_value",
)

# Derived certificate facts and all of their existing operands. An exposed
# request is supported only if a callable was looked up, its call ran, and the
# resulting request and continuation remain in the history.
DEPENDENCIES = {
    "admission": ("challenge_ok", "request_exposed", "owner_valid"),
    "request_exposed": ("request_produced", "continuation_retained"),
    "request_produced": ("provider_lookup", "call_executed"),
}
SCHEMA_SEEDS = frozenset({"admission"})


def evaluate(node: str, assignment: dict[str, bool]) -> bool:
    if node in assignment:
        return assignment[node]
    operands = DEPENDENCIES[node]
    return all(evaluate(operand, assignment) for operand in operands)


def dependency_closure(
    seeds: frozenset[str], skipped_edges: frozenset[tuple[str, str]] = frozenset()
) -> frozenset[str]:
    seen = set()
    pending = list(seeds)
    while pending:
        node = pending.pop()
        if node in seen:
            continue
        seen.add(node)
        for operand in DEPENDENCIES.get(node, ()):
            if (node, operand) not in skipped_edges:
                pending.append(operand)
    return frozenset(seen)


def assignment_for(bits: tuple[bool, ...]) -> dict[str, bool]:
    return dict(zip(INPUTS, bits, strict=True))


def preserved_on_hidden_complement(closure: frozenset[str]) -> tuple[int, int]:
    hidden = frozenset(INPUTS) - closure
    assignments = [
        assignment_for(bits)
        for bits in product((False, True), repeat=len(INPUTS))
    ]
    admitted = sum(evaluate("admission", row) for row in assignments)
    comparisons = 0
    for left in assignments:
        for right in assignments:
            if all(left[name] == right[name] for name in closure if name in INPUTS):
                # The two assignments may differ only in hidden inputs; the
                # closure variables that are derived are deterministic nodes.
                assert evaluate("admission", left) == evaluate("admission", right)
                comparisons += 1
    return admitted, comparisons


def minimal_missing_producer_counterexample():
    # Mutant scanner follows `request_exposed -> continuation_retained` but
    # omits `request_exposed -> request_produced`. The evaluator still follows
    # the real complete dependency graph.
    bad = dependency_closure(
        SCHEMA_SEEDS,
        skipped_edges=frozenset({("request_exposed", "request_produced")}),
    )
    assignments = [
        assignment_for(bits)
        for bits in product((False, True), repeat=len(INPUTS))
    ]
    candidates = []
    for left in assignments:
        for right in assignments:
            if all(left[name] == right[name] for name in bad if name in INPUTS):
                if evaluate("admission", left) != evaluate("admission", right):
                    changed = tuple(name for name in INPUTS if left[name] != right[name])
                    candidates.append((len(changed), changed, left, right))
    assert candidates
    _, changed, left, right = min(
        candidates,
        key=lambda row: (row[0], row[1], row[2]["call_executed"]),
    )
    assert changed == ("call_executed",)
    return bad, left, right


def main() -> None:
    closure = dependency_closure(SCHEMA_SEEDS)
    admitted, comparisons = preserved_on_hidden_complement(closure)
    bad, left, right = minimal_missing_producer_counterexample()
    assert frozenset(INPUTS) - closure == frozenset({"private_body_value"})
    assert left["call_executed"] is False and right["call_executed"] is True
    assert evaluate("admission", left) is False and evaluate("admission", right) is True
    print(f"finite certificate assignments checked: {2 ** len(INPUTS)}")
    print(f"full-closure assignment-pair checks: {comparisons}")
    print(f"admitted assignments: {admitted}")
    print(f"safe hidden complement under transitive incidence: {sorted(set(INPUTS) - closure)}")
    print(f"mutant omitted-producer closure: {sorted(bad)}")
    print("minimal mutant failure: one `call_executed` bit changes admission while all mutant-marked inputs stay fixed")
    print("scope: exposed-request admission dependency only; no production certificate extraction or callback bound interpretation")


if __name__ == "__main__":
    main()
