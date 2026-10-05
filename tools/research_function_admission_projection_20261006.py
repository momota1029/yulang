#!/usr/bin/env python3
"""Finite information-loss experiment; NOT a production semantics oracle.

Supplied envelope U contains four same-typed complete packets (x,y).
Coordinates stand for two history-linked references, not integer values.
No source transitions, EnvStore, endpoint judgments, or production predicates
are implemented. The reference is exact inclusion of supplied packet sets.
The candidate uses only unary projections, or a constant shallow/port view.
An exact packet-bitset control checks that these losses are avoidable.
Exhaustive range: all 16 subsets of U, all 256 ordered pairs; no random seed.
No filesystem writes, subprocesses, dependencies, or compiler tests.
"""

from itertools import product
import json


U = tuple(product(range(2), repeat=2))
RELATIONS = tuple(
    frozenset(packet for i, packet in enumerate(U) if mask & (1 << i))
    for mask in range(1 << len(U))
)


def exact_inclusion(left, right):
    # Reference uses complete supplied packets, never candidate summaries.
    return all(packet in right for packet in left)


def marginals(relation):
    return tuple(frozenset(packet[i] for packet in relation) for i in range(2))


def projected_inclusion(left, right):
    return all(a <= b for a, b in zip(marginals(left), marginals(right)))


def bitset(relation):
    return sum(1 << i for i, packet in enumerate(U) if packet in relation)


def show(relation):
    return sorted(map(list, relation))


def main():
    pairs = tuple(product(RELATIONS, repeat=2))
    losses = [
        (left, right) for left, right in pairs
        if projected_inclusion(left, right) and not exact_inclusion(left, right)
    ]
    collisions = [
        (left, right) for left, right in losses
        if marginals(left) == marginals(right)
    ]
    common_base_collisions = [
        (left, right) for left, right in collisions if left & right
    ]
    assert losses and collisions and common_base_collisions
    # Exhaustive minima in this supplied 2x2 envelope, counting tuple entries.
    assert min(len(a) + len(b) for a, b in losses) == 3
    assert min(len(a) + len(b) for a, b in collisions) == 4
    assert min(len(a) + len(b) for a, b in common_base_collisions) == 5
    assert all(
        exact_inclusion(a, b) == ((bitset(a) & ~bitset(b)) == 0)
        for a, b in pairs
    )
    assert all(
        not exact_inclusion(a, b) or projected_inclusion(a, b)
        for a, b in pairs
    )

    base = frozenset({(0, 0)})
    diagonal = frozenset({(0, 0), (1, 1)})
    three = frozenset({(0, 0), (0, 1), (1, 0)})
    assert base <= diagonal and base <= three
    assert marginals(diagonal) == marginals(three)
    assert (1, 1) in diagonal and (1, 1) not in three
    # P experiment: identical singleton challenge, supplied output relations.
    p_actual = {"h": diagonal}
    p_checked = {"h": three}
    assert projected_inclusion(p_actual["h"], p_checked["h"])
    assert not exact_inclusion(p_actual["h"], p_checked["h"])
    # D experiment: independently supplied admission predicates; direction C<=A.
    d_checked, d_actual = diagonal, three
    assert projected_inclusion(d_checked, d_actual)
    assert not exact_inclusion(d_checked, d_actual)
    # Named mutant: separately hide the linked witnesses and recombine them.
    cartesian = frozenset(product(*marginals(diagonal)))
    assert cartesian - diagonal == {(0, 1), (1, 0)}
    # Even retaining exact returned-provider IDs drops their history linkage.
    shallow_view = lambda relation: frozenset(packet[1] for packet in relation)
    # The supplied packet types agree; no production pretty-printer is modeled.
    printed_view = lambda relation: frozenset({"same typed ports"}) if relation else frozenset()
    assert shallow_view(diagonal) == shallow_view(three)
    assert printed_view(diagonal) == printed_view(three)

    print(json.dumps({
        "claim": "bounded supplied-predicate projection counterexample",
        "domain": list(U), "relations": len(RELATIONS), "ordered_pairs": len(pairs),
        "projection_false_positives": len(losses),
        "same_marginals_false_positives": len(collisions),
        "common_nonempty_base_false_positives": len(common_base_collisions),
        "minimal_total_entries": {"inclusion_only": 3, "same_marginals": 4,
                                   "same_marginals_common_base": 5},
        "base": show(base), "left": show(diagonal), "right": show(three),
        "missing_packet": [1, 1],
        "mutants_rejected": ["independent witness recombination", "shallow value",
                             "printed ports", "coordinate inclusion"],
        "exact_bitset_control": "256/256",
        "failure_condition": "If production restrictions forbid the packet relations, no production falsification follows.",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
