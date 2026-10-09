#!/usr/bin/env python3
"""Small source-inspected algebra witnesses; not an Oracle/compiler invocation.

Natural counts intentionally replace Oracle u32 storage. One ID's set is E.
This checks arbitrary operation contexts, not source reachability or output rows.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class W:
    p: int = 0
    n: int = 0
    r: int = 0
    filter: frozenset = frozenset(("E", "F"))


ALL = frozenset(("E", "F"))
E = frozenset(("E",))
F = frozenset(("F",))
ZERO = W()


def compose_counts(p, n, q, m):
    if q <= n:
        return p, n - q + m
    return p + q - n, m


def replay(a, b):
    p, n = compose_counts(a.p, a.n, b.p, b.n)
    r = b.r + a.r
    filter_set = a.filter & b.filter
    # Exact DirectedWeights::mix specialization, including single-side guard.
    if not (p or n) or not r:
        return W(p, n, r, filter_set)
    p, n = compose_counts(p, n, r, 0)
    return W(p, n, 0, filter_set) if n else W(0, 0, p, filter_set)


def swap(a):
    return W(a.r, 0, a.p, ALL)


def support_key(a):
    return bool(a.p), bool(a.n), E if a.n else None, bool(a.r)


def active_filter_passes(a, permitted):
    return not a.n or E <= permitted


def literal_replay(a, b):
    # Independent literal reduction before directed placement, one ID only.
    stream = ["-"] * a.p + ["+"] * a.n
    stream += ["-"] * b.p + ["+"] * b.n
    reduced = []
    for token in stream:
        if token == "-" and reduced and reduced[-1] == "+":
            reduced.pop()
        else:
            reduced.append(token)
    rpops = b.r + a.r
    if not reduced or not rpops:
        return W(reduced.count("-"), reduced.count("+"), rpops,
                 a.filter & b.filter)
    for _ in range(rpops):
        if reduced and reduced[-1] == "+":
            reduced.pop()
        else:
            reduced.append("-")
    if "+" in reduced:
        return W(reduced.count("-"), reduced.count("+"), 0,
                 a.filter & b.filter)
    return W(0, 0, len(reduced), a.filter & b.filter)


def main():
    tiny = [W(p, n, r) for p in range(3) for n in range(3) for r in range(3)]
    comparisons = 0
    for a in tiny:
        for b in tiny:
            assert replay(a, b) == literal_replay(a, b)
            comparisons += 1

    push1, push2, right_pop = W(n=1), W(n=2), W(r=1)
    assert support_key(push1) == support_key(push2)
    assert replay(push1, right_pop) == ZERO
    assert replay(push2, right_pop) == push1
    assert active_filter_passes(replay(push1, right_pop), F)
    assert not active_filter_passes(replay(push2, right_pop), F)

    # All pairs in this bounded prefix illustrate the universal proof in note.
    pop_pairs = 0
    for n in range(1, 33):
        for m in range(n + 1, 34):
            assert support_key(W(p=n)) == support_key(W(p=m))
            small = replay(swap(W(p=n)), W(n=n + 1))
            large = replay(swap(W(p=m)), W(n=n + 1))
            assert not active_filter_passes(small, F)
            assert active_filter_passes(large, F)
            pop_pairs += 1

    a, b, c = W(p=1), W(r=1), W(n=1)
    left_grouped = replay(replay(a, b), c)
    right_grouped = replay(a, replay(b, c))
    assert left_grouped == W(r=1)
    assert right_grouped == W(p=1)
    assert replay(left_grouped, c) == ZERO
    assert replay(right_grouped, c) == W(p=1, n=1)

    # Minimal uniform insertion contract: a contextual self-use with E filter
    # registers it on x; later F lower conflicts. Dropping first task loses it.
    retained_filters = {E}
    assert any(not F <= permitted for permitted in retained_filters)
    dropped_filters = set()
    assert not any(not F <= permitted for permitted in dropped_filters)

    # Equal row and family do not cancel distinct attachment coordinates.
    attached = {0: (0, 1)}
    consumed = dict(attached)
    consumed[0] = compose_counts(*consumed[0], 1, 0)
    assert consumed[0] == (0, 0)
    independent = dict(attached)
    independent[1] = compose_counts(0, 0, 1, 0)
    assert independent[0] == (0, 1) and independent[1] == (1, 0)
    print(f"PASS {comparisons} literal/count comparisons; {pop_pairs} POP-pair "
          "distinguishers; support replay, nonassociativity, self-filter, "
          "distinct-authority witnesses")


if __name__ == "__main__":
    main()
