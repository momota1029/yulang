#!/usr/bin/env python3
"""Finite quotient feedback playground for q = Function(x, Int), x <: q.

This small checker exercises the reviewed Fbar/G conflict-rank account on the
open structural feedback example from 2026-10-04. It enumerates truncated
free-monoid quotients, including noncommuting left descriptor shifts and right
comparison descent. It is a characterization experiment for this package,
not an FMP checker or proof.

Run: python3 tools/research_structural_feedback.py [max-depth]
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import sys


ARG, RET = "arg", "ret"
TRACKS = ("q", "x", "i")


@dataclass(frozen=True)
class CutoffMonoid:
    depth: int
    words: tuple[tuple[str, ...], ...]
    overflow: int
    table: tuple[tuple[int, ...], ...]
    generators: tuple[int, int]

    @classmethod
    def build(cls, depth: int) -> "CutoffMonoid":
        if depth < 0:
            raise ValueError("depth must be nonnegative")
        words = [()]
        for n in range(1, depth + 1):
            words.extend(product((ARG, RET), repeat=n))
        index = {word: i for i, word in enumerate(words)}
        overflow = len(words)
        size = overflow + 1
        table = []
        for left in range(size):
            row = []
            for right in range(size):
                if left == overflow or right == overflow:
                    row.append(overflow)
                    continue
                joined = words[left] + words[right]
                row.append(index.get(joined, overflow))
            table.append(tuple(row))
        return cls(depth, tuple(words), overflow, tuple(table),
                   (index[(ARG,)] if depth else overflow,
                    index[(RET,)] if depth else overflow))

    @property
    def size(self) -> int:
        return self.overflow + 1

    def mul(self, left: int, right: int) -> int:
        return self.table[left][right]


@dataclass(frozen=True)
class FiniteMonoid:
    table: tuple[tuple[int, ...], ...]
    generators: tuple[int, int]

    @property
    def size(self) -> int:
        return len(self.table)

    def mul(self, left: int, right: int) -> int:
        return self.table[left][right]


def generated_monoid(table: tuple[tuple[int, ...], ...], generators: tuple[int, int]) -> set[int]:
    seen = {0, *generators}
    changed = True
    while changed:
        old = len(seen)
        seen |= {table[x][y] for x in tuple(seen) for y in tuple(seen)}
        changed = len(seen) != old
    return seen


def enumerate_two_generated_monoids(max_size: int) -> list[FiniteMonoid]:
    """Enumerate labelled finite monoids with identity 0 and two generators."""
    found = {}
    for n in range(1, max_size + 1):
        cells = tuple((i, j) for i in range(1, n) for j in range(1, n))
        for outputs in product(range(n), repeat=len(cells)):
            rows = [[0] * n for _ in range(n)]
            for i in range(n):
                rows[0][i] = i
                rows[i][0] = i
            for (i, j), value in zip(cells, outputs):
                rows[i][j] = value
            table = tuple(tuple(row) for row in rows)
            if any(table[table[i][j]][k] != table[i][table[j][k]]
                   for i in range(n) for j in range(n) for k in range(n)):
                continue
            for generators in product(range(n), repeat=2):
                if len(generated_monoid(table, generators)) == n:
                    found[(table, generators)] = FiniteMonoid(table, generators)
    return list(found.values())


@dataclass
class Closure:
    domain: set[tuple[str, int]]
    heads: dict[tuple[str, int], str]
    active: set[tuple[int, int]]  # address, orientation (+1/-1)
    conflict: str | None = None


@dataclass(frozen=True)
class GraphNode:
    head: str
    children: tuple[tuple[str, int], ...]


def build_and_check_witness(monoid: FiniteMonoid,
                            state: Closure) -> tuple[list[GraphNode], dict[tuple[str, int], int]]:
    """Default the saturated quotient facts and check the resulting graph.

    This is an independent finite-graph check of the no-conflict completion:
    it checks exact shifted descriptors and the original comparison directly,
    using coinductive pair traversal rather than the Fbar/G saturation sets.
    """
    refs = {(track, m): i * monoid.size + m
            for i, track in enumerate(TRACKS) for m in range(monoid.size)}
    graph = []
    for track in TRACKS:
        for m in range(monoid.size):
            head = state.heads.get((track, m), "Record")
            if (track, m) not in state.domain:
                # Non-live states are never referenced by a live parent or
                # descriptor equation; give them a harmless private default.
                head = "Record"
            if head == "Function":
                children = ((ARG, refs[(track, monoid.mul(m, monoid.generators[0]))]),
                            (RET, refs[(track, monoid.mul(m, monoid.generators[1]))]))
                assert all((track, monoid.mul(m, c)) in state.domain
                           for c in monoid.generators)
            else:
                children = ()
            graph.append(GraphNode(head, children))

    def equal(left: int, right: int) -> bool:
        pending, seen = [(left, right)], set()
        while pending:
            pair = pending.pop()
            if pair in seen:
                continue
            seen.add(pair)
            x, y = graph[pair[0]], graph[pair[1]]
            if x.head != y.head or tuple(k for k, _ in x.children) != tuple(k for k, _ in y.children):
                return False
            pending.extend((xc, yc) for (_, xc), (_, yc) in zip(x.children, y.children))
        return True

    def sub(lower: int, upper: int) -> bool:
        pending, seen = [(lower, upper)], set()
        while pending:
            pair = pending.pop()
            if pair in seen:
                continue
            seen.add(pair)
            lo, hi = graph[pair[0]], graph[pair[1]]
            if lo.head != hi.head:
                return False
            if lo.head == "Function":
                lc, uc = dict(lo.children), dict(hi.children)
                pending.append((uc[ARG], lc[ARG]))
                pending.append((lc[RET], uc[RET]))
            elif lo.head == "Record" and not dict(hi.children).keys() <= dict(lo.children).keys():
                return False
        return True

    q, x, integer = refs[("q", 0)], refs[("x", 0)], refs[("i", 0)]
    q_children = dict(graph[q].children)
    assert graph[q].head == "Function" and graph[integer].head == "Int"
    assert equal(q_children[ARG], x), "descriptor q[arg] = x failed in graph witness"
    assert equal(q_children[RET], integer), "descriptor q[ret] = Int failed in graph witness"
    assert sub(x, q), "original bound x <: q failed in graph witness"
    return graph, refs


def saturate(monoid: CutoffMonoid | FiniteMonoid) -> tuple[int | None, Closure, list[tuple[int, int, int]]]:
    """Return first conflicting round under the complete restricted rules.

    Fbar saturates exact shifted descriptors, domain/head/child coherence, and
    same-address head transfer for active comparisons. G saturates guarded
    Function descent, retaining original orientation and never composing
    separate concrete comparisons.
    """
    a, r = monoid.generators
    state = Closure({(t, 0) for t in TRACKS},
                    {("q", 0): "Function", ("i", 0): "Int"},
                    {(0, 1)})
    round_sizes = []

    def set_head(key: tuple[str, int], head: str) -> bool:
        old = state.heads.get(key)
        if old is not None and old != head:
            state.conflict = f"head clash at {key}: {old} vs {head}"
            return False
        if old is None:
            state.heads[key] = head
            return True
        return False

    def fbar(include_active: bool = True) -> bool:
        changed_any = False
        while state.conflict is None:
            changed = False

            # Every forced head is attached to a live structural address.
            for key in tuple(state.heads):
                if key not in state.domain:
                    state.domain.add(key)
                    changed = True

            # Descriptor equations q[arg w] = x[w], q[ret w] = i[w].
            for m in range(monoid.size):
                for c, child_track in ((a, "x"), (r, "i")):
                    qm = ("q", monoid.mul(c, m))
                    cm = (child_track, m)
                    if qm in state.domain or cm in state.domain:
                        for item in (qm, cm):
                            if item not in state.domain:
                                state.domain.add(item)
                                changed = True
                    qh, ch = state.heads.get(qm), state.heads.get(cm)
                    if qh is not None and ch is None:
                        changed |= set_head(cm, qh)
                    elif ch is not None and qh is None:
                        changed |= set_head(qm, ch)
                    elif qh is not None and ch is not None and qh != ch:
                        state.conflict = f"descriptor head clash: {qm}={qh}, {cm}={ch}"
                        break
                if state.conflict:
                    break

            # Prefix closure, shape-forced children, and child-to-parent heads.
            if state.conflict is None:
                for track in TRACKS:
                    for m in range(monoid.size):
                        parent = (track, m)
                        parent_live = parent in state.domain
                        parent_head = state.heads.get(parent)
                        for c in (a, r):
                            child = (track, monoid.mul(m, c))
                            child_live = child in state.domain
                            # Full domain/head coherence in both directions.
                            # Every child coordinate is a tagged Function
                            # port; in this fragment there are no Record fields.
                            if child_live:
                                if not parent_live:
                                    state.domain.add(parent)
                                    parent_live = True
                                    changed = True
                                if parent_head is None:
                                    changed |= set_head(parent, "Function")
                                    parent_head = state.heads.get(parent)
                            if parent_head == "Function" and not child_live:
                                state.domain.add(child)
                                changed = True
                            if parent_head == "Int" and child_live:
                                state.conflict = f"atom has live child: {(track, m, c)}"
                                break
                        if state.conflict:
                            break
                    if state.conflict:
                        break

            # Active comparison requires compatible heads and transfers a
            # known fixed head across both endpoints.
            if state.conflict is None and include_active:
                for m, _orientation in tuple(state.active):
                    left, right = state.heads.get(("x", m)), state.heads.get(("q", m))
                    if left is not None and right is not None and left != right:
                        state.conflict = f"comparison head clash at {m}: {left} vs {right}"
                        break
                    if left is not None and right is None:
                        changed |= set_head(("q", m), left)
                    elif right is not None and left is None:
                        changed |= set_head(("x", m), right)

            changed_any |= changed
            if not changed:
                return changed_any
        return changed_any

    def g() -> bool:
        changed_any = False
        while state.conflict is None:
            changed = False
            for m, orientation in tuple(state.active):
                left, right = state.heads.get(("x", m)), state.heads.get(("q", m))
                if left is not None and right is not None and left != right:
                    state.conflict = f"comparison head clash at {m}: {left} vs {right}"
                    break
                if left == right == "Function":
                    children = ((monoid.mul(m, a), -orientation),
                                (monoid.mul(m, r), orientation))
                    for item in children:
                        if item not in state.active:
                            state.active.add(item)
                            changed = True
            changed_any |= changed
            if not changed:
                return changed_any
        return changed_any

    # The initial U_0 descriptor-only closure has rank zero. This matters for
    # quotients such as the singleton, where exact child shifts identify the
    # q root with its incompatible Function/Int observations before the bound
    # activation contributes anything.
    fbar(include_active=False)
    if state.conflict:
        return 0, state, round_sizes

    # There are at most 11*|M| positive facts: three tracks of domain bits,
    # two possible heads per track/address, and two orientations per address.
    for round_no in range(1, monoid.size * 11 + 2):
        fbar()
        if state.conflict:
            return round_no, state, round_sizes
        g()
        round_sizes.append((len(state.domain), len(state.heads), len(state.active)))
        if state.conflict:
            return round_no, state, round_sizes
        # Both phases compute least fixed points; no newly added facts means
        # the joint feedback has stabilized conflict-free.
        before = (len(state.domain), len(state.heads), len(state.active))
        fbar()
        if state.conflict:
            return round_no, state, round_sizes
        after = (len(state.domain), len(state.heads), len(state.active))
        if before == after:
            return None, state, round_sizes
    raise AssertionError("finite monotone closure exceeded its fact bound")


def expected_overflow_rank(monoid: CutoffMonoid) -> int:
    """Closed-form rank for this package under the documented round convention."""
    # The failure first appears when q's Int return observation and Function
    # spine have been transported to the same cutoff class. This formula is
    # tested against saturation below; it is not used by the saturation.
    return monoid.depth - 1


def main() -> None:
    max_depth = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    if max_depth < 2 or max_depth > 10:
        raise SystemExit("max-depth must be in 2..=10 (finite search budget)")
    rows = []
    for depth in range(2, max_depth + 1):
        monoid = CutoffMonoid.build(depth)
        rank, state, rounds = saturate(monoid)
        assert rank is not None, (depth, state, rounds)
        assert rank == expected_overflow_rank(monoid), (depth, rank, rounds)
        # The fully coherent model must reject through a real local denial;
        # depending on which quotient preimage is saturated first, that can be
        # the atom/live-child clash on x, q, or i rather than a head clash at Ω.
        assert state.conflict.startswith(("atom has live child:",
                                          "comparison head clash:",
                                          "descriptor head clash:"))
        rows.append((depth, monoid.size, rank, len(state.domain), len(state.heads)))
    print("package: q = Function(x, Int), x <: q; alphabet={arg,ret}")
    print("depth quotient-elements first-conflict-round live-pairs forced-heads")
    for row in rows:
        print("%5d %16d %20d %11d %13d" % row)
    small = enumerate_two_generated_monoids(4)
    outcomes = {"SAT": 0, "CONFLICT": 0}
    rank_histogram: dict[int, int] = {}
    earliest: tuple[int, FiniteMonoid, str] | None = None
    witness: tuple[FiniteMonoid, Closure] | None = None
    for monoid in small:
        rank, state, _ = saturate(monoid)
        if rank is None:
            outcomes["SAT"] += 1
            build_and_check_witness(monoid, state)
            if witness is None:
                witness = (monoid, state)
        else:
            outcomes["CONFLICT"] += 1
            rank_histogram[rank] = rank_histogram.get(rank, 0) + 1
            candidate = (rank, monoid, state.conflict or "unknown")
            if earliest is None or candidate[0] < earliest[0]:
                earliest = candidate
    print("exhaustive two-generated monoids through size 4: %d presentations; %s"
          % (len(small), outcomes))
    singleton_rank, singleton_state, _ = saturate(FiniteMonoid(((0,),), (0, 0)))
    assert singleton_rank == 0 and singleton_state.conflict is not None
    print("conflict-rank histogram: %r; singleton descriptor conflict is rank 0"
          % rank_histogram)
    if witness:
        wm, _ = witness
        assert wm.mul(wm.generators[0], wm.generators[1]) != wm.mul(wm.generators[1], wm.generators[0]), \
            "selected witness should exercise distinct left and right actions"
        print("first independently checked finite graph witness: |M|=%d generators=%r table=%r"
              % (wm.size, wm.generators, wm.table))
        print("witness has noncommuting address actions: arg*ret=%d, ret*arg=%d"
              % (wm.mul(wm.generators[0], wm.generators[1]),
                 wm.mul(wm.generators[1], wm.generators[0])))
    if earliest:
        print("smallest conflict witness: |M|=%d generators=%r rank=%d reason=%s"
              % (earliest[1].size, earliest[1].generators,
                 earliest[0], earliest[2]))
    print("finite cutoff quotients fail with increasing ranks; this package has\n"
          "a regular model x=q=Function(self,Int), so this is not a BR/FMP\n"
          "counterexample. Search covers only this package family and cutoff\n"
          "monoids; arbitrary finite monoids and arbitrary Gamma_P remain open.")


if __name__ == "__main__":
    main()
