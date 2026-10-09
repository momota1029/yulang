#!/usr/bin/env python3
"""Unbounded cyclic word summaries and upward observers, research only.

This is not a second production solver or a source-to-Oracle equivalence test.
The reference is finite walks with literal per-ID cancellation.  Full directed
replay, Function swap, family-changing residuals and public support are excluded.
See notes/progress/2026-10-10-contextual-effect-path-theorem.md.

The algorithms impose no counter or iteration limit.  Bounds in main() delimit
only differential experiments; Python integers carry exact natural counts.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    op: str = ""
    attachment: int = 0
    # A conjunction of coordinate thresholds, tested before the operation.
    guard: tuple = ()


def compose(left, right):
    return {(a, c) for a, b in left for x, c in right if b == x}


def relation_power(relation, exponent, vertices):
    """Exact Boolean relation power, including arbitrarily large exponents."""
    assert exponent >= 0
    result = {(v, v) for v in range(vertices)}
    while exponent:
        if exponent & 1:
            result = compose(result, relation)
        relation = compose(relation, relation)
        exponent >>= 1
    return result


class NormalForms:
    """Finite automaton for exact one-ID normal forms POP^p PUSH^n.

    Balanced epsilon summaries retain actual original-edge witnesses.  Other
    IDs are projected to epsilon only for this one-ID query, never identified.
    """

    def __init__(self, vertices, edges, attachment=0):
        self.vertices = vertices
        self.edges = tuple(edges)
        self.attachment = attachment
        assert all(not e.guard for e in self.edges), "guarded walks need the observer"
        self.up = []
        self.down = []
        self.balanced = {(v, v): () for v in range(vertices)}
        for number, edge in enumerate(self.edges):
            assert edge.op in ("", "+", "-")
            if not edge.op or edge.attachment != attachment:
                self.balanced.setdefault((edge.source, edge.target), (number,))
            elif edge.op == "+":
                self.up.append(number)
            else:
                self.down.append(number)
        # Each successful addition fills one of exactly vertices**2 slots.
        while True:
            before = len(self.balanced)
            for (a, b), first in tuple(self.balanced.items()):
                for (x, c), second in tuple(self.balanced.items()):
                    if b == x:
                        self.balanced.setdefault((a, c), first + second)
            for up in self.up:
                for down in self.down:
                    a, z = self.edges[up], self.edges[down]
                    middle = self.balanced.get((a.target, z.source))
                    if middle is not None:
                        self.balanced.setdefault(
                            (a.source, z.target), (up,) + middle + (down,)
                        )
            if len(self.balanced) == before:
                break
        balanced = set(self.balanced)
        self.pop = compose(
            {(self.edges[e].source, self.edges[e].target) for e in self.down},
            balanced,
        )
        self.push = compose(
            {(self.edges[e].source, self.edges[e].target) for e in self.up},
            balanced,
        )

    def accepts(self, source, target, pops, pushes):
        paths = compose(
            set(self.balanced), relation_power(self.pop, pops, self.vertices)
        )
        paths = compose(paths, relation_power(self.push, pushes, self.vertices))
        return (source, target) in paths

    def witness(self, source, target, pops, pushes):
        """Decode a finite accepted word to an actual walk (small test queries)."""
        frontier = {
            v: walk for (u, v), walk in self.balanced.items() if u == source
        }
        for labels, count in ((self.down, pops), (self.up, pushes)):
            for _ in range(count):
                following = {}
                for v, prefix in frontier.items():
                    for label in labels:
                        edge = self.edges[label]
                        if edge.source == v:
                            for (u, w), suffix in self.balanced.items():
                                if u == edge.target:
                                    following.setdefault(w, prefix + (label,) + suffix)
                frontier = following
        return frontier.get(target)


def leq(a, b):
    return all(x <= y for x, y in zip(a, b))


class UpwardObserver:
    """Backward Simple-sub-style demand propagation on a supplied word graph.

    Each insertion is a genuine predecessor of an existing demand.  No source
    contribution, attachment, permission or new edge is manufactured here.
    """

    def __init__(self, vertices, dimensions, edges, targets):
        self.vertices, self.dimensions = vertices, dimensions
        self.edges = tuple(edges)
        self.basis = [set() for _ in range(vertices)]
        self.pending = deque()
        self.admissions = 0
        self.peak_basis = 0
        self.incoming = [[] for _ in range(vertices)]
        for edge in self.edges:
            assert edge.op in ("", "+", "-")
            assert not edge.guard or len(edge.guard) == dimensions
            self.incoming[edge.target].append(edge)
        for vertex, threshold in targets:
            self.insert(vertex, threshold)
        while self.pending:
            vertex, threshold = self.pending.popleft()
            if threshold not in self.basis[vertex]:
                continue
            for edge in self.incoming[vertex]:
                previous = list(threshold)
                i = edge.attachment
                if edge.op == "+":
                    previous[i] = max(previous[i] - 1, 0)
                elif edge.op == "-" and previous[i] > 0:
                    previous[i] += 1
                if edge.guard:
                    previous = [max(x, y) for x, y in zip(previous, edge.guard)]
                self.insert(edge.source, tuple(previous))

    def insert(self, vertex, threshold):
        assert len(threshold) == self.dimensions and min(threshold, default=0) >= 0
        current = self.basis[vertex]
        if any(leq(old, threshold) for old in current):
            return
        current.difference_update(old for old in tuple(current) if leq(threshold, old))
        current.add(threshold)
        self.pending.append((vertex, threshold))
        self.admissions += 1
        self.peak_basis = max(self.peak_basis, sum(map(len, self.basis)))

    def observes(self, vertex, incoming):
        assert len(incoming) == self.dimensions
        return any(leq(bound, incoming) for bound in self.basis[vertex])


def literal_normal(edges, walk, attachment=0):
    stack = []
    for number in walk:
        edge = edges[number]
        if edge.attachment != attachment or not edge.op:
            continue
        if edge.op == "-" and stack and stack[-1] == "+":
            stack.pop()
        else:
            stack.append(edge.op)
    return stack.count("-"), stack.count("+")


def forward(vertices, edges, source, incoming, targets, depth):
    """Independent bounded path search; its depth is an experiment bound only."""
    at = {(source, incoming)}
    target_set = tuple(targets)
    for _ in range(depth + 1):
        if any(v == u and leq(t, x) for v, x in at for u, t in target_set):
            return True
        following = set()
        for vertex, vector in at:
            for edge in edges:
                if edge.source != vertex or (edge.guard and not leq(edge.guard, vector)):
                    continue
                values = list(vector)
                if edge.op == "+":
                    values[edge.attachment] += 1
                elif edge.op == "-":
                    values[edge.attachment] = max(values[edge.attachment] - 1, 0)
                following.add((edge.target, tuple(values)))
        at = following
    return False


def main():
    # Materializing an edge iterator preserves observer propagation and guards.
    iterator_edges = [Edge(0, 1, "+", 0, (0, 1)), Edge(1, 2, "-", 1)]
    iterator_targets = ((2, (1, 1)),)
    listed = UpwardObserver(3, 2, iterator_edges, iterator_targets)
    iterated = UpwardObserver(3, 2, iter(iterator_edges), iterator_targets)
    assert listed.basis == iterated.basis
    assert listed.basis[0] == {(0, 2)}
    for initial in product(range(3), repeat=2):
        assert listed.observes(0, initial) == iterated.observes(0, initial)
    try:
        NormalForms(3, iter(iterator_edges))
    except AssertionError as error:
        assert str(error) == "guarded walks need the observer"
    else:
        raise AssertionError("guarded edge iterator was accepted")

    # Every directed two-vertex graph with at most one epsilon/+/− edge per pair.
    pairs = tuple(product(range(2), repeat=2))
    graph_count = bounded_walks = decoded = 0
    for labels in product((None, "", "+", "-"), repeat=4):
        edges = tuple(Edge(a, b, op) for (a, b), op in zip(pairs, labels) if op is not None)
        machine = NormalForms(2, edges)
        graph_count += 1
        for source in range(2):
            walks = {(source, ())}
            for _ in range(6):
                following = set()
                for target, walk in walks:
                    p, n = literal_normal(edges, walk)
                    assert machine.accepts(source, target, p, n)
                    bounded_walks += 1
                    for number, edge in enumerate(edges):
                        if edge.source == target:
                            following.add((edge.target, walk + (number,)))
                walks = following
            for target, p, n in product(range(2), range(3), range(3)):
                accepted = machine.accepts(source, target, p, n)
                witness = machine.witness(source, target, p, n)
                assert accepted == (witness is not None)
                if witness is not None:
                    vertex = source
                    for number in witness:
                        assert edges[number].source == vertex
                        vertex = edges[number].target
                    assert vertex == target and literal_normal(edges, witness) == (p, n)
                    decoded += 1

    # A nonself POP/identity cycle permits every POP count on a return to 0.
    # The separate all-POP cycle below permits exactly even return counts.
    # These counts are not solver bounds.
    cycle = NormalForms(2, (Edge(0, 1, "-"), Edge(1, 0, "")))
    for k in (0, 1, 2, 10**6, 10**30):
        assert cycle.accepts(0, 0, k, 0)
        assert not cycle.accepts(0, 0, k, 1)
    parity = NormalForms(2, (Edge(0, 1, "-"), Edge(1, 0, "-")))
    assert parity.accepts(0, 0, 10**30, 0)
    assert not parity.accepts(0, 0, 10**30 + 1, 0)

    # Unbounded PUSH cycles need no arbitrary source PUSH budget.
    growth = (Edge(0, 0, "+"), Edge(0, 1, "-"))
    target = ((1, (7,)),)
    assert UpwardObserver(2, 1, growth, target).basis[0] == {(0,)}
    assert forward(2, growth, 0, (0,), target, 10)
    pop_cycle = (Edge(0, 1, "-"), Edge(1, 0, ""))
    demand = UpwardObserver(2, 1, pop_cycle, ((1, (1,)),))
    assert demand.basis == [{(2,)}, {(1,)}]
    assert not demand.observes(0, (1,))
    assert demand.observes(0, (2,))  # late lower is a query, not new authority

    # Correlation control: independent branches never jointly activate both IDs.
    branches = (Edge(0, 1, "+", 0), Edge(0, 1, "+", 1))
    joint = UpwardObserver(2, 2, branches, ((1, (1, 1)),))
    assert joint.basis[0] == {(0, 1), (1, 0)}
    assert not joint.observes(0, (0, 0))
    assert joint.observes(0, (1, 0))
    assert joint.observes(0, (0, 1))

    # Same-family attachments remain different coordinates.  POP_0 removes only
    # its own protection.  Fresh copies rename IDs consistently, never alias them.
    original = (Edge(0, 1, "-", 0),)
    first = UpwardObserver(2, 2, original, ((1, (1, 0)),))
    second = UpwardObserver(2, 2, original, ((1, (0, 1)),))
    assert not first.observes(0, (1, 1)) and second.observes(0, (1, 1))
    renamed = UpwardObserver(2, 2, (Edge(0, 1, "-", 1),), ((1, (0, 1)),))
    assert renamed.basis[0] == {(0, 2)}

    # Delayed structural edge / row-coordinate quotient are finite graph edits.
    # They are abstract mutation controls, not production Function/intrusion tests.
    before_edges = (Edge(0, 1, "+", 0),)
    before = UpwardObserver(3, 1, before_edges, ((2, (1,)),))
    assert not before.observes(0, (0,))
    after = UpwardObserver(3, 1, before_edges + (Edge(1, 2),), ((2, (1,)),))
    assert after.observes(0, (0,))
    quotient = UpwardObserver(2, 1, (Edge(0, 1, "+", 0),), ((1, (1,)),))
    assert quotient.observes(0, (0,))
    # A separate speculative rebuild leaves the original immutable snapshot unchanged.
    snapshot = (before_edges, tuple(frozenset(b) for b in before.basis))
    speculative = UpwardObserver(3, 1, before_edges + (Edge(1, 2),), ((2, (1,)),))
    assert speculative.observes(0, (0,))
    assert snapshot == (before_edges, tuple(frozenset(b) for b in before.basis))

    # Finite DAGs give an independent COMPLETE reference, not bounded evidence
    # about cycles.  Guards exercise intersections and forbidden-family queries.
    alternatives = (None, ("", 0, ()), ("+", 0, ()), ("-", 0, ()),
                    ("+", 1, ()), ("-", 1, ()), ("", 0, (1, 0)))
    comparisons = 0
    for selected in product(alternatives, repeat=3):
        edges = tuple(Edge(a, b, *choice) for (a, b), choice in
                      zip(((0, 1), (1, 2), (0, 2)), selected) if choice is not None)
        for threshold in ((1, 0), (0, 1), (1, 1), (0, 0)):
            targets = ((2, threshold),)
            observer = UpwardObserver(3, 2, edges, targets)
            for initial in product(range(3), repeat=2):
                assert observer.observes(0, initial) == forward(3, edges, 0, initial, targets, 2)
                comparisons += 1

    print(f"PASS {graph_count} cyclic word graphs; {bounded_walks} bounded walks; "
          f"{decoded} decoded exact witnesses; {comparisons} complete DAG observer queries; "
          "iterator/vector, unbounded-count, correlation, late-lower, identity, graph-edit controls")


if __name__ == "__main__":
    main()
