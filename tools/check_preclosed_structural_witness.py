#!/usr/bin/env python3
"""Executable research model for the two-sided preclosed structural theorem.

This is not a compiler solver or an acceptance policy. Terms are flat; all
constructor children refer to input variables. Identity atoms, mandatory Record
width, Function (-,+), and declared fixed variance (+,-,0) are modeled. Closure
has exactly the input variables and original constructor terms as its universe.
Only witness construction allocates new objects, as a finite regular graph.

Run without arguments for focused examples and a bounded independent oracle.
The oracle is incomplete in general: its search bound is two graph nodes.
Assertions check generated witnesses independently of the closure relation.
"""

from dataclasses import dataclass
from itertools import product
from time import perf_counter


@dataclass(frozen=True)
class Flat:
    head: str
    children: tuple = ()       # sorted (coordinate, variable) pairs
    variance: tuple = ()       # (coordinate, +1/-1/0) pairs

    def __post_init__(self):
        labels = tuple(k for k, _ in self.children)
        if labels != tuple(sorted(set(labels))):
            raise ValueError("coordinates must be sorted and distinct")
        if tuple(k for k, _ in self.variance) != labels:
            raise ValueError("every coordinate needs a declared variance")
        if any(v not in (-1, 0, 1) for _, v in self.variance):
            raise ValueError("invalid variance")
        if self.head == "Record" and any(v != 1 for _, v in self.variance):
            raise ValueError("mandatory Record coordinates are covariant")
        if self.head == "Function" and self.variance != (("arg", -1), ("ret", 1)):
            raise ValueError("Function has exactly arg- and ret+")


def atom(name):
    if name in ("Record", "Function"):
        raise ValueError("reserved constructor name")
    return Flat(name)


def record(**fields):
    children = tuple(sorted(fields.items()))
    return Flat("Record", children, tuple((k, 1) for k, _ in children))


def function(arg, ret):
    return Flat("Function", (("arg", arg), ("ret", ret)),
                (("arg", -1), ("ret", 1)))


def invariant(child):
    return Flat("Box", (("value", child),), (("value", 0),))


@dataclass
class Problem:
    variables: tuple
    inequalities: tuple = ()
    equations: tuple = ()

    def __post_init__(self):
        if len(set(self.variables)) != len(self.variables):
            raise ValueError("duplicate variable")
        heads = {}
        for lhs, rhs in self.original_bounds():
            for term in (lhs, rhs):
                if isinstance(term, str):
                    if term not in self.variables:
                        raise ValueError("unknown variable: " + term)
                elif isinstance(term, Flat):
                    if any(v not in self.variables for _, v in term.children):
                        raise ValueError("unknown child variable")
                    if term.head != "Record":
                        signature = term.variance
                        if term.head in heads and heads[term.head] != signature:
                            raise ValueError("fixed head has inconsistent signature")
                        heads[term.head] = signature
                else:
                    raise ValueError("endpoint is neither variable nor flat term")
        if any(lhs not in self.variables or not isinstance(rhs, Flat)
               for lhs, rhs in self.equations):
            raise ValueError("equations must be x = constructor(children)")

    def original_bounds(self):
        return (self.inequalities + self.equations
                + tuple((rhs, lhs) for lhs, rhs in self.equations))


def child_obligations(lower, upper):
    """Root test/decomposition, with no recursion and no allocated terms."""
    if lower.head != upper.head:
        return None
    lc, uc = dict(lower.children), dict(upper.children)
    if lower.head == "Record":
        if not uc.keys() <= lc.keys():
            return None
    elif lower.variance != upper.variance:
        return None
    pairs = []
    for label, variance in upper.variance:
        a, b = lc[label], uc[label]
        if variance >= 0:
            pairs.append((a, b))
        if variance <= 0:
            pairs.append((b, a))
    return pairs


@dataclass
class Node:
    head: str
    children: dict
    variance: tuple


@dataclass
class Result:
    status: str
    nodes: list
    roots: dict
    universe_size: int
    relation_size: int
    reason: str = ""


def solve(problem):
    bounds = problem.original_bounds()
    flats = frozenset(t for pair in bounds for t in pair if isinstance(t, Flat))
    universe = tuple(problem.variables) + tuple(sorted(flats, key=repr))
    relation = {(t, t) for t in universe} | set(bounds)
    # Saturation alternates finite transitivity and reached-root decomposition.
    while True:
        previous = len(relation)
        successors = {t: set() for t in universe}
        for a, b in relation:
            successors[a].add(b)
        for a in universe:
            for b in tuple(successors[a]):
                relation.update((a, c) for c in successors[b])
        obligations = set()
        for a, b in relation:
            if isinstance(a, Flat) and isinstance(b, Flat):
                pairs = child_obligations(a, b)
                if pairs is None:
                    return Result("UNSAT", [], {}, len(universe), len(relation),
                                  "incompatible reached constructor roots")
                obligations.update(pairs)
        relation.update(obligations)
        assert all(a in universe and b in universe for a, b in relation)
        if len(relation) == previous:
            break
    lowers = {v: frozenset(t for t in flats if (t, v) in relation)
              for v in problem.variables}
    uppers = {v: frozenset(t for t in flats if (v, t) in relation)
              for v in problem.variables}
    if any(not lowers[v] or not uppers[v] for v in problem.variables):
        return Result("OUTSIDE_PREMISE", [], {}, len(universe), len(relation),
                      "some variable lacks a nonvariable lower or upper bound")

    nodes, memo, pending = [], {}, []

    def allocate(a, b):
        a, b = frozenset(a), frozenset(b)
        assert a and b
        assert all((x, y) in relation for x in a for y in b)
        state = (a, b)
        if state not in memo:
            memo[state] = len(nodes)
            nodes.append(None)       # allocate before expanding recursive ports
            pending.append(state)
        return memo[state]

    roots = {v: allocate([v], [v]) for v in problem.variables}
    while pending:
        a, b = pending.pop()
        lower = set().union(*(lowers[v] for v in a))
        upper = set().union(*(uppers[v] for v in b))
        assert lower and upper
        assert all((l, u) in relation for l in lower for u in upper)
        representative = min(upper, key=repr)
        assert all(t.head == representative.head for t in lower | upper)
        if representative.head == "Record":
            labels = set().union(*(dict(t.children).keys() for t in upper))
            assert all(labels <= dict(t.children).keys() for t in lower)
            variance = tuple((k, 1) for k in sorted(labels))
        else:
            variance = representative.variance
            assert all(t.variance == variance for t in lower | upper)
        children = {}
        for label, sign in variance:
            lc = {dict(t.children)[label] for t in lower
                  if label in dict(t.children)}
            uc = {dict(t.children)[label] for t in upper
                  if label in dict(t.children)}
            assert lc and uc
            if sign == 1:
                child_a, child_b = lc, uc
            elif sign == -1:
                child_a, child_b = uc, lc
            else:
                child_a = child_b = lc | uc
                assert all((x, y) in relation for x in child_a for y in child_b)
            children[label] = allocate(child_a, child_b)
        nodes[memo[(a, b)]] = Node(representative.head, children, variance)
    assert len(nodes) <= (2 ** len(problem.variables) - 1) ** 2
    result = Result("SAT", nodes, roots, len(universe), len(relation))
    assert validate(problem, result), "constructed witness fails original constraints"
    return result


def simulates(nodes, lower, upper, exact=False):
    """Direct greatest finite pair simulation; never reads solver closure.

    A visited pair is a coinductive obligation, not a depth cutoff. Every
    reachable pair's root and ports are checked, including back edges.
    Exact equality requires identical masks and recursive equality of ports.
    """
    pending, visited = [(lower, upper)], set()
    while pending:
        pair = pending.pop()
        if pair in visited:
            continue
        visited.add(pair)
        a, b = (nodes[i] for i in pair)
        if a.head != b.head:
            return False
        if exact:
            if a.variance != b.variance or a.children.keys() != b.children.keys():
                return False
        elif a.head == "Record":
            if not b.children.keys() <= a.children.keys():
                return False
        elif a.variance != b.variance:
            return False
        for label, sign in b.variance:
            x, y = a.children[label], b.children[label]
            if exact or sign >= 0:
                pending.append((x, y))
            if not exact and sign <= 0:
                pending.append((y, x))
    return True


def instantiate(problem, nodes, roots):
    """Interpret original flat terms in a graph under the given assignment."""
    graph, refs = list(nodes), dict(roots)
    for pair in problem.original_bounds():
        for term in pair:
            if isinstance(term, Flat) and term not in refs:
                refs[term] = len(graph)
                graph.append(Node(term.head,
                                  {k: roots[v] for k, v in term.children},
                                  term.variance))
    return graph, refs


def validate(problem, result):
    if result.status != "SAT" or set(result.roots) != set(problem.variables):
        return False
    graph, refs = instantiate(problem, result.nodes, result.roots)
    return (all(simulates(graph, refs[a], refs[b])
                for a, b in problem.inequalities)
            and all(simulates(graph, refs[a], refs[b], exact=True)
                    for a, b in problem.equations))


def focused_tests():
    checks = 0

    def expect(problem, status):
        nonlocal checks
        result = solve(problem)
        assert result.status == status, (status, result)
        if status == "SAT":
            assert validate(problem, result)
        checks += 1
        return result

    # Recursive contravariant argument: {a:Y} <= {} reverses at Function.arg.
    expect(Problem(("E", "A", "Y", "X"), (("X", "Y"),),
                   (("E", record()), ("A", record(a="Y")),
                    ("Y", function("A", "Y")),
                    ("X", function("E", "X")))), "SAT")
    expect(Problem(("X",), ((record(a="X", b="X"), "X"),
                             ("X", record(a="X")))), "SAT")
    expect(Problem(("X",), equations=(("X", invariant("X")),)), "SAT")
    expect(Problem(("A", "B", "X"),
                   ((invariant("A"), "X"), ("X", invariant("B"))),
                   (("A", record()), ("B", record()))), "SAT")
    expect(Problem(("X",), ((atom("Int"), "X"),
                             ("X", atom("Bool")))), "UNSAT")
    expect(Problem(("X",), ((record(), "X"),
                             ("X", record(a="X")))), "UNSAT")
    expect(Problem(("I", "B", "X"),
                   ((record(a="I"), "X"), ("X", record(a="B"))),
                   (("I", atom("Int")), ("B", atom("Bool")))), "UNSAT")
    expect(Problem(("I", "B", "X"),
                   ((invariant("I"), "X"), ("X", invariant("B"))),
                   (("I", record()), ("B", record(a="I")))), "UNSAT")
    expect(Problem(("X",)), "OUTSIDE_PREMISE")
    expect(Problem(("X",), ((atom("Int"), "X"),)), "OUTSIDE_PREMISE")
    expect(Problem(("X",), (("X", atom("Int")),)), "OUTSIDE_PREMISE")

    # Strict nonselector multi-open-anchor example. All descriptors are named
    # variables with exact equations; the free Z is anchored on both sides.
    masks = ("a", "b", "fgh", "fgk", "abc", "abd", "f", "g", "ab", "fg")
    variables = ("E", "Z", "Y", "X", "L1", "L2", "U1", "U2")
    variables += tuple("R_" + mask for mask in masks)
    equations = (("E", record()), ("Y", function("Z", "Y")))
    equations += tuple(("R_" + mask, record(**{k: "Y" for k in mask}))
                       for mask in masks)
    equations += (("L1", function("R_a", "R_fgh")),
                  ("L2", function("R_b", "R_fgk")),
                  ("U1", function("R_abc", "R_f")),
                  ("U2", function("R_abd", "R_g")))
    bounds = (("E", "Z"), ("Z", "E"), ("L1", "X"),
              ("L2", "X"), ("X", "U1"), ("X", "U2"))
    problem = Problem(variables, bounds, equations)
    result = expect(problem, "SAT")
    graph = result.nodes
    xn = graph[result.roots["X"]]
    assert xn.head == "Function"
    assert set(graph[xn.children["arg"]].children) == set("ab")
    assert set(graph[xn.children["ret"]].children) == set("fg")
    failed_anchors = 0
    for anchor in ("L1", "L2", "U1", "U2"):
        substituted = Result("SAT", graph, dict(result.roots), 0, 0)
        substituted.roots["X"] = result.roots[anchor]
        assert not validate(problem, substituted), anchor
        failed_anchors += 1
    # Also validate the stated fresh witness directly using the named R_ab/fg.
    fresh_nodes = graph + [Node("Function",
                              {"arg": result.roots["R_ab"],
                               "ret": result.roots["R_fg"]},
                              (("arg", -1), ("ret", 1)))]
    fresh_roots = dict(result.roots, X=len(graph))
    assert validate(problem, Result("SAT", fresh_nodes, fresh_roots, 0, 0))
    return checks, failed_anchors, len(result.nodes)


def bounded_oracle_tests():
    """2401 packages against all 225 labeled two-node graphs.

    Node inventory (each child i ranges over the two graph node references):
    2 atoms + 1 empty + 2 single-a + 2 single-b + 4 a/b + 4 Functions = 15.
    Two labeled nodes therefore give 15**2 = 225 graphs; self loops include
    every one-node graph. Unreachable node 1 is intentionally allowed.
    """
    terms = (atom("Int"), atom("Bool"), record(), record(a="X"),
             record(b="X"), record(a="X", b="X"), function("X", "X"))
    descriptors = [Node("Int", {}, ()), Node("Bool", {}, ()),
                   Node("Record", {}, ())]
    for labels in (("a",), ("b",), ("a", "b")):
        for refs in product(range(2), repeat=len(labels)):
            descriptors.append(Node("Record", dict(zip(labels, refs)),
                                    tuple((k, 1) for k in labels)))
    for a, b in product(range(2), repeat=2):
        descriptors.append(Node("Function", {"arg": a, "ret": b},
                                (("arg", -1), ("ret", 1))))
    assert len(descriptors) == 15
    # Cache each graph's compatible term lower/upper bit masks. This oracle
    # uses only the direct simulation on the concrete graph, not saturation.
    compatibility = set()
    for a, b in product(descriptors, repeat=2):
        nodes = [a, b]
        flat_nodes = [Node(t.head, {k: 0 for k, _ in t.children}, t.variance)
                      for t in terms]
        nodes += flat_nodes
        low = sum(1 << i for i in range(7) if simulates(nodes, 2 + i, 0))
        high = sum(1 << i for i in range(7) if simulates(nodes, 0, 2 + i))
        compatibility.add((low, high))
    counts = {"SAT": 0, "UNSAT": 0, "OUTSIDE_PREMISE": 0}
    agreement = 0
    for i, j, k, l in product(range(7), repeat=4):
        problem = Problem(("X",), ((terms[i], "X"), (terms[j], "X"),
                                   ("X", terms[k]), ("X", terms[l])))
        result = solve(problem)
        counts[result.status] += 1
        low, high = (1 << i) | (1 << j), (1 << k) | (1 << l)
        oracle = any(low & lm == low and high & hm == high
                     for lm, hm in compatibility)
        if result.status == "UNSAT":
            assert not oracle, (i, j, k, l)
        if result.status == "SAT":
            assert validate(problem, result)
        assert result.status != "OUTSIDE_PREMISE"
        agreement += oracle == (result.status == "SAT")
    return counts, agreement, len(compatibility)


def main():
    started = perf_counter()
    focused, anchors, states = focused_tests()
    counts, agreement, profiles = bounded_oracle_tests()
    print("Focused systems: %d passed; failed anchor checks: %d; "
          "nonselector witness states: %d" % (focused, anchors, states))
    print("Bounded oracle: 225 two-node graphs, %d distinct compatibility "
          "profiles, 2401 packages: %s" % (profiles, counts))
    print("Solver/oracle agreement: %d/2401 (oracle bound: two nodes)" % agreement)
    print("All SAT witnesses independently validate; all UNSAT packages lack "
          "an oracle witness.")
    print("Elapsed: %.3fs" % (perf_counter() - started))


if __name__ == "__main__":
    main()
