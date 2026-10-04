#!/usr/bin/env python3
"""Executable pure-structural decision candidate from the finite-fence proof.

Implements the reviewed finite-distance closure and profile construction for
normalized pure structural packages. It constructs a finite regular graph,
then checks original bounds/equations with the closure-independent coinductive
validator from ``check_preclosed_structural_witness.py``. Per-root rigid
permissions are checked separately using the reviewed same-address shadow
theorem. This is research code, not the production solver or coupled
Function/effect semantics.

Run: python3 tools/check_structural_fence_completion.py
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

if __package__:
    from .check_preclosed_structural_witness import (
        Flat,
        Node,
        Problem,
        Result as ValidatedGraph,
        atom,
        function,
        invariant,
        record,
        validate,
    )
else:
    from check_preclosed_structural_witness import (
        Flat,
        Node,
        Problem,
        Result as ValidatedGraph,
        atom,
        function,
        invariant,
        record,
        validate,
    )


# Distances are stored as names; tuple coordinates are the proof's lengths.
DISTANCES = {
    "E0": (1, 1),
    "U": (1, 2),
    "Dn": (2, 1),
    "B": (2, 2),
    "H": (2, 3),
    "L": (3, 2),
    "C": (3, 3),
}
NAME_BY_DISTANCE = {value: name for name, value in DISTANCES.items()}


class RigidFlat(Flat):
    """An identity atom with a per-root permission name."""


def distance_leq(a: str, b: str) -> bool:
    return all(x <= y for x, y in zip(DISTANCES[a], DISTANCES[b]))


def distance_meet(a: str, b: str) -> str:
    pair = tuple(min(x, y) for x, y in zip(DISTANCES[a], DISTANCES[b]))
    return NAME_BY_DISTANCE[pair]


def inverse(a: str) -> str:
    # Reversing endpoints changes only up/down orientation. A common upper
    # or lower remains common after swapping the two endpoints.
    return "Dn" if a == "U" else "U" if a == "Dn" else a


def star(a: str) -> str:
    # Variance conjugation is distinct from endpoint reversal: it swaps the
    # two fence-length coordinates and therefore exchanges H with L.
    return NAME_BY_DISTANCE[DISTANCES[a][::-1]]


def distance_plus(a: str, b: str) -> str:
    up, down = DISTANCES[a]
    next_up, next_down = DISTANCES[b]
    result = (
        min(3, up + (next_down if up % 2 == 0 else next_up) - 1),
        min(3, down + (next_up if down % 2 == 0 else next_down) - 1),
    )
    return NAME_BY_DISTANCE[result]


def is_rigid(term: Flat) -> bool:
    return (
        isinstance(term, RigidFlat)
        and term.head.startswith("$rigid:")
        and not term.children
    )


def rigid(name: str) -> Flat:
    return RigidFlat("$rigid:" + name)


@dataclass(frozen=True)
class Conflict:
    kind: str
    left: object
    right: object
    distance: str
    reason: str


@dataclass
class FenceResult:
    status: str
    nodes: list[Node]
    roots: dict[str, int]
    term_roots: dict[Flat, int]
    universe_size: int
    relation_size: int
    profiles: int
    reason: str = ""
    conflict: Conflict | None = None
    forbidden_rigid: tuple[str, str, tuple[str, ...]] | None = None


class FenceConstruction:
    """Sections 4–10 finite closure and reachable profile graph."""

    def __init__(
        self,
        problem: Problem,
        permissions: dict[str, frozenset[str]] | None = None,
        profile_limit: int | None = 100_000,
    ):
        self.problem = problem
        self.bounds = problem.original_bounds()
        self.variables = tuple(problem.variables)
        terms = {x for pair in self.bounds for x in pair if isinstance(x, Flat)}
        self.terms = tuple(sorted(terms, key=repr))
        self.universe = self.variables + self.terms
        self.index = {item: i for i, item in enumerate(self.universe)}
        self.dist: dict[tuple[object, object], str] = {}
        self.conflict: Conflict | None = None
        self.profile_limit = profile_limit
        self.rigid_names = frozenset(
            t.head.removeprefix("$rigid:") for t in self.terms if is_rigid(t)
        )
        default_permission = self.rigid_names
        if any(
            (t.head.startswith("$rigid:") and not is_rigid(t))
            or (isinstance(t, RigidFlat) and not is_rigid(t))
            for t in self.terms
        ):
            raise ValueError("$rigid: is reserved for rigid identity atoms")
        self.permissions = {
            root: (permissions or {}).get(root, default_permission)
            for root in self.variables
        }
        self.signatures: dict[str, tuple[tuple[str, int], ...]] = {}
        for term in self.terms:
            if term.head != "Record" and term.children:
                old = self.signatures.setdefault(term.head, term.variance)
                if old != term.variance:
                    raise ValueError(f"inconsistent fixed signature for {term.head}")

    def _meet_bound(self, left, right, value: str) -> bool:
        old = self.dist.get((left, right))
        new = value if old is None else distance_meet(old, value)
        if old == new:
            return False
        self.dist[(left, right)] = new
        return True

    def _shallow_check(self, left: Flat, right: Flat, distance: str) -> str | None:
        lc, rc = dict(left.children), dict(right.children)
        if left.head == "Record" and right.head == "Record":
            left_fields, right_fields = lc.keys(), rc.keys()
            if distance == "E0" and left_fields != right_fields:
                return "equality requires identical Record masks"
            if distance == "U" and not right_fields <= left_fields:
                return "lower Record lacks an upper-required field"
            if distance == "Dn" and not left_fields <= right_fields:
                return "upper Record has an extra field"
            return None

        if not left.children and not right.children:
            return None if left.head == right.head else "distinct atomic identities"
        if (not left.children or not right.children or left.head != right.head
                or left.variance != right.variance):
            return "incompatible constructor heads or coordinate signatures"
        return None

    def saturate(self) -> None:
        for item in self.universe:
            self._meet_bound(item, item, "E0")
        for left, right in self.bounds:
            self._meet_bound(left, right, "U")

        while True:
            before = dict(self.dist)
            entries = tuple((a, b, d) for (a, b), d in before.items())
            changed = False

            for a, b, d in entries:
                changed |= self._meet_bound(b, a, inverse(d))
                if isinstance(a, Flat) and isinstance(b, Flat):
                    reason = self._shallow_check(a, b, d)
                    if reason is not None:
                        self.conflict = Conflict("shallow", a, b, d, reason)
                        return

                    ac, bc = dict(a.children), dict(b.children)
                    if a.head == "Record":
                        common = ac.keys() & bc.keys()
                        if d in ("E0", "U", "Dn"):
                            child_d = d
                        elif d in ("B", "L"):
                            child_d = "L"
                        else:
                            child_d = None
                        if child_d is not None:
                            for label in common:
                                changed |= self._meet_bound(ac[label], bc[label], child_d)
                    else:
                        for label, variance in a.variance:
                            lower_child, upper_child = ac[label], bc[label]
                            if variance > 0:
                                changed |= self._meet_bound(lower_child, upper_child, d)
                            elif variance < 0:
                                changed |= self._meet_bound(lower_child, upper_child, star(d))
                            else:
                                changed |= self._meet_bound(lower_child, upper_child, "E0")
                                changed |= self._meet_bound(upper_child, lower_child, "E0")

            # Transitive fence composition; repeat after reversal and child
            # decomposition because those can add entries in this round.
            entries = tuple((a, b, d) for (a, b), d in self.dist.items())
            outgoing: dict[object, list[tuple[object, str]]] = {}
            for a, b, d in entries:
                outgoing.setdefault(a, []).append((b, d))
            for a, b, ab in entries:
                for c, bc in outgoing.get(b, ()):
                    changed |= self._meet_bound(a, c, distance_plus(ab, bc))

            if not changed and self.dist == before:
                return

    def _profile(self, mapping: dict[object, str]) -> tuple[str | None, ...]:
        return tuple(mapping.get(item) for item in self.universe)

    def _profile_dict(self, profile: tuple[str | None, ...]) -> dict[object, str]:
        return {item: d for item, d in zip(self.universe, profile) if d is not None}

    def _expand(self, raw: dict[object, str]) -> tuple[str | None, ...]:
        expanded: dict[object, str] = {}
        for target in self.universe:
            contributions = [
                distance_plus(bound, self.dist[(source, target)])
                for source, bound in raw.items()
                if (source, target) in self.dist
            ]
            if contributions:
                value = contributions[0]
                for other in contributions[1:]:
                    value = distance_meet(value, other)
                expanded[target] = value
        return self._profile(expanded)

    def _admissible(self, profile: tuple[str | None, ...]) -> bool:
        values = self._profile_dict(profile)
        for left, left_bound in values.items():
            for right, right_bound in values.items():
                d = self.dist.get((left, right))
                if d is None or not distance_leq(
                    d, distance_plus(inverse(left_bound), right_bound)
                ):
                    return False
        return bool(values)

    def _start(self, item) -> tuple[str | None, ...]:
        return self._profile({
            target: d for (source, target), d in self.dist.items() if source == item
        })

    def _head_and_successors(self, profile: tuple[str | None, ...]):
        values = self._profile_dict(profile)
        anchors = [t for t in self.terms if t in values]
        fixed = [t for t in anchors if t.head != "Record" and t.children]
        atoms = [t for t in anchors if t.head != "Record" and not t.children]
        records = [t for t in anchors if t.head == "Record"]

        if fixed:
            head = fixed[0].head
            variance = fixed[0].variance
            if any(t.head != head or t.variance != variance for t in fixed):
                raise AssertionError("saturated profile has incompatible fixed anchors")
            raw_by_label: dict[str, dict[object, str]] = {
                label: {} for label, _ in variance
            }
            for term in fixed:
                children = dict(term.children)
                parent_bound = values[term]
                for label, sign in variance:
                    if sign > 0:
                        child_bound = parent_bound
                    elif sign < 0:
                        child_bound = star(parent_bound)
                    else:
                        child_bound = "E0"
                    child = children[label]
                    old = raw_by_label[label].get(child)
                    raw_by_label[label][child] = (
                        child_bound if old is None else distance_meet(old, child_bound)
                    )
            successors = {
                label: self._expand(raw)
                for label, raw in raw_by_label.items()
            }
            return head, variance, successors

        if atoms:
            atom_head = atoms[0].head
            if any(t.head != atom_head for t in atoms):
                raise AssertionError("saturated profile has distinct atom anchors")
            return atom_head, (), {}

        if records:
            selected = set()
            for term in records:
                if distance_leq(values[term], "U"):
                    selected.update(dict(term.children))
            raw_by_label: dict[str, dict[object, str]] = {
                label: {} for label in selected
            }
            projection = {"E0": "E0", "U": "U", "Dn": "Dn",
                          "B": "L", "L": "L"}
            for term in records:
                children = dict(term.children)
                bound = values[term]
                child_bound = projection.get(bound)
                if child_bound is None:
                    continue
                for label in selected & children.keys():
                    child = children[label]
                    old = raw_by_label[label].get(child)
                    raw_by_label[label][child] = (
                        child_bound if old is None else distance_meet(old, child_bound)
                    )
            if any(not raw for raw in raw_by_label.values()):
                raise AssertionError("selected Record field has no projected anchor")
            variance = tuple((label, 1) for label in sorted(selected))
            successors = {
                label: self._expand(raw)
                for label, raw in raw_by_label.items()
            }
            return "Record", variance, successors

        # With no constructor anchor the proof chooses the existing empty Record.
        return "Record", (), {}

    def _forbidden_rigid(self, root: str, start: int, nodes: list[Node]):
        allowed = self.permissions[root]
        pending = deque([(start, ())])
        visited = set()
        while pending:
            node_id, path = pending.popleft()
            if node_id in visited:
                continue
            visited.add(node_id)
            node = nodes[node_id]
            if node.head.startswith("$rigid:"):
                name = node.head.removeprefix("$rigid:")
                if name not in allowed:
                    return name, path
            for label, child in sorted(node.children.items()):
                pending.append((child, path + (label,)))
        return None

    def solve(self) -> FenceResult:
        self.saturate()
        if self.conflict is not None:
            return FenceResult(
                "UNSAT", [], {}, {}, len(self.universe), len(self.dist), 0,
                reason=self.conflict.reason, conflict=self.conflict,
            )

        starts = {item: self._start(item) for item in self.universe}
        if any(not self._admissible(profile) for profile in starts.values()):
            raise AssertionError("closed finite matrix produced inadmissible start profile")

        nodes: list[Node | None] = []
        ids: dict[tuple[str | None, ...], int] = {}
        pending: deque[tuple[str | None, ...]] = deque()

        def allocate(profile):
            if profile in ids:
                return ids[profile]
            if self.profile_limit is not None and len(nodes) >= self.profile_limit:
                raise OverflowError("profile budget exceeded")
            if len(nodes) >= 8 ** len(self.universe):
                raise AssertionError("profile construction exceeded 8^N theorem bound")
            if not self._admissible(profile):
                raise AssertionError("successor profile is not admissible")
            node_id = len(nodes)
            ids[profile] = node_id
            nodes.append(None)  # memoize before following recursive ports
            pending.append(profile)
            return node_id

        try:
            start_ids = {item: allocate(profile) for item, profile in starts.items()}
            while pending:
                profile = pending.popleft()
                node_id = ids[profile]
                head, variance, successors = self._head_and_successors(profile)
                children = {
                    label: allocate(successor)
                    for label, successor in successors.items()
                }
                nodes[node_id] = Node(head, children, variance)
        except OverflowError as error:
            return FenceResult(
                "LIMIT", [], {}, {}, len(self.universe), len(self.dist), len(nodes),
                reason=str(error),
            )

        finished_nodes = [node for node in nodes if node is not None]
        if len(finished_nodes) != len(nodes):
            raise AssertionError("unfinished profile graph state")
        roots = {v: start_ids[v] for v in self.variables}
        term_roots = {t: start_ids[t] for t in self.terms}
        graph = ValidatedGraph("SAT", finished_nodes, roots, len(self.universe), len(self.dist))
        if not validate(self.problem, graph):
            return FenceResult(
                "MODEL_BUG", finished_nodes, roots, term_roots,
                len(self.universe), len(self.dist), len(nodes),
                reason="independent coinductive check rejected the generated witness",
            )
        for root, node_id in roots.items():
            forbidden = self._forbidden_rigid(root, node_id, finished_nodes)
            if forbidden is not None:
                name, path = forbidden
                return FenceResult(
                    "UNSAT", finished_nodes, roots, term_roots,
                    len(self.universe), len(self.dist), len(nodes),
                    reason="constructed witness violates this root's rigid permission",
                    forbidden_rigid=(root, name, path),
                )
        return FenceResult(
            "SAT", finished_nodes, roots, term_roots,
            len(self.universe), len(self.dist), len(nodes),
        )


def solve(problem: Problem, permissions=None, profile_limit=100_000) -> FenceResult:
    return FenceConstruction(problem, permissions, profile_limit).solve()


def focused_cases():
    cases = [
        ("unconstrained root", Problem(("X",)), "SAT"),
        ("lower-only root", Problem(("X",), ((atom("Int"), "X"),)), "SAT"),
        ("upper-only root", Problem(("X",), (("X", atom("Int")),)), "SAT"),
        ("mutual variable bounds", Problem(("X", "Y"), (("X", "Y"), ("Y", "X"))), "SAT"),
        ("recursive Function equation", Problem(("X",), equations=(("X", function("X", "X")),)), "SAT"),
        ("recursive invariant equation", Problem(("X",), equations=(("X", invariant("X")),)), "SAT"),
        (
            "incompatible Record payloads share empty upper",
            Problem(("I", "B", "X"),
                    ((record(a="I"), "X"), (record(a="B"), "X")),
                    (("I", atom("Int")), ("B", atom("Bool")))),
            "SAT",
        ),
        (
            "Function argument uses variance conjugation",
            Problem(("E", "A", "F", "G"),
                    (("F", "G"),),
                    (("E", record()), ("A", record(a="E")),
                     ("F", function("E", "E")),
                     ("G", function("A", "E")))),
            "SAT",
        ),
        (
            "empty Record remains a Record anchor",
            Problem(("E", "A", "X"), (("X", record()),),
                    (("E", record()), ("A", record(a="E")),
                     ("X", record(a="A")))),
            "SAT",
        ),
        ("incompatible atomic bounds", Problem(("X",), ((atom("Int"), "X"), ("X", atom("Bool")))), "UNSAT"),
        (
            "overlapping Record payload clash",
            Problem(("I", "B", "X"),
                    ((record(a="I", b="I"), "X"), ("X", record(a="B", b="B"))),
                    (("I", atom("Int")), ("B", atom("Bool")))),
            "UNSAT",
        ),
    ]
    return cases


def check_rigid_permissions():
    problem = Problem(
        ("X", "K"),
        equations=(("X", record(a="K")), ("K", rigid("k"))),
    )
    allowed = solve(problem, {"X": frozenset({"k"}), "K": frozenset({"k"})})
    forbidden = solve(problem, {"X": frozenset(), "K": frozenset({"k"})})
    assert allowed.status == "SAT", allowed
    assert forbidden.status == "UNSAT" and forbidden.forbidden_rigid is not None
    assert forbidden.forbidden_rigid[0] == "X"
    return allowed, forbidden


def main() -> None:
    result_counts = {"SAT": 0, "UNSAT": 0}
    total_profiles = total_matrix_entries = 0
    for name, problem, expected in focused_cases():
        result = solve(problem)
        assert result.status == expected, (name, expected, result)
        if result.status == "SAT":
            assert validate(
                problem,
                ValidatedGraph("SAT", result.nodes, result.roots,
                               result.universe_size, result.relation_size),
            )
        result_counts[result.status] += 1
        total_profiles += result.profiles
        total_matrix_entries += result.relation_size

    allowed, forbidden = check_rigid_permissions()
    result_counts[allowed.status] += 1
    result_counts[forbidden.status] += 1
    print(f"focused packages: {sum(result_counts.values())}; statuses={result_counts}")
    print(f"reachable profile states: {total_profiles + allowed.profiles + forbidden.profiles}")
    print(f"closed-matrix entries across cases: {total_matrix_entries + allowed.relation_size + forbidden.relation_size}")
    print(f"rigid permission counterpath: {forbidden.forbidden_rigid}")
    print("every SAT graph passed the closure-independent original-bound/equation validator")
    limited = solve(Problem(("X",)), profile_limit=0)
    assert limited.status == "LIMIT", limited
    spoofed_rigid = Problem(
        ("X",),
        equations=(("X", Flat("$rigid:constructor", (("x", "X"),), (("x", 1),))),),
    )
    try:
        solve(spoofed_rigid)
    except ValueError as error:
        assert "$rigid:" in str(error)
    else:
        raise AssertionError("ordinary fixed head spoofed the rigid namespace")
    malformed_rigid = Problem(("X",), equations=(("X", RigidFlat("k")),))
    try:
        solve(malformed_rigid, {"X": frozenset()})
    except ValueError as error:
        assert "$rigid:" in str(error)
    else:
        raise AssertionError("malformed rigid atom bypassed root permissions")
    print("profile budget exhaustion is reported as LIMIT, never UNSAT")
    print(
        "scope: normalized pure structural terms and per-root rigid permissions; "
        "no effects, optional Records, extrema, source adequacy, or principality"
    )


if __name__ == "__main__":
    main()
