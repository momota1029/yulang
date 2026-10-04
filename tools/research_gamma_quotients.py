#!/usr/bin/env python3
"""Small generated-package differential playground for finite Gamma quotients.

This extends the fixed-package feedback probe to arbitrary collections of
root tracks, fixed ranked descriptors, and original inequalities over a small
Function/atom signature. Each inequality keeps its own identity and orientation;
successful concrete comparisons are never composed. It is intentionally not
the full Yulang structural language: Record defaults are empty, and optional
fields, custom variance constructors, rigid permissions, effects, and source
generation are out of scope.

Run: python3 tools/research_gamma_quotients.py [max-monoid-size]
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations_with_replacement, product
import sys

from research_structural_feedback import (
    ARG, RET, FiniteMonoid, enumerate_two_generated_monoids,
    saturate as saturate_fixed_example,
)


@dataclass(frozen=True)
class Port:
    name: str
    generator: int
    variance: int


SCHEMA = {
    "Function": (Port(ARG, 0, -1), Port(RET, 1, 1)),
    "Int": (),
    "Bool": (),
    "Record": (),  # canonical empty Record default only
}


@dataclass(frozen=True)
class Package:
    tracks: tuple[str, ...]
    fixed_heads: tuple[tuple[str, str], ...]
    descriptor_ports: tuple[tuple[str, str, str], ...]
    bounds: tuple[tuple[str, str], ...]

    def validate(self) -> None:
        tracks = set(self.tracks)
        if len(tracks) != len(self.tracks):
            raise ValueError("duplicate track")
        heads = dict(self.fixed_heads)
        if len(heads) != len(self.fixed_heads):
            raise ValueError("duplicate fixed head")
        if any(t not in tracks or h not in SCHEMA for t, h in heads.items()):
            raise ValueError("invalid fixed head")
        edges = {(t, p): c for t, p, c in self.descriptor_ports}
        if len(edges) != len(self.descriptor_ports):
            raise ValueError("duplicate descriptor port")
        if any(t not in heads for t, _ in edges):
            raise ValueError("descriptor edge has no fixed constructor head")
        for t, h in heads.items():
            expected = {p.name for p in SCHEMA[h]}
            actual = {port for (parent, port) in edges if parent == t}
            if actual != expected:
                raise ValueError(f"descriptor ports for {t}:{h}: {actual} != {expected}")
        if any(t not in tracks or c not in tracks for t, _, c in self.descriptor_ports):
            raise ValueError("descriptor edge references unknown track")
        if any(a not in tracks or b not in tracks for a, b in self.bounds):
            raise ValueError("bound references unknown track")


@dataclass
class State:
    domain: set[tuple[str, int]]
    heads: dict[tuple[str, int], str]
    active: set[tuple[int, int, int]]  # bound id, address, orientation
    conflict: str | None = None


def saturate(package: Package, monoid: FiniteMonoid) -> tuple[int | None, State]:
    package.validate()
    state = State({(t, 0) for t in package.tracks}, dict(
        ((t, 0), h) for t, h in package.fixed_heads),
        {(i, 0, 1) for i in range(len(package.bounds))})
    descriptors = {(t, p): child for t, p, child in package.descriptor_ports}
    coord = {p.name: p for ports in SCHEMA.values() for p in ports}

    def put_head(key: tuple[str, int], head: str) -> bool:
        old = state.heads.get(key)
        if old is not None and old != head:
            state.conflict = f"head clash {key}: {old} vs {head}"
            return False
        if old is None:
            state.heads[key] = head
            return True
        return False

    def endpoints(bound_id: int, orientation: int) -> tuple[str, str]:
        lower, upper = package.bounds[bound_id]
        return (lower, upper) if orientation > 0 else (upper, lower)

    def fbar(with_bounds: bool) -> bool:
        changed_any = False
        while state.conflict is None:
            changed = False
            for key in tuple(state.heads):
                if key not in state.domain:
                    state.domain.add(key)
                    changed = True

            # Exact descriptor shifts use prefix action c*m.
            for parent, port, child in package.descriptor_ports:
                generator = monoid.generators[coord[port].generator]
                for m in range(monoid.size):
                    left = (parent, monoid.mul(generator, m))
                    right = (child, m)
                    if left in state.domain or right in state.domain:
                        for key in (left, right):
                            if key not in state.domain:
                                state.domain.add(key)
                                changed = True
                    lh, rh = state.heads.get(left), state.heads.get(right)
                    if lh is not None and rh is None:
                        changed |= put_head(right, lh)
                    elif rh is not None and lh is None:
                        changed |= put_head(left, rh)
                    elif lh is not None and rh is not None and lh != rh:
                        state.conflict = f"descriptor clash {left}={lh}, {right}={rh}"
                        break
                if state.conflict:
                    break

            # Full restricted domain/head/child coherence. Child coordinates
            # are constructor-tagged by their port name.
            if state.conflict is None:
                for track in package.tracks:
                    for m in range(monoid.size):
                        parent = (track, m)
                        head = state.heads.get(parent)
                        declared = {p.name: p for p in SCHEMA[head]} if head else {}
                        for port, p in coord.items():
                            child = (track, monoid.mul(m, monoid.generators[p.generator]))
                            if child in state.domain:
                                if parent not in state.domain:
                                    state.domain.add(parent)
                                    changed = True
                                expected_head = next(
                                    (h for h, ports in SCHEMA.items()
                                     if any(q.name == port for q in ports)), None)
                                if head is None:
                                    changed |= put_head(parent, expected_head)
                                    head = state.heads.get(parent)
                                    declared = {q.name: q for q in SCHEMA[head]}
                                elif port not in declared:
                                    state.conflict = f"undeclared live port {parent}.{port}"
                                    break
                            if port in declared and child not in state.domain:
                                state.domain.add(child)
                                changed = True
                        if state.conflict:
                            break
                    if state.conflict:
                        break

            # Bounds are independent labelled comparisons, never transitively
            # composed. A known compatible head transfers across that edge.
            if state.conflict is None and with_bounds:
                for bound_id, m, orientation in tuple(state.active):
                    left_track, right_track = endpoints(bound_id, orientation)
                    left, right = (left_track, m), (right_track, m)
                    lh, rh = state.heads.get(left), state.heads.get(right)
                    if lh is not None and rh is not None and lh != rh:
                        state.conflict = f"bound {bound_id} head clash at {m}: {lh} vs {rh}"
                        break
                    if lh is not None and rh is None:
                        changed |= put_head(right, lh)
                    elif rh is not None and lh is None:
                        changed |= put_head(left, rh)

            changed_any |= changed
            if not changed:
                return changed_any
        return changed_any

    # Descriptor-only conflicts have rank zero.
    fbar(False)
    if state.conflict:
        return 0, state

    max_facts = len(package.tracks) * monoid.size * (1 + len(SCHEMA))
    max_facts += len(package.bounds) * monoid.size * 2
    for round_no in range(1, max_facts + 2):
        fbar(True)
        if state.conflict:
            return round_no, state
        changed = False
        # G(U) is complete suffix-path closure within the feedback round.
        # Repeated rounds are reserved for mutual feedback through Fbar.
        while state.conflict is None:
            path_changed = False
            for bound_id, m, orientation in tuple(state.active):
                left_track, right_track = endpoints(bound_id, orientation)
                left_head = state.heads.get((left_track, m))
                right_head = state.heads.get((right_track, m))
                if left_head is not None and right_head is not None and left_head != right_head:
                    state.conflict = f"bound {bound_id} head clash at {m}: {left_head} vs {right_head}"
                    break
                if left_head is None or right_head is None or left_head != right_head:
                    continue
                for port in SCHEMA[left_head]:
                    child_m = monoid.mul(m, monoid.generators[port.generator])
                    child_orientations = ((orientation * port.variance,)
                                          if port.variance else (1, -1))
                    for child_orientation in child_orientations:
                        fact = (bound_id, child_m, child_orientation)
                        if fact not in state.active:
                            state.active.add(fact)
                            path_changed = True
            changed |= path_changed
            if not path_changed or state.conflict:
                break
        if state.conflict:
            return round_no, state
        before = (len(state.domain), len(state.heads), len(state.active))
        fbar(True)
        if state.conflict:
            return round_no, state
        after = (len(state.domain), len(state.heads), len(state.active))
        if not changed and before == after:
            return None, state
    raise AssertionError("finite positive closure exceeded its fact bound")


@dataclass(frozen=True)
class Node:
    head: str
    children: tuple[tuple[str, int], ...]


def check_witness(package: Package, monoid: FiniteMonoid, state: State) -> bool:
    """Independently check a default-completed regular graph model."""
    refs = {(t, m): ti * monoid.size + m
            for ti, t in enumerate(package.tracks) for m in range(monoid.size)}
    graph = []
    for t in package.tracks:
        for m in range(monoid.size):
            head = state.heads.get((t, m), "Record") if (t, m) in state.domain else "Record"
            children = tuple((p.name, refs[(t, monoid.mul(m, monoid.generators[p.generator]))])
                             for p in SCHEMA[head])
            if head != "Record":
                assert all((t, monoid.mul(m, monoid.generators[p.generator])) in state.domain
                           for p in SCHEMA[head])
            graph.append(Node(head, children))

    def equal(a: int, b: int) -> bool:
        todo, seen = [(a, b)], set()
        while todo:
            x, y = todo.pop()
            if (x, y) in seen:
                continue
            seen.add((x, y))
            xn, yn = graph[x], graph[y]
            if xn.head != yn.head or tuple(k for k, _ in xn.children) != tuple(k for k, _ in yn.children):
                return False
            todo.extend((xc, yc) for (_, xc), (_, yc) in zip(xn.children, yn.children))
        return True

    def subtype(lower: int, upper: int) -> bool:
        todo, seen = [(lower, upper)], set()
        while todo:
            x, y = todo.pop()
            if (x, y) in seen:
                continue
            seen.add((x, y))
            xn, yn = graph[x], graph[y]
            if xn.head != yn.head:
                return False
            if xn.head == "Record":
                if not dict(yn.children).keys() <= dict(xn.children).keys():
                    return False
            else:
                xc, yc = dict(xn.children), dict(yn.children)
                for p in SCHEMA[xn.head]:
                    if p.variance > 0:
                        todo.append((xc[p.name], yc[p.name]))
                    elif p.variance < 0:
                        todo.append((yc[p.name], xc[p.name]))
                    else:
                        todo.extend(((xc[p.name], yc[p.name]), (yc[p.name], xc[p.name])))
        return True

    for parent, port, child in package.descriptor_ports:
        generator = monoid.generators[next(p.generator for p in SCHEMA[dict(package.fixed_heads)[parent]] if p.name == port)]
        for m in range(monoid.size):
            parent_at = (parent, monoid.mul(generator, m))
            child_at = (child, m)
            if (parent_at in state.domain) != (child_at in state.domain):
                return False
            if not equal(refs[parent_at], refs[child_at]):
                return False
    if any((track, 0) not in state.domain for track in package.tracks):
        return False
    for track, expected_head in package.fixed_heads:
        if (track, 0) not in state.domain or graph[refs[(track, 0)]].head != expected_head:
            return False
    return all(subtype(refs[(a, 0)], refs[(b, 0)]) for a, b in package.bounds)


def shrink_bad_witness(package: Package, monoid: FiniteMonoid) -> Package:
    """Greedily remove original bounds while a SAT/witness mismatch persists."""
    current = package

    def mismatch(candidate: Package) -> bool:
        rank, state = saturate(candidate, monoid)
        if rank is not None:
            return False
        try:
            return not check_witness(candidate, monoid, state)
        except (AssertionError, KeyError):
            return True

    changed = True
    while changed:
        changed = False
        for i in range(len(current.bounds)):
            candidate = Package(current.tracks, current.fixed_heads,
                                current.descriptor_ports,
                                current.bounds[:i] + current.bounds[i + 1:])
            if mismatch(candidate):
                current = candidate
                changed = True
                break
    return current


def generated_packages() -> list[Package]:
    tracks = ("q", "x", "i")
    result = []
    child_choices = tuple(product(tracks, repeat=2))
    bound_choices = tuple(product(tracks, repeat=2))
    for (arg, ret) in child_choices:
        base = Package(tracks, (("q", "Function"), ("i", "Int")),
                       (("q", ARG, arg), ("q", RET, ret)), ())
        for count in (0, 1, 2):
            for bounds in combinations_with_replacement(bound_choices, count):
                pkg = Package(base.tracks, base.fixed_heads, base.descriptor_ports, bounds)
                pkg.validate()
                result.append(pkg)
    return result


def focused_checker_invariants() -> int:
    """Keep validator and independent-root checks from regressing silently."""
    singleton = FiniteMonoid(((0,),), (0, 0))
    bad_descriptor = Package(("x", "i"), (("i", "Int"),),
                             (("x", ARG, "i"),), ())
    try:
        bad_descriptor.validate()
    except ValueError:
        pass
    else:
        raise AssertionError("descriptor edge without a fixed parent was accepted")

    false_int_witness = State({("i", 0)}, {}, set())
    assert not check_witness(Package(("i",), (("i", "Int"),), (), ()),
                             singleton, false_int_witness)
    return 2


def main() -> None:
    max_size = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    if max_size < 1 or max_size > 4:
        raise SystemExit("max-monoid-size must be in 1..=4")
    monoids = enumerate_two_generated_monoids(max_size)
    packages = generated_packages()
    focused_checks = focused_checker_invariants()
    checked = sat = conflict = 0
    differential = 0
    for package in packages:
        for monoid in monoids:
            rank, state = saturate(package, monoid)
            if (package.fixed_heads == (("q", "Function"), ("i", "Int"))
                    and package.descriptor_ports == (("q", ARG, "x"), ("q", RET, "i"))
                    and package.bounds == (("x", "q"),)):
                fixed_rank, _, _ = saturate_fixed_example(monoid)
                assert rank == fixed_rank, ("fixed/generic rank mismatch", monoid, rank, fixed_rank)
                differential += 1
            if len(package.bounds) == 2 and package.bounds[0] == package.bounds[1]:
                # Duplicate source inequalities retain distinct original IDs.
                assert {0, 1} <= {bound_id for bound_id, _, _ in state.active}
            if rank is None:
                if not check_witness(package, monoid, state):
                    minimal = shrink_bad_witness(package, monoid)
                    raise AssertionError(("SAT/witness mismatch", minimal, monoid, state))
                sat += 1
            else:
                conflict += 1
            checked += 1
    print("generated packages: %d (q=Function(child,child), i=Int; 0-2 original bounds)" % len(packages))
    print("focused malformed-input / independent-root checks: %d passed" % focused_checks)
    print("two-generated monoid presentations: %d; checked package/quotient pairs: %d"
          % (len(monoids), checked))
    print("fixed-example differential rank comparisons: %d passed" % differential)
    print("quotient outcomes: %d finite graph witnesses independently checked, %d conflicts"
          % (sat, conflict))
    print("scope is the generated Function/atom/empty-Record fragment only; no arbitrary-package FMP conclusion")


if __name__ == "__main__":
    main()
