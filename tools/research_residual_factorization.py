#!/usr/bin/env python3
"""Bounded differential search for open structural residual factorization.

The checker compares direct structural satisfaction with normalization into
closed structural checks plus retained open-head residuals. It keeps one
supplied finite Phi relation and copies an opaque context marker while
projecting the resulting joint solutions onto finite coordinates. A deliberate
Function-variance mutant is shrunk to a two-variable witness.

This is an executable characterization of a small acyclic fragment. It does
not decide arbitrary open bounds, recursive residual SCCs, rigid scope guards,
source-context finiteness, effects, or production acceptance.

Run: python3 tools/research_residual_factorization.py
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from random import Random


@dataclass(frozen=True, order=True)
class Atom:
    name: str


@dataclass(frozen=True, order=True)
class Var:
    name: str


@dataclass(frozen=True, order=True)
class Function:
    argument: "Type"
    result: "Type"


@dataclass(frozen=True, order=True)
class Record:
    fields: tuple[tuple[str, "Type"], ...]


Type = Atom | Var | Function | Record
BASE = (Atom("Bool"), Atom("Int"), Var("x"), Var("y"))
ATOMS = (Atom("Bool"), Atom("Int"))
CONTEXT = ("nu0", "K0", "D0", "guard0")


def make_terms() -> tuple[Type, ...]:
    terms: set[Type] = set(BASE)
    terms.update(Function(a, r) for a, r in product(BASE, repeat=2))
    terms.add(Record(()))
    for label in ("a", "b"):
        terms.update(Record(((label, child),)) for child in BASE)
    terms.update(
        Record((("a", left), ("b", right)))
        for left, right in product(BASE, repeat=2)
    )
    return tuple(sorted(terms, key=lambda item: (size(item), repr(item))))


def size(ty: Type) -> int:
    if isinstance(ty, (Atom, Var)):
        return 1
    if isinstance(ty, Function):
        return 1 + size(ty.argument) + size(ty.result)
    return 1 + sum(size(child) for _, child in ty.fields)


TERMS = make_terms()


def make_closed_domain() -> tuple[Type, ...]:
    atoms = tuple(ATOMS)
    values: set[Type] = set(atoms)
    values.update(Function(a, r) for a, r in product(atoms, repeat=2))
    values.add(Record(()))
    for label in ("a", "b"):
        values.update(Record(((label, child),)) for child in atoms)
    values.update(
        Record((("a", left), ("b", right)))
        for left, right in product(atoms, repeat=2)
    )
    return tuple(sorted(values, key=lambda item: (size(item), repr(item))))


CLOSED = make_closed_domain()
ASSIGNMENTS = tuple(
    (x, y, k)
    for x, y, k in product(CLOSED, CLOSED, (0, 1))
)
FULL_MASK = (1 << len(ASSIGNMENTS)) - 1


@lru_cache(maxsize=None)
def substitute(ty: Type, x: Type, y: Type) -> Type:
    if isinstance(ty, Var):
        return x if ty.name == "x" else y
    if isinstance(ty, Function):
        return Function(substitute(ty.argument, x, y), substitute(ty.result, x, y))
    if isinstance(ty, Record):
        return Record(tuple((name, substitute(child, x, y)) for name, child in ty.fields))
    return ty


@lru_cache(maxsize=None)
def structural_subtype(left: Type, right: Type) -> bool:
    if isinstance(left, Atom) and isinstance(right, Atom):
        return left == right
    if isinstance(left, Function) and isinstance(right, Function):
        return structural_subtype(right.argument, left.argument) and structural_subtype(
            left.result, right.result
        )
    if isinstance(left, Record) and isinstance(right, Record):
        left_fields = dict(left.fields)
        return all(
            name in left_fields and structural_subtype(left_fields[name], child)
            for name, child in right.fields
        )
    return False


@dataclass(frozen=True)
class Bound:
    bound_id: int
    left: Type
    right: Type
    context: tuple[str, str, str, str]


@dataclass(frozen=True)
class NormalForm:
    residuals: tuple[Bound, ...]
    visited: tuple[Bound, ...]
    failure: str | None


def normalize_bound(
    bound: Bound,
    *,
    wrong_function_variance: bool = False,
) -> NormalForm:
    residuals: list[Bound] = []
    visited: list[Bound] = []
    seen: set[tuple[int, Type, Type]] = set()

    def visit(left: Type, right: Type) -> bool:
        key = (bound.bound_id, left, right)
        if key in seen:
            return True
        seen.add(key)
        child = Bound(bound.bound_id, left, right, bound.context)
        visited.append(child)

        if isinstance(left, Var) or isinstance(right, Var):
            residuals.append(child)
            return True
        if isinstance(left, Atom) and isinstance(right, Atom):
            return left == right
        if isinstance(left, Function) and isinstance(right, Function):
            if wrong_function_variance:
                argument_pair = (left.argument, right.argument)
            else:
                argument_pair = (right.argument, left.argument)
            return visit(*argument_pair) and visit(left.result, right.result)
        if isinstance(left, Record) and isinstance(right, Record):
            left_fields = dict(left.fields)
            if any(name not in left_fields for name, _ in right.fields):
                return False
            return all(
                visit(left_fields[name], child_type)
                for name, child_type in right.fields
            )
        return False

    ok = visit(bound.left, bound.right)
    return NormalForm(tuple(residuals), tuple(visited), None if ok else "structural")


def direct_mask(bound: Bound) -> int:
    mask = 0
    for index, (x, y, _k) in enumerate(ASSIGNMENTS):
        left = substitute(bound.left, x, y)
        right = substitute(bound.right, x, y)
        if structural_subtype(left, right):
            mask |= 1 << index
    return mask


def residual_mask(form: NormalForm) -> int:
    if form.failure is not None:
        return 0
    mask = FULL_MASK
    for residual in form.residuals:
        local = 0
        for index, (x, y, _k) in enumerate(ASSIGNMENTS):
            left = substitute(residual.left, x, y)
            right = substitute(residual.right, x, y)
            if structural_subtype(left, right):
                local |= 1 << index
        mask &= local
    return mask


def relation_mask(predicate) -> int:
    return sum(
        1 << index
        for index, assignment in enumerate(ASSIGNMENTS)
        if predicate(*assignment)
    )


def project(mask: int, coordinates: tuple[int, ...]) -> frozenset[tuple]:
    projected = set()
    for index, assignment in enumerate(ASSIGNMENTS):
        if mask & (1 << index):
            projected.add(tuple(assignment[position] for position in coordinates))
    return frozenset(projected)


def all_bound_pairs() -> tuple[tuple[Type, Type], ...]:
    return tuple(product(TERMS, repeat=2))


def contains_variable(ty: Type) -> bool:
    if isinstance(ty, Var):
        return True
    if isinstance(ty, Function):
        return contains_variable(ty.argument) or contains_variable(ty.result)
    if isinstance(ty, Record):
        return any(contains_variable(child) for _, child in ty.fields)
    return False


def exhaust_single_bounds():
    pairs = all_bound_pairs()
    direct_by_pair = {}
    normal_by_pair = {}
    residual_count = 0
    visited_count = 0
    for bound_id, (left, right) in enumerate(pairs):
        bound = Bound(bound_id, left, right, CONTEXT)
        form = normalize_bound(bound)
        direct = direct_mask(bound)
        normalized = residual_mask(form)
        assert direct == normalized, (bound, form)
        assert all(item.context is CONTEXT for item in form.visited)
        assert all(item.context is CONTEXT for item in form.residuals)
        direct_by_pair[(left, right)] = direct
        normal_by_pair[(left, right)] = normalized
        residual_count += len(form.residuals)
        visited_count += len(form.visited)
    return pairs, direct_by_pair, normal_by_pair, residual_count, visited_count


def phi_relations(seed: int, count: int = 128) -> tuple[int, ...]:
    rng = Random(seed)
    relations = [FULL_MASK, 0]
    relations.append(relation_mask(lambda x, y, _k: x == y))
    relations.append(relation_mask(lambda x, y, _k: x != y))
    relations.append(relation_mask(lambda _x, _y, k: k == 0))
    relations.append(relation_mask(lambda x, y, k: k == ((CLOSED.index(x) + CLOSED.index(y)) % 2)))
    relations.extend(
        sum(1 << index for index in range(len(ASSIGNMENTS)) if rng.getrandbits(1))
        for _ in range(count - len(relations))
    )
    return tuple(relations)


def check_joint_projection(direct_by_pair, normal_by_pair):
    rng = Random(20261006)
    keys = tuple(direct_by_pair)
    phis = phi_relations(20261006)
    cases = 0
    nonempty = 0
    for _ in range(2048):
        pair_count = rng.choice((1, 2, 3))
        package = tuple(rng.sample(keys, pair_count))
        context = CONTEXT
        assert all(context is CONTEXT for _ in package)
        direct = FULL_MASK
        normalized = FULL_MASK
        for pair in package:
            direct &= direct_by_pair[pair]
            normalized &= normal_by_pair[pair]
        phi = rng.choice(phis)
        direct &= phi
        normalized &= phi
        assert direct == normalized
        assert project(direct, (0,)) == project(normalized, (0,))
        assert project(direct, (1,)) == project(normalized, (1,))
        assert project(direct, (2,)) == project(normalized, (2,))
        assert project(direct, (0, 2)) == project(normalized, (0, 2))
        nonempty += bool(direct)
        cases += 1
    return cases, nonempty


def minimum_variance_mutant():
    candidates = []
    assignments = tuple(product(CLOSED, CLOSED))
    for left, right in all_bound_pairs():
        if not isinstance(left, Function) or not isinstance(right, Function):
            continue
        bound = Bound(0, left, right, CONTEXT)
        mutant = normalize_bound(bound, wrong_function_variance=True)
        for x, y in assignments:
            direct = structural_subtype(substitute(left, x, y), substitute(right, x, y))
            mutated = all(
                structural_subtype(substitute(item.left, x, y), substitute(item.right, x, y))
                for item in mutant.residuals
            ) and mutant.failure is None
            if direct != mutated:
                candidates.append((size(left) + size(right), repr(left), repr(right), left, right, x, y, direct, mutated))
                break
    assert candidates
    candidate = min(
        candidates,
        key=lambda item: (item[0], item[1], item[2], repr(item[5]), repr(item[6])),
    )
    _, _, _, left, right, x, y, direct, mutated = candidate
    assert direct and not mutated
    return left, right, x, y, direct, mutated


def main() -> None:
    pairs, direct, normalized, residuals, visits = exhaust_single_bounds()
    joint_cases, nonempty = check_joint_projection(direct, normalized)
    left, right, x, y, exact, mutant = minimum_variance_mutant()
    assert len(CLOSED) == 15
    assert len(TERMS) == 45
    assert len(pairs) == 45 * 45
    print(f"finite closed assignments: {len(CLOSED) ** 2} type pairs × 2 symbolic tags")
    open_pairs = sum(contains_variable(left) or contains_variable(right) for left, right in pairs)
    print(
        f"structural inequalities checked: {len(pairs)} total; "
        f"{open_pairs} contain open variables, {len(pairs) - open_pairs} are closed-only"
    )
    print(f"normalization visits: {visits}; retained residual instances: {residuals}")
    print(
        f"joint packages checked under correlated Phi masks: {joint_cases}; "
        f"nonempty solutions: {nonempty}; x/y/tag coordinate projections preserved"
    )
    print(
        "minimum wrong-variance mutant: "
        f"{left} <: {right}, x={x}, y={y}; direct={exact}, mutant={mutant}"
    )
    print(
        "scope: bounded acyclic structural types, copied opaque context marker, "
        "one generic binary correlated tag and supplied finite Phi; "
        "no rigid scopes, feedback SCCs, effects, "
        "source-context generation, or production solver"
    )


if __name__ == "__main__":
    main()
