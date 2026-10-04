#!/usr/bin/env python3
"""Finite checks for source-contract/common-allowance proof clauses.

Research only. This is neither a source elaborator nor a production resolver.
It enumerates complete finite provider bounds, including conservative may
fields, and keeps correlated providers at one typed assignment. The general
proof and its additional interpretation hypotheses are in
notes/design/2026-10-05-source-contracts-and-common-allowance.md.
"""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Event:
    family: str
    type_argument: int
    origin: int
    continuation: int
    resumed_state: int


@dataclass(frozen=True)
class Provider:
    identity: int
    returned_provider: int
    may: frozenset[tuple[str, int]]
    history: tuple[Event, ...]
    returns: bool


def row(mask: int, nu: int) -> frozenset[tuple[str, int]]:
    return frozenset((family, nu) for bit, family in enumerate(("Read", "Write"))
                     if mask & (1 << bit))


def providers(nu: int) -> tuple[Provider, ...]:
    result = []
    for identity, mask, word, returns in product(
            range(2), range(4), ((), ("Read",), ("Write",),
                                ("Read", "Write"), ("Write", "Read")),
            (False, True)):
        may = row(mask, nu)
        if not frozenset((family, nu) for family in word) <= may:
            continue
        history = tuple(Event(family, nu, identity, step, (step + identity) % 2)
                        for step, family in enumerate(word))
        # Distinct roots can return the same or a different later provider.
        result.append(Provider(identity, (identity + len(word)) % 2,
                               may, history, returns))
    return tuple(result)


def bound(p: Provider, allowance: frozenset[tuple[str, int]]) -> bool:
    # The whole declared may-bound is checked, including conservative extras.
    # The noncoverage envelope and finite history grammar are fixed here.
    return p.may <= allowance


def source_history(p: Provider, q: Provider) -> tuple[Event, ...]:
    # A nonreturning prefix keeps q latent. Its allocation need not disappear.
    return p.history + (q.history if p.returns else ())


def abstract_closure(source: int, guard: int, extras: int,
                     edges: tuple[int, int, int]) -> int:
    """Least guarded closure on three abstract WHOLE tuples, encoded as bits."""
    current = guard & (source | extras)
    while True:
        following = current
        for point in range(3):
            if current & (1 << point):
                following |= edges[point]
        following &= guard
        if following == current:
            return current
        current = following


def check_abstraction() -> tuple[int, int]:
    inputs = tuple((r, g) for r, g in product(range(8), repeat=2)
                   if not r & ~g)
    ordered = tuple((i, j) for i, (ra, ga) in enumerate(inputs)
                    for j, (rb, gb) in enumerate(inputs)
                    if not ra & ~rb and not ga & ~gb)
    extensive_cases = monotone_cases = 0
    # Every binary rewrite relation on three tuples, and every constant Z.
    for relation, extras in product(range(512), range(8)):
        edges = tuple((relation >> (3 * point)) & 7 for point in range(3))
        outputs = tuple(abstract_closure(r, g, extras, edges) for r, g in inputs)
        for (r, g), out in zip(inputs, outputs):
            assert not r & ~out
            assert not out & ~g
            extensive_cases += 1
        for i, j in ordered:
            assert not outputs[i] & ~outputs[j]
            monotone_cases += 1

    no_edges = (0, 0, 0)
    assert abstract_closure(1, 3, 2, no_edges) == 3
    assert abstract_closure(0, 3, 2, no_edges) == 2  # No source anchor.
    assert abstract_closure(1, 1, 2, no_edges) == 1  # Old bound enforced.
    assert (1 | 2) & ~1  # Omitting the guard admits a forbidden extra.
    assert abstract_closure(1, 3, 2, no_edges) & ~abstract_closure(1, 3, 0, no_edges)

    def negative_seed_mutant(r: int) -> int:
        return r | (0 if r & 1 else 2)

    assert not 0 & ~1  # Source inclusion 0 <= 1.
    assert negative_seed_mutant(0) & ~negative_seed_mutant(1)
    return extensive_cases, monotone_cases


def main() -> None:
    absorption_cases = 0
    allocation_cases = 0
    assignment_pairs = 0
    empty_domains = 0
    conservative_provider_count = 0
    old_bound_erasure_witness = None
    independent_witness = None

    for nu in range(2):
        ps = providers(nu)
        rows = tuple(row(mask, nu) for mask in range(4))
        pairs = tuple(product(range(len(ps)), repeat=2))
        assignment_pairs += len(pairs)
        conservative_provider_count += sum(
            frozenset((e.family, e.type_argument) for e in p.history) < p.may
            for p in ps)

        # Phi models retained source dependencies. The final case is empty;
        # emptiness is not confused with a malformed typed-row fiber.
        kernels = (
            frozenset(pairs),
            frozenset((i, j) for i, j in pairs
                      if ps[i].identity == ps[j].identity),
            frozenset((i, j) for i, j in pairs
                      if ps[i].returned_provider == ps[j].identity),
            frozenset(),
        )
        allowed = tuple(frozenset(i for i, p in enumerate(ps) if bound(p, r))
                        for r in rows)

        for kernel, e1, e2, eout in product(kernels, range(4), range(4), range(4)):
            old_domain = frozenset((i, j) for i, j in kernel
                                   if i in allowed[e1] and j in allowed[e2])
            empty_domains += not old_domain
            # Observable may fields can be strictly larger than executions.
            # Original output coordinates stay in the joint residual.
            old_observations = frozenset(
                (i, j, rows[eout], source_history(ps[i], ps[j]))
                for i, j in old_domain
                if frozenset((e.family, e.type_argument)
                             for e in source_history(ps[i], ps[j])) <= rows[eout])

            for a, common in enumerate(rows):
                if not (rows[e1] | rows[e2] | rows[eout]) <= common:
                    continue
                common_domain = frozenset((i, j) for i, j in old_domain
                                          if i in allowed[a] and j in allowed[a])
                common_observations = frozenset(
                    o for o in old_observations if o[2] <= common)
                assert common_domain == old_domain
                assert common_observations == old_observations
                absorption_cases += 1

                if old_bound_erasure_witness is None:
                    erased_domain = frozenset((i, j) for i, j in kernel
                                              if i in allowed[a] and j in allowed[a])
                    extra = erased_domain - old_domain
                    if extra:
                        i, j = min(extra)
                        old_bound_erasure_witness = (nu, e1, e2, a,
                                                     ps[i].may, ps[j].may)

            # An independent allocation view may have W strictly above the
            # FIXED old E_out. Nothing assigns that old endpoint to W.
            for outer in rows:
                if not (rows[e1] | rows[e2] | rows[eout]) <= outer:
                    continue
                view_domain = old_domain
                submitted_common_domain = frozenset(
                    (i, j) for i, j in old_domain
                    if bound(ps[i], outer) and bound(ps[j], outer))
                assert submitted_common_domain == view_domain
                assert all(o[2] <= outer for o in old_observations)
                allocation_cases += 1

        diagonal = kernels[1]
        left = {i for i, _ in diagonal}
        right = {j for _, j in diagonal}
        extra = set(product(left, right)) - diagonal
        assert extra
        if independent_witness is None:
            i, j = min(extra)
            independent_witness = (ps[i].identity, ps[j].identity)

    assert old_bound_erasure_witness is not None
    assert independent_witness is not None
    assert conservative_provider_count > 0

    # A quiet execution can come from a provider with a larger MAY interface.
    quiet_read = next(p for p in providers(0)
                      if not p.history and p.may == row(1, 0) and p.returns)
    exact_trace_test = not quiet_read.history
    assert exact_trace_test and not bound(quiet_read, row(0, 0))

    # Same families at different dependent type assignments are not coverage.
    typed_read = next(p for p in providers(1) if p.may == row(1, 1))
    assert not bound(typed_read, row(1, 0))
    assert {family for family, _ in typed_read.may} == {"Read"}

    # The old fixed outer row remains Read in a wider public view.
    fixed_outer = row(1, 0)
    public_outer = row(3, 0)
    assert fixed_outer < public_outer
    assert (fixed_outer | public_outer) == public_outer
    assert fixed_outer != public_outer  # Overwriting it violates its old Eq.

    # Guarantee inclusion cannot discharge a newly enlarged input domain.
    old_challenges = frozenset({"quiet"})
    new_challenges = frozenset({"quiet", "Read"})
    old_guarantee = new_guarantee = frozenset()
    assert old_guarantee <= new_guarantee
    assert not new_challenges <= old_challenges

    # An unreachable stage separates exact validity from allocation validity.
    divergent = next(p for p in providers(0)
                     if not p.returns and not p.history and not p.may)
    unreachable = quiet_read
    actual_history = source_history(divergent, unreachable)
    exact_valid_at_empty = not actual_history
    allocation_valid_at_empty = (divergent.may | unreachable.may) <= row(0, 0)
    allocation_valid_at_read = (divergent.may | unreachable.may) <= row(1, 0)
    assert exact_valid_at_empty and not allocation_valid_at_empty
    assert allocation_valid_at_read  # The source is not rejected for divergence.

    print(f"typed provider pairs: {assignment_pairs}")
    print(f"conservative provider bounds: {conservative_provider_count}")
    print(f"complete joint absorption cases: {absorption_cases}")
    print(f"fixed-fiber allocation view cases: {allocation_cases}")
    print(f"empty correlated domains included: {empty_domains}")
    print("old-bound-erasure mutant: rejected; witness "
          f"nu/E1/E2/a={old_bound_erasure_witness[:4]}")
    print("independent-provider projection mutant: rejected; "
          f"distinct identities={independent_witness}")
    print("exact-trace-only provider check: rejected by quiet conservative bound")
    print("family-only typed coverage: rejected by dependent type arguments")
    print("fixed-old-output overwrite: rejected by Read versus Read,Write")
    print("negative-domain widening: rejected despite equal guarantees")
    print("unreachable-stage boundary: exact empty valid; allocation Read valid")
    extensive, monotone = check_abstraction()
    print(f"guarded abstraction extensivity/envelope cases: {extensive}")
    print(f"two-parameter positive abstraction comparisons: {monotone}")
    print("unanchored constant extra: admitted within the complete guard")
    print("guard-erasure, unmatched-extra, negative-seed mutants: rejected")


if __name__ == "__main__":
    main()
