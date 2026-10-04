#!/usr/bin/env python3
"""Check sharp operand coverage for reconstructing source relations.

This isolated model exhausts Boolean relation factors and coordinate-projection
families. It does not define a production descriptor or Function query. The
separate proof states the unbounded theorem and original-scope requirements.

Run: python3 tools/research_source_factor_cover.py
"""

from __future__ import annotations

from functools import lru_cache
from itertools import product


ROWS = tuple(product((0, 1), repeat=3))
SCOPES = tuple(tuple(i for i in range(3) if mask & (1 << i)) for mask in range(8))
FAMILIES = tuple(tuple(i for i in range(8) if mask & (1 << i)) for mask in range(256))
FULL = (1 << len(ROWS)) - 1


def projection(row, scope):
    return tuple(row[i] for i in scope)


def row_set(mask):
    return frozenset(row for i, row in enumerate(ROWS) if mask & (1 << i))


def relation_mask(rows):
    return sum(1 << i for i, row in enumerate(ROWS) if row in rows)


@lru_cache(maxsize=None)
def reconstruct(source_mask: int, family_mask: int) -> int:
    source = row_set(source_mask)
    bags = tuple(SCOPES[i] for i in FAMILIES[family_mask])
    images = tuple(frozenset(projection(row, bag) for row in source) for bag in bags)
    joined = frozenset(
        row for row in ROWS
        if all(projection(row, bag) in image for bag, image in zip(bags, images))
    )
    return relation_mask(joined)


def covers(schema: tuple[int, ...], family_mask: int) -> bool:
    # This syntactic test knows only declared operand scopes, not relation rows.
    return all(
        any(set(SCOPES[factor]) <= set(SCOPES[bag]) for bag in FAMILIES[family_mask])
        for factor in schema
    )


def factor_relations(scope_id):
    tuples = tuple(product((0, 1), repeat=len(SCOPES[scope_id])))
    return tuple(
        frozenset(row for i, row in enumerate(tuples) if mask & (1 << i))
        for mask in range(1 << len(tuples))
    )


def source_relations(schema):
    # Includes empty factors and empty source relations. With no factors the
    # original conjunction is True; with a false zero-arity factor it is False.
    choices = tuple(factor_relations(scope_id) for scope_id in schema)
    for factors in product(*choices):
        yield relation_mask(frozenset(
            row for row in ROWS
            if all(projection(row, SCOPES[scope_id]) in allowed
                   for scope_id, allowed in zip(schema, factors))
        ))


def check_uniform_characterization():
    schemas = (
        ("one ternary factor", (7,), 256, 128),
        ("two overlapping binary factors", (3, 6), 256, 160),
        ("three unary factors", (1, 2, 4), 64, 218),
        ("one zero-arity factor", (0,), 2, 255),
        ("no factors", (), 1, 256),
    )
    reports = []
    total = 0
    for name, schema, expected_sources, expected_uniform in schemas:
        uniform = [True] * len(FAMILIES)
        sources = tuple(source_relations(schema))
        assert len(sources) == expected_sources
        for source in sources:
            for family in range(len(FAMILIES)):
                joined = reconstruct(source, family)
                assert source & ~joined == 0
                exact = source == joined
                uniform[family] &= exact
                if covers(schema, family):
                    assert exact, (name, source, family, joined)
                total += 1
        for family, exact_for_all in enumerate(uniform):
            assert exact_for_all == covers(schema, family), (name, family)
        assert sum(uniform) == expected_uniform
        reports.append((name, len(sources), sum(uniform)))
    assert total == 148224
    return total, reports


def parity_counterexample():
    # All three binary projections, each retaining its actual shared indices.
    pair_family = sum(1 << scope for scope in (3, 5, 6))
    candidates = []
    for source in range(1, FULL):
        rows = row_set(source)
        pair_images_full = all(
            len({projection(row, SCOPES[scope]) for row in rows}) == 4
            for scope in (3, 5, 6)
        )
        if pair_images_full and reconstruct(source, pair_family) != source:
            candidates.append(source)
    minimum = min(candidates, key=lambda mask: (len(row_set(mask)), mask))
    even = relation_mask(frozenset(row for row in ROWS if sum(row) % 2 == 0))
    assert minimum == even
    assert len(row_set(minimum)) == 4
    assert sum(len(row_set(mask)) == 4 for mask in candidates) == 2
    assert reconstruct(even, pair_family) == FULL
    bad = min(row_set(FULL) - row_set(even))
    assert bad == (0, 0, 1)
    # The same obstruction defeats every proper coordinate projection at once.
    every_proper_bag = (1 << 7) - 1
    assert reconstruct(even, every_proper_bag) == FULL
    return even, bad


def source_request_image(even, bad):
    # Finite source-core instance with independently supplied exact XOR and
    # selector primitives. a,b are retained in the input challenge; c selects
    # an already existing provider. Pi keeps request/continuation origin.
    def observation(row):
        a, b, c = row
        provider = "L" if c == 0 else "R"
        return ((a, b), ("request", "q", provider, "continuation:" + provider))

    original = frozenset(observation(row) for row in row_set(even))
    rebuilt = frozenset(observation(row) for row in ROWS)
    forbidden = observation(bad)
    assert forbidden not in original and forbidden in rebuilt
    assert ((0, 0), ("request", "q", "L", "continuation:L")) in original
    # A joint client predicate selecting the uncovered tuple also separates
    # source and reconstruction without inventing a new Function resolver.
    client = frozenset({bad})
    assert not row_set(even) & client
    assert row_set(FULL) & client
    return forbidden


def shared_private_witness_mutant():
    # Rebinding one original shared witness independently is not local hiding.
    left = frozenset({0})
    right = frozenset({1})
    original = bool(left & right)
    independently_hidden = bool(left) and bool(right)
    assert not original and independently_hidden


def main():
    total, reports = check_uniform_characterization()
    even, bad = parity_counterexample()
    forbidden = source_request_image(even, bad)
    shared_private_witness_mutant()
    print(f"factor-assignment/projection-family cases: {total}")
    for name, sources, uniform in reports:
        print(f"{name}: {sources} factor assignments; {uniform}/256 uniform exact families")
    print(f"minimum all-pairwise-full proper relation: {tuple(sorted(row_set(even)))}")
    print(f"added tuple: {bad}; projected request outside original source: {forbidden}")
    print("scope: Boolean relational model and supplied-primitive source-core witness; "
          "no production descriptor, Function resolution, or principal theorem")


if __name__ == "__main__":
    main()
