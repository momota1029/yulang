#!/usr/bin/env python3
"""Non-authoritative finite emitted-constraint reconstruction experiment.

Reference: original direct inequalities plus unexpanded Function challenge.
Candidate: Q-substituted Cartesian Function parts and conjunctive routing.
Fixed payload rows are model-only tests, NOT a current closed carrier.
"""
import itertools as it
import json
import resource
import time

START = time.monotonic()
PATTERNS = ((0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 1, 2))
COUNT = dict(configurations=0, valuation_visits=0, route_pair_checks=0,
             observable_tuples=0, positive_tuples=0, negative_tuples=0,
             caller_predicate_checks=0, freshening_checks=0)


def check_budget():
    assert time.monotonic() - START < 9.0, 'internal 9-second deadline'


def leq(a, b):
    return a & b == a


def build_artifact(slots):
    # Reviewed bridge: every distinct payload row is Q in both polarities.
    rows = tuple(range(max(slots) + 1))
    q_map = {row: ordinal for ordinal, row in enumerate(reversed(rows))}
    # Permuted Q numbering deliberately avoids assuming q(row)==row.
    return q_map, ('Function', ('Intersection', tuple(q_map[r] for r in rows)),
                   ('Union', tuple(q_map[r] for r in rows)))


def instantiate(artifact, use):
    _, (_, (_, negative), (_, positive)) = artifact
    subst = {q: (use, q) for q in set(negative + positive)}
    # Same substitution for both polarities, all Cartesian Function parts.
    pairs = tuple((subst[a], subst[c]) for a in negative for c in positive)
    assert set(a for a, _ in pairs) == set(c for _, c in pairs)
    return subst, pairs


def reference(slots, valuation, u, v):
    a, b, c = slots
    return (leq(valuation[a], valuation[b]) and leq(valuation[b], valuation[c])
            and leq(valuation[a], valuation[c])
            and leq(u, valuation[a]) and leq(valuation[c], v))


def emitted(pairs, live, u, v):
    # Each routed positive Function is challenged by negative Function(u,v).
    # Source §22 decomposes each pair into u <= arg and result <= v.
    for argument, result in pairs:
        COUNT['route_pair_checks'] += 1
        if not (leq(u, live[argument]) and leq(live[result], v)):
            return False
    return True


def reconstruct(slots, fixed, u):
    previous = u
    result = []
    for row in range(max(slots) + 1):
        previous = fixed.get(row, previous)
        result.append(previous)
    return tuple(result)


def main():
    obstruction = None
    for atoms in (1, 2):
        domain = tuple(range(1 << atoms))
        for slots in PATTERNS:
            n = max(slots) + 1
            artifact = build_artifact(slots)
            q_map, _ = artifact
            subst0, pairs0 = instantiate(artifact, 0)
            subst1, pairs1 = instantiate(artifact, 1)
            assert set(subst0.values()).isdisjoint(subst1.values())
            COUNT['freshening_checks'] += 1
            for fixed_count in range(min(n, 2) + 1):
                for selected in it.combinations(range(n), fixed_count):
                    for values in it.product(domain, repeat=fixed_count):
                        check_budget()
                        fixed = dict(zip(selected, values))
                        source_ports, candidate_ports = set(), set()
                        for valuation in it.product(domain, repeat=n):
                            COUNT['valuation_visits'] += 1
                            if any(valuation[r] != x for r, x in fixed.items()):
                                continue
                            live0 = {subst0[q_map[r]]: valuation[r] for r in range(n)}
                            live1 = {subst1[q_map[r]]: valuation[r] for r in range(n)}
                            for u, v in it.product(domain, repeat=2):
                                before = reference(slots, valuation, u, v)
                                after = emitted(pairs0, live0, u, v)
                                assert after == emitted(pairs1, live1, u, v)
                                if before:
                                    source_ports.add((u, v))
                                if after:
                                    candidate_ports.add((u, v))
                                    if fixed_count <= 1:
                                        rebuilt = reconstruct(slots, fixed, u)
                                        assert reference(slots, rebuilt, u, v)
                        for uses in (1, 2):
                            COUNT['configurations'] += 1
                            sr = set(it.product(source_ports, repeat=uses))
                            cr = set(it.product(candidate_ports, repeat=uses))
                            for ports in it.product(tuple(it.product(domain, repeat=2)), repeat=uses):
                                COUNT['observable_tuples'] += 1
                                before, after = ports in sr, ports in cr
                                if fixed_count <= 1:
                                    COUNT['positive_tuples'] += 1
                                    assert before == after
                                else:
                                    COUNT['negative_tuples'] += 1
                                    assert not before or after
                                    if before != after and obstruction is None:
                                        obstruction = dict(atoms=atoms, slots=slots, fixed=fixed,
                                                           ports=ports, source=before, emitted=after)
                            # Every singleton characteristic predicate is checked by tuple
                            # membership above. They form a basis for every finite caller
                            # predicate; no powerset of predicate tables is enumerated.
                            if fixed_count <= 1:
                                assert sr == cr
                                universe = tuple(it.product(tuple(it.product(domain, repeat=2)), repeat=uses))
                                # Explicit correlated predicates, with shared fixed values.
                                predicates = (
                                    lambda p: True,
                                    lambda p: p[0][0] == p[-1][1],
                                    lambda p: leq(p[0][1], p[-1][0]),
                                    lambda p: p[0] != p[-1],
                                    lambda p: all(leq(x, p[0][1]) for x in fixed.values()),
                                )
                                for predicate in predicates:
                                    assert {p for p in sr if predicate(p)} == {p for p in cr if predicate(p)}
                                    COUNT['caller_predicate_checks'] += 1
    assert obstruction is not None
    # Smallest repeated-binder split: one atom, one row, one use, u=1,v=0.
    original = any(reference((0, 0, 0), (q,), 1, 0) for q in (0, 1))
    split_mutant = leq(1, 1) and leq(0, 0)
    assert not original and split_mutant
    # Smallest cross-use alias: one atom, one row, two singleton intervals.
    independent = all(any(reference((0, 0, 0), (q,), u, v) for q in (0, 1))
                      for u, v in ((0, 0), (1, 1)))
    shared_mutant = any(all(reference((0, 0, 0), (q,), u, v)
                           for u, v in ((0, 0), (1, 1))) for q in (0, 1))
    assert independent and not shared_mutant
    usage = resource.getrusage(resource.RUSAGE_SELF)
    print(json.dumps(dict(status='conditional emitted-constraint projection checked',
                         counts=COUNT, seeds=None, atoms=[1, 2], uses=[1, 2],
                         patterns=PATTERNS, model_only_two_fixed_obstruction=obstruction,
                         split_mutation=dict(ports=[[1, 0]], source=False, mutant=True),
                         shared_use_mutation=dict(ports=[[0, 0], [1, 1]], source=True, mutant=False),
                         wall_seconds=time.monotonic()-START,
                         cpu_seconds=usage.ru_utime+usage.ru_stime,
                         max_rss_kib_linux=usage.ru_maxrss), sort_keys=True))


if __name__ == '__main__':
    main()
