#!/usr/bin/env python3
"""Finite conditional relation experiment; not a Yulang semantics oracle.

One root Function(a,c), forwarding a <= b <= c and a <= c. Contiguous
aliases preserve acyclicity. Root has no own symbol. Payloads use powerset
of two atoms; one assignment per identity, including repeated occurrences.
Budget: one process, <=5000 generated (graph, fixed map, challenge) models.
"""
import itertools
import json
import resource
import time

DOMAIN = tuple(range(4))
GRAPHS = ((0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 1, 2))


def leq(left, right):
    return left & right == left


def expand(row, positive, edges, valuation, retain):
    # Independent from the oracle's direct constraint predicate. This is the
    # supplied candidate rule, not a derivation of compiler/source rules.
    neighbors = tuple(a if positive else b for a, b in edges
                      if (b if positive else a) == row)
    if not neighbors:
        return valuation[row]
    result = valuation[row] if retain else (0 if positive else 3)
    for neighbor in neighbors:
        child = expand(neighbor, positive, edges, valuation, retain)
        result = result | child if positive else result & child
    return result


def main():
    start = time.monotonic()
    models = assignments = guarded_successes = pointwise = 0
    dropped_witness = erasure_witness = split_witness = None
    for slots in GRAPHS:
        count = max(slots) + 1
        edges = tuple(sorted({(a, b) for a, b in
                              ((slots[0], slots[1]), (slots[1], slots[2]),
                               (slots[0], slots[2])) if a != b}))
        valuations = tuple(itertools.product(DOMAIN, repeat=count))
        # None = existential, integer = externally fixed coordinate.
        for partial in itertools.product((None,) + DOMAIN, repeat=count):
            for u, v in itertools.product(DOMAIN, repeat=2):
                models += 1
                assert models <= 5000
                assert time.monotonic() - start < 9.0, "internal wall stop"
                reference = candidate_retained = candidate_dropped = erased = False
                for valuation in valuations:
                    assignments += 1
                    if any(f is not None and valuation[i] != f
                           for i, f in enumerate(partial)):
                        continue
                    direct = all(leq(valuation[a], valuation[b]) for a, b in edges)
                    before = leq(u, valuation[slots[0]]) and leq(valuation[slots[2]], v)
                    neg = expand(slots[0], False, edges, valuation, True)
                    pos = expand(slots[2], True, edges, valuation, True)
                    after = leq(u, neg) and leq(pos, v)
                    if direct:
                        pointwise += 1
                        assert neg == valuation[slots[0]]
                        assert pos == valuation[slots[2]]
                    reference |= direct and before
                    candidate_retained |= direct and after
                    candidate_dropped |= after
                    erased |= (direct and leq(u, expand(slots[0], False, edges, valuation, False))
                               and leq(expand(slots[2], True, edges, valuation, False), v))
                assert reference == candidate_retained
                fixed_in_interval = (leq(u, v) and all(
                    f is None or (leq(u, f) and leq(f, v)) for f in partial))
                fixed_ordered = all(partial[i] is None or partial[j] is None
                                    or leq(partial[i], partial[j])
                                    for i in range(count) for j in range(i + 1, count))
                assert candidate_dropped == fixed_in_interval
                assert reference == (fixed_in_interval and fixed_ordered)
                if fixed_ordered:
                    guarded_successes += 1
                    assert reference == candidate_dropped
                packet = {"slots": slots, "fixed": partial, "challenge": [u, v],
                          "reference": reference, "candidate_dropped": candidate_dropped}
                if reference != candidate_dropped and dropped_witness is None:
                    dropped_witness = packet
                if reference != erased and erasure_witness is None:
                    erasure_witness = dict(packet, erased=erased)
                # Freshen each occurrence and each side independently, only
                # with no fixed coordinates: choose all negative values Top
                # and all positive values Bottom. This admits every challenge.
                if all(f is None for f in partial) and not candidate_dropped and split_witness is None:
                    split_witness = dict(packet, occurrence_split=True)
    assert dropped_witness and erasure_witness and split_witness
    usage = resource.getrusage(resource.RUSAGE_SELF)
    print(json.dumps({"status": "conditional-laws-checked; dropped-bounds-counterexample",
                      "seed": None, "domain": "powerset of two atoms (0..3)",
                      "graph_slot_patterns": GRAPHS, "max_total_rows_including_root": 4,
                      "generated_models": models, "valuation_visits": assignments,
                      "direct_satisfying_pointwise_checks": pointwise,
                      "ordered_fixed_models": guarded_successes,
                      "first_dropped_bounds_witness": dropped_witness,
                      "first_own_erasure_mutation_witness": erasure_witness,
                      "first_occurrence_split_mutation_witness": split_witness,
                      "wall_seconds": round(time.monotonic() - start, 6),
                      "cpu_seconds": round(usage.ru_utime + usage.ru_stime, 6),
                      "max_rss_kib_linux": usage.ru_maxrss}, sort_keys=True))


if __name__ == "__main__":
    main()
