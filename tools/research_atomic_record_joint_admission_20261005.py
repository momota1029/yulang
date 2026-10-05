#!/usr/bin/env python3
"""Finite joint-admission attack; supplied predicates, no source semantics."""

import json
import resource
import signal


BASELINE = "0ab7620e167f190691a9ec50fde507d039265aa4"
SOURCES = (
    (("a", "kappa"),),
    (("a", "kappa"), ("b", "kappa")),
    (("a", "kappa"), ("b", "lambda")),
    (("a", "kappa"), ("b", "Int")),
)
OMEGA = (0, 1)
HIDDEN = frozenset(("kappa", "lambda"))


def positive_atomic_record(fields):
    return tuple((label, atom) for label, atom in fields if atom not in HIDDEN)


VIEWS = ((), (("b", "Int"),))
CANONICAL = (0, 3)
PAIRS = tuple((source, omega) for source in range(4) for omega in OMEGA)
VIEW_OF = tuple(VIEWS.index(positive_atomic_record(source)) for source in SOURCES)


def permission_pairs(profile):
    """kappa always permitted; profile bit omega permits extra hidden lambda."""
    mask = 0
    for bit, (source, omega) in enumerate(PAIRS):
        rigid = {atom for _, atom in SOURCES[source] if atom in HIDDEN}
        permitted = {"kappa"}
        if profile & (1 << omega):
            permitted.add("lambda")
        if rigid <= permitted:
            mask |= 1 << bit
    return mask


def project_pairs(mask):
    result = 0
    for bit, (source, omega) in enumerate(PAIRS):
        if mask & (1 << bit):
            result |= 1 << (2 * VIEW_OF[source] + omega)
    return result


def forget_omega(view_pairs):
    return int(bool(view_pairs & 3)) | (int(bool(view_pairs & 12)) << 1)


def canonical_image(mask):
    result = 0
    for view, source in enumerate(CANONICAL):
        if any(mask & (1 << PAIRS.index((source, omega))) for omega in OMEGA):
            result |= 1 << view
    return result


def same_witness_retraction(admission, permitted):
    for bit, (source, omega) in enumerate(PAIRS):
        if admission & permitted & (1 << bit):
            canonical = CANONICAL[VIEW_OF[source]]
            if not admission & (1 << PAIRS.index((canonical, omega))):
                return False
    return True


def entries(mask):
    return [[source, omega] for bit, (source, omega) in enumerate(PAIRS)
            if mask & (1 << bit)]


def run():
    assert all(dict(source).get("a") == "kappa" for source in SOURCES)
    assert tuple(positive_atomic_record(SOURCES[s]) for s in CANONICAL) == VIEWS
    assert len(set(SOURCES)) == 4  # Distinct finite trees, no sharing observability.
    pair_images = tuple(project_pairs(mask) for mask in range(256))
    images = tuple(forget_omega(pair_images[mask]) for mask in range(256))
    canonical_images = tuple(canonical_image(mask) for mask in range(256))
    counters = dict.fromkeys((
        "cases", "canonical_exact", "joint_retraction", "exact_without_retraction",
        "canonical_false_negative", "join_projected_same_omega_false_positive",
        "join_after_forgetting_omega_false_positive",
        "separately_exact_but_joint_canonical_inexact",
    ), 0)
    witnesses = {}
    for profile in range(4):
        permitted = permission_pairs(profile)
        retracts = tuple(same_witness_retraction(mask, permitted) for mask in range(256))
        for guards in range(256):
            for phi in range(256):
                counters["cases"] += 1
                admitted = guards & phi & permitted
                exact_image = images[admitted]
                graft_image = canonical_images[admitted]
                joint_retraction = retracts[guards & phi]
                assert graft_image & ~exact_image == 0
                if joint_retraction:
                    counters["joint_retraction"] += 1
                    assert exact_image == graft_image
                if exact_image == graft_image:
                    counters["canonical_exact"] += 1
                    if not joint_retraction:
                        counters["exact_without_retraction"] += 1
                else:
                    counters["canonical_false_negative"] += 1
                # Retaining omega still loses the original source witness if
                # each predicate's projection is computed independently.
                same_omega_join = forget_omega(
                    pair_images[guards & permitted] & pair_images[phi & permitted])
                forgetful_join = images[guards & permitted] & images[phi & permitted]
                assert exact_image & ~same_omega_join == 0
                assert same_omega_join & ~forgetful_join == 0
                flags = {
                    "join_projected_same_omega_false_positive": same_omega_join != exact_image,
                    "join_after_forgetting_omega_false_positive": forgetful_join != exact_image,
                    "separately_exact_but_joint_canonical_inexact": (
                        images[guards & permitted] == canonical_images[guards & permitted]
                        and images[phi & permitted] == canonical_images[phi & permitted]
                        and exact_image != graft_image),
                }
                # Independent same-omega retraction of each factor is sufficient.
                if retracts[guards] and retracts[phi]:
                    assert joint_retraction
                for name, flag in flags.items():
                    if flag:
                        counters[name] += 1
                        rank = (guards.bit_count() + phi.bit_count(), profile, guards, phi)
                        if name not in witnesses or rank < witnesses[name][0]:
                            witnesses[name] = (rank, {
                                "permission_profile": profile,
                                "guards_true_at_source_omega": entries(guards),
                                "phi_true_at_source_omega": entries(phi),
                                "exact_image_bits": exact_image,
                                "canonical_image_bits": graft_image,
                                "same_omega_marginal_join_bits": same_omega_join,
                                "omega_forgotten_join_bits": forgetful_join,
                            })

    # Pin the discriminating witnesses independently of minimizer order.
    permitted = permission_pairs(0)
    guards, phi = 1, 4  # {} and {b:kappa}, both omega 0, same projected {}.
    assert images[guards & phi & permitted] == 0
    assert forget_omega(pair_images[guards] & pair_images[phi]) == 1
    guards, phi = 1, 2  # Same canonical graph but disjoint omega coordinates.
    assert forget_omega(pair_images[guards] & pair_images[phi]) == 0
    assert images[guards] & images[phi] == 1
    guards, phi = 5, 6  # Each marginal has a canonical representative, at different omega.
    assert images[guards & permitted] == canonical_images[guards & permitted] == 1
    assert images[phi & permitted] == canonical_images[phi & permitted] == 1
    assert images[guards & phi & permitted] == 1
    assert canonical_images[guards & phi & permitted] == 0
    assert not same_witness_retraction(guards & phi, permitted)
    # Denying required kappa removes all witnesses, even the empty visible image.
    assert all("kappa" in {atom for _, atom in source} for source in SOURCES)
    assert images[255 & 0] == canonical_images[255 & 0] == 0
    assert counters["cases"] == 4 * 256 * 256
    return {
        "claim": "finite supplied-predicate characterization; no theorem promotion",
        "baseline": BASELINE,
        "range": "exhaustive, no random seed; four atomic source Records, two omega coordinates",
        "sources": SOURCES,
        "views": VIEWS,
        "canonical_source_indices": CANONICAL,
        "permission_profiles": "four choices permitting lambda at omega 0/1; kappa always allowed",
        "counters": counters,
        "minimal_mutant_witnesses": {name: result for name, (_, result) in witnesses.items()},
        "self_checks": "PASS: conditional reduction, same-witness joins, permission exclusion, mutations",
        "budget": "one process; wall 5 s; CPU 5 s; address space 256 MiB",
    }


if __name__ == "__main__":
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    signal.setitimer(signal.ITIMER_REAL, 5)
    print(json.dumps(run(), indent=2, sort_keys=True))
