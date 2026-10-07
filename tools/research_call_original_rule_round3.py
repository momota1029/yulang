#!/usr/bin/env python3
"""Sorted coverage discriminators; no Yulang semantics or source admission.

The countable separation is proved analytically in the companion note. This
probe checks named finite instances and the finite-fiber lemma's whole 3x3
Boolean envelope. It never constructs or replaces an original Yulang kernel.
"""

from itertools import combinations


def check_call_input_seam():
    """Propositional law-instance test, not an admitted semantic model.

    CalRet yields world/callable. Delay, the first phase, and Bind are
    implications whose antecedents need independently constructed inputs.
    Hold raw Call output and initial argument typing fixed throughout.
    """
    implies = lambda premise, conclusion: not premise or conclusion
    raw_call_output = initial_argument_typed = world = callable_mem = True
    target_typed = False

    def local_laws(arg_at_return, arg_compatible, carrier, receipt_input,
                   phase_typed, bind_interface):
        return all((
            implies(True, world and callable_mem),  # CalRet
            implies(arg_at_return and arg_compatible, carrier),
            implies(callable_mem and carrier and receipt_input, phase_typed),
            implies(phase_typed and bind_interface, target_typed),
        ))

    # Missing return-frame transport: initial typing survives only as a fact
    # at C0. Every preservation implication is true; no constructor types O.
    assert local_laws(False, False, False, False, False, False)
    assert raw_call_output and initial_argument_typed and not target_typed
    # Supplying argument/carrier facts does not supply receipt authority.
    assert local_laws(True, True, True, False, False, False)
    # Supplying a typed phase does not supply its ordered Bind interface.
    assert local_laws(True, True, True, True, True, False)

    # The repaired bridge provides one joint tuple. With each implication
    # instantiated, successive modus ponens determines the typed conclusion.
    arg_at_return = arg_compatible = receipt_input = bind_interface = True
    carrier = arg_at_return and arg_compatible
    phase_typed = callable_mem and carrier and receipt_input
    composed_typed = phase_typed and bind_interface
    assert composed_typed

    # Separately inhabited facts need not have a common evidence extension.
    argument_extensions, compatibility_extensions = {"w-a"}, {"w-b"}
    assert argument_extensions and compatibility_extensions
    assert not argument_extensions.intersection(compatibility_extensions)


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def main():
    check_call_input_seam()
    # Two distinct evidence arms survive at every candidate contribution.
    # All semantic coordinate fields are constant; only the coverage bound
    # varies. The contribution label, position and slot are different sorts.
    original_coordinates = ("X", "beta", "slot", "p0", "u", "scope", "xi")

    def witness(bound, arm, retained_inputs=()):
        assert arm in ("own-upper", "provider-owned")
        return original_coordinates, ("contribution", bound), arm, retained_inputs

    def covers(association, history):
        coordinates, contribution, _, _ = association
        assert coordinates == original_coordinates
        return history <= contribution[1]

    assembly_cases = 0
    for finite_family in subsets(range(6)):
        bound = max(finite_family, default=0)
        # Assembly preserves both licensed evidence arms, without quotient.
        assembled = tuple(witness(bound, arm, tuple(witness(z, arm)
                                                  for z in finite_family)) for arm in
                          ("own-upper", "provider-owned"))
        assert len(set(assembled)) == 2
        assert all(covers(a, z) for a in assembled for z in finite_family)
        assert assembled[0][2] != assembled[1][2]
        assert all(set(a[3]) == {witness(z, a[2]) for z in finite_family}
                   for a in assembled)
        assembly_cases += 1

    diagonal_cases = 0
    for bound in range(64):
        for arm in ("own-upper", "provider-owned"):
            a = witness(bound, arm)
            assert covers(a, bound)
            assert not covers(a, bound + 1)
            diagonal_cases += 1

    # Exhaustive finite-fiber check: 3 original witnesses, 3 observations,
    # every Boolean coverage relation. Empty-family existence is included.
    finite_matrices = 0
    compact_successes = 0
    for mask in range(1 << 9):
        cover = lambda a, z: bool(mask & (1 << (3 * a + z)))
        finite_cover = all(any(all(cover(a, z) for z in family)
                              for a in range(3))
                           for family in subsets(range(3)))
        uniform = any(all(cover(a, z) for z in range(3)) for a in range(3))
        assert finite_cover == uniform
        compact_successes += int(finite_cover)
        finite_matrices += 1

    # Exact independent-predicate nonimplications. Same association data,
    # same full coverage and original evidence are held fixed in each pair.
    association_exists = True
    complete_coverage = True
    attach = False
    assert association_exists and complete_coverage and not attach
    attach = True
    licensing_derivation = False
    license_origin_record = "original-own-upper-origin"
    assert association_exists and complete_coverage and attach
    assert license_origin_record and not licensing_derivation

    # Global denotation preimage is insufficient at a particular owned fiber.
    owned_slot, other_slot = "s-owned", "s-other"
    contribution = "c-full"
    denotation = {contribution: "full-family"}
    incidence = {(other_slot, contribution)}
    assert denotation[contribution] == "full-family"
    assert (owned_slot, contribution) not in incidence

    print(f"PASS: {assembly_cases} finite-family assemblies retaining two arms; "
          f"{diagonal_cases} countable-model diagonal instances; "
          f"{finite_matrices} finite-fiber matrices "
          f"({compact_successes} satisfy finite/uniform coverage); "
          "3 independent-rule seam discriminators")
    print("PASS: Call-input vacuity discriminator (return-frame, receipt, "
          "Bind interface), joint-input composition, incompatible witnesses")
    print("Scope: sorted algebra only; countable theorem is analytical; "
          "no source admission, original-kernel closure, or gate closure")


if __name__ == "__main__":
    main()
