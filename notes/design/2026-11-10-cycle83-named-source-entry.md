# Cycle83: checked source entry from named scalar assumptions

Status: Draft. Date: 2026-11-10. Scope: the existing finite, scope-resolved,
scope-at-most-one scalar fragment, not a language restriction.

## Partial goal

Remove the caller's accepted Package and package-indexed ordinary State from
the outer entry. Input consists of source clauses and a finite list of named
scalar assumptions. Compute validation, all allocation, initial equality atoms,
associated saturation, ordinary consistency and every role check internally.
The list supplies explicit known source equations, not a total head oracle.
Only names occurring in the source are interpreted by this fragment. Bindings
outside that domain are irrelevant; this is an explicit interface boundary,
not a decision about source syntax, scope errors or language diagnostics.

## Independent meaning and quantified target

Define Derives on original source names, with initial assumption membership
and the existing independent source-equation Step as its only rules. Define
Models by one source-name type valuation satisfying every derived scalar fact
on the original source's finite name domain. Neither definition mentions an
allocated slot, Package, ordinary State, executable resolver or saturator.

For arbitrary associated environment, role registry, core WellFormed and
AssocWellFormed proofs, arbitrary source and arbitrary named assumptions:
runSource = true iff source validity, independent Models, and every original
role clause has an independently derived scalar receiver and independently
Discharges. No successful check, package, dependent state, fuel, chosen model
or complete visit sequence is supplied. Also aim to transport named derivations
across source and assumption membership equivalences, yielding sibling-order
invariance without caller state reallocation.

## Limits and verification

The new entry has no arbitrary incoming ordinary constraints or effects. The
cycle82 entry retaining arbitrary old State is preserved. Scalar encoding is
still int/str for role materialization. Bool/unit remain representable evidence,
not materializable roles. This Bool is readiness, not a final diagnostic.
Dynamic where generation, visibility, source inference, K2 and B4 remain open.
Spec6.3 and the audit C3-PARENT/C3-PARENT-NEG support conjunctive role checking;
the new carrier has not been run in Yulang2.

Focused build, trust=0 audit, direct accepted/rejected fragment cases,
contradictory assumptions, unseeded receivers, propagation to bare clauses,
permuted sources and assumptions. No full local build or full Audit.
