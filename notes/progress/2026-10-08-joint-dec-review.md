# JOINT-DEC research attempts: review and adjudication

Date: 2026-10-08
Branch: `research/simple-sub-intrusion`
Status: two reviewed conditional artifacts; JOINT_DEC remains OPEN-PROOF
Authority: no semantic or production authority added

## Scope and decisions

This record adjudicates the bounded constructive and falsification attempts at
the artifact snapshots below. It does not certify a finite complete Yulang
solver, establish undecidability for Yulang, change the canonical proof DAG, or
authorize F5 replacement.

### Conditional residual decision construction

The [constructive attempt](2026-10-08-joint-dec-constructive-attempt.md) is at
SHA-256 `ea26c27bfadd05441a708aab150ddb26f7a1c39ae01bcaf4be4ae25d3b043a56`,
after repair commit `b9fe8f927`.

The initial independent compiler-referee review accepted a **MAJOR** finding:
EPR's semantic prefix map `q_n` did not let an effective strategy extractor
classify an actual universal challenge. Effective existential lifts alone do
not compute that map. The reviewer supplied the ordered example
`forall n. exists b in {0,1}. b = H(n)` for noncomputable `H`; finite abstract
truth evaluation and effective existential lifts can coexist with a
noncomputable winning response. This finding did not invalidate EPR's
truth-equivalence induction.

The repair added ER, an explicit finite encoding interface, terminating prefix
classifier, universal-challenge coding/replay, Boolean-prefix preservation,
and closure under subsequent effective lifts. The repaired extraction claim
requires ER; truth equivalence still requires only EPR. A fresh bounded
compiler-referee delta review found **no remaining BLOCKING, major or minor
finding**. It confirmed the countermodel and the separation between EPR truth
and ER effective extraction.

Adjudication: accept the repair for this conditional theorem only. EPR and ER
are not constructed for Yulang. The selected original predicates, scopes,
quantifier order, and prerequisite gates remain unchanged; `JOINT_DEC` remains
OPEN-PROOF.

### Pairwise witness-amalgamation falsification

The independent [falsification artifact](2026-10-08-joint-dec-falsification.md)
is at SHA-256
`5742dca297cc4fd942edf48ceb658e3b543bcd14216c780a810424b223ff90c3`, commit
`20375f34e`.

Its compiler-referee review found **no BLOCKING, major or minor finding** in
the finite three-witness/three-predicate counterexample, minimality proof,
fixed-arity family, experiment accounting, or stated scope. The example
refutes pairwise reuse of independently chosen witnesses. It does not refute
pointwise truth-preserving quotient reflection with a coherent lift, supply
an admitted Yulang primitive, or prove Yulang undecidability. The 682-profile
Python enumeration, exit status and resource report are recorded in the
artifact; the reviewer inspected the reproduction statically and did not
rerun it.

Adjudication: accept this as a bounded shortcut falsifier only. It closes no
canonical gate and supplies no implementation permission.

## Verification and omissions

- Constructive review baseline: `6967ac589`; repair baseline:
  `20375f34eeae91c7f29473f3a787514c37c74abb`.
- All reviews were pinned to artifact hashes. The delta reviewer noted one
  process deviation: it used a read-only `git diff` despite the packet's
  instruction not to run Git commands. No index/ref mutation occurred, and
  this did not affect the mathematical review.
- No Cargo tests/builds or performance measurements ran. The bounded
  falsification artifact's own experiment is not a compiler test.
- Actual Yulang primitive enumeration, effective residual construction,
  production correspondence, principal public projection and F5 cutover were
  outside review scope.

## Next evidence

Trace one actual active non-name admission/future predicate from its selected
source owner through the original scoped operands. Establish, or identify the
first missing supplier for, both effective joint-cell decision and
prefix-local lift after arbitrary legal universal challenges. Keep the result
conditional and retain the OPEN-PROOF status unless the full gate's exact
prerequisites are discharged.
