# JOINT-DEC research attempts: review and adjudication

Date: 2026-10-08
Branch: `research/simple-sub-intrusion`
Status: six reviewed conditional artifacts; JOINT_DEC remains OPEN-PROOF
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

### Selected native id input-image owner cut

The [id inlet owner cut](2026-10-08-id-inlet-whole-output-image-owner-cut.md)
was frozen at SHA-256
`381371986bbf76490db5097a1efe1060bf5adb2be0c09f04cb222e982b8cf1c4`, commit
`d9f452ec3`. Its independent compiler-referee review found no BLOCKING,
major or minor finding within the original telescope, conditional prefix-local
image lift, and checker-boundary comparison.

The selected uniform-inlet construction supplies a concrete whole-image law
for bare native `id` at its original scopes, given authentic J/Car/context and
local-law evidence plus one coherent original strategy. This yields the
conditional prefix lift for those supplied inputs. It does not construct such
a strategy or decide arbitrary joint residual cells. The reference checker
validates external-law metadata and references, not the law bodies; submitted
finite proof recognition is not semantic proof search. The first missing
effective decision field remains joint preservation/reflection of possible
J/strategy witnesses. Production H7/F5 correspondence, foreign inlets and
general State/recursive cases were not certified.

Adjudication: accept the owner cut and conditional lift under their stated
premises. No semantic definition, source language, or production gate changed.

### Native id joint-witness representation and owner cut

The [relative finite-code transport](2026-10-08-joint-witness-representation-constructive.md)
was independently reviewed at SHA-256
`3f7fc08e07e497aab5d155abe2b87e4ee4d89b16ccbe1a37938c9dfd232fe21b` by a
compiler-referee. The review found no BLOCKING, major or minor issue in the
conditional transport theorem. It confirmed preservation/reflection for
arbitrary original residual predicates under the supplied effective input-code
and replay hypotheses, while confirming those hypotheses are not supplied by
Joint-ID, PE-ID or the native export. This is a relative transport result, not
a finite code construction for every admitted argument or a residual solver.

The independent [prefix-quotient mutation counterexample](2026-10-08-joint-witness-representation-counterexample.md)
was reviewed at SHA-256
`cdb0c2af8db72cd25193efc2002ddbb8916c0c14882b0d30fd71cf43d6f8a301` by a
compiler-referee. No BLOCKING, major or minor issue was found. Under H1–H4,
merging Unit and Bool description prefixes while retaining the original
`Eq(J.payload, Unit)` observer violates EPR clause 3's prefix-local lift.
The observer's actual source emission is not established; the counterexample
does not apply to bare `id` or refute JOINT_DEC.

The [native-id source-owner correspondence](2026-10-08-joint-witness-source-owner-correspondence.md)
was reviewed at its pre-repair SHA-256
`ad46e0959ef97e85427a423ec74a70ed0c303eed177210e1d3504ab38844feaf`. The
compiler-referee found no BLOCKING or major issue and one minor precision
issue. The primary corrected EPR.1 to require a finite layered presentation
and semantic map on legal original prefixes, leaving inhabitance/reflection
with EPR.3–4, and corrected the `ResolvedExpr::Lambda` locator. The final note
is a conditional source/implementation map; it does not claim that Rust
discarded a semantic witness it never constructed. The missing effective
inhabited-cell reflection, whole-prefix classification and replay remain A
correctness obligations; retaining genuinely constructed owner records may
prevent D reconstruction debt but cannot prove those laws.

Adjudication: accept all three research results within their exact scopes.
Retain `JOINT_DEC` as OPEN-PROOF and preserve its required-before-cutover
status. The source-owner audit used read-only Git inspection contrary to its
packet's no-Git instruction; no index or ref changed, and the artifact records
the deviation. No code, tests, builds or measurements ran.

## Verification and omissions

- Constructive review baseline: `6967ac589`; repair baseline:
  `20375f34eeae91c7f29473f3a787514c37c74abb`.
- All reviews were pinned to artifact hashes. The delta reviewer noted one
  process deviation: it used a read-only `git diff` despite the packet's
  instruction not to run Git commands. No index/ref mutation occurred, and
  this did not affect the mathematical review.
- No Cargo tests/builds or performance measurements ran. The bounded
  falsification artifact's own experiment is not a compiler test.
- Actual exhaustive Yulang primitive enumeration, effective residual
  construction, production correspondence, principal public projection and F5
  cutover remain outside review scope.

## Next evidence

Find an effective representation and reflection law for the exact native
`id` J/strategy witnesses identified by the owner cut. Preserve arbitrary
original joint residuals, binder order and simultaneous witness identity.
The relative transport only needs an already-coded strategy; the source audit
locates no such effective owner, while the conditional mutation shows why
prefix keys must preserve actual J-observers. Next, derive an independently
interpreted effective witness interface for one complete native J/current-
context family, addressing EPR.3–4 and ER. Keep `JOINT_DEC` OPEN-PROOF unless
its complete prerequisites are discharged.
