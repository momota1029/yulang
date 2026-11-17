# Cycle245: concrete Common public models and passive query transport

## Scope and recovered state

Started 2026-11-17T18:30:00Z. Prior244 was already published/reported; no pending
writer or unpublished prior result was found. Starting integration was
f516ae3f967ada900fc07bc5ebe335c66dfcac1f. At18:57 fetched and merged latest
integration939fe87ba6d0b93c03e152fb22d2021818991f10: its tree is exactly the
already integrated244 tree, with no changed standing orders or inbox. I47
remains active; no STOP appeared. I46 token hygiene and frozen Audit.lean /
README.md were respected. All new code is additive; barrel imports append only.

Two checked checkpoints were published during the cycle:
- 4d986636ce18e2409df062b5aa294ddf2af946e1: six modules /162 constants.
- 10aebfc109a6d5af98d41c23cddb485aa81429fe: thirteen modules /276 constants.

## Main verified result

`GeneralPresencePreorderExtension245.public_models_iff` proves equality of
public existential solution sets for the actual Presence owner-table `rebase`.
It requires selected owner present, disjoint owner targets, old/fresh External
and Coherent blocks, fresh targets within old targets, and public names outside
old targets. The law interface is a subtype preorder and primitive constructor
congruence, not antisymmetry of type syntax.

`GeneralPresenceCommonLaws245.common_laws` proves all these semantic laws for
`CommonNominalFullCarrier.model`, including arrow variance and whole-record
default at depth zero and positive depths. `RebasePlan245.common_plan_exact`
therefore instantiates the public iff for this concrete nominal Common model
and composes it through a finite list of actual table rebases certified at
every intermediate state. Public Comp coordinates are literally equal;
private type values may be equivalent rather than identical. A two-edit
example checks changed private definitions and the rewritten base constraint.

`QueryTransport245`, `ObservedPlan245`, and `CommonObserved245` extend the
result to passive tagged CompTerm query bundles that are actually rewritten
at every step. Type values remain mutually below each other; row values are
identical; every concrete all-depth/all-negative-rank demand observation and
arbitrary exact-row predicate is preserved. Tags and table projection are
preserved. This is not a claim that actual cache/inspection metadata has been
exhaustively enumerated or mutated.

## Representation checks and exact limitations

- UsedSupport245 distinguishes type reads from unchanged row reads. Its
  transformed External criterion is exact; under old External it examines only
  old RHSs actually selected by typed lookup. Unused-entry and row-only examples
  pass where the former sufficient checker rejects.
- UsedTable245 applies the check to the actual owner table.
- RankedTable245 proves rank/uniform-target-rank/disjointness preservation and
  every next guard under explicit fresh-ranked and TargetsWithin premises.
  The actual producer for these premises is not supplied.
- Readback245 restores old models in one direction with explicit subtype
  reflexivity. ReadbackLimit245 proves that the bare Model signature does not
  suffice without it. The stronger preorder result above closes the other
  direction under its stated conditions.
- CheckClosureLimit245 verifies that all current active checks can pass in a
  three-owner cycle yet the next check fails after one safe fresh edit.
- PlanTerminationLimit245 proves that Safe alone permits a bottom/top cycle
  (not accessible), and arbitrarily deep closed-pair fresh definitions with
  one owner and one unchanged private identity. Thus neither stopping nor a
  finite syntax bound follows from this permissive certificate.
- GuardedBlockLimit245 constructs a regular Common solution of the actual
  block `2 = pair(2,0)` for every public boundary, preserving all non2 Comp
  coordinates and all rows. That satisfiable block fails External and every
  strict source rank. These sufficient guards must not become language
  rejection conditions.

All negative examples concern auxiliary interfaces. None is claimed reachable
from source execution or a counterexample to an intended language theorem.

## Verification

All18 new modules were independently rebuilt with Lean4.35.0,
`--trust=0 -DwarningAsError=true`; all exits0. A generated new audit scans every
constant belonging to these modules, allowing only propext, Classical.choice,
and Quot.sound in their transitive axiom dependencies:

    CYCLE245-OBSERVED-PASS: 381 constants in18 modules

`notes/verification/cycle245/verified-build-audit.txt` contains the complete
module/build/audit result. `source-sha256.json` records the verified sources.
`verify.py` reproduces the focused new-module checks. Audits published at
previous checkpoints were not overwritten; `Cycle245Observed.lean` is new.
No prohibited Lean tokens were found, and diff whitespace checks pass.

Only focused existing dependencies were restored, at most the58-module closure
of CommonNominalFullGuardedClosure. No whole repository/journal build was run.
Six prior recovery drafts under notes/recovery/cycle244 remain unverified and
unimported. The global frozen gate remains supervisor work.

## Open work and why the next adapter was not built here

The actual OriginView243 import closure is726 modules,649 absent at measurement.
Launching that rebuild would contradict the focused-cache recovery constraint.
A source review instead recorded precise adapter targets in
`notes/design/2026-11-17-cycle245-metadata-adapter-review.md`.

In particular, Origin.Observes.source returns an exact value. Mutual subtype
query transport does not preserve that exact witness; one must transport
witnesses up to equivalence and prove Fits/Test invariance. Historical Effect
snapshots and their indexed proofs, current/source/live copies, semantic
projection reports versus real inspector control lists, and proof-bearing
non-enumerated caches must all be handled explicitly.

SafePlan production, actual fresh aggregate/source obligations, full
SourceBoundary/journal simulation, finite plan generation, solver Acc, and
EvidenceNode completion remain open. The newly proved Common laws and public
iff are semantic table results, not a claim that these operational gaps closed.

Publication verification and final head are recorded in the completion receipt.
