# Cycle 178: nominal pair same-model residual (in progress)

Started 2026-11-14 01:25:44 UTC. Latest fetched integration:
`d636750ce44de9271ebf328a5ab27ad4955cb845`. Fresh standing-orders and inbox I30
read; previous cycle177 completed with report; no previous writer observed.
55-minute user cap overrides longer text. No STOP observed.

## First source checkpoint

Six modules cover arbitrary finite linear type binders at two different
same-name nominal slots. Parameter intervals need not be point-valued.
The actual BranchModels is equivalent to source Models, endpoint subtyping and
the actual fresh capture merge equations. A finite form says each fresh lower
is equivalent to the union of the two lowers, and each fresh upper to the
intersection of the two uppers. Zero arity and source identity distinctions
are retained.

Current centered Candidate plus Models supplies endpoint subtyping. The
candidate's supplied-model Holds is exactly the merge/extrema residual;
conditional leaf and EvidenceNode-shaped producers consume that residual.
No historical journal membership or packet installation assumption is used.

The finite regression strengthens the old warning into a concrete centered
Models + Candidate example: the wrong value of a fresh lower gives no Evidence;
correcting that value gives Evidence. The two assignments agree on old source
identities. This has a nonpoint root and does NOT assert G reachability or
Stable. Therefore it is NOT a counterexample to G.EvidenceNode.

## Verification and limits

Focused Lean 4.35.0 trust-zero builds passed. The small audit scans all 146
new declarations (including private/generated declarations) and admits only
the standard propext/Classical.choice/Quot.sound set. Raw logs accompany this
checkpoint. Minor elaboration issues in newly written proofs were corrected;
none remain. No local full build or runtime oracle was executed.

The exact unrestricted G.EvidenceNode field is still OPEN. This fragment has
one nominal head, type-only linear binders, no requirements and no named
outputs. Nested patterns, repeated binders across positions, rows, compound
outputs and the general stable-selection model-extension/guard bridge remain
outside this new result. Runtime X13/X15 observations are not promoted to an
internal-state completeness theorem. Usage remaining: unknown.

At 01:40 UTC a fresh fetch found integration `60373c8c4194ec97a95f13c6f2ad335d7eb12b95`.
Its 28 added files and two append-only indexes were incorporated without dropping
any earlier work/dots-main file. This includes Astra's counterexample to the
nonterminal installation preservation contract, not to termination or G.
Focused validation of those upstream additions is running separately.

## Second checkpoint: corrected CI and stable comparison

The initial CI on 56a8a338 passed core but failed the Lean job because its build
policy treats an unused-simp warning as failure. The redundant simp argument
was removed without changing the theorem statement. Focused compilation now
uses `-DwarningAsError=true` as well as `--trust=0`. This was a verification
failure, not a newly introduced false theorem. Full CI will be rechecked on
the corrected source commit.

Thirteen source modules are now locally validated; the expanded small audit
passes all 285 declarations. Descriptor/parameter witnesses are recovered from
actual Finished inspection. Additional unconditional producers cover point
outer nominal arguments with arbitrary finite linear type binders, and
nullary nominal heads at either point or nonpoint endpoints.

A third assignment sets the explicit actual binder center to int and proves
full centered Plan.Holds. It must not be confused with the earlier corrected
raw-branch assignment. Source value support, raw Joint, raw Installable and
full centered Installable are constructed for the finite fixture. Consequently
`stable_not_selected` proves its bad-fixed-model state cannot simultaneously
be Stable and selected. The apparent gap is therefore not a stable-selection
counterexample.

The source-support construction is generalized to arbitrary finite nominal-pair
shapes in an initial singleton registry. The initial adapter derives raw Joint
and raw Installable from Candidate+selected, then full Installable from the
explicit common-centered-model existence premise. General production of that
common model remains OPEN. This nonpoint initial shape does not directly meet
G's point-root Initial predicate; support preservation to arbitrary reachable
states also remains open.

Independent review found no model substitution or G completion overclaim and
recompiled the point/nonpoint contrast separately. The two roots/states in
that contrast are different, despite equal nominal endpoint values.

## Final fragment: repeated binders and a restricted G consumer

Sixteen new source modules pass serial focused compilation with trust zero and
warnings as errors. The final small audit checks all 327 new declarations.
The shared-binder extension removes the distinct-name hypothesis: exact Holds
now requires same-model repeated-name coherence plus actual fresh endpoint
merges. Coherence is equivalent to the necessary projection condition;
it is not silently assumed automatic from Candidate.

Under a role-local restriction that every visible matching declaration has a
nullary nominal query, no input names, no associated outputs and no requirements,
GeneralDictionaryCenteredNullary178.evidence_at_G produces Evidence on the actual
G boundary for root or generated instances, using the supplied current model.
The associated=[] premise is not confused with outputNames. This restricted
consumer does NOT discharge unrestricted G.EvidenceNode: OPEN, 0 completed fields.

Independent review recompiled the shared-binder and nullary-G modules with
trust zero and warnings as errors. No model substitution or hidden distinctness
was found. The merge-only residual is conditional on source/order/coherence;
comments now explicitly state this qualification.

Checkpoint 30f8f6beb36c680babe4b1dac92e1e3be4244db3 passed both GitHub CI jobs:
core 43543184819, proof 43543184926. The proof job's Lean action, all-declaration
audit and executable examples all succeeded. Its 25 changed paths were fetched
back and matched byte hashes. This CI covers the thirteen-module checkpoint,
not automatically the later additions; final CI is checked separately.

Final declaration types were printed with full names (155 public checks).
The read-only dependency report reaches 257/327 new declarations from seven
fragment consumers and 50/327 from the restricted nullary G consumer alone.
The unchanged unrestricted composition reaches 0/327: no completion is claimed.
All three reach scans, the final 327-declaration axiom gate and type checks exit0.

## Final-source verification checkpoint

Commit cfb568e868a0938875c17f779a67376f1342e648 was fetched back: all 27
changed paths match. Core CI run43544084384 and proof run43544084478 both
completed success. Proof includes Lean action, every-declaration audit and
source/value/regular/semantic examples, all success. This is remote CI;
no local full lake build or verify-lean run is claimed.

The prior-cycle immutable-prefix check found changes only to lean/Yulang.lean
and notes/design/INDEX.md, both exact append-only; no prior content was removed.
The latest integration still60373c8 includes the new upstream additions.

Commands (focused runs use Lean4.35.0, LEAN_PATH=cycle178 dependency cache):
- python cycle178-verification/build.py <16 cycle178 module roots>: exit0,
  sequential --trust=0 -DwarningAsError=true; final-focused.log records all16.
- lean -j1 --trust=0 -DwarningAsError=true Audit/Cycle178FinalGate.lean: exit0,
  all327 declarations allowed-standard-axioms only.
- same flags tools/TypesCycle178.lean: exit0,155 public type checks.
- same flags tools/ReachCycle178.lean with each roots/output environment pair:
  all three exit0; raw log and per-declaration TSV retained.
- check-source.py: all imports/base/published paths retained, frozen configs,
  no forbidden source constructs and no trailing whitespace; exit0.
- git diff --check: exit0. Raw focused upstream build also exit0 (70 modules).

See notes/design/2026-11-14-cycle178-module-guide.md for Japanese statements,
quantifiers, explicit premises, and distinction of raw/centered/current models.
No unresolved language-design choice was decided, so no new question note was
needed. Usage budget remaining: unknown.

## Last source extension: actual G original-root consumer

The seventeenth source module GeneralDictionaryCenteredRootNominal178 connects
the finite linear point producer to the actual G original root. Reachability
recovers the unchanged original root's point-input property; actual lookup and
source injectivity force singleton bounds to one slot. A role-local finite
linear terminal nominal format then yields root Evidence in the supplied
current model. No Stable, Installable or alternate joint-model premise is used.
It does not cover generated children or unrestricted declarations, and the
EvidenceNode field remains OPEN. Independent source review checked the root
versus generated distinction and direct current-model use.

At02:08 fresh fetch found integration9adc7227ebbe1f428005e2158794c9ffcd58b383.
Its23 new files and two append-only indexes were incorporated without replacing
any prior content. These are Astra's canonical-executor/reachable-permutation
additions; they do not remove the current EvidenceNode obligation.

Final root-focused build and trust-zero/warning-as-error gate passed. The gate
now covers332 declarations across17 modules. Five additional public types bring
the type-check inventory to160. Original-root G consumer reaches10/332 new
symbols; unrestricted composition still0/332. This low dependency count reflects
reuse of existing point-spine theorems, not a measure of semantic coverage.

The root extension and latest integration were published as08f808cb7a597cdfc0f2db4040ddd2cc5ed65026.
All47 changed paths were fetched back with zero hash mismatches. The latest
upstream focused closure passed19 modules. I30 still names original G; the
new canonical-executor notes discuss G-prime but no instruction moved this
cycle to it. No target or classifier was strengthened.

Next-cycle candidates (not proved here):
1. Produce initial_point_linear_plan_joint: assign every actual binder center
   while preserving source and root-center Models; prove all Fits/headSchema.
2. Extend source-only PacketGuard preservation to arbitrary reachable states,
   retaining existing journal and recorded centered facts, not just initialAt.
3. For generated nonpoint nominal children, produce same-model shared coherence
   and fresh extrema from actual stable/installed invariants, without treating
   existential Candidate consistency as universal current-model validity.
The first is independent of the now-completed original-root raw Evidence
fragment; it concerns full centered installation, not raw packet.Holds.

Read-only documentation review checked the exact root theorem names and
current-model/root-only quantifiers. Clarification: the shared coherence versus
projection equivalence is under source Models and outer endpoint order, not an
unconditional standalone equivalence. The module guide explicitly labels the
older16/327/155 inventory as a historical checkpoint and records latest17/332/160.

## Latest source CI and focused-audit limitation

08f808cb7a597cdfc0f2db4040ddd2cc5ed65026 passed Core CI43544729305 and
Lean inference kernel43544729157. The proof job's Lean action, full audit and
executable examples each completed success. These checks include the latest
integration9adc7227 and all17 cycle178 modules.

Additional local upstream verification: CenteredCanonicalExecutor audit exit0.
CenteredReachablePermutation's original audit exit1 because it imports the full
Yulang aggregate, which this focused cache intentionally does not build. This
is an explicit local environment limitation, not suppressed as a pass. A scratch
copy replacing only that aggregate import with the exact focused dependency
root GeneralNominalCenteredPermutationRepresentation checks the same152
printed declarations and exits0; the copy and both logs are retained. The remote
full audit already passed the original unmodified file. No local full-build
restriction was bypassed, and no upstream file was edited.

At02:14 final fetch still found integration9adc7227 and source08f808cb.
After building the latest upstream dependency closure, the full new-module
332-declaration trust-zero/warning-as-error gate was rerun immediately before
publication and again exited0. Its raw prepublication-gate log is retained.
All verification processes finished; no background Lean writer remains.

## Completion (supersedes in-progress heading)

Status: completed at 2026-11-14T02:15:55Z, elapsed 50.20 minutes before final publication.
All17 own source modules match the CI-successful source08f808cb. Publication
and heartbeat are limited to work/dots-main. Latest integrated baseline is
9adc7227ebbe1f428005e2158794c9ffcd58b383. No approval blocker or writer overlap
was encountered. Earlier CI lint failure and local aggregate-audit limitation
are recorded above, corrected/independently bounded rather than hidden.

Final result: exact nominal residuals, current-model point/nullary producers,
restricted G nullary consumer and actual G original-root finite-linear consumer.
Unrestricted G.EvidenceNode remains OPEN; completed general fields this cycle:0.
No claim of a reachable Stable G counterexample, unrestricted completeness,
new runtime validation, or completion of Astra's remaining fields.

Source checkpoint deltas were44,25,27,47 paths respectively (overlap included;
upstream incorporation included). Final documentation/log delta and total unique
path count are recorded in the final publication manifest. The next cycle must
fresh-fetch integration/inbox and verify this completed heartbeat before writing.
