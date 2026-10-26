# Independent native replay/saturation review

Date: 2026-10-26
Reviewer: `/root/native_replay_review`, fresh generic bounded leaf
Assignment baseline: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, branch `yulang3`
Decision: **REPAIR_REQUIRED** — one bounded source-correspondence correction.
The Lean finite lemmas and the paper's P-specialized local Effect extension
have no other substantial finding. Original whole-native saturation,
native/model `Satisfied`, complete Call and whole-source soundness remain OPEN.

## 1. Exact reviewed bytes and evidence

| Frozen artifact | Independently read-back SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeReplayCoverage.lean` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| `notes/theory/2026-10-26-native-replay-saturation.md` | `4759c80a17b6275e4184880cc43407ed86846b65b79bc592d3446eb26dfd90a4` |
| `tasks/agent-loop/inbox/20261026-inference-native-saturation.md` | `ae1063b94527fd16d274a7c183e2552f4455e76df3fa9eb58dbf0a667e04bbe2` |
| isolated built `NativeReplayCoverage.olean` | `677860b08f586a0782d71dcdbf22dd084700b9ea69a1faf165d8606e759c2131` |
| isolated `NativeReplayOriginAudit.lean` | `aa2a640bf575d6ac4f04accf6edd62cdd04d40dee1762a84f78f8cdbc230a2eb` |
| `check-05-final.log` | `b27e952c6a839de8179ff44b6b7418f0deefe947d6999de281dae238453b8e81` |
| `origin-audit-06.log` | `60a6d71b7e94da2c7ef1f2e054ec018d5d857977228fd92d6e7f13a614a86675` |

All isolated paths are below
`/workspace/scratch/f98087c7ac1a/inference-native-saturation`.
The review recomputed every one of the freeze manifest's 19 hashes: zero
mismatches. Repository and isolated module source bytes are equal. This
includes current Rust dependencies; the candidate-context test-only sibling
declaration has not changed the reviewed hash at this check.

Read the actual Lean module, named audit's complete printed types/axioms,
module-origin audit program and output, project pin/manifest/configuration,
relevant README, original parent statements, governing top-level inference
principles, selected suspension contract section 4, and the previously reviewed
2026-10-13 complete Value-block derivation. Source checks followed the actual
Rust owners rather than treating the old receipt as current source evidence.

The final recorded build is the focused
`lake --no-cache build +YulangClosure.NativeReplayCoverage`, followed by the
named audit, both exit 0. Actual versions recorded and inspected are Lean
4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb (Lean version 4.35.0)`. The origin audit uses
`lake --no-cache env lean -j1 -M1024 NativeReplayOriginAudit.lean` against that
same isolated built module. No default/root project build is inferred.

Independent parsing confirms exactly 276 unique, ordered matching
`ORIGIN_BEGIN`/`ORIGIN_END` names, 276 TYPE records and 276 AXIOMS records,
including five private declarations. These are **276 originating declarations,
not 276 theorems**. The audit enumerates module origin, checks its required
roots are theorem constants, and recursively collects axioms. The named audit
checks all 14 delivered theorem roots. Observed complete axiom sets are only
`[]`, `[propext]`, and `[propext, Quot.sound]`. No `Classical.choice`, project
axiom, `sorryAx`, unchecked native evaluation assumption or source checker
bypass occurs. The generated `run._unsafe_rec` and `runRoutes._unsafe_rec`
names are ordinary compiler-generated entries in that origin inventory, not
source declarations adding an axiom or bypass.

## 2. Required correction: merge lookup is not unconditional enqueue

**R1 — medium, source-correspondence claim.** Paper section 3 says:

> No typed children run inside these loops, so every resulting target
> lower/upper pair is queued. This establishes local target-product generation.

The first clause about noninterleaving is supported, but the asserted queue
conclusion is stronger than the owner implements:

- `merge_candidate_rows` at `candidate_intrusion.rs:699–708` calls
  `candidate_replay_bound` once per resulting target lower.
- `candidate_replay_bound` at `candidate_extrusion.rs:1070–1113` visits each
  current opposite physical position and calls `candidate_context_begin_replay`
  with `incoming_use=false`.
- `candidate_context_begin_replay` at `candidate_context.rs:4009–4070` uses
  recorded replay heads, emits only the two incremental quadrants, and skips
  an already retained Replay dependency in ordinary mode.
- `candidate_context_canonicalize_bounds` at `:4230–4250` adds transports for
  changed keys; it does not reset all replay heads or clear the ordinary
  dependency-skip guard. Existing unchanged target BoundKeys can therefore
  have a nonempty old/old product with no newly queued child for that product.

For example, an already replayed pair of unchanged target bounds remains in
the resulting target product after an unrelated merge addition. Reaching its
physical pair in the merge replay loop does not cause old/old fibers to be
enumerated again. Even within an enumerated quadrant the dependency guard can
skip a child. This is directly visible in the selected owners and requires no
new compiler test or claim that native inference is unsound.

This matters because Lean `step .merge` explicitly enqueues the **entire**
resulting product. Its theorem is correct for that program; the quoted sentence
does not establish an exact native refinement of its merge action. In addition,
the actual merge increments intrusion generation. Existence of an old dependency
alone cannot silently establish its still-valid completion after that change.
The note correctly keeps broader merge/currentness transport OPEN elsewhere;
the local queue assertion must respect that boundary too.

**Minimal repair:** replace the quoted assertion with the exact local result:
the merge owner visits all resulting target physical lower/upper positions
without typed-child interleaving and invokes ordinary replay lookup for each;
that lookup generates its new fiber quadrants while retaining old/old and
dependency-skipped work as a separate disposition/currentness obligation.
Explicitly say that correspondence to the abstract full-product merge action
requires this additional disposition/transport proof. Do not add a saturation
assumption, claim existing dependencies are completed merely from their IDs,
or alter the native implementation. A paper-only correction is sufficient;
the Lean source and checked theorem types need no change.

No other substantial issue was found within the frozen packet's stated scope.
A focused delta review of this paragraph and any changed summary suffices.

## 3. Lean theorem types and premise comparison

All names below have prefix `YulangClosure.NativeReplayCoverage.`. Exact fully
qualified printed types are retained in the hash-pinned named audit above.

| Root | Actual conclusion and relevant inputs | Complete axioms |
| --- | --- | --- |
| `mem_product` | Pair membership iff membership of both list components | `propext`, `Quot.sound` |
| `replay_quadrants_cover` | Current full product iff delta product or old/old product, for arbitrary four lists and selected endpoints | `propext`, `Quot.sound` |
| `incoming_replay_covers_all` | Empty old heads make replayDelta equal the full current product | `propext`, `Quot.sound` |
| `empty_covered` | Empty Owner is Covered | none |
| `step_covered` | Covered input implies Covered after one explicit Action | `propext`, `Quot.sound` |
| `run_covered` | Covered input implies Covered after a finite action list | `propext`, `Quot.sound` |
| `committed_routes_covered` | Covered input implies Covered after committed routes; rejected routes leave it unchanged | `propext`, `Quot.sound` |
| `completed_routes_cover` | From empty Owner, empty final pending list and final lower/upper membership imply completed pair membership | `propext`, `Quot.sound` |
| `scan_direct` | Any original direct member occurs in the saved-count scan despite arbitrary direct/exact suffix growth | `propext`, `Quot.sound` |
| `scan_exact_without_direct_growth` | Any original exact member occurs when directGrowth is constantly empty; exact suffix growth is arbitrary | `propext`, `Quot.sound` |
| `temporal_three_case_coverage` | Three conditional physical-snapshot membership inputs imply one of the two actual scan-membership alternatives | `propext`, `Quot.sound` |
| `equal_level_row_bound_is_upper` | Equal supplied levels choose `(lower,false,upper)` in selectRowBound | `propext`, `Quot.sound` |
| `function_children_exact` | Membership iff one of the four signed, kind-correct Function demands | `propext` |
| `live_concat_saved_count_misses_atom` | Concrete two-read arithmetic example misses the shifted exact atom | `propext` |

The finite completion root is exactly conditional on
`(runRoutes {} routes).pending = []` and membership in that program's resulting
lower and upper lists. It has no input semantic model, `Satisfied`,
`RegularSub`, saturation, or supplied Covered state. Covered is established
from the empty owner by induction. This is a legitimate finite scheduling
result, while relating arbitrary native execution to this program is still
an independent obligation.

The temporal theorem does not assume its own scan-membership conclusion.
Its inputs say DL is present in the upper-restoration direct-lower snapshot,
DU is present in the EL-restoration direct-upper snapshot, or EL is present
in the EU-restoration exact-lower snapshot. Its upper-restoration scan fixes
the direct-lower prefix; the source proof must derive that fact. The abstract
scan uses arbitrary suffix functions and therefore proves a stronger harmless
list fact than monotone callback growth alone requires.

Rollback is represented by ignoring a rejected route's whole ghost action
suffix, including consumes of older pending work. This matches the inspected
context undo/truncation/reset mechanisms at `candidate_context.rs:2081–2173`
and retirement at `:2190–2245`, with the explicit separate route-transaction
correspondence still required. Numeric operation-ID reuse is not treated as
permanent event identity. No runtime trace-retention architecture is proposed.

## 4. Independent check of the bounded plain Effect extension

The paper's P hypotheses are operational restrictions on this lemma's
constructor instance, not new restrictions on accepted Yulang or premises
equivalent to saturation. They retain authentic immediate capture, all-local
fresh allocation under the current representative/level/generic guard, one
use level and map, plain Effect endpoints, absent capture-incidence and reverse
frontier additions, identity contexts, zero/no-demand scoped flow, no extra
source activation, no initial extrusion parents, an idle worklist, and completed
successful restoration. Completion is not claimed for arbitrary source programs.

The following current-owner checks support the claimed bounded result:

1. `candidate_scheme.rs:2137–2255` gives DL/DU/EL/EU for Value and, after
   removing the two explicitly excluded Effect additions, exactly that order
   for Effect. The reverse-frontier guard is `boundary > 0` together with shape
   membership; boundary zero really disables it. Capture-incidence records are
   separately emitted before ordinary Effect lanes and correctly excluded.
2. Preparation at `:4248–4283` consults current representatives and metadata,
   deduplicates by the kind-tagged representative, and fresh-allocates at the
   common use level only under the real guard. Structural reconstruction at
   `:4370–4498` uses those same mapped rows throughout Function, record, tuple,
   and variant children. It introduces no independently fresh child row.
3. Both native row/row apply branches select direct **upper** storage at equal
   levels. Non-row endpoints can append only exact bounds. Under P the Effect
   terminal pair is BottomPositive against EmptyNegative (with row cases handled
   earlier), and `candidate_check_effect_operand` returns without creating rows.
   Support/Contribution/AnnotationMember/Allowance producer branches are outside P.
4. `candidate_context_execute_relation` returns immediately for identity after
   scoped checks; its scoped observation branch requires one of the excluded
   effect operands. Its Allowance registration lies beyond the identity return.
   `candidate_register_capture_bound` itself requires an Allowance upper and
   therefore cannot repopulate capture incidence under P. Function admission
   preserves identity and empty scoped flow; actual Call-demand transformations
   remain outside P. Record/tuple/variant ports preserve the same flow and choose
   existing structural children; they do not introduce a hidden lower-row write.
5. Mapped-row structural extrusion returns the existing row at equal target
   level, so it creates no extrusion parent. Parent-free intrusion settlement
   returns before compression/merging. Consequently no callback changes a
   representative or level, and no callback grows a direct-lower prefix.
6. The outer fresh-bound cursor waits for the active restoration before moving
   to the next captured record (`:5069–5087`). Within restoration, saved-count
   live reads and retained child returns match the inspected scan interpretation.
   The three DL/DU/EL/EU snapshot premises are therefore supplied under P.
7. Fresh transport attaches mapped original fibers before physical admission
   (`candidate_scheme.rs:4612–4638`; `candidate_context.rs:4278–4292`). Incoming
   replay resets old heads and bypasses ordinary dependency skipping, so the
   full ordered mapped fiber pair is actually generated here. This does not
   have the ordinary-merge issue R1.
8. All four Function children at `lib.rs:14804–14853` match the Lean table:
   argument and argument-effect are contravariant, result-effect and result are
   covariant. `:14955–14981` retains each distinct port and enqueues it before
   advancing its cursor. Completion passes typed Transport/Context/Dispatch,
   diagnostics and acknowledgement/return ownership. Memo use is guarded by
   the actual relation and current intrusion generation, not endpoint equality.

No omitted bound/row mutation under these explicit P hypotheses was found.
This accepts the bounded paper reasoning, not a formal Rust semantics proof.
Original physical duplicates deduplicated by capture and admission authentication
are still outside its record-level activation conclusion and remain in the
unchanged parent obligation.

The shifted-index example is established selected behavior from 2026-10-13,
consistent with suspension-contract section 4. It is neither new progress nor
a fresh solver counterexample, and requires no snapshot-index repair.

## 5. Disposition and stopped writes

After R1's documentary correction, this packet can be accepted as checked
finite scheduling/scan lemmas plus a bounded P-specialized source derivation.
It still cannot instantiate a saturated finite model table for every native
history. Mixed/shared FreshUse, merge/currentness and third-owner incidence,
contextual effects, later reuse, physical admission authentication and full
original source/Call witnesses retain their stated owners and OPEN status.

Reviewer resources: static source and hash/log inspection only; **zero Lean
invocations**, zero Cargo runs, zero native probes, no children and no Git
commands. Frozen producer logs were sufficient; no isolated cache or checker
was mutated. No source, production, shared status or import file was edited.
The sole write is this review handoff. Reviewer writes are **STOPPED** at this
receipt; parent owns adjudication and the one batched repair/delta review.

## 6. Primary repair and narrow delta acceptance

Date: 2026-10-26
Reviewer: same independent `/root/native_replay_review`
Final decision: **ACCEPT** for the stated finite lemmas and bounded paper
source derivation. This supersedes the initial REPAIR_REQUIRED disposition
above; the initial evidence and finding remain preserved.

The primary's paper-only revision has independently read-back SHA-256
`548777c8e252acbf94f8d6c084b8d366ba9e18aca874ee26d6fc03eafdd81fbc`.
The delta review read only section 3 and checked its two revised applicability
paragraphs against R1. The ordinary-append summary now explicitly requires
preserved pending/completed dispositions for work skipped by recorded heads or
dependency reuse. The merge paragraph correctly distinguishes visiting every
physical pair and generating incremental quadrants from enqueuing a new full
product. It explicitly leaves old work's disposition, currentness after the
generation change, third-owner incidence transport and later scheme reuse as
additional obligations. R1 is fully resolved without changing the Lean program
or smuggling a saturation/currentness conclusion into an established premise.

No new substantial issue occurs in this delta. Acceptance retains every scope
limit in sections 3–5 above: the abstract scheduler is not instantiated for
arbitrary native merge histories; original whole-native saturation/model,
complete Call and whole-source soundness remain OPEN. The prior Lean/native
and producer-receipt hashes and audits remain the frozen review inputs supplied
for this delta; no new checker run or independent re-audit is claimed.

Delta resources: one read/hash command, zero tests/checkers, no Git, no children.
Only this acceptance appendix was written. Reviewer writes are **STOPPED**.
