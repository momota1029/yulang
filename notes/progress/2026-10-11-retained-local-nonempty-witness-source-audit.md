# Parsed Local: smallest literal route to nonempty retained replay

Date: 2026-10-11
Status: source characterization followed by a passing focused parsed-source test and bounded regression review; no theorem closure or production suspension claim.
Producer: `/root/retained_local_witness_source_audit`, leaf.
Exclusive lease: this note only; frozen at handoff.
Baseline: `56a8dd529bf530549730a65ccccd06f821d27b3b`, branch supplied by the primary: `research/simple-sub-intrusion`. Source evidence uses the frozen worktree hashes below, including five concurrent uncommitted solver files.

## Objective, authority, and result

Find the smallest authentic parsed Local source path that can generate a nonempty native replay batch, enter Running, publish/deliver Ready, and leave restoration/Local cursors blocked until their completion gates. The producer used static producer-to-consumer tracing, comparing annotated and unannotated literal locals; primary later executed the focused test recorded below.

Authority is the user-approved [private candidate suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md), §3 (innermost ownership and completed-child advancement), §4 (saved opposite count and live lookup), §6 (route rollback/accounting), and §7 (distinguishing authentic lifecycle verification from synthetic adapter checks). Its recorded user decision is “承認して実装を進めて”. The accepted correction in [the retained source bridge](2026-10-11-retained-parent-handoff-source-bridge.md), “Objective, authority and frozen claim”, remains fixed: terminal acknowledgement consumes in F; Ready is the post-consumption barrier; delivery validates `consumed == index + 1` and does not acknowledge again.

Smallest source candidate found:

```yulang
my outer = { my local = 1; local }
```

This removes `:int` from the current parsed retained fixture. It needs one local declaration, one literal initializer, and one resolved local use; no ascription, formal annotation, application, effect declaration, or injected graph state. This is structural minimization within the inspected literal-local route, not a proof of global grammar/token minimality. Parsing this exact text and its actual retained trace have **not** been executed in this lane.

The decisive difference is that unannotated Install publishes the literal's own row C, which source generation constrains on both sides. `LocalAnnotation` publishes a new exposed row A with only a positive annotation lower bound; the initializer's negative bound stays on C. Moreover, the present parsed test stops after the first captured-bound restoration. Removing the annotation alone cannot fix that test's coverage: the first restoration of the unannotated C also has zero opposite products. The second captured bound is the decisive one.

## Exact source constructors and reachability premises

Locators refer to the frozen current bytes in `crates/yu-solver/src/`.

1. **Authentic front end.** Reuse `candidate_context_tests.rs:358–378`, `session_with_source`: `parse_file` with scanned header and empty syntax environment → `lower_module_with_local_source` with a real module/file identity and empty semantic imports → `ConstraintBatch::collect_candidate_mode(hir, true, true)` → `InferenceSession::try_new` → `start_candidate_graph`. This is an existing entrypoint, not a manually created Local/HIR/Graph object. The source preflight at `candidate_source.rs:82–110` has no annotation/operation/unresolved-name obstacle for this candidate, assuming ordinary local-name resolution succeeds.
2. **Levels and ordinary initializer.** Collection visits the outer body at level 1; Block schedules each initializer at child level 2 and Install at boundary 1 (`candidate_source.rs:255–264,288–309`). `initialize_candidate_source_levels` installs those component levels (`532–542`); collected metadata begins `non_generic=false` (`lib.rs:10030–10063`). Let C denote the actual literal Value component row. The literal constructor emits `IntPositive <: C` and `C <: IntNegative`, plus separate computation-effect facts (`candidate_source.rs:336–349`). These are actual source constraints, not assumed bounds.
3. **Retained physical and fiber evidence.** Source fact admission reaches the typed drain and candidate application. `apply_value_task` selects `candidate_apply_value` when the candidate graph is present (`lib.rs:13707–13714`); `candidate_apply_value` puts the first comparison in C's positive atom lane and the second in C's negative atom lane (`candidate_extrusion.rs:805–842`). Insertion calls `candidate_bound_origin_with_evidence` before physical publication (`406–466`); that calls `candidate_context_bound` (`candidate_effect.rs:341–350`). The latter constructs the relation/dependency and attaches its BoundKey fiber (`candidate_context.rs:2813–2854`). `attach` deduplicates by relation within a key and retains the head/list (`2408–2420`). Thus this route supplies both physical opposites and their replay fibers. Prior ordinary replay does not erase these fibers.
4. **Install preserves C.** Unannotated Work::Install emits `Action::Install` using the initializer endpoint (`candidate_source.rs:325–328`). The source executor calls `install_candidate_local` (`681`), which obtains that endpoint, requires a ValueRow, and stores `LocalScheme { root:C, boundary:1 }` (`candidate_scheme.rs:1316–1341`). Initializer computation effects are one-shot block effects outside this local value scheme (`candidate_source.rs:311–316`). No later source use/action has run yet.
5. **Real Local action.** The final name resolves to the already installed local and is outside an active initializer, so source collection emits `Action::Local { slot, occurrence, value, level:1 }` (`candidate_source.rs:369–390`). Execution dispatches `route_candidate_local` (`680`). `route_candidate_local_run` captures C at the stored boundary and prepares one FreshUse before retaining Local (`candidate_scheme.rs:1361–1382`). Capture classifies C local when `level(C)=2>1` and `!non_generic` (`303–325`). The leaf-only comparisons have no parent/copy row cycle or named-variable action that requires lowering/merging C; nevertheless the experiment must assert C's actual level/representative/metadata rather than inventing numeric row IDs.
6. **Captured bounds and one fresh identity.** C's exact positive atom lane is enumerated before its exact negative atom lane (`candidate_scheme.rs:595–617`). `Capture::bound` enumerates each fiber and retains its original `source_bound`, relation and evidence snapshot (`520–566`). Freshening creates one use origin and, for the local eligible C, one fresh row U at use level 1 (`982–1021`); remaps retain original dependencies. `begin_candidate_fresh_bound` maps the captured side/endpoints, transports its relation with the same use identity, and creates one bound restoration (`1221–1270`). Transport itself attaches the mapped fiber (`candidate_context.rs:3144–3154`), and physical restoration admission also records its bound fiber.

These facts establish a bounded constructional derivation under successful ordinary parsing/lowering/collection, allocation/accounting, and completion of the finite whole typed-stage helpers. They do not assume an arbitrary injected pair of replay fibers. They are source evidence about the inspected Rust artifact, not a universal semantic theorem or evidence of an executed trace.

## Discriminating retained trace and parent barriers

Keep source occurrence/cause, captured source BoundKeys, original fiber relations, U/use origin, each accepted emission, restoration B, replay R and ordered child ack `(R,i)`. Concrete row ordinals or equal RelationIds do not identify child occurrences.

Use the existing real source scheduler to advance to the first Local action, as in `candidate_context_tests.rs:4891–4902`, then `candidate_test_local_script(&[DriveOne])` to construct the Local once and admit its first captured bound. Follow with `candidate_test_retained_local_step(false)`; this helper owns each RetainedResume transaction and retains Local in its vector throughout child work (`candidate_scheme.rs:1467–1499`). It can construct the next restoration after the preceding cursor becomes None. Do not use `LocalScriptStep::Complete` for the decisive segment, since that adapter synchronously completes typed children.

Expected sequence, with explicit conditions:

| Stage | Source-owned state and discriminating observation |
| --- | --- |
| First bound | Restore `BoundKey(U,+,IntPositive)`. U is newly allocated and has no old negative bound, so saved `m=0`; completion returns its accepted emission and Local `next_bound` becomes 1. No replay child is expected. |
| Second bound | Restore `BoundKey(U,-,IntNegative)` after the first completion. The positive `IntPositive` bound/fiber remains, so saved opposite count is at least 1. On the literal-only route it is expected to be exactly 1; assert this in execution rather than assuming all maps/vector sizes. |
| Replay generation | Saved index 0 constructs task `Value(IntPositive,IntNegative)`, with lower input `BoundKey(U,+,IntPositive)` and upper input `BoundKey(U,-,IntNegative)` (`candidate_extrusion.rs:728–753`). `candidate_context_begin_replay(..., true)` resets prior heads to `(None,None)`; both head lists are nonempty, and the Cartesian-product loop appends at least one child even if its dependency was previously admitted (`candidate_context.rs:2927–2981`). This is the direct nonempty-generation premise. Identity context is not an empty child batch. |
| Select → Running | Idle requires queued=consumed, takes `children[consumed]`, starts one F with exact ack `(R,i)`, binds F.destination and publishes Running (`candidate_context.rs:3016–3033`; `lib.rs:12101–12114`). The helper returns More; B.next_opposite and Local.next_bound remain unchanged. |
| Running steps | The driver checks matching operation/index/destination/occurrence/cause and resumes F, never calling the constructor again (`candidate_context.rs:3035–3043`). Transport/Context/Dispatch drain actual queued work; diagnostics precede acknowledgement (`lib.rs:12170–12276`). Existing completed atom memo may shorten Dispatch; it does not bypass the exact queue ack or parent slot. |
| Final ack / Ready | Terminal consumes the exact ack, then sets ReturnReady; a later terminal step publishes Ready with the exact ack/F index/receipt before removing F (`lib.rs:12546–12597`). Running returns More even on that step, so the retained transaction commits Ready with B.next_opposite and Local.next_bound unchanged. Here consumed=queued=i+1; re-consumption would be wrong. |
| Deliver / restoration | A subsequent call validates Ready and clears only its barrier; no second ack. `candidate_context_replay_returned` requires Idle+retired (`3105–3107`). Only then may restoration clear R and increment its opposite cursor (`candidate_extrusion.rs:716–727`, `candidate_context.rs:1815–1821`). Delivery itself still returns None to Local. |
| Local completion | A later B step at n=m retires restoration and returns the same accepted emission (`candidate_extrusion.rs:709–711`). Only Some clears Local.restoration and increments Local.next_bound (`candidate_scheme.rs:1481–1484`). Finish the remaining Local/source route separately; no second fresh use or duplicate emission is justified. |

Assert that Running and Ready were actually seen and `children.len()>0`, with exact U/use origin and per-restoration emission retained. At each failed retained step (`fail_after=true`), compare the existing Local cursor, exact B/R, F/destination/acks/stage, Q and their named capacities, diagnostic projection, use counter and emission census with the checkpoint. This is a proposed focused experiment; **none of these assertions were executed by this leaf**. A failure to reach the second restoration, a missing head fiber, changed local eligibility, unowned queued work, or Ready bypass falsifies this constructional handoff at its exact owner. Record the first such state, not merely eventual Local completion.

## Why the existing annotated fixture does not establish this witness

`construct_candidate_local_annotation` checks initializer C against the negative annotation, then allocates a fresh exposed A and admits the positive annotation into A (`candidate_effect.rs:1051–1071`). Install uses A. For `:int`, A has `IntPositive` as lower but has no source construction giving it `IntNegative` as upper before the Local action. Capture starts at A and reaches only its bound leaves; it does not follow source constraint provenance backwards into the checked initializer C as a physical row bound. The existing fixture's first restoration can consequently finish with m=0, without any replay generation.

The loop in `parsed_local_retained_child_steps_restore_parent_cursor_after_failure` (`candidate_context_tests.rs:4905–4929`) exits as soon as that first restoration clears and one Local bound cursor increments. It neither traverses all captured bounds nor asserts nonempty H/Running/Ready. The synthetic two equal-relation child fixture (`4801–4870`) exercises the barrier but cannot establish this source generation. This note identifies both source-shape and caller-control reasons for the coverage gap; it does not call the existing rollback assertions invalid.

## Evidence independence, coverage, and limits

This audit reads authentic parser/HIR/constraint producers and implementation consumers rather than defining transition rules in a checker. It does not supply an independent semantic oracle: all derived runtime expectations share the same inspected Rust implementation and accepted contract. The proposed comparison to the annotated fixture discriminates the root constructor; it cannot prove source semantics, soundness, principality, lawful arbitrary replay provenance, semantic journal correctness, or full rollback arithmetic.

Static coverage: one literal-local route and the existing annotated/control adapters; actual level, bound/fiber, fresh transport, native incoming replay, typed terminal return and parent guards. No random seed/range or enumeration was used. No mutation was executed. The proposed annotation deletion and continuation past the first bound are a source/control contrast, not new language meaning.

Omitted: real certified component, late unsupported Function/swap incidence, lifecycle dirty withdrawal/recomputation, multiple remaining products, initially published SCC member, external canonicalization during suspension, repeated unchanged-wait stability, full §7 recovery, general nested scheduler, production certificate creation, Call/effect hygiene, soundness/principality and cutover. This source has one product and identity context, so even a passing execution would not satisfy the full §7 regression. No globally minimal witness or impossibility result is claimed.

The primary assigned the focused test below using this exact unannotated source and existing retained helper. Authentic §7/lifecycle and the original parent theorem remain OPEN.

## Primary execution and independent regression review

The test `parsed_literal_local_retains_nonempty_child_until_exact_once_receipt_delivery`
was added to `candidate_context_tests.rs`. It parses the source above through
the normal entrypoint, completes the first zero-opposite restoration, then
observes the second restoration with one opposite and a nonempty native replay.
It checks Running and Ready for each child, exact acknowledgement/index,
`consumed == index + 1` before delivery, blocked parent cursors, successful
delivery without another acknowledgement, retained fresh-use/emission identity,
and rollback of the retained child step.

Focused verification passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 timeout 120s cargo test -p yu-solver --features shadow-apply-candidate --offline --jobs=1 parsed_literal_local_retains_nonempty_child_until_exact_once_receipt_delivery -- --test-threads=1
```

Result: 1 passed, 0 failed; the filtered integration targets ran zero tests.
The compile emitted no package warnings. A regression-auditor found no
blocking issue and noted that the progress loop should be bounded and Ready
failure should compare the full route snapshot; both were repaired and the
focused test passed again. The test checks exact ack/index and successful
delivery, but does not assert an independently reconstructed receipt payload.
A temporary assertion that `completion.transitions > 0` failed; that stronger
claim was removed because this source route can legitimately produce a zero
transition receipt. The test does not claim that payload value.

This execution establishes one authentic source path through the retained
helper, not a production suspension lifecycle. It does not exercise certified
support invalidation, external mutation permission, withdrawal/recomputation,
SCC publication, full §7 recovery, or arbitrary parent-theorem histories.

## Frozen dependencies and checks

SHA-256 values below are the source audit's freeze-time inputs. HEAD advanced concurrently from the pinned baseline to `742624c45728a74798fa8b5b85fb1c136a651f0c`; the inspected solver worktree hashes in the table remained unchanged at that audit freeze. The governing contract and source bridge were also unchanged. Later test edits are recorded below and do not change the source-constructor analysis.

| Path | SHA-256 at source-audit freeze |
| --- | --- |
| `notes/design/2026-10-11-private-candidate-suspension-contract.md` | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| `notes/progress/2026-10-11-retained-parent-handoff-source-bridge.md` | `538ccff23338c0c55cdc6bc4cda535b50f55644e342d9fe925ae8c63dcc0a44d` |
| `crates/yu-solver/src/candidate_context.rs` | `e8c7547260b20c086daca0300611eb5da972b5c56b1cb109491bb32833adf896` |
| `crates/yu-solver/src/candidate_context_tests.rs` | `397eade3d5a8aae946dd6929aa75cd2424d7b0a0f5067b6cb0e7428d0384a1b9` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `a76979f01feaf76ffa351625b0443802fca3e6e2b0288b55e274d7538ae22ead` |
| `crates/yu-solver/src/candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| `crates/yu-solver/src/lib.rs` | `7ace990203b77f1b8aad185e8cdbb2cdac90b967e38479774b7081e45c9429ee` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |

For the five concurrent files in the table, the baseline hashes, in the same order context/tests/extrusion/scheme/lib, are `7d758c4177dad59a6c7c3422e68955905db12441b06816f4206bac9960fba416`, `936097b62e3133a7d87f85a850c6e7c755970ece0dee6f95fc1a26dcae3ec137`, `1fcfd729cc1a2afb080efc6ceeb424146bead7aba0142313b3a12d4ee120fade`, `ad3208eea2b348f1e87f1c6958b1d13b2d625ba38a42f5eac22959edd371a825`, and `9a32a53d75892521f28d9cce2955244f99ff5f27fc0a22364e656aedfa540e54`. These differences were already present at lane entry and are preserved.

Checks run by the source-audit producer: read-only `git rev-parse HEAD`, `git status --short`, narrowly scoped `git diff --stat`; bounded `rg`/`sed` source/contract/fixture reads; `sha256sum` worktree inputs and `git show 56a8dd529:<path> | sha256sum` for baseline comparison; leased-note whitespace/scope inspection. One search for a nonexistent `candidate_signature.rs` returned no file; the signature implementation was found and read in `candidate_effect.rs`. No build/test/run/format/Git mutation occurred in that lane. One leaf, short read/hash shell processes, zero Cargo/heavy processes and zero samples. Static reads remained within the assigned 30-minute ceiling; actual elapsed CPU/RSS were not measured. Primary execution and review are recorded above.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-retained-local-nonempty-witness-source-audit.md`.
- Baseline SHA: `56a8dd529bf530549730a65ccccd06f821d27b3b`; exact worktree and changed-from-baseline dependency hashes are above. No dependency was changed by this leaf; observed worktree inputs remained stable across the audit.
- Claim/review status: the static source characterization now has one focused parsed-source execution and bounded regression review. No theorem or §7 closure.
- Checks already run: bounded static producer/consumer/control reads, exact input/baseline hashes and note scope/whitespace inspection; primary's focused test command/result are recorded above.
- Proposed one-line research-checkpoint commit message: `research: identify unannotated literal Local for nonempty retained replay`.
- Shared-record deltas intentionally left to primary/curator: record this source candidate and the first-bound early-exit gap; preserve original parent proof and authentic §7/lifecycle gates OPEN. No design/index/theory/question/authority record changed.

The producer's write lease stopped before review, as assigned. The primary later
added the execution and review record above. Current test-source SHA-256 after
the addition is `5589562bfa4de07f8324f61a98c04cbebc898c28bfc2796a1f81a84d985aca39`;
the historical freeze-time hash remains in the dependency table.
