# R167 native successful execution proof handoff

Sprint: EFFECT-PERMISSION-NATIVE-EXECUTION/20261102-R167. Assignment: R167-PROOF.
Revision: 1. Baseline supplied by primary: `f5af010783f8bd7c748b2e2838078a08283be496`.
Author/worker: `/root/r167_native_scope_execution_proof`; requested Sol/high;
effective route metadata UNKNOWN. No descendants or coauthors.
Claim class: **checker-accepted finite source-trace mathematics**. Independent
Lean review and compiler/source review are **NOT_RUN by this producer**.
Original effect hygiene, original A/B, principality, termination and production
remain OPEN. No semantic or production authority is claimed.

## Original parent, corrections and exact scope

Read `notes/design/2026-10-15-compose-scoped-effect-release.md`, “Direct decision”
and “Scope of the operation”, and the original parent in
`notes/theory/2026-10-15-compose-scoped-release-construction.md` §§1–2.
The parent quantifies over compatible providers, complete Call witnesses, one
original shared scoped assignment and every emitted contribution. It requires
release of the selected original protection also inside the output effect,
including `compose id g`, while preserving contribution membership, attribution,
grants and independent protections. The finite normal form in §2 is reused;
the research construction does not supply new semantic authority.

The current annotation corrections were read in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2:
permission, actual inflow and residual remain distinct; actual Catch performs
handling; unknown variables and the same provider/assignment/correlated Function
obligations remain. Top-level inference principles §§1–5 retain ordinary
inference and require only safe abnormal exits. This packet changes none of
those policies or any accepted language feature.

The immediate parent is R166
`YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent`,
which retains encoded-field equality plus `Generated`. R167 constructs local
source traces and derives operation equality and `Generated` afterward.
R165 `YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent`
is then applied for **every initial State**, including duplicate/unsorted lists.
The empty initial state used by `candidate_context.rs::evaluate_observation`
(lines 3280–3284) is not imposed on the theorem.

## Source mapping and construction

All authored declarations are under `YulangClosure.NativeScopeExecutionR167`.

| Native source phase | Checked construction/application |
| --- | --- |
| identity, stamp_input, protect_body, release | `NativeTrace` constructor rules retain raw UInt32 fields. `nativeTrace_successful` derives their R166 encodings. Release uses a false keep bit and empty guard, retained by `emit_release_retained`; `emit_neutral_omitted` drops only true-keep/empty-guard entries. |
| ordered union | `MergeTrace` records left-smaller, right-smaller, equal-once and exhausted-suffix branches. `mergeTrace_result` derives exact `unionCursor` output. |
| then scope cursor | `ScopeRun` carries actual remaining records, reads matching heads, uses identity defaults for absent entries, and advances exactly left/right/both. `PendingAgreement`, `agreement_advance_left/right` and `scopeRun_trace` derive preservation of original keyed reads at each transition from operand ordering. `ScopeTrace` is only the intermediate keyed-read trace. |
| then local fields | `sourceEntry` transcribes second.keep && first.keep, conditional retention of the first guard, first-stamp binary-search filtering of the second guard and ordered guard union. `sourceEntry_model` derives equality with `composeEntryModel` from the sorted-slice membership contract. `thenTrace_result` derives full result equality with `thenModel`; ordering is obtained from earlier successful operations. |
| input support collection | R166 `inputSupport` is normalization of stamped IDs followed by all guards. `SortContract`/`DedupContract`, `sortedCopy_contract` and uniqueness theorems justify replacing a successful std sort/dedup output with this canonical list. Each stamped/guard lookup belongs to this support by R166 inputSupport_stamp/inputSupport_guard. |
| FnMut samples | `Samples` retains each input ID, returned image and arbitrary before/after state. `RemapSampling` threads one shared state from all input_map calls into all scope_map calls. The two call relations may interact through that state; neither is a pure map. Keys occur in source order: distinct sorted input support first, original ordered scope keys second. |
| sampled lookup | `table` is derived from recorded key/image pairs, with identity fallback outside finite support. `samples_keys`, `samples_values` and `table_pair` establish exact on-support values. `BinarySearchContract`, `binarySearch_present` and `sample_index_lookup` show that any valid matching binary-search index selects the same sampled image; there is no second closure invocation. |
| remap outputs | `sampledEntries` consumes recorded scope output images directly, in call order, while reusing the input table in stamped/guard lanes. `sampledEntries_table` derives its equality with the R166 finite map. `RemapSourceReturn` records actual sorted stamped/scope outputs and the two collision checks under std mathematical contracts. No canonical final output equality is an execution premise. |
| sort/windows checks | `EntrySortContract` is sorted keys plus permutation. `entrySortContract_windows` derives exact Nodup equivalence of the sorted windows check; `entrySortContract_success` then derives exact sorted record output, including payloads, on success. Input collision rejection uses normalized image length, scope collision rejection uses sorted adjacent equality. `remapTrace_result` derives `remapModel = some result`; `remapTrace_injective` derives finite private-support injection. |
| reserve/overflow/success boundary | `Gate`, `finish`, `Return` and `successful_return_boundary` make abstract reserve/capacity failure exits explicit: success requires all recorded gates passed and a successful body return. These are mathematical outcomes, not allocation/runtime receipts. Failed executions and closure effects before a later error are not execution traces claimed by `NativeTrace`. |
| parent application | `successful_generated` and `nativeTrace_generated` derive R166 Generated by induction over successful calls, using derived then/remap equalities. `nativeTrace_evaluate_equivalent` applies R166/R165 with arbitrary initial state. `thenTrace_denotation` also applies the full ordered composition equation. |

The std boundary is explicit: sort is a sorted permutation; sorted adjacent
dedup preserves membership and gives strictly ordered IDs; windows rejects equal
adjacent sorted scope keys; binary search either returns a matching in-bounds
index or reports absence. These contracts are not proofs of std machine code.
Nat intermediate traces may overapproximate the UInt32 range; the native root
retains raw UInt32 fields, and no arbitrary Nat trace is claimed to have run.

## Parent application and precise remaining premise

For any native field value `native`, `NativeTrace native` now derives
`Generated (encodeFields native)` and the R165 evaluator equivalence for every
initial state. Neither final encoded-field equality nor Generated is supplied
as an execution premise. Then operand ordering and remap representation follow
from the preceding successful trace, rather than strengthened external hypotheses.

First remaining source/native premise and owner: **Luna/source correspondence
and the fresh compiler reviewer** must validate that each successful actual
private Rust API path and its std calls instantiate this exact source-trace
abstraction. The source map is frozen, but this leaf does not certify it, execute
Rust, mechanize the Rust language or produce std/runtime receipts. The new
mathematics removes final R166 output equality as an assumed trace property;
it does not turn an unvalidated actual-program/trace correspondence into a
kernel theorem.

The original parent still requires authentic original contribution/route/scope
attribution, complete Call/source witness, external-state/FreshUse shared
injection, actual Catch consumption and the remaining whole effect hygiene
premises. Finite private-support injection does not authenticate external state.
No source language was reduced and no separate per-port witness substituted.
Source records, optional/method/effect cases outside this finite coordinate
kernel remain obligations of their existing owners. The pending typed-Union
question is not consumed.

Mutual TODO R167-ACTUAL-TRACE-1: owner Luna/source review; exact inputs below;
validate the branch/stdlib abstraction for every successful operation. A falsifier
is a successful native operation whose encoded local transition, call order,
lookup image or result differs from the defined trace. Independent review and
production remain separate gates.

## Actual checks and material failures

Both leased paths were absent before construction (`ls`, exit 2). The primary
confirmed sole Lean verification/cache ownership. Read-only `elan which lake`
resolved the installed native distribution (exit 0). Actual versions: Lake
`5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release; both commands exit 0.
Pin, lakefile and manifest were read; no external packages.

Incremental command, repeatedly repaired against actual diagnostics:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 YulangClosure/NativeScopeExecutionR167.lean`
from `notes/theory/lean`. Final direct invocation exit 0, no own warnings.
Focused build/checker commands and all printed types/axiom results are retained
verbatim below. The wrapped checker command exited 0, shell tool wall 3.003s,
covering all **41 authored theorem declarations** (including helper theorems).
Axiom groups: 23 use `[propext, Quot.sound]`; 10 use
`[propext, Classical.choice, Quot.sound]`; 5 use `[propext]`; 3 use no axioms.
No other axioms occur. R165 unchanged deprecation/linter warnings were replayed;
R167 has no own warnings. No full/default integration build was run by this leaf.

Material failed attempts, all repaired:

- Initial file creation used a repository-relative path from the Lean cwd; shell
  reported `No such file or directory`, and focused build reported the missing
  module (exit 1). No file was created there; subsequent edits used the exact
  leased path.
- First actual build exit 1 exposed well-founded union reduction, a consumed
  prefix identifier parsed as a keyword, structure injection projection syntax,
  and data fields in Prop-valued sampling records. Repairs used explicit union
  equations, `consumed`, direct congruence and Type-valued sampling records.
- Remap proof initially failed `split` on a let expression; `dsimp only` exposed
  the actual check. The Successful.then induction needed quoted constructor
  syntax. Binary-search negation needed explicit parentheses due Bool coercion
  precedence. Raw-record trace constructors needed explicit selected-key arguments.
- Entry sorting proof required unfolding `sortEntries`, and the key-uniqueness
  induction needed separate head/tail membership names. Success-boundary proof
  used explicit membership cases after simp could not retain the gate predicate.
- One mistyped native executable path ending `leanprover--lean4.35.0/bin/lake`
  returned `No such file or directory`, exit 127. The installed pinned executable
  was used for every successful check and for the final checker.

Final source search over R167, R166, R165 and NativeScopeTransformer found no
`sorry`, `admit`, project `axiom`, `skipKernelTC`, `native_decide` or
`implemented_by` matches (`rg`, exit 1 = no matches). All contract-pinned hashes
were rechecked unchanged after construction. Final audit contains exactly 41
BEGIN/END pairs. The checker temporary directory
`/tmp/yulang-lean-audit-j9ph_ovb` was removed; explicit absence check exit 0.

Pinned local Lean sources consulted: Init/Data/List/Perm.lean,
Pairwise.lean, Sort/Lemmas.lean, Zip.lean, Find.lean and Lemmas.lean beneath the
verified 4.35.0 distribution. No network/dependency installation was used.

## Writes, resources and stop receipt

Authored writes are exactly the module and this handoff. No Rust, tests,
expected outputs, root imports, task/current/status/index, rules, configuration,
manifests, lockfiles or Git state changed. No Git commands, Cargo, Rust execution,
tests or benchmarks were run. No descendants, nested CLI, scheduling or contacts.

Existing `.lake` outputs only: `build/ir/YulangClosure/NativeScopeExecutionR167`
with `.c`, `.c.hash`, `.setup.json`, and `build/lib/lean/YulangClosure/NativeScopeExecutionR167`
with `.olean`, `.olean.hash`, `.ilean`, `.ilean.hash`, `.trace`. No new environment,
cache root, target definition or persistent scratch. Checker temporary scratch
was self-removed. Exact total construction CPU/wall were not separately measured;
primary launch timing owns the 2400-second cap. Lean ran serially with `-j1
-M1024`; checker total timeout 120 seconds.

Worker disposition: **WRITES_STOPPED** after this frozen revision; no running
subprocesses or descendants. Primary owns subsequent independent review,
adjudication, records and Git integration. This is a producer handoff, not
self-certification.

## Frozen inputs and artifact hashes

- `tasks/agent-loop/sprints/effect-permission-native-execution-r167.md`: `ce025f3a5315a054b2c10ca7edf68c674faa4b70162ad4a587b5aad41f179779`.
- `tasks/agent-loop/inbox/effect-permission-native-execution-r167-source.md`: `02636ae9141342aaa3ac94fce08e9dcebf999ae6e1c1ff0f4697e4fedbcdff77`.
- `crates/yu-solver/src/candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `crates/yu-solver/src/candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`: `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- `notes/theory/lean/YulangClosure/NativeScopeRepresentationR166.lean`: `bee9bc1d052d05cc39e43da8614f52d09eac4c117d58b040e4eab3334be25e7f`.
- `tasks/agent-loop/sprints/effect-permission-native-scope-evaluate-r165.md`: `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.
- `tasks/agent-loop/sprints/effect-permission-native-scope-representation-r166.md`: `85fb9acc51d8e2ce470fc28b4d9054cdea71ecbf28a9edf6f7a751f1201c1037`.
- `tasks/agent-loop/inbox/effect-permission-scope-representation-r166-proof.md`: `2433e4ece6fb5de9a728d57494b9be09ca26e490cc7da5d0873ec9bb4d723d37`.
- `tasks/agent-loop/inbox/effect-permission-scope-representation-r166-source.md`: `a8bbdebf22c657f26365104f68d62089dbb312967c69b757b186137d591e54e9`.
- `notes/theory/lean/YulangClosure/NativeScopeExecutionR167.lean`: `fb4d6802089eb256c0a5aac5a7ba0d7f5124f240e4ec0e02422d81dd158ff55d`.
- `notes/design/2026-10-15-compose-scoped-effect-release.md`: `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`.
- `notes/theory/2026-10-15-compose-scoped-release-construction.md`: `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e`.
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.

## Authored theorem census

- `YulangClosure.NativeScopeExecutionR167.mergeTrace_result`.
- `YulangClosure.NativeScopeExecutionR167.sortIds_contract`.
- `YulangClosure.NativeScopeExecutionR167.sortContract_unique`.
- `YulangClosure.NativeScopeExecutionR167.dedupContract_unique`.
- `YulangClosure.NativeScopeExecutionR167.sortedCopy_contract`.
- `YulangClosure.NativeScopeExecutionR167.sortEntries_contract`.
- `YulangClosure.NativeScopeExecutionR167.unique_key`.
- `YulangClosure.NativeScopeExecutionR167.entrySortContract_windows`.
- `YulangClosure.NativeScopeExecutionR167.entrySortContract_success`.
- `YulangClosure.NativeScopeExecutionR167.emit_eq_encode`.
- `YulangClosure.NativeScopeExecutionR167.emit_release_retained`.
- `YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted`.
- `YulangClosure.NativeScopeExecutionR167.sourceEntry_model`.
- `YulangClosure.NativeScopeExecutionR167.scopeTrace_result`.
- `YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed`.
- `YulangClosure.NativeScopeExecutionR167.entryAt_selected_head`.
- `YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read`.
- `YulangClosure.NativeScopeExecutionR167.before_head_absent`.
- `YulangClosure.NativeScopeExecutionR167.agreement_advance_left`.
- `YulangClosure.NativeScopeExecutionR167.agreement_advance_right`.
- `YulangClosure.NativeScopeExecutionR167.scopeRun_trace`.
- `YulangClosure.NativeScopeExecutionR167.thenTrace_result`.
- `YulangClosure.NativeScopeExecutionR167.samples_keys`.
- `YulangClosure.NativeScopeExecutionR167.table_pair`.
- `YulangClosure.NativeScopeExecutionR167.samples_values`.
- `YulangClosure.NativeScopeExecutionR167.sample_index_lookup`.
- `YulangClosure.NativeScopeExecutionR167.binarySearch_present`.
- `YulangClosure.NativeScopeExecutionR167.successful_return_boundary`.
- `YulangClosure.NativeScopeExecutionR167.sampledEntries_table`.
- `YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result`.
- `YulangClosure.NativeScopeExecutionR167.remapTrace_result`.
- `YulangClosure.NativeScopeExecutionR167.remapTrace_injective`.
- `YulangClosure.NativeScopeExecutionR167.input_collision_rejected`.
- `YulangClosure.NativeScopeExecutionR167.scope_collision_rejected`.
- `YulangClosure.NativeScopeExecutionR167.successful_generated`.
- `YulangClosure.NativeScopeExecutionR167.successful_representation`.
- `YulangClosure.NativeScopeExecutionR167.nativeTrace_successful`.
- `YulangClosure.NativeScopeExecutionR167.nativeTrace_generated`.
- `YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent`.
- `YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent`.
- `YulangClosure.NativeScopeExecutionR167.thenTrace_denotation`.

## Complete focused checker receipt

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.NativeScopeExecutionR167
⚠ [3/5] Replayed YulangClosure.NativeScopeEvaluateRefinementR165
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:143:44: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:147:46: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:147:58: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:151:46: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:151:58: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:188:36: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:196:38: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:196:50: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:202:38: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:202:50: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:194:47: This simp argument is unused:
  or_comm

Hint: Omit it from the simp argument list.
  [apply] simp only [or_assoc, or_left_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:201:59: This simp argument is unused:
  or_comm

Hint: Omit it from the simp argument list.
  [apply] simp [List.mem_cons, or_assoc, or_left_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:209:20: This simp argument is unused:
  List.mem_cons

Hint: Omit it from the simp argument list.
  [apply] simp [or_assoc, or_left_comm, or_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:209:59: This simp argument is unused:
  or_comm

Hint: Omit it from the simp argument list.
  [apply] simp [List.mem_cons, or_assoc, or_left_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:219:33: This simp argument is unused:
  Bool.and_eq_true

Hint: Omit it from the simp argument list.
  [apply] simp [active, Bool.or_eq_true]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:364:36: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:376:38: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:376:50: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:389:38: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:389:50: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:389:50: This simp argument is unused:
  if_neg hba

Hint: Omit it from the simp argument list.
  [apply] simp only [unionCursor, if_neg hab, List.pairwise_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:441:41: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:458:45: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:458:57: `if_pos` has been deprecated: Use `ite_eq_left` instead

Hint: Replace the deprecated name:
  i̵f̵_̵p̵o̵s̵i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:478:45: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:478:57: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:422:62: This simp argument is unused:
  List.nil_append

Hint: Omit it from the simp argument list.
  [apply] simp only [protectionCursor, activeNow, ite_true, List.singleton_append, List.pairwise_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/NativeScopeEvaluateRefinementR165.lean:478:57: This simp argument is unused:
  if_neg hsa

Hint: Omit it from the simp argument list.
  [apply] simp only [protectionCursor, if_neg has, activeNow, ite_true, List.singleton_append, List.pairwise_cons]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
✔ [5/5] Built YulangClosure.NativeScopeExecutionR167 (1.1s)
Build completed successfully (5 jobs).
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-j9ph_ovb /tmp/yulang-lean-audit-j9ph_ovb/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.mergeTrace_result
@YulangClosure.NativeScopeExecutionR167.mergeTrace_result : ∀ {xs ys out : List Nat},
  YulangClosure.NativeScopeExecutionR167.MergeTrace xs ys out →
    out = YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor xs ys
'YulangClosure.NativeScopeExecutionR167.mergeTrace_result' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.mergeTrace_result
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sortIds_contract
YulangClosure.NativeScopeExecutionR167.sortIds_contract : ∀ (ids : List Nat),
  YulangClosure.NativeScopeExecutionR167.SortContract ids (YulangClosure.NativeScopeRepresentationR166.sortIds ids)
'YulangClosure.NativeScopeExecutionR167.sortIds_contract' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sortIds_contract
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sortContract_unique
@YulangClosure.NativeScopeExecutionR167.sortContract_unique : ∀ {ids output : List Nat},
  YulangClosure.NativeScopeExecutionR167.SortContract ids output →
    output = YulangClosure.NativeScopeRepresentationR166.sortIds ids
'YulangClosure.NativeScopeExecutionR167.sortContract_unique' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sortContract_unique
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.dedupContract_unique
@YulangClosure.NativeScopeExecutionR167.dedupContract_unique : ∀ {ids output : List Nat},
  YulangClosure.NativeScopeExecutionR167.DedupContract ids output →
    output = YulangClosure.NativeScopeEvaluateRefinementR165.normalize ids
'YulangClosure.NativeScopeExecutionR167.dedupContract_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.dedupContract_unique
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sortedCopy_contract
@YulangClosure.NativeScopeExecutionR167.sortedCopy_contract : ∀ {ids sorted output : List Nat},
  YulangClosure.NativeScopeExecutionR167.SortContract ids sorted →
    YulangClosure.NativeScopeExecutionR167.DedupContract sorted output →
      output = YulangClosure.NativeScopeEvaluateRefinementR165.normalize ids
'YulangClosure.NativeScopeExecutionR167.sortedCopy_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sortedCopy_contract
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sortEntries_contract
YulangClosure.NativeScopeExecutionR167.sortEntries_contract : ∀
  (entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  YulangClosure.NativeScopeExecutionR167.EntrySortContract entries
    (YulangClosure.NativeScopeRepresentationR166.sortEntries entries)
'YulangClosure.NativeScopeExecutionR167.sortEntries_contract' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sortEntries_contract
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.unique_key
YulangClosure.NativeScopeExecutionR167.unique_key : ∀
  (entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  (YulangClosure.NativeScopeTransformer.keys entries).Nodup →
    ∀ (a b : Nat × YulangClosure.NativeScopeTransformer.Entry), a ∈ entries → b ∈ entries → a.fst = b.fst → a = b
'YulangClosure.NativeScopeExecutionR167.unique_key' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.unique_key
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.entrySortContract_windows
@YulangClosure.NativeScopeExecutionR167.entrySortContract_windows : ∀
  {entries output : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.EntrySortContract entries output →
    (YulangClosure.NativeScopeRepresentationR166.adjacentDistinct (YulangClosure.NativeScopeTransformer.keys output) =
        Bool.true ↔
      (YulangClosure.NativeScopeTransformer.keys entries).Nodup)
'YulangClosure.NativeScopeExecutionR167.entrySortContract_windows' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.entrySortContract_windows
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.entrySortContract_success
@YulangClosure.NativeScopeExecutionR167.entrySortContract_success : ∀
  {entries output : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.EntrySortContract entries output →
    YulangClosure.NativeScopeRepresentationR166.adjacentDistinct (YulangClosure.NativeScopeTransformer.keys output) =
        Bool.true →
      output = YulangClosure.NativeScopeRepresentationR166.sortEntries entries
'YulangClosure.NativeScopeExecutionR167.entrySortContract_success' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.entrySortContract_success
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.emit_eq_encode
YulangClosure.NativeScopeExecutionR167.emit_eq_encode : ∀ (scope : Nat)
  (entry : YulangClosure.NativeScopeTransformer.Entry),
  YulangClosure.NativeScopeExecutionR167.emit scope entry =
    YulangClosure.NativeScopeTransformer.encode [scope] fun x => entry
'YulangClosure.NativeScopeExecutionR167.emit_eq_encode' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.emit_eq_encode
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.emit_release_retained
YulangClosure.NativeScopeExecutionR167.emit_release_retained : ∀ (scope : Nat),
  YulangClosure.NativeScopeExecutionR167.emit scope { keep := Bool.false } = [(scope, { keep := Bool.false })]
'YulangClosure.NativeScopeExecutionR167.emit_release_retained' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.emit_release_retained
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted
YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted : ∀ (scope : Nat),
  YulangClosure.NativeScopeExecutionR167.emit scope YulangClosure.NativeScopeTransformer.identityEntry = []
'YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sourceEntry_model
YulangClosure.NativeScopeExecutionR167.sourceEntry_model : ∀ (first second : YulangClosure.NativeScopeTransformer.Entry)
  (stamps : List Nat),
  List.Pairwise (fun x1 x2 => x1 < x2) stamps →
    YulangClosure.NativeScopeExecutionR167.sourceEntry first second stamps =
      YulangClosure.NativeScopeRepresentationR166.composeEntryModel first second stamps
'YulangClosure.NativeScopeExecutionR167.sourceEntry_model' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sourceEntry_model
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.scopeTrace_result
@YulangClosure.NativeScopeExecutionR167.scopeTrace_result : ∀
  {first second : YulangClosure.NativeScopeTransformer.Transformer} {xs ys : List Nat}
  {out : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.ScopeTrace first second xs ys out →
    List.Pairwise (fun x1 x2 => x1 < x2) first.stamped →
      out =
        YulangClosure.NativeScopeTransformer.encode (YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor xs ys)
          fun s =>
          YulangClosure.NativeScopeRepresentationR166.composeEntryModel (first.entry s) (second.entry s) first.stamped
'YulangClosure.NativeScopeExecutionR167.scopeTrace_result' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.scopeTrace_result
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed
YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed : ∀
  (consumed suffix : List (Nat × YulangClosure.NativeScopeTransformer.Entry)) (scope : Nat),
  (∀ (pair : Nat × YulangClosure.NativeScopeTransformer.Entry), pair ∈ consumed → pair.fst < scope) →
    YulangClosure.NativeScopeTransformer.entryAt (consumed ++ suffix) scope =
      YulangClosure.NativeScopeTransformer.entryAt suffix scope
'YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.entryAt_selected_head
YulangClosure.NativeScopeExecutionR167.entryAt_selected_head : ∀
  (consumed : List (Nat × YulangClosure.NativeScopeTransformer.Entry)) (scope : Nat)
  (entry : YulangClosure.NativeScopeTransformer.Entry) (rest : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  (∀ (pair : Nat × YulangClosure.NativeScopeTransformer.Entry), pair ∈ consumed → pair.fst < scope) →
    YulangClosure.NativeScopeTransformer.entryAt (consumed ++ (scope, entry) :: rest) scope = entry
'YulangClosure.NativeScopeExecutionR167.entryAt_selected_head' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.entryAt_selected_head
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read
YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read : ∀
  (consumed pending : List (Nat × YulangClosure.NativeScopeTransformer.Entry)) (scope : Nat),
  (∀ (pair : Nat × YulangClosure.NativeScopeTransformer.Entry), pair ∈ consumed → pair.fst < scope) →
    ∀ (ordered : List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys pending))
      (lower : ∀ (pair : Nat × YulangClosure.NativeScopeTransformer.Entry), pair ∈ pending → scope ≤ pair.fst),
      YulangClosure.NativeScopeTransformer.entryAt (consumed ++ pending) scope =
        match pending, ordered, lower with
        | [], ordered, lower => YulangClosure.NativeScopeTransformer.identityEntry
        | (key, entry) :: tail, ordered, lower =>
          if key = scope then entry else YulangClosure.NativeScopeTransformer.identityEntry
'YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.before_head_absent
YulangClosure.NativeScopeExecutionR167.before_head_absent : ∀ (key head : Nat)
  (entry : YulangClosure.NativeScopeTransformer.Entry) (rest : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  key < head →
    List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys ((head, entry) :: rest)) →
      ¬key ∈ YulangClosure.NativeScopeTransformer.keys ((head, entry) :: rest)
'YulangClosure.NativeScopeExecutionR167.before_head_absent' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.before_head_absent
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.agreement_advance_left
@YulangClosure.NativeScopeExecutionR167.agreement_advance_left : ∀
  {first second : YulangClosure.NativeScopeTransformer.Transformer} {x : Nat}
  {entry : YulangClosure.NativeScopeTransformer.Entry}
  {xs right : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.PendingAgreement first second ((x, entry) :: xs) right →
    ¬x ∈ YulangClosure.NativeScopeTransformer.keys xs ∧ ¬x ∈ YulangClosure.NativeScopeTransformer.keys right →
      YulangClosure.NativeScopeExecutionR167.PendingAgreement first second xs right
'YulangClosure.NativeScopeExecutionR167.agreement_advance_left' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.agreement_advance_left
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.agreement_advance_right
@YulangClosure.NativeScopeExecutionR167.agreement_advance_right : ∀
  {first second : YulangClosure.NativeScopeTransformer.Transformer}
  {left : List (Nat × YulangClosure.NativeScopeTransformer.Entry)} {x : Nat}
  {entry : YulangClosure.NativeScopeTransformer.Entry} {xs : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.PendingAgreement first second left ((x, entry) :: xs) →
    ¬x ∈ YulangClosure.NativeScopeTransformer.keys left ∧ ¬x ∈ YulangClosure.NativeScopeTransformer.keys xs →
      YulangClosure.NativeScopeExecutionR167.PendingAgreement first second left xs
'YulangClosure.NativeScopeExecutionR167.agreement_advance_right' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.agreement_advance_right
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.scopeRun_trace
@YulangClosure.NativeScopeExecutionR167.scopeRun_trace : ∀
  {first second : YulangClosure.NativeScopeTransformer.Transformer}
  {left right out : List (Nat × YulangClosure.NativeScopeTransformer.Entry)},
  YulangClosure.NativeScopeExecutionR167.ScopeRun first.stamped left right out →
    List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys left) →
      List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys right) →
        YulangClosure.NativeScopeExecutionR167.PendingAgreement first second left right →
          YulangClosure.NativeScopeExecutionR167.ScopeTrace first second
            (YulangClosure.NativeScopeTransformer.keys left) (YulangClosure.NativeScopeTransformer.keys right) out
'YulangClosure.NativeScopeExecutionR167.scopeRun_trace' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.scopeRun_trace
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.thenTrace_result
@YulangClosure.NativeScopeExecutionR167.thenTrace_result : ∀
  {first second result : YulangClosure.NativeScopeTransformer.Transformer},
  YulangClosure.NativeScopeExecutionR167.ThenTrace first second result →
    YulangClosure.NativeScopeEvaluateRefinementR165.Canonical first →
      YulangClosure.NativeScopeEvaluateRefinementR165.Canonical second →
        result = YulangClosure.NativeScopeRepresentationR166.thenModel first second
'YulangClosure.NativeScopeExecutionR167.thenTrace_result' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.thenTrace_result
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.samples_keys
@YulangClosure.NativeScopeExecutionR167.samples_keys : ∀ {State : Type} {call : State → Nat → State → Nat → Prop}
  {before : State} {ids : List Nat} {after : State} {pairs : List (Nat × Nat)},
  YulangClosure.NativeScopeExecutionR167.Samples call before ids after pairs → List.map Prod.fst pairs = ids
'YulangClosure.NativeScopeExecutionR167.samples_keys' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.samples_keys
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.table_pair
YulangClosure.NativeScopeExecutionR167.table_pair : ∀ (pairs : List (Nat × Nat)),
  (List.map Prod.fst pairs).Nodup →
    ∀ (key value : Nat), (key, value) ∈ pairs → YulangClosure.NativeScopeExecutionR167.table pairs key = value
'YulangClosure.NativeScopeExecutionR167.table_pair' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.table_pair
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.samples_values
@YulangClosure.NativeScopeExecutionR167.samples_values : ∀ {State : Type} {call : State → Nat → State → Nat → Prop}
  {before : State} {ids : List Nat} {after : State} {pairs : List (Nat × Nat)},
  YulangClosure.NativeScopeExecutionR167.Samples call before ids after pairs →
    ids.Nodup → List.map (YulangClosure.NativeScopeExecutionR167.table pairs) ids = List.map Prod.snd pairs
'YulangClosure.NativeScopeExecutionR167.samples_values' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.samples_values
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sample_index_lookup
@YulangClosure.NativeScopeExecutionR167.sample_index_lookup : ∀ {State : Type} {call : State → Nat → State → Nat → Prop}
  {before : State} {ids : List Nat} {after : State} {pairs : List (Nat × Nat)},
  YulangClosure.NativeScopeExecutionR167.Samples call before ids after pairs →
    ids.Nodup →
      ∀ (index key : Nat) (bound : index < ids.length),
        ids[index] = key →
          ∃ image,
            (List.map Prod.snd pairs)[index]? = Option.some image ∧
              YulangClosure.NativeScopeExecutionR167.table pairs key = image
'YulangClosure.NativeScopeExecutionR167.sample_index_lookup' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sample_index_lookup
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.binarySearch_present
@YulangClosure.NativeScopeExecutionR167.binarySearch_present : ∀ {ids : List Nat} {key : Nat} {result : Option Nat},
  YulangClosure.NativeScopeExecutionR167.BinarySearchContract ids key result →
    key ∈ ids → ∃ index, result = Option.some index ∧ ∃ bound, ids[index] = key
'YulangClosure.NativeScopeExecutionR167.binarySearch_present' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.binarySearch_present
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.successful_return_boundary
YulangClosure.NativeScopeExecutionR167.successful_return_boundary : ∀
  (gates : List YulangClosure.NativeScopeExecutionR167.Gate) (body : YulangClosure.NativeScopeExecutionR167.Return)
  (result : YulangClosure.NativeScopeTransformer.Transformer),
  YulangClosure.NativeScopeExecutionR167.finish gates body = YulangClosure.NativeScopeExecutionR167.Return.ok result →
    (∀ (gate : YulangClosure.NativeScopeExecutionR167.Gate), gate ∈ gates → gate.passed) ∧
      body = YulangClosure.NativeScopeExecutionR167.Return.ok result
'YulangClosure.NativeScopeExecutionR167.successful_return_boundary' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.successful_return_boundary
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.sampledEntries_table
@YulangClosure.NativeScopeExecutionR167.sampledEntries_table : ∀ {State : Type}
  {call : State → Nat → State → Nat → Prop} {before : State}
  {entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)} {after : State} {pairs : List (Nat × Nat)},
  YulangClosure.NativeScopeExecutionR167.Samples call before (YulangClosure.NativeScopeTransformer.keys entries) after
      pairs →
    (YulangClosure.NativeScopeTransformer.keys entries).Nodup →
      ∀ (tags : Nat → Nat),
        YulangClosure.NativeScopeExecutionR167.sampledEntries entries (List.map Prod.snd pairs) tags =
          List.map
            (fun entry =>
              YulangClosure.NativeScopeRepresentationR166.renameEntryModel entry
                (YulangClosure.NativeScopeExecutionR167.table pairs) tags)
            entries
'YulangClosure.NativeScopeExecutionR167.sampledEntries_table' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.sampledEntries_table
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result
@YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result : ∀
  {transformer : YulangClosure.NativeScopeTransformer.Transformer} {inputs scopes : List (Nat × Nat)}
  {result : YulangClosure.NativeScopeTransformer.Transformer},
  YulangClosure.NativeScopeExecutionR167.RemapSourceReturn transformer inputs scopes result →
    YulangClosure.NativeScopeExecutionR167.remapReturn transformer inputs scopes =
      YulangClosure.NativeScopeExecutionR167.Return.ok result
'YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.remapTrace_result
@YulangClosure.NativeScopeExecutionR167.remapTrace_result : ∀ {State : Type}
  {inputCall scopeCall : State → Nat → State → Nat → Prop}
  {transformer result : YulangClosure.NativeScopeTransformer.Transformer}
  (trace : YulangClosure.NativeScopeExecutionR167.RemapTrace inputCall scopeCall transformer result),
  YulangClosure.NativeScopeRepresentationR166.Representation transformer →
    YulangClosure.NativeScopeRepresentationR166.remapModel transformer
        (YulangClosure.NativeScopeExecutionR167.table trace.scopes)
        (YulangClosure.NativeScopeExecutionR167.table trace.inputs) =
      Option.some result
'YulangClosure.NativeScopeExecutionR167.remapTrace_result' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.remapTrace_result
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.remapTrace_injective
@YulangClosure.NativeScopeExecutionR167.remapTrace_injective : ∀ {State : Type}
  {inputCall scopeCall : State → Nat → State → Nat → Prop}
  {transformer result : YulangClosure.NativeScopeTransformer.Transformer}
  (trace : YulangClosure.NativeScopeExecutionR167.RemapTrace inputCall scopeCall transformer result),
  YulangClosure.NativeScopeRepresentationR166.Representation transformer →
    (∀ (a : Nat),
        a ∈ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer →
          ∀ (b : Nat),
            b ∈ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer →
              YulangClosure.NativeScopeExecutionR167.table trace.inputs a =
                  YulangClosure.NativeScopeExecutionR167.table trace.inputs b →
                a = b) ∧
      ∀ (a : Nat),
        a ∈ YulangClosure.NativeScopeTransformer.keys transformer.scopes →
          ∀ (b : Nat),
            b ∈ YulangClosure.NativeScopeTransformer.keys transformer.scopes →
              YulangClosure.NativeScopeExecutionR167.table trace.scopes a =
                  YulangClosure.NativeScopeExecutionR167.table trace.scopes b →
                a = b
'YulangClosure.NativeScopeExecutionR167.remapTrace_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.remapTrace_injective
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.input_collision_rejected
YulangClosure.NativeScopeExecutionR167.input_collision_rejected : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer) (inputs scopes : List (Nat × Nat)),
  (YulangClosure.NativeScopeEvaluateRefinementR165.normalize (List.map Prod.snd inputs)).length ≠ inputs.length →
    YulangClosure.NativeScopeExecutionR167.remapReturn transformer inputs scopes =
      YulangClosure.NativeScopeExecutionR167.Return.collisionFailure
'YulangClosure.NativeScopeExecutionR167.input_collision_rejected' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.input_collision_rejected
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.scope_collision_rejected
YulangClosure.NativeScopeExecutionR167.scope_collision_rejected : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer) (inputs scopes : List (Nat × Nat)),
  (YulangClosure.NativeScopeEvaluateRefinementR165.normalize (List.map Prod.snd inputs)).length = inputs.length →
    YulangClosure.NativeScopeRepresentationR166.adjacentDistinct
          (YulangClosure.NativeScopeTransformer.keys
            (YulangClosure.NativeScopeRepresentationR166.sortEntries
              (YulangClosure.NativeScopeExecutionR167.sampledEntries transformer.scopes (List.map Prod.snd scopes)
                (YulangClosure.NativeScopeExecutionR167.table inputs)))) =
        Bool.false →
      YulangClosure.NativeScopeExecutionR167.remapReturn transformer inputs scopes =
        YulangClosure.NativeScopeExecutionR167.Return.collisionFailure
'YulangClosure.NativeScopeExecutionR167.scope_collision_rejected' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.scope_collision_rejected
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.successful_generated
@YulangClosure.NativeScopeExecutionR167.successful_generated : ∀
  {transformer : YulangClosure.NativeScopeTransformer.Transformer},
  YulangClosure.NativeScopeExecutionR167.Successful transformer →
    YulangClosure.NativeScopeRepresentationR166.Generated transformer
'YulangClosure.NativeScopeExecutionR167.successful_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.successful_generated
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.successful_representation
@YulangClosure.NativeScopeExecutionR167.successful_representation : ∀
  {transformer : YulangClosure.NativeScopeTransformer.Transformer},
  YulangClosure.NativeScopeExecutionR167.Successful transformer →
    YulangClosure.NativeScopeRepresentationR166.Representation transformer
'YulangClosure.NativeScopeExecutionR167.successful_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.successful_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.nativeTrace_successful
@YulangClosure.NativeScopeExecutionR167.nativeTrace_successful : ∀
  {native : YulangClosure.NativeScopeRepresentationR166.NativeFields},
  YulangClosure.NativeScopeExecutionR167.NativeTrace native →
    YulangClosure.NativeScopeExecutionR167.Successful (YulangClosure.NativeScopeRepresentationR166.encodeFields native)
'YulangClosure.NativeScopeExecutionR167.nativeTrace_successful' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.nativeTrace_successful
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.nativeTrace_generated
@YulangClosure.NativeScopeExecutionR167.nativeTrace_generated : ∀
  {native : YulangClosure.NativeScopeRepresentationR166.NativeFields},
  YulangClosure.NativeScopeExecutionR167.NativeTrace native →
    YulangClosure.NativeScopeRepresentationR166.Generated
      (YulangClosure.NativeScopeRepresentationR166.encodeFields native)
'YulangClosure.NativeScopeExecutionR167.nativeTrace_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.nativeTrace_generated
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent
YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent : ∀
  (native : YulangClosure.NativeScopeRepresentationR166.NativeFields)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeExecutionR167.Successful (YulangClosure.NativeScopeRepresentationR166.encodeFields native) →
    YulangClosure.NativeScopeTransformer.Equivalent
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor
        (YulangClosure.NativeScopeRepresentationR166.encodeFields native) initial)
      ((YulangClosure.NativeScopeRepresentationR166.encodeFields native).evaluate initial)
'YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent
YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent : ∀
  (native : YulangClosure.NativeScopeRepresentationR166.NativeFields)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeExecutionR167.NativeTrace native →
    YulangClosure.NativeScopeTransformer.Equivalent
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor
        (YulangClosure.NativeScopeRepresentationR166.encodeFields native) initial)
      ((YulangClosure.NativeScopeRepresentationR166.encodeFields native).evaluate initial)
'YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeExecutionR167.thenTrace_denotation
@YulangClosure.NativeScopeExecutionR167.thenTrace_denotation : ∀
  {first second result : YulangClosure.NativeScopeTransformer.Transformer},
  YulangClosure.NativeScopeExecutionR167.ThenTrace first second result →
    YulangClosure.NativeScopeEvaluateRefinementR165.Canonical first →
      YulangClosure.NativeScopeEvaluateRefinementR165.Canonical second →
        ∀ (initial : YulangClosure.NativeScopeTransformer.State),
          YulangClosure.NativeScopeTransformer.Equivalent (result.evaluate initial)
            (second.evaluate (first.evaluate initial))
'YulangClosure.NativeScopeExecutionR167.thenTrace_denotation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeExecutionR167.thenTrace_denotation
[exit 0]
PASS: YulangClosure.NativeScopeExecutionR167.mergeTrace_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sortIds_contract, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sortContract_unique, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.dedupContract_unique, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sortedCopy_contract, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sortEntries_contract, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.unique_key, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.entrySortContract_windows, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.entrySortContract_success, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.emit_eq_encode, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.emit_release_retained, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.emit_neutral_omitted, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sourceEntry_model, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.scopeTrace_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.entryAt_skip_consumed, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.entryAt_selected_head, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.entryAt_cursor_read, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.before_head_absent, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.agreement_advance_left, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.agreement_advance_right, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.scopeRun_trace, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.thenTrace_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.samples_keys, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.table_pair, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.samples_values, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sample_index_lookup, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.binarySearch_present, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.successful_return_boundary, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.sampledEntries_table, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.remapSourceReturn_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.remapTrace_result, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.remapTrace_injective, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.input_collision_rejected, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.scope_collision_rejected, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.successful_generated, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.successful_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.nativeTrace_successful, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.nativeTrace_generated, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.successful_evaluate_equivalent, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.nativeTrace_evaluate_equivalent, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeExecutionR167.thenTrace_denotation, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.
```

Checker exit: 0
