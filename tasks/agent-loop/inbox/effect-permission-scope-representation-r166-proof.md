# R166 scope representation proof handoff

Sprint-ID: effect-permission-native-scope-representation-r166.
Assignment-ID: r166_native_scope_proof. Handoff revision: 1.
Outcome class: checked Lean model proof; native execution correspondence remains conditional.
Baseline: `3d8ba0b91c720cce142c6b0e19984c5efd938360`.
Contract: `tasks/agent-loop/sprints/effect-permission-native-scope-representation-r166.md`, SHA-256 `85fb9acc51d8e2ce470fc28b4d9054cdea71ecbf28a9edf6f7a751f1201c1037`.
Worker: `/root/r166_native_scope_proof`; requested route Sol/high; effective model/effort UNKNOWN.
Author: this leaf only; no contributing descendants.

## Original obligation and scope

The authoritative compose decision is `notes/design/2026-10-15-compose-scoped-effect-release.md`, “Direct decision” and “Scope of the operation”. The original parent and complete witness/quantifier boundary are in `notes/theory/2026-10-15-compose-scoped-release-construction.md` §§1–2. Its finite normal-form equations are the model used here: initial route tags, stamped route tags, initial protections, one keep bit and Missing disjunction per scope; composition tests the original input and filters the second guard only against first stamps. The note is a construction/source argument, not independent authority to change semantics. The top-level inference principles and annotation-hygiene decision remain governing; this packet adds no semantics.

The immediate parent is R165 `YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent`: for **every** transformer and **every** initial `State`, `Canonical transformer` implies extensional equivalence of cursor evaluation and denotation. R166 derives this Canonical premise for its inductively generated operation model. Arbitrary unsorted/duplicate initial lists remain accepted. No premise about initial-state freshness, support containment, ID injection or empty state was added.

## Source-to-Lean correspondence

All new public names are under `YulangClosure.NativeScopeRepresentationR166`.

| Native owner | Model and proved fact |
| --- | --- |
| Ordered `InputRouteId(u32)` / `EffectScopeId(u32)` | `encodeId = UInt32.toNat`; injective, strictly order preserving, below `2^32`. `NativeFields`/`encodeFields` explicitly encode the raw fields; `NativeOrdered` implies `Representation`. |
| identity / singleton stamp, protection and release | `identityModel`, `stampModel`, `protectModel`, `releaseModel`; each establishes `Representation`, including ordered guard vectors. |
| ordered set union and `then` per-scope formula | R165 `unionCursor` for stamps, support and guard union; `thenModel` maps the merged scope support through `composeEntryModel`, filters second guards against first stamps, and uses existing `encode` to omit identity entries. `then_representation` derives ordered stamps, unique scope keys and ordered guards; `thenModel_denotation` proves the full ordered-composition equation for arbitrary initial states. |
| remap input support collection, sorted-copy length check, mapped guard/stamp sorting | `inputSupport`, `normalize_length_eq_iff`, `remapModel`; successful remap derives injection on private input support. `inputSupport_stamp` and `inputSupport_guard` supply the actual finite-support subsets needed by sorting proofs. |
| remap scope sort + `windows(2)` duplicate rejection | `sortEntries`, `adjacentDistinct`, `adjacent_sort_iff_nodup`, `scope_collision_check`: the sorted adjacent-distinct criterion is exactly mapped-scope Nodup. Success derives injection on scope support and `remap_representation`. |
| Missing guard search over sorted initial input slice | Concrete executable `orderedSearch` stops before any larger head; `orderedSearch_iff`, `missingSearch_iff`, `missingSearch_encoded` prove membership/Missing correspondence. This is an ordered-list search model, **not an implementation of Rust binary search**. |
| R165 application | `Generated` has exactly singleton, ordered-then and successful-remap construction rules. `generated_representation` derives the invariant, and `generated_evaluate_equivalent` consumes it in R165. `encoded_native_evaluate_equivalent` explicitly retains both `encodeFields native = transformer` and `Generated transformer`. |

The model's `Representation` contains the ordering/uniqueness facts required by searches and R165, plus ordered guards. It does not claim a new theorem about representation minimality or authenticated identifiers. Pure `Nat -> Nat` maps represent consistently sampled renaming tables and permit a larger mathematical codomain; no arbitrary Nat model value is claimed to come from u32. Actual encoded native fields remain visibly related by the encoding equality in the final theorem.

`thenModel` is a finite-support/per-scope model of the inspected merge branches, not a step-by-step formalization of the Rust scope cursor. `sortIds`/`sortEntries` use Lean mergeSort; Rust sort_unstable execution is outside the formalization. Remap maps are pure sampled tables; Rust FnMut invocation count, table lookup/binary-search index execution and allocation failure behavior are not Lean theorems here. The Rust sorted-slice binary_search membership contract is a source boundary; only its required mathematical membership/Missing property is proved. All allocation errors are omitted from this successful-value model.

## Parent application and remaining premise

The model Canonical premise is now derived for every `Generated` value, including every successful modeled remap. It no longer needs to be separately assumed at the R165 application. All 27 public theorems are kernel accepted with exact types and complete transitive axiom lists below.

First remaining native premise / owner: Luna's source correspondence lane must validate that **every successful actual private API construction** is represented by these model operations with the same encoded fields and sampled maps; the final theorem deliberately retains that relation. This packet does not mechanize Rust or the standard library, and therefore does not remove this native relation premise by relabeling `Generated` as Rust execution. Independent proof and source review are NOT_RUN by this producer.

Original effect hygiene remains OPEN: allocation/state authentication, authentic route tags/scope ownership, complete Call witness/source attribution, shared FreshUse/external-state injection, actual Catch consumer, original A/B, principality, termination and production are omitted. Private-support injection does not imply injection on incoming external state. No pending typed-Union decision is consumed, and no language feature or parent quantifier is weakened.

Mutual TODO R166-NATIVE-RELATION: owner Luna/source lane; inputs pinned candidate_scope.rs, candidate_context.rs, R165 and this module; output exact branch-to-model correspondence and explicit standard-library contracts; falsifier any successful constructor/then/remap path whose encoded fields differ from the model, fail the representation invariant, or use a search on an unordered input.

## Checks, repairs, resources and writes

Pinned native Lake resolved read-only with `elan which lake`; actual Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)` and Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Project `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` were read; no external packages and no dependency/toolchain edits. Pinned local sources consulted: `Init/Data/UInt/Lemmas.lean`, `Init/Data/List/Pairwise.lean`, `Init/Data/List/Sublist.lean`, `Init/Data/List/Perm.lean`, `Init/Data/List/Sort/Lemmas.lean` in that toolchain.

Focused native `lake build +YulangClosure.NativeScopeRepresentationR166` passed after incremental repairs. Final bundled checker used `--no-cache`, named module coverage and all 27 public theorems, timeout 120s, Lean `-j1 -M1024`; exit 0 in 2.893s. Complete receipt below. It found only permitted standard axioms; three encoding theorems use none. R165 dependency warnings were replayed unchanged. This new module emits no own warnings. No full/default integration build, Rust execution, Cargo build, tests or benchmarks were run by this leaf.

Material intermediate failures (all repaired, no holes retained): initial build exit 1 exposed UInt32 injectivity's implicit-argument mismatch, an entry/entryAt reduction mismatch and an unreduced identity guard union; next build exit 1 exposed unavailable localized list notation (`<+`, `~`) and membership/Pairwise implicit-binder mistakes; another build exit 1 exposed the implicit binder shape of Pairwise.imp. Repairs used explicit introduced arguments, definitional entry reduction, explicit List.Sublist/List.Perm and correct membership binders. Subsequent focused builds and the complete checker exited 0. One intermediate shell build was piped to tail without pipefail; its visible build-success result was not used as final evidence. All later builds used pipefail; the bundled checker checks subprocess exits directly.

Source search of this module, R165 and NativeScopeTransformer found no `sorry`, `admit`, project `axiom`, `skipKernelTC`, `native_decide` or `implemented_by` matches. All six input hashes were rechecked unchanged after construction. `git diff --check` on the two leased paths passed.

Exact authored paths: this handoff and `notes/theory/lean/YulangClosure/NativeScopeRepresentationR166.lean`. Existing project `.lake` generated outputs for this module only were used; no environment, dependency, additional target or persistent scratch directory was created. The checker made `/tmp/yulang-lean-audit-y7e4ntwp/YulangProofAudit.lean` temporarily and removed its directory; absence was checked. No Rust/root import/current status/Git writes. No descendants were started. Exact total construction wall/CPU use was not separately instrumented (UNKNOWN); parent launch timing owns the 1800s bound. Checker wall time is measured above.

Worker state: STOPPED after this frozen handoff. All authored and generated writes stopped; no descendants or unresolved child leases. Ready for independent review, not producer-certified integration or production.

## Frozen dependencies and artifact

- `crates/yu-solver/src/candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `crates/yu-solver/src/candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`: `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-proof.md`: `8398752890ad0976f5f9d6f9725f62de5b7dbb2a4c53fa5760a32dcd2249a21b`.
- `tasks/agent-loop/sprints/effect-permission-native-scope-evaluate-r165.md`: `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.
- `notes/theory/lean/YulangClosure/NativeScopeRepresentationR166.lean`: `bee9bc1d052d05cc39e43da8614f52d09eac4c117d58b040e4eab3334be25e7f`.

## Complete bundled checker receipt

Elapsed: 2.893 seconds. Exit: 0. Public declarations requested: 27.

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
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.NativeScopeRepresentationR166
⚠ [3/4] Replayed YulangClosure.NativeScopeEvaluateRefinementR165
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
Build completed successfully (4 jobs).
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-y7e4ntwp /tmp/yulang-lean-audit-y7e4ntwp/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeId_injective
YulangClosure.NativeScopeRepresentationR166.encodeId_injective : Function.Injective
  YulangClosure.NativeScopeRepresentationR166.encodeId
'YulangClosure.NativeScopeRepresentationR166.encodeId_injective' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeId_injective
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeId_lt
YulangClosure.NativeScopeRepresentationR166.encodeId_lt : ∀ (a b : UInt32),
  YulangClosure.NativeScopeRepresentationR166.encodeId a < YulangClosure.NativeScopeRepresentationR166.encodeId b ↔
    a < b
'YulangClosure.NativeScopeRepresentationR166.encodeId_lt' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeId_lt
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeId_bound
YulangClosure.NativeScopeRepresentationR166.encodeId_bound : ∀ (a : UInt32),
  YulangClosure.NativeScopeRepresentationR166.encodeId a < 2 ^ 32
'YulangClosure.NativeScopeRepresentationR166.encodeId_bound' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeId_bound
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeId_mem
YulangClosure.NativeScopeRepresentationR166.encodeId_mem : ∀ (ids : List UInt32) (id : UInt32),
  YulangClosure.NativeScopeRepresentationR166.encodeId id ∈
      List.map YulangClosure.NativeScopeRepresentationR166.encodeId ids ↔
    id ∈ ids
'YulangClosure.NativeScopeRepresentationR166.encodeId_mem' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeId_mem
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeId_sorted
YulangClosure.NativeScopeRepresentationR166.encodeId_sorted : ∀ (ids : List UInt32),
  List.Pairwise (fun x1 x2 => x1 < x2) (List.map YulangClosure.NativeScopeRepresentationR166.encodeId ids) ↔
    List.Pairwise (fun x1 x2 => x1 < x2) ids
'YulangClosure.NativeScopeRepresentationR166.encodeId_sorted' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeId_sorted
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encodeFields_representation
YulangClosure.NativeScopeRepresentationR166.encodeFields_representation : ∀
  (native : YulangClosure.NativeScopeRepresentationR166.NativeFields),
  YulangClosure.NativeScopeRepresentationR166.NativeOrdered native →
    YulangClosure.NativeScopeRepresentationR166.Representation
      (YulangClosure.NativeScopeRepresentationR166.encodeFields native)
'YulangClosure.NativeScopeRepresentationR166.encodeFields_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encodeFields_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.identity_representation
YulangClosure.NativeScopeRepresentationR166.identity_representation : YulangClosure.NativeScopeRepresentationR166.Representation
  YulangClosure.NativeScopeRepresentationR166.identityModel
'YulangClosure.NativeScopeRepresentationR166.identity_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.identity_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.stamp_representation
YulangClosure.NativeScopeRepresentationR166.stamp_representation : ∀ (tag : UInt32),
  YulangClosure.NativeScopeRepresentationR166.Representation
    (YulangClosure.NativeScopeRepresentationR166.stampModel tag)
'YulangClosure.NativeScopeRepresentationR166.stamp_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.stamp_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.protect_representation
YulangClosure.NativeScopeRepresentationR166.protect_representation : ∀ (scope tag : UInt32),
  YulangClosure.NativeScopeRepresentationR166.Representation
    (YulangClosure.NativeScopeRepresentationR166.protectModel scope tag)
'YulangClosure.NativeScopeRepresentationR166.protect_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.protect_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.release_representation
YulangClosure.NativeScopeRepresentationR166.release_representation : ∀ (scope : UInt32),
  YulangClosure.NativeScopeRepresentationR166.Representation
    (YulangClosure.NativeScopeRepresentationR166.releaseModel scope)
'YulangClosure.NativeScopeRepresentationR166.release_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.release_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.then_representation
YulangClosure.NativeScopeRepresentationR166.then_representation : ∀
  (first second : YulangClosure.NativeScopeTransformer.Transformer),
  YulangClosure.NativeScopeRepresentationR166.Representation first →
    YulangClosure.NativeScopeRepresentationR166.Representation second →
      YulangClosure.NativeScopeRepresentationR166.Representation
        (YulangClosure.NativeScopeRepresentationR166.thenModel first second)
'YulangClosure.NativeScopeRepresentationR166.then_representation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.then_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.composeEntryModel_missing
YulangClosure.NativeScopeRepresentationR166.composeEntryModel_missing : ∀
  (first second : YulangClosure.NativeScopeTransformer.Entry) (stamps inputs : List Nat),
  YulangClosure.NativeScopeTransformer.Missing
      (YulangClosure.NativeScopeRepresentationR166.composeEntryModel first second stamps).missing inputs ↔
    YulangClosure.NativeScopeTransformer.Missing
      (YulangClosure.NativeScopeTransformer.composeEntry first second stamps).missing inputs
'YulangClosure.NativeScopeRepresentationR166.composeEntryModel_missing' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.composeEntryModel_missing
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.thenModel_entry
YulangClosure.NativeScopeRepresentationR166.thenModel_entry : ∀
  (first second : YulangClosure.NativeScopeTransformer.Transformer) (scope : Nat),
  (YulangClosure.NativeScopeRepresentationR166.thenModel first second).entry scope =
    YulangClosure.NativeScopeRepresentationR166.composeEntryModel (first.entry scope) (second.entry scope) first.stamped
'YulangClosure.NativeScopeRepresentationR166.thenModel_entry' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.thenModel_entry
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.thenModel_denotation
YulangClosure.NativeScopeRepresentationR166.thenModel_denotation : ∀
  (first second : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeTransformer.Equivalent
    ((YulangClosure.NativeScopeRepresentationR166.thenModel first second).evaluate initial)
    (second.evaluate (first.evaluate initial))
'YulangClosure.NativeScopeRepresentationR166.thenModel_denotation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.thenModel_denotation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.adjacent_sort_iff_nodup
YulangClosure.NativeScopeRepresentationR166.adjacent_sort_iff_nodup : ∀ (ids : List Nat),
  YulangClosure.NativeScopeRepresentationR166.adjacentDistinct
        (YulangClosure.NativeScopeRepresentationR166.sortIds ids) =
      Bool.true ↔
    ids.Nodup
'YulangClosure.NativeScopeRepresentationR166.adjacent_sort_iff_nodup' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.adjacent_sort_iff_nodup
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.normalize_length_eq_iff
YulangClosure.NativeScopeRepresentationR166.normalize_length_eq_iff : ∀ (ids : List Nat),
  (YulangClosure.NativeScopeEvaluateRefinementR165.normalize ids).length = ids.length ↔ ids.Nodup
'YulangClosure.NativeScopeRepresentationR166.normalize_length_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.normalize_length_eq_iff
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.inputSupport_stamp
YulangClosure.NativeScopeRepresentationR166.inputSupport_stamp : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer),
  transformer.stamped ⊆ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer
'YulangClosure.NativeScopeRepresentationR166.inputSupport_stamp' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.inputSupport_stamp
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.inputSupport_guard
YulangClosure.NativeScopeRepresentationR166.inputSupport_guard : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (entry : Nat × YulangClosure.NativeScopeTransformer.Entry),
  entry ∈ transformer.scopes → entry.snd.missing ⊆ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer
'YulangClosure.NativeScopeRepresentationR166.inputSupport_guard' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.inputSupport_guard
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.scope_collision_check
YulangClosure.NativeScopeRepresentationR166.scope_collision_check : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer) (scopes tags : Nat → Nat),
  YulangClosure.NativeScopeRepresentationR166.adjacentDistinct
        (YulangClosure.NativeScopeTransformer.keys
          (YulangClosure.NativeScopeRepresentationR166.sortEntries
            (List.map (fun entry => YulangClosure.NativeScopeRepresentationR166.renameEntryModel entry scopes tags)
              transformer.scopes))) =
      Bool.true ↔
    (List.map scopes (YulangClosure.NativeScopeTransformer.keys transformer.scopes)).Nodup
'YulangClosure.NativeScopeRepresentationR166.scope_collision_check' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.scope_collision_check
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.remap_success_injective
YulangClosure.NativeScopeRepresentationR166.remap_success_injective : ∀
  (transformer result : YulangClosure.NativeScopeTransformer.Transformer) (scopes tags : Nat → Nat),
  YulangClosure.NativeScopeRepresentationR166.remapModel transformer scopes tags = Option.some result →
    (∀ (a : Nat),
        a ∈ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer →
          ∀ (b : Nat),
            b ∈ YulangClosure.NativeScopeRepresentationR166.inputSupport transformer → tags a = tags b → a = b) ∧
      ∀ (a : Nat),
        a ∈ YulangClosure.NativeScopeTransformer.keys transformer.scopes →
          ∀ (b : Nat), b ∈ YulangClosure.NativeScopeTransformer.keys transformer.scopes → scopes a = scopes b → a = b
'YulangClosure.NativeScopeRepresentationR166.remap_success_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.remap_success_injective
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.remap_representation
YulangClosure.NativeScopeRepresentationR166.remap_representation : ∀
  (transformer result : YulangClosure.NativeScopeTransformer.Transformer) (scopes tags : Nat → Nat),
  YulangClosure.NativeScopeRepresentationR166.Representation transformer →
    YulangClosure.NativeScopeRepresentationR166.remapModel transformer scopes tags = Option.some result →
      YulangClosure.NativeScopeRepresentationR166.Representation result
'YulangClosure.NativeScopeRepresentationR166.remap_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.remap_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.orderedSearch_iff
YulangClosure.NativeScopeRepresentationR166.orderedSearch_iff : ∀ (tag : Nat) (ids : List Nat),
  List.Pairwise (fun x1 x2 => x1 < x2) ids →
    (YulangClosure.NativeScopeRepresentationR166.orderedSearch tag ids = Bool.true ↔ tag ∈ ids)
'YulangClosure.NativeScopeRepresentationR166.orderedSearch_iff' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.orderedSearch_iff
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.missingSearch_iff
YulangClosure.NativeScopeRepresentationR166.missingSearch_iff : ∀ (guards inputs : List Nat),
  List.Pairwise (fun x1 x2 => x1 < x2) inputs →
    (YulangClosure.NativeScopeRepresentationR166.missingSearch guards inputs = Bool.true ↔
      YulangClosure.NativeScopeTransformer.Missing guards inputs)
'YulangClosure.NativeScopeRepresentationR166.missingSearch_iff' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.missingSearch_iff
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.missingSearch_encoded
YulangClosure.NativeScopeRepresentationR166.missingSearch_encoded : ∀ (guards inputs : List UInt32),
  List.Pairwise (fun x1 x2 => x1 < x2) inputs →
    (YulangClosure.NativeScopeRepresentationR166.missingSearch
          (List.map YulangClosure.NativeScopeRepresentationR166.encodeId guards)
          (List.map YulangClosure.NativeScopeRepresentationR166.encodeId inputs) =
        Bool.true ↔
      ∃ tag, tag ∈ guards ∧ ¬tag ∈ inputs)
'YulangClosure.NativeScopeRepresentationR166.missingSearch_encoded' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.missingSearch_encoded
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.generated_representation
YulangClosure.NativeScopeRepresentationR166.generated_representation : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer),
  YulangClosure.NativeScopeRepresentationR166.Generated transformer →
    YulangClosure.NativeScopeRepresentationR166.Representation transformer
'YulangClosure.NativeScopeRepresentationR166.generated_representation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.generated_representation
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.generated_evaluate_equivalent
YulangClosure.NativeScopeRepresentationR166.generated_evaluate_equivalent : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeRepresentationR166.Generated transformer →
    YulangClosure.NativeScopeTransformer.Equivalent
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor transformer initial)
      (transformer.evaluate initial)
'YulangClosure.NativeScopeRepresentationR166.generated_evaluate_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.generated_evaluate_equivalent
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent
YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent : ∀
  (native : YulangClosure.NativeScopeRepresentationR166.NativeFields)
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeRepresentationR166.encodeFields native = transformer →
    YulangClosure.NativeScopeRepresentationR166.Generated transformer →
      YulangClosure.NativeScopeTransformer.Equivalent
        (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor
          (YulangClosure.NativeScopeRepresentationR166.encodeFields native) initial)
        ((YulangClosure.NativeScopeRepresentationR166.encodeFields native).evaluate initial)
'YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent
[exit 0]
PASS: YulangClosure.NativeScopeRepresentationR166.encodeId_injective, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encodeId_lt, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encodeId_bound, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encodeId_mem, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encodeId_sorted, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encodeFields_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.identity_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.stamp_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.protect_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.release_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.then_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.composeEntryModel_missing, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.thenModel_entry, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.thenModel_denotation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.adjacent_sort_iff_nodup, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.normalize_length_eq_iff, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.inputSupport_stamp, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.inputSupport_guard, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.scope_collision_check, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.remap_success_injective, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.remap_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.orderedSearch_iff, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.missingSearch_iff, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.missingSearch_encoded, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.generated_representation, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.generated_evaluate_equivalent, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.NativeScopeRepresentationR166.encoded_native_evaluate_equivalent, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.

```
