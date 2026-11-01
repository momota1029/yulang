# R165 Lean proof handoff — native scope evaluator

Status: **CHECKER_ACCEPTED under the printed Canonical premise; proof and Rust/source reviews accepted. The Rust-to-Lean encoding and binary-search bridge remains open.** Writer: `/root/r165_native_scope_proof`, requested Sol/high, effective runtime model/effort UNKNOWN. No self-certification.

## Frozen inputs and authority

- Sprint contract revision 1, SHA-256 `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`; HEAD `92b7b726e35476254b4772dc59a7881667e65916`.
- `crates/yu-solver/src/candidate_scope.rs` SHA-256 `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`; caller `candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`; `NativeScopeTransformer.lean` `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- New Lean artifact `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean` SHA-256 `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b` (final header accurately states that source encoding and binary-search correspondence are not formalized in this module).
- Governing local scope normal form: `notes/theory/2026-10-15-compose-scoped-release-construction.md` §2, especially “Input tags and conditional introduction of a new scope” and “Exact correspondence to the frozen native kernel”; explicit policy `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1, 1.2, 3–5; inference principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5.
- Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1 and `docs/yulang-whole-proof-closure-ja.md` §§1, 4, with current birth-level SCC correction. Quantifiers remain every supported source program, lawful finite construction, actual retained occurrence and its joint source evidence, plus principal coverage/progress/termination; the compose example keeps one shared scoped assignment and complete Call witnesses. The original Simple-sub reference is `/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2 and §5, as located in the source note. This local evaluator result does not discharge that source theorem.

## Construction and application

`normalize` sorts and deduplicates arbitrary initial slices by membership and strict ascending order. This models the content of Rust `sorted_copy`; the exact sort implementation order differs but has the same canonical set representation. `unionCursor` and `protectionCursor` recursively consume the exact Rust two-cursor branches, including equal heads and the original normalized input in `Missing`. `ProtectionCursor.step` records the emitted prefix and unvisited suffixes. `step_preserves_remainder` and `Steps_preserves_remainder` prove the prefix/remaining invariant for every modeled transition/run. `protectionCursor_mem` proves the scope membership equation from that cursor execution, and `evaluateCursor_equivalent` applies it to the existing `YulangClosure.NativeScopeTransformer.Transformer.evaluate` for every `Transformer`, every `State`, under `Canonical transformer`.

`Canonical` states strict ascending stamped tags and scope keys, exactly the representation the private Rust constructors, successful `then`, and successful `remap` are intended to maintain. `evaluateCursor_canonical` and `evaluateCursor_nodup` show the resulting two coordinates are sorted and duplicate free. No order or uniqueness condition is imposed on arbitrary initial slices. Rust `ScopeTransformer` is private; the source lane must independently validate that every successful Rust value maps to this `Canonical` premise. The existing Lean `Transformer.then` uses append/encode set semantics and is not claimed to be a sorted Rust vector representation; its extensional composition law remains applicable after a separate representation bridge.

Represented: all finite initial input/protection slices, including unsorted duplicates; absent/overlapping/independent scopes; each less/greater/equal cursor branch; keep and Missing disjunction; empty guards; sorted unique output; arbitrary canonical transformer supports. Rust identifiers `u32` embed in Lean `Nat`. Omitted: fallible allocation and overflow paths (the theorem concerns successful return); source attribution and shared witness authentication; FreshUse map support, native Catch execution, constructor/`then`/`remap` representation derivation in Lean, and full A/B/principality/termination/production authority. The pending typed-Union R164 question is untouched.

First remaining premise for this implementation correspondence: an independently checked source-to-model encoding of every successfully constructed Rust `ScopeTransformer` into a Lean `Transformer` satisfying `Canonical`, together with binary-search/step correspondence under that encoding. Luna owns the Rust/source lane and adjudication. Beyond this local bridge, the first source-level premise is authentic input-route tags and scope ownership on the same full contribution witness, as identified in the compose construction §2 and its native-entry section.

## Actual execution and audit

- `elan which lake`: exit 0, resolved `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
- Resolved Lake `--version`: exit 0, `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`; `lake env lean --version`: exit 0, `Lean 4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- From `notes/theory/lean`: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.NativeScopeEvaluateRefinementR165`: final exit 0. Earlier focused builds failed on ordinary elaboration/proof goals (unknown `List.length_rec_on`/`Nat.strong_induction_on`, missing list length simplification, cursor branch equality, then missing nil cursor equation); each was repaired from actual diagnostics. No timeout, memory increase, or retry of an exhausted invocation.
- From repository root: `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --module YulangClosure.NativeScopeEvaluateRefinementR165 --theorem YulangClosure.NativeScopeEvaluateRefinementR165.mem_normalize --theorem YulangClosure.NativeScopeEvaluateRefinementR165.nodup_eraseDups_nat --theorem YulangClosure.NativeScopeEvaluateRefinementR165.sorted_normalize --theorem YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step_preserves_remainder --theorem YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps_preserves_remainder --theorem YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_mem --theorem YulangClosure.NativeScopeEvaluateRefinementR165.active_false --theorem YulangClosure.NativeScopeEvaluateRefinementR165.active_true --theorem YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_mem --theorem YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_support --theorem YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_sorted --theorem YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_sorted --theorem YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_canonical --theorem YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_nodup --theorem YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent --timeout 120`: exit 0, helper built the named module and audited all 15 delivered public theorems. It created and removed its ordinary audit temp directory under `/tmp`; no persistent scratch path was retained. Existing `.lake` build/cache was used by this assignment as R165 owner. The build emitted deprecation and unused-simp warnings only; no errors at final audit.
- Source cone scan `rg -n 'sorry|admit|\\baxiom\\b|debug.skipKernelTC|native_decide' notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`: exit 1, no matches. No project axiom or checker bypass was added.
- Checker acceptance is kernel evidence under printed premises and whitelist. Independent mathematical/source review remains NOT_RUN. Production gate remains OPEN.

## Printed theorem types and complete transitive axiom results

```text
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.mem_normalize
YulangClosure.NativeScopeEvaluateRefinementR165.mem_normalize : ∀ (xs : List Nat) (x : Nat),
  x ∈ YulangClosure.NativeScopeEvaluateRefinementR165.normalize xs ↔ x ∈ xs
'YulangClosure.NativeScopeEvaluateRefinementR165.mem_normalize' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.mem_normalize
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.nodup_eraseDups_nat
YulangClosure.NativeScopeEvaluateRefinementR165.nodup_eraseDups_nat : ∀ (xs : List Nat), xs.eraseDups.Nodup
'YulangClosure.NativeScopeEvaluateRefinementR165.nodup_eraseDups_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.nodup_eraseDups_nat
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.sorted_normalize
YulangClosure.NativeScopeEvaluateRefinementR165.sorted_normalize : ∀ (xs : List Nat),
  List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeEvaluateRefinementR165.normalize xs)
'YulangClosure.NativeScopeEvaluateRefinementR165.sorted_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.sorted_normalize
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step_preserves_remainder
YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step_preserves_remainder : ∀ (inputs : List Nat)
  (cursor next : YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor),
  YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step inputs cursor = Option.some next →
    cursor.emitted ++
        YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs cursor.inherited cursor.entries =
      next.emitted ++
        YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs next.inherited next.entries
'YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step_preserves_remainder' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.step_preserves_remainder
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps_preserves_remainder
YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps_preserves_remainder : ∀ (inputs : List Nat)
  {start finish : YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor},
  YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps inputs start finish →
    start.emitted ++
        YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs start.inherited start.entries =
      finish.emitted ++
        YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs finish.inherited finish.entries
'YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps_preserves_remainder' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.ProtectionCursor.Steps_preserves_remainder
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_mem
YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_mem : ∀ (xs ys : List Nat) (x : Nat),
  x ∈ YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor xs ys ↔ x ∈ xs ∨ x ∈ ys
'YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_mem' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_mem
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.active_false
YulangClosure.NativeScopeEvaluateRefinementR165.active_false : ∀ (entry : YulangClosure.NativeScopeTransformer.Entry)
  (inputs : List Nat),
  YulangClosure.NativeScopeEvaluateRefinementR165.active entry inputs Bool.false = Bool.true ↔
    YulangClosure.NativeScopeTransformer.Missing entry.missing inputs
'YulangClosure.NativeScopeEvaluateRefinementR165.active_false' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.active_false
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.active_true
YulangClosure.NativeScopeEvaluateRefinementR165.active_true : ∀ (entry : YulangClosure.NativeScopeTransformer.Entry)
  (inputs : List Nat),
  YulangClosure.NativeScopeEvaluateRefinementR165.active entry inputs Bool.true = Bool.true ↔
    entry.keep = Bool.true ∨ YulangClosure.NativeScopeTransformer.Missing entry.missing inputs
'YulangClosure.NativeScopeEvaluateRefinementR165.active_true' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.active_true
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_mem
YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_mem : ∀ (inputs left : List Nat)
  (entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  List.Pairwise (fun x1 x2 => x1 < x2) left →
    List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys entries) →
      ∀ (x : Nat),
        x ∈ YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs left entries ↔
          (YulangClosure.NativeScopeTransformer.entryAt entries x).keep = Bool.true ∧ x ∈ left ∨
            YulangClosure.NativeScopeTransformer.Missing
              (YulangClosure.NativeScopeTransformer.entryAt entries x).missing inputs
'YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_mem' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_mem
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_support
YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_support : ∀ (inputs left : List Nat)
  (entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  List.Pairwise (fun x1 x2 => x1 < x2) left →
    List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys entries) →
      ∀ (scope : Nat),
        scope ∈ YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs left entries →
          scope ∈ left ∨ scope ∈ YulangClosure.NativeScopeTransformer.keys entries
'YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_support' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_support
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_sorted
YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_sorted : ∀ (xs ys : List Nat),
  List.Pairwise (fun x1 x2 => x1 < x2) xs →
    List.Pairwise (fun x1 x2 => x1 < x2) ys →
      List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor xs ys)
'YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_sorted' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.unionCursor_sorted
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_sorted
YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_sorted : ∀ (inputs left : List Nat)
  (entries : List (Nat × YulangClosure.NativeScopeTransformer.Entry)),
  List.Pairwise (fun x1 x2 => x1 < x2) left →
    List.Pairwise (fun x1 x2 => x1 < x2) (YulangClosure.NativeScopeTransformer.keys entries) →
      List.Pairwise (fun x1 x2 => x1 < x2)
        (YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor inputs left entries)
'YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_sorted' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.protectionCursor_sorted
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_canonical
YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_canonical : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeEvaluateRefinementR165.Canonical transformer →
    YulangClosure.NativeScopeEvaluateRefinementR165.CanonicalState
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor transformer initial)
'YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_canonical
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_nodup
YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_nodup : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeEvaluateRefinementR165.Canonical transformer →
    (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor transformer initial).inputs.Nodup ∧
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor transformer initial).protections.Nodup
'YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_nodup
YULANG_AUDIT_BEGIN YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent
YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent : ∀
  (transformer : YulangClosure.NativeScopeTransformer.Transformer)
  (initial : YulangClosure.NativeScopeTransformer.State),
  YulangClosure.NativeScopeEvaluateRefinementR165.Canonical transformer →
    YulangClosure.NativeScopeTransformer.Equivalent
      (YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor transformer initial)
      (transformer.evaluate initial)
'YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.NativeScopeEvaluateRefinementR165.evaluateCursor_equivalent
```

Resource use: approximately 9 minutes wall active work through final audit, within the 1800-second Lean packet; focused Lean builds ran at the pinned `-j1 -M1024` project bound. Writes are stopped after this handoff. No Rust, test expectation, root import, manifest, shared task/status, Git, or unrelated path was edited.
