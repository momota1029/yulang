# Native inference progress r2 — independent frozen review

Reviewer: `/root/closure_strategy_r2`, fresh nonauthor for this packet. Date: 2026-10-26.

**ACCEPT at the stated local scope:** successful-result Context closure for the existing Lean `NativeContextExpansion.expand`, plus preservation of the explicitly defined constructor projection. **The original whole-inference termination contract remains OPEN.** No producer repair is requested. This receipt does not promote the constructor projection to the native inference transition relation or certify complete Rust correspondence.

## Frozen inputs and review authority

Baseline: `45d307a0aa01722b5aac289b07d71953630abca7`.

| Reviewed file | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/NativeInferenceProgress.lean` | `d22167d330ce1bb000677e2915a85beddb0e7a483600ac8c6a92cfdf37c79b12` |
| `notes/theory/2026-10-26-native-inference-progress.md` | `1814465a05140e772bd4affd0c801c324d14e1d8d44a80028252687d0f8bb4ab` |
| `tasks/agent-loop/inbox/20261026-whole-global-termination-r2.md` | `6abac5b1e122e633b57f467dc349a63f77ec3d6caf5d3f8f65cca3f33b1330bb` |

The handoff hash above is the producer's final documentation-only removal of embedded raw logs. The proof and theory note retained their assigned hashes. I read the full proof, note, final handoff, exact imported definitions and relevant native constructor/consumer code. All thirteen imported project source files and nine inspected native/design authority inputs independently matched the frozen baseline. The 14-file proof cone includes the new module.

The governing original claim is `YulangClosure.SourceProblem.InferenceTermination`, `Contracts.lean:151–154`:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

I applied the Lean proof skill and bounded generic leaf review instructions, read the original top-level principles §§1–1.1 and the birth-level SCC correction §§2–4,6, and preserved their distinction between immutable source Value births and mutable type-row levels. This review neither changes the source domain nor proves runtime strong normalization. Exact write lease: this receipt only. No descendants, Git mutations, producer edits, compiler changes, shared caches or repository configuration edits occurred.

## What the checked statement establishes

The main theorem is `YulangClosure.NativeInferenceProgress.native_expand_context_closure` at `NativeInferenceProgress.lean:301`. Its complete mathematical inputs are arbitrary `t : Tables`, `a : Availability`, `levels q : Nat → Nat`, `fuel : Nat`, `parent : Key`, `body : Body`, and these two premises:

```lean
Shallow t parent.context
NativeContextExpansion.expand t a levels q fuel parent = some body
```

It derives:

```lean
body.postContext = 0 ∧
(∀ fiber ∈ body.fibers, fiber.key.context = 0) ∧
(∀ child ∈ body.children, Atom t child.context)
```

`expand_consumes` at line 273 applies the actual existing `expand` success to the total-parser `consume` at line 240. The identity and nonidentity branches are both covered. It retains the original entry/current-pair/parser gates through the successful computation premise. It does not infer successful expansion from `Shallow`, or infer return of Rust callbacks from a Boolean availability table. `expand` and `decompose` are the existing proof-side operations at `NativeContextExpansion.lean:395–423`, not newly defined acceptance predicates.

The nontrivial local step is `consume_context_closure`: the atomic and shallow-Replay scan analysis constructs `ParsedClean`, including the implication that an empty filter list forces the original root to be identity. That implication matters because `decompose` preserves the stored parent Context when there are no filters. Invalid weights follow actual rejecting branches. Equal operands and repeated weights are handled in the Replay proof. `decompose_fibers_identity` covers both checked-filter fibers and the optional unconsumed continuation; `decompose_children_atom` follows the existing aligned child admissions. Thus the output shape is proved from the existing computation, rather than assumed as a premise.

Complete keys and bodies retain endpoint/source/transformer coordinates, but the main theorem observes their Context coordinates. It is not a semantic preservation theorem for those other coordinates. `transport_atom` additionally proves the exact source and transformer equalities for the existing `transport` definition.

## Native mapping and deliberate limits

All Rust locators below refer to the frozen baseline under `crates/yu-solver/src`.

| Reviewed owner | Evidence and accepted boundary |
|---|---|
| Source Context and negative annotation bootstrap | `candidate_context.rs:3366–3372,3898–3936`; `candidate_effect.rs:2161–2291`. Source construction can attach `PrefixLeft(weight, Identity)` before consumption. `Atom` at proof line 14 preserves this case. An all-Identity retained-fiber invariant would be false here. `signatureFiber` is the explicit projected source constructor, not an extraction theorem for every signature execution. |
| Checked filters and continuation | `candidate_context.rs:3800–3885`; `NativeContextExpansion.applyFilter`, `decompose`, `expand`. The registered branch attaches origin/replay without repeating physical insertion; the other branch performs the ordinary application. Both are represented. The continuation is included in the checked `Body`, while callback completion/readback into that body remains a separate native owner. |
| Replay construction | `candidate_context.rs:3992–4077`. The native both-identity case avoids allocation; otherwise the exact ordered operands are interned. `replay_context_shallow` preserves this distinction and requires actual table readback/strict earlier-child IDs. It does not bound the number of distinct atoms or replay IDs. |
| Full-expression interning and FreshUse rename | `candidate_context.rs:2630–2655,1556–1694`. `RenamedAtom` already contains the mapped prefix readback; its preservation lemma alone is a projection lemma. `fresh_prefix_constructed` independently derives a nonzero prefix from the existing interner. The full Rust renamer-to-`RenamedAtom` extraction, lawful maps and rollback are still open. The original renamer's other constructors remain available. |
| Post-check and transport | `candidate_context.rs:3297–3302` and retained bound transport; `NativeMergeExpansion.postCheck`, `transport`. Zero entries must be completed successful consume outputs. Pending relation membership is not substituted for completion. Transport retains sources/transformers exactly. |
| Value ports | Existing `NativeValuePorts.buildContext` at line 279. `value_port_context_atom` fixes the inherited post-context to zero and permits either swap flag. It does not prove that every original Value request has that zero post-context. |
| Growing history | Proof `State`, `Step`, `GrowingReachable` at lines 381,391,506. These preserve historical constructor objects and witnessed append-only readbacks. They omit queue removal, complete callback execution, rollback and scheduler correspondence. Arbitrarily many constructor steps are allowed. No accessibility conclusion follows from this invariant. |

The source/note/handoff consistently state these limits. In particular, the note's constructor claims must be read with its explicit remaining native extraction, and not as a proof that every original source run already satisfies `Shallow`.

## Application to the original parent and first remaining owner

The exact local application is the chain
`expand = some body` → `expand_consumes` → `consume_context_closure` → the zero post/fiber and atomic-child conclusion. This discharges the Context-shape result for a shallow request whose existing expansion succeeds. `step_invariant` and `growing_context_closure` then propagate the grammar inside the stated constructor projection, allowing actual table extensions without assuming a fixed final table.

The first missing parent bridge is a theorem extracting that projection and its entry premises from every original supported source initialization and every actual `inferStep`, including all Value/Effect bound lanes, the Value post-context premise, actual FreshUse maps, callback scheduling, captures, rollback and generation changes. The producer has not defined `inferStep` as `Step`, or `supported` as `GrowingReachable`, and must not do so to close the parent. Availability/success and `RenamedAtom` readback premises remain local successful-construction inputs, not whole-source theorems.

Even after that extraction, finite Context syntax depth does not prove global inference termination. The concrete remaining growth obligation is confirmed in `candidate_extrusion.rs:28–160`: `rows` and `structure` memo maps are recreated per invocation. A new parent/copy edge decreases the current level, but separate invocations can create repeated siblings for the same source/polarity/target. A bound on chain depth supplies no bound on that multiplicity.

The native drain runs Context before Dispatch (`lib.rs:14344–14363`). Currentness requires completion of the actual processing relation at the current intrusion generation (`lib.rs:13507` onward). Intrusion merges retain/copy bounds and advance generation (`candidate_intrusion.rs:568–725`), while fresh rows replenish the representative population. Finite source action cursors (`candidate_source.rs:2403–2461`) and per-use occurrence checks do not bound the size of the current graph captured by later uses (`candidate_scheme.rs:4128–4133,4911–4947`).

Closing the original quantified `Acc` obligation therefore still requires a source-derived finite demand/copy supply or another valid well-founded measure that accounts for repeated siblings, live captured graphs, views/weights/scoped maps, complete relation identities, generation invalidation and nested drain return order. Neither strict per-copy level descent nor a finite completed store may be substituted for this construction. No divergent original source program or counterexample is claimed by this review. Soundness, Effect hygiene and principality roots receive no closure claim from this packet.

## Independent verification

Fresh project/cache: `/workspace/scratch/e3678bef96db/native-progress-review-r2/project`. No producer/shared `.olean` artifacts were copied. Pinned executable: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`; Lake reports `5.0.0-src+eb6cafb`, Lean reports `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Checks used `LEAN_NUM_THREADS=1`, project and direct Lean arguments `-j1 -M1024`, owned `TMPDIR`, and 120-second bounds. Three focused checks were used within the eight-check budget.

| Check | Exact command after the environment prefix | Observed result |
|---|---|---|
| 01 | `<lake> --no-cache build +YulangClosure.NativeInferenceProgress` | All 14 modules built; log ends `Build completed successfully (15 jobs).` The exec transport disconnected before the exit receipt, so no numeric process exit is asserted for this call. Subsequent inspection found no surviving compiler. |
| 02 | `<lake> --no-cache env lean -j1 -M1024 YulangClosure/NativeInferenceProgress.lean` | Exit 0, 4.296 seconds, empty output. Independently rechecked the frozen proof after the transport incident. |
| 03 | `<lake> --no-cache env lean -j1 -M1024 NativeProgressOriginAudit.lean` | Exit 0, 1.877 seconds, no warnings. Full originating-declaration audit. |

The origin auditor was read before use. It selects by the environment's module index, includes private/generated declarations, prints actual complete types and transitive axioms, rejects project axioms and nonstandard dependencies, and checks every required authored root is an originating theorem. I independently parsed all begin/end records, checked uniqueness and all 28 required roots, inspected the printed authored theorem types against the source, and compared the resulting complete output hash. The independently produced audit output exactly matches the producer's output bytes.

| Complete census | Result |
|---|---:|
| Originating declarations | 117 |
| Originating theorem constants | 50 |
| Required authored roots | 28 |
| Theorems with no axioms | 16 |
| Theorems using only `propext` | 8 |
| Theorems using `propext, Quot.sound` | 21 |
| Theorems using `propext, Classical.choice, Quot.sound` | 5 |
| Project/unapproved axioms or audit warnings | 0 |

The 14-source dependency scan found only the ordinary native `admit` declaration/constructor names and prose. No proof holes, project axioms, unsafe declarations, native-evaluation assumptions, kernel bypass or increased heartbeat/recursion options were found. No mathematical repair or failed Lean check occurred in this review. The lost exec transport is retained as an execution incident, not a proof failure or a successful exit receipt.

All evidence below remains in `/workspace/scratch/e3678bef96db/native-progress-review-r2`; raw logs are not committed.

| Evidence | SHA-256 |
|---|---|
| `check-01-build.log` | `ee351002d8c36eb5afdc1a2329713e6ad1c421c18eb9b87e2c47363bc7e6e64a` |
| `check-02-module.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `check-03-audit.log` | `7d5e6045c7b67a317a4c9422f5d5ba019fb151a91fa6d2480191ede272cd668e` |
| `project/NativeProgressOriginAudit.lean` | `9f4be3dc13b375998aa9d41b6eee5413e99254bd835eae11afa9371b05b8df38` |
| `checks.json` | `4aa8f2d36d43ec86f24dc8d7bdc891177785ac62bad1462642eb204daaec3198` |
| `inputs.json` | `1a4ca53826b40f90a0506cc23b6cc45b3f17b2dc5e8b8244e8937747a5c27072` |
| `native-inputs.json` | `fa260e9e230e3144a47f6926e7419067ee243cf1c93a9a2d6d6c5f5d97c61ede` |
| `origin-census.json` | `c7b121d5f9f48cdcfc944d3c1f5bf0f1bccdeafa38627aea8b32068afd9dccd0` |
| `static-scan.log` | `fcd903a66e62c9fb90b9c0a1e2f82093221aca433a4f88bb52676c461988017f` |

## Freeze receipt

Accepted only for the frozen local proof and accurately bounded note/handoff above. Root integration owns imports, default-target verification, shared status, commits and pushes. All review checks are finished; no review-owned Lean processes or descendants remain. Reviewer writes stop after freezing this receipt. No original full-root proof or production correspondence is accepted by this receipt.
