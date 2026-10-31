# R89 proof handoff — repaired original App inversion

Assignment `R89-PROOF`; candidate/handoff revision **2**; constructed; revision 1 failed the first bounded audit and revision 2 is **UNCHECKED**. Contract revision 1, SHA-256 `c036d191f2748d971862aab638ac92bd7147ac8ff27289a68e35ed1d7c23e45b`; manifest SHA-256 `86727cb01dc42a4b51148e1dff9c75a4f37af01c7862a56afa18eed25ca2a256`. Admission commit supplied by primary: `4781d06da`; manifest source baseline: `e56d1b618c2025859f5ab912d7ba3168634aaaed`.

Actual received task identity: `/root/r88_proof`, resumed with the R89 NEW_TASK. The primary-owned compact state records `/root/r89_proof` as the R89 proof identity/lease owner. This mismatch was reported to `/root`; it is not silently normalized here. Exact writes were directly granted by the R89 packet. Requested model/effort in that R89 state row: `gpt-6.1-sol` / `high`; observed runtime model/effort: **UNKNOWN**. One author, no descendants/coauthors. State/identity reconciliation remains primary-owned.

## Frozen outputs and repair

- `notes/theory/lean/YulangClosure/SourceAppDemandIncidenceR89.lean`: **8,973 bytes**, SHA-256 **`27facf01f86f7a0c86e1ef5160667b1e1b283b909a7b0535857abb182c20aeb5`** (primary revision 2; revision 1 hash: `ae1e029cc2ac1fed98dbb1a9059bb7ed94573df6aa9a35e677bbed51395baa0f`).
- This handoff is the only other write. No scratch/generated/cache/project/environment/worktree or `/tmp` output exists from this leaf.

The sole project import is `YulangClosure.OriginalSourceGeneration`, whose project dependency is `OriginalSourceSyntax`, then pinned `Std`. R88's checker-failing artifact is neither imported nor modified.

The changes to the proof surface are:

1. Conditional App atom uses explicit `AtomKind.roleAndInitialCallOrigin`, resolving the exact R88 dotted-identifier error. The complete five-atom base, optional singleton-formal clause and both checks stay present.
2. `app_rule` now uses `simp only [sourceRules] <;> cases mark.annotation <;> rfl`. The first step rewrites with the actual original builder equation. The remaining reductions handle the actual annotation wrapper, helper lists and endpoints. A bare definitional `rfl` is no longer assumed for the mutual source builder.
3. `app_derivation_iff` keeps its proof structure but removes the two R88 unused annotation-`simp` steps; case analysis already specializes those matches.

A read-only Python comparison extracted each theorem's source statement through `:= by` from R88 and R89. All **four statement texts are identical**; only their enclosing namespace/helper resolution changes from `YulangClosure.SourceScopedJointLiftR88` to `YulangClosure.SourceAppDemandIncidenceR89`. This is textual preservation evidence, not a Lean type/equivalence receipt.

Exact fully qualified declarations, with the unchanged types frozen at their source definitions:

- `YulangClosure.SourceAppDemandIncidenceR89.app_rule`: every original `Mark`, context and callee/argument; original `sourceRules` App equals its complete original core, with the original formation/boundary wrapper exactly when `mark.annotation = some target`.
- `YulangClosure.SourceAppDemandIncidenceR89.app_witness_scope_fields`: every payload type, environment, source site and `ScopedValue`; extending with that ViewLogic payload preserves root, anchors, publications, origin, actual event path, names, replay and initializer entries, and appends exactly the original incoming-path frame.
- `YulangClosure.SourceAppDemandIncidenceR89.app_core_iff`: every local Kernel, original environment/site/context and raw callee/argument; the core judgment iff **one** admitted ViewLogic witness satisfies every generated local premise and both original source children in its same extension.
- `YulangClosure.SourceAppDemandIncidenceR89.app_derivation_iff`: every local Kernel, original environment/Mark/context and raw callee/argument; the complete original App judgment iff its original optional annotation premises hold in the incoming environment and the same existential package above holds at `mark.site`.

The exact Lean signatures are byte-identical to the four signatures in pinned R88 except for enclosing namespace resolution, and are present in the new artifact. The artifact also requests `#print` of all three helper definitions and `#check @...` / full `#print axioms ...` for all four theorems. **No R89 printed type or axiom output exists yet.**

## Governing source, coverage and parent application

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, 7, with the immutable-birth correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Every supported original source program, lawful finite Simple-sub history and actual retained qualified occurrence remains in scope. Native pointwise diagonal lifting and conditional algebraic fiber descent do not establish the required source-scoped joint strategy.

Source definitions remain the selected `notes/design/2026-10-08-source-generalize-definition.md` §§2–3 and construction §§3–5, including actual Call/argument/effect evidence, local L1–L5, fixed dependencies, one Shared strategy, original ViewLogic/EventProof telescopes, publication and lawful independent-use allocation. These are not newly instantiated by this candidate. The original paper's non-let result is not imported as a leveled/full-Call/effect theorem.

Decisive inspected definitions: `OriginalSource.sourceRules` at its original App equation (lines 111–123), `Kernel`, `Local`, `Judgment`, `SourceJudgment`, `Environment.extend`; pinned R88 source/review handoffs and the unchanged parent §§1 and 5. Existing scope/call/native field meanings read in the R88 packet retain their pinned hashes. No research draft supplies a new semantic law.

Represented in the candidate: arbitrary callee/argument syntax and original environments/contexts; both annotation cases; both singleton-formal outcomes; every complete generated App local premise; returned-callee/descriptor Value check; callable-image/synthesis Computation check; both original children; one existential payload; all Environment fields. Nested syntax is retained as the existing full `Source`/`sourceRules`, without changing the source language. The generic Kernel parameter is the original local grammar parameter, not an arbitrary model declared to be concrete Yulang.

No source/native incidence equation, concrete complete-App Kernel instance, admitted birth-qualified extrusion occurrence, pair interpretation, fiber constancy, semantic effect transport, publication/use allocation transport, or whole-source theorem is added. No source case is rejected or removed by these limits.

Application to the original parent: once an actual original App source derivation is supplied by its owning construction, `app_derivation_iff` extracts its full source-side input at one witness, and `app_witness_scope_fields` fixes the incoming Shared/runtime/publication context. This is the App inversion part of the unchanged §5 induction. It cannot presently connect that package to the native selected parent/copy equalities or construct the source-indexed simultaneous substitution.

**First remaining premise: `R88-SOURCE-EXTRUSION-INCIDENCE-1`, now investigated by the R89 source lane.** Owner: primary's actual `candidate_source` → `shadow_apply::admit_candidate_fact` → `candidate_call` → `candidate_context_seed` constructor bridge. It must obtain from the actual construction the original App site/context/callee/argument/environment and complete Call law, relate `ApplySourceInput.introduction`/slot-0 `ScopedDemand` and actual retained `Operation`/`Parent` pairs to that same telescope, and preserve both Value and both Effect ports with original provider/capture/current/receipt/path/consumer/incidence/observation/support data. It must cover absent-introduction cases and the original annotations, publication and lawful-use allocation. IDs, a supplied qualification Bool or four native port labels do not supply that law.

No new R89 source-lane result was supplied to this leaf before freezing. Accordingly no application to an unestablished native constructor is claimed. The primary must consume the separately frozen source result and its exact evidence; any further dependency/statement change requires the fixed amendment path. The candidate neither assumes fiber constancy nor adds a LocalLaws conclusion. A/B, full effects, source/native joint lift, Rust and production remain **OPEN**.

## Actual diagnostics, checks and execution ownership

Material R88 failure evidence is preserved at the pinned review path, SHA-256 `41dde35dcea564d100d06d941f0ae6779028f6f0b610847e648d49d2578379e1`: first primary pipeline failed before input delivery with `FileNotFoundError`; the second Lean invocation exited 1 with ambiguous `.roleAndInitialCallOrigin`, failed `app_rule` `rfl`, and two unused-simp warnings. The old audit reported `propext` for `app_witness_scope_fields`; the other three carried `propext, sorryAx, Classical.choice, Quot.sound` under error recovery. Those are failing R88 receipts, not R89 acceptance or proofs of the bridge. Upstream definition error recovery prevents treating the old signatures as accepted proof evidence.

Actual R89 leaf commands: bounded `cat`, `sed`, `rg`; Python read-only byte/hash checks for **33/33** manifest inputs, all matching; exact four-statement source comparison, all identical; read-only compact-state metadata lookup; candidate size/SHA-256; comment-stripped lexical scan, no `sorry`, `admit`, `axiom`, `unsafe`, kernel bypass or `native_decide` token. Four theorem declarations found. These shell operations returned exit 0 and no timeout. The lexical scan is not a transitive axiom audit or a theorem check.

Pinned project files remain Lean `leanprover/lean4:v4.35.0`, `YulangClosure`, `-j1 -M1024`, no external packages. This leaf invoked **no Lean, Lake, elan, build, tests, compiler or installation**, and created no checker output. Actual R89 executable/version/exit/printed types/full axiom results: **NOT RUN / UNKNOWN**. Calls used by leaf: **0/2**; the primary owns the two direct 120-second checks after exact-hash preflight and fresh independent pre-execution review. The skill checker cannot be used in this envelope because it runs Lake and creates scratch audit files. No default build is substituted.

First explicit R89 observation: `2026-10-31 15:01:39 UTC`; candidate hash observation: `15:03:01 UTC`; final metadata/lexical observation: `15:03:51 UTC`. The environment's local date is 2026-11-01. Launch-to-first-observation elapsed, CPU time and peak RSS were not exposed; primary retains elapsed accounting within the unchanged **1,400-second** proof envelope. No resource reset or unobserved runtime receipt is claimed.

**WRITES STOPPED** on the candidate and this handoff at revision 1. No descendants or running proof/build process; no unaccounted output paths. Only these two newly leased paths were written. Old R88 artifacts, other workers' outputs, Rust, shared status/index/tasks, root imports, toolchain/manifests, rules/configuration, questions and Git were not changed. Frozen bytes await primary intake, independent review and execution; a repair requires a new acknowledged revision.


## Primary repair, revision 2

The first exact Lean call failed at candidate line 41 because field notation `.map` attached ambiguously after the `if` expression. This caused an error-recovery `sorryAx` in the generated premise list and cascading errors in `app_rule`, `app_core_iff` and `app_derivation_iff`. The primary changed only `appPremises` to call `List.map` explicitly over the parenthesized conditional list. No theorem statement or source law changed.

Revision 2 candidate: 8973 bytes, SHA-256 `27facf01f86f7a0c86e1ef5160667b1e1b283b909a7b0535857abb182c20aeb5`. The original author `/root/r88_proof` stopped after freezing revision 1. The primary took ownership of the two exact proof paths for this repair; the first-call failure is preserved in the primary review receipt. The repaired candidate awaits fresh independent pre-execution review. No second Lean call has run.
