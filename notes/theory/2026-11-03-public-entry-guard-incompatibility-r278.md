# R278 stage 1: conditional public-entry guard incompatibility

Disposition: **CONDITIONAL_GUARD_INCOMPATIBILITY**. This is an independently checked inversion of the pinned production `assemble` body, conditional on a precisely stated HIR shape. It is not a source-to-HIR derivation, actual witness rejection, R71 application, or parent proof.

## Parent, authority and resource receipt

The unchanged parent is inference/effects soundness → R70 → `R71-RAW-CANONICAL-FIBER-COVERAGE-1`, preserving original Parent/A/B claims, quantifiers, accepted source domain, Simple-sub source/native correspondence, independent satisfying assignments, shared witnesses, F1/FK1 and foreign continuations. Parent/A/B **0→0**; `Need_D`, R71 and full soundness remain OPEN. `NO_SAFE_CODE_SLICE` remains.

R278 contract `26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233`, R277-r2 contract `952973eb7a61e2b0e9866eb54382eceead68956c4eda97cbf723721f6f23fd33`, R277-r2 STOP `cdf5921f2bd763728d01257a3d0b1ba93f8d5ef22625e5ca5c1e3b3c9685ee37`, R277 view `ebeae02540be5811850017b6f8b7ff49783a95e17d2b05358a155bd47bb22b21`, index `8fb7a74c4953d0f78e04f321f437432bbdb9baae811027c555854ade06bfa0da`, ranges `63f2ce9d1ffb2e14a497d89b928065edd955f3ecd2266b0eb51f670fabd4e855`, and 229-entry inventory `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f` matched the pinned hashes. The sole technical body displayed/read for reasoning was indexed `R277-E001`, `crates/yu-solver/src/candidate_receiver.rs:2921–3179`, exactly 9,723 bytes. Its path occurs once in the inventory, with whole-file SHA-256 `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade`; original interval, indexed payload and expected excerpt digest matched. Original source bytes were accessed only for in-memory hash/byte comparison; no original source body was displayed.

Trial identity `/root/sol_r274_source_acceptance`, coordination session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`, requested gpt-6-sol/high, observed model/effort UNKNOWN. Full issued stage-1 reservation of 300 seconds is charged; prior Sol cumulative 11,100 seconds retained, new cumulative 11,400 seconds. No stage-2 source or grant used.

## Backward guard inversion

`R277-E001:2993–3014` first constructs

```text
bindings = [b | item ∈ hir.items(), item = HirItem::Binding(b)]
```

and immediately returns `Err(unavailable())` if `bindings.len() != 2` **or** any `HirItem::Expression` occurs in `hir.items()`. `R277-E001:2951–2953` defines `unavailable()` as `CandidateError::Unsupported`. Since `||` evaluates its left operand first and short circuits, a binding count other than two reaches this return before the expression scan, `answer` lookup, carrier lookup or any later guard. `R277-E001:3156–3161` calls `assemble(&hir, &answer)?` before candidate collection in the public entry, so the same error exits that entry without reaching collection or session startup.

For an admitted `Assembly`, necessary conditions therefore include exactly two top-level `HirItem::Binding` entries and no top-level `HirItem::Expression`; one binding's `definition_root()` must equal `answer` and a different binding must exist as relay (`3015–3024`). Both associated local sources must exist, stay within `SCOPED_RECORD_LIMIT`, have no annotation, and have empty local binding lists (`3023–3032`). The caller source must peel to an Apply of the relay to an Apply of a resolved unit operation to Unit, with the visited source-expression set exhaustive. The relay source must peel to the required Lambda/Catch form, singleton concrete effect row, selected operation arm and fallback binder arm, with corresponding identities and visited set exhaustive. These later requirements are necessary only after the first guard; none is evaluated for the conditional count-one case. `source_operation_match` is outside `assemble` and is not used as a guard premise here.

## Conditional result and exact missing application

Define the precise carrier-shape premise `H_count` as: the HIR returned by production lowering for the fixed source has exactly one item that matches `HirItem::Binding`, namely the root `outer`; nested `my loop`, `my direct` and `my helper` remain local bindings in a `LocalSource` carrier and do not add `HirItem::Binding` entries to `hir.items()`. This is a **hypothesis**, not an authenticated result from R271/R272 prose or a test. Under `H_count`, the computed `bindings.len()` is **1**, whereas `assemble` requires **2**. Thus, for every `answer: DefinitionRootId` and normal execution of the initial vector collection,

```text
H_count(hir) ⇒ assemble(&hir, &answer) = Err(CandidateError::Unsupported)
```

and an application of `solve_receiving_residual_experiment(hir, answer)` exits at its first `assemble` guard before candidate collection. The result is independent of the identity of `answer`; no invented answer is needed to show this conditional. The looser phrase “one root Binding” is insufficient unless it entails the exact filtered count, because additional `HirItem::Binding` entries would change the first guard's value.

The missing premise for an **actual** fixed-witness rejection is the source-to-HIR census:

```text
production parse/lowering of the exact 87-byte source returns hir
∧ count { item ∈ hir.items() | item is HirItem::Binding } = 1.
```

To connect this to a public application with `answer=R`, a later packet additionally needs the production-created `outer` `DefinitionRootId R` and proof that it belongs to that same returned HIR. Neither fact is needed for the first-guard conditional itself. The minimum stage-2 owner set is the exact production lexical/root parser path that establishes one top-level Binding and keeps braced `my` declarations nested, followed by the HIR module-lowering and `HirModule::items()`/definition-root construction path that preserves the one-item census. R277-r2 already identified missing `crates/yu-syntax/src/lexical/lexer.rs::scan_trivia_part` at the live `current_item` callsite; if no independent authenticated token fact replaces that step, its complete production definition and direct helpers are required to justify the source-to-shape implication. Stage 1 neither opens that owner nor assumes its behavior. Luna must pin exact ranges/bytes and decide stage 2 separately.

Prior R277-r2 source-forward attempt stopped at this missing lexical owner; its failure is reused only as a scope warning. R271/R272 shape prose, the R277 fixture-only test body, test assertions/outcomes and a hypothetical private HIR/answer are rejected as premises. No compiler execution, tests, builds, probes, Cargo, Lean, network, scratch/generated outputs, external reads, descendants, source edits, semantics changes or production writes. The only new paths are this note and the leased R278 handoff; writer stops after freeze. No Lean theorem/axiom audit applies to this source-native conditional.
