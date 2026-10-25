# R18 variant correspondence obstruction — frozen handoff revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r18`, contract revision r1 SHA-256 `d7c0e9b060687dd60aab5ded32f256f4675f71d1a2117df621c998266a9b69ac`. Contract read from primary checkout's committed path `tasks/agent-loop/sprints/paper-execution-typing-r18-variant.md`; that contract is absent from the earlier detached baseline, so no copy or edit was made. Baseline `e6ff152a983129edbdf3e4d3529d446a50844e38`; isolated worktree `/tmp/yulang-r18-variant`.

Role/author/actual worker: registered leaf `/root/r17_forall`, reused for the new R18 assignment; no descendants or contributing authors. Requested role `lean_prover`; observed model/effort/session UUID UNKNOWN. Fresh active receipt sent to primary before any Lean/Lake process. No independent review or semantic authority is claimed.

Outcome: source-correspondence obstruction reached the contract's mandatory stop condition. No theorem construction or proof was attempted, and no mathematical counterexample is claimed. Original full-paper simultaneous type-substitution parent and the variant introduction/inversion premise remain OPEN. The mismatch must be resolved by primary's semantic/source authority owner before a faithful variant constructor can be added.

## Original source and exact existing definitions

The original parent is manuscript `docs/yulang-operational-type-safety-ja.tex` §types, variant rule line219, and simultaneous type-substitution lemma lines953–977. The raw value syntax lines150–155 has `t(\bar v)`. Line219 gives `t(\bar v) : <t_j(\bar A_j)>` with matching tag, correct arity and each payload typed by the corresponding ordered component type. Line109 says constructor/payload type arguments are not erased, but supplies no separate type-argument list for this variant value constructor and no relationship for that extra list.

Current correction `notes/theory/2026-10-24-corrected-core-value-continuation.md` §2 V1(b) and §3 V2 retains simultaneous substitution and same-tag/instance payload typing; it supplies no rule assigning meaning to the extra raw variant type-argument list. This research draft is not used to invent semantic authority. Whole parent `docs/yulang-whole-proof-closure-ja.md` §1 retains original full source scope and shared witnesses.

Lean names, all under `YulangClosure.PaperTypes`:
- `Value.variant (constructor : DeclarationId) (typeArguments : List Ty) (payload : List Value)`, Syntax lines46–47. This has an extra independent field compared with manuscript `t(payload)`.
- `mapPaperValue` variant branch, Syntax lines183–185: retains tag, maps every `typeArguments` element by `mapTypeArguments σ`, and maps every payload by `mapPaperValue σ`, preserving their order. It has no premise that explains what `typeArguments` means.
- `Ty.variantCons (label : Nat) (payloads tail : Ty)` stores the row arm's payload-type sequence.
- `VariantFormed` (`PaperTypeFormation.lean:63–67`) requires `ArgumentFormed scope payloads`, formed tail, and `label ∉ labels`, preserving distinct tag uniqueness and payload formation. It has no raw value/typeArguments index or relationship.
- Existing `PaperValueTyped` lacks variant introduction. Existing transports `PaperValueTyped.subst_explicit`, `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, `PaperContinuationTyped.typeTransport` are unchanged. Their previously accepted R17 proof does not type a currently unrepresented variant case.

No fixed ambient formation assumption was introduced; no constructor or premise was narrowed, dropped or relabeled.

## Precise missing premise and discriminating example

Take the distinct-tag row with first arm tag1/payload `[]`, second arm tag7/payload types `[int,bool]`; take ordered values `[integer3, boolean true]`. The manuscript fixes matching non-head tag7 and arity2 with those ordered payload types. Existing Lean syntax still permits both raw objects:

```text
Value.variant 7 [] [Value.literal (Literal.integer 3), Value.literal (Literal.boolean true)]
Value.variant 7 [Ty.base Base.string] [Value.literal (Literal.integer 3), Value.literal (Literal.boolean true)]
```

These display the same paper term `t7(3,true)` after ignoring the additional list. The cited rule does not determine which such raw objects are admissible or what their extra list means. Neither object's typing or rejection is asserted here. This is an underdetermined correspondence, not an executable or Lean-checked counterexample.

A rule would have to choose whether the extra list is unrestricted annotation metadata, equals the payload-type sequence, is a declaration's instance list, or has a restricted canonical representation. None follows from the cited variant rule or VariantFormed. Treating the list as unrestricted would itself assert that changing it cannot affect typing; requiring equality/emptiness/instance evidence would introduce a new premise or restrict accepted raw scope. The packet explicitly forbids guessing that meaning or silently discarding the field. Consequently I stopped before changing the paper claim or adding an ungrounded typing constructor.

Stable TODO `R18-VARIANT-TYPEARG-CORRESPONDENCE-1`: primary semantic/source authority owner supplies an authoritative raw-to-paper variant correspondence defining typeArguments' role and its substitution action while preserving original supported source scope; alternatively supplies an existing governing source that already determines that relationship. Required falsifier: the correspondence must decide the two displayed raw objects without conflating payload component types with declaration type parameters or losing ordered arity/tag uniqueness. Then an authorized proof packet can construct variant row membership/shape, introduction, inversion, non-head ordered example and arbitrary-σ transport. No such followup is scheduled by this leaf.

## Source/native boundary

Read-only inspected `tools/inference-playground/src/runtime/program.rs:891` emits `Instruction::Variant { tag, payloads }`, with the payload labels in source order. `machine.rs:729` processes the ordered payload list using the tuple evaluation path and retains the variant tag. These inspected instructions do not establish a declared row typing proof or the Lean raw typeArguments correspondence. No native run, Rust edit or production slice was attempted; NO_SAFE_CODE_SLICE remains in force.

## Verification, resources and cessation

Only read-only shell inspections, SHA-256 checks and this handoff write were performed. An initial relative contract lookup failed with `cat: tasks/agent-loop/sprints/paper-execution-typing-r18-variant.md: No such file or directory`; reading the exact assigned absolute primary path succeeded and its hash matched. No proof/checker failure is hidden by this source blocker.

Lean/Lake invocations: 0. Checker seconds: 0. No version/reconnaissance command was run. Toolchain/project files were read: pin Lean4.35.0, library YulangClosure, no external packages, project moreLeanArgs `-j1 -M1024`. Actual running version in R18 is NOT_OBSERVED, since no Lean process ran; previous R17 version receipts are not relabeled as R18 execution. No new theorem types or axiom reports exist; none are claimed. No tests, dependency/global-default changes, compiler edits, Git mutations, scheduling/reviewer appointments or external contact.

All six frozen Lean dependency hashes and manuscript hash were verified unchanged before and after inspection. Neither leased source module was written. No `.lake/R18Audit.lean` or `notes/theory/lean/.lake/R18Audit.lean` was created, and no generated cache output was written by this leaf. The only changed file is this exact leased handoff. Active model-time telemetry unavailable; no invented duration. The source stop occurred before the 900-second bound and without spending the six worker or two primary reserved calls.

STOPPED: no Lean/Lake subprocess session or other command remains running; all read commands returned completion. No children or descendant leases. After this final write, all source/scratch/handoff/cache writes STOPPED. Primary owns intake, any authority resolution and review. This receipt is a frozen source obstruction, not a proved variant rule, independent certification, parent closure or production permission.

Frozen input hashes:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
