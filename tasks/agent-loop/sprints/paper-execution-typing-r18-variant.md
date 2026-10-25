# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r18 — variant introduction and inversion

Status: ADMITTED by Luna after R17.1 review/integration and selector consultation. Revision r1. Branch `research/simple-sub-intrusion`; frozen baseline `e6ff152a983129edbdf3e4d3529d446a50844e38`. Isolated proof candidate only; no production, semantic-adoption, Rust, or main-checkout source rights.

## Original parent and fixed outcome

Parent remains the original full-paper simultaneous type-substitution theorem and the user's goal of Lean proofs for Yulang type inference/executor semantics. Preserve every original quantifier, accepted source/native domain, value-only forall condition, and all prior constructors/premises. R16.2 raw syntax/declaration shift commutation and reviewed R17.1 shared-context forall transport are accepted prerequisites. R17.1 commits `e6ff152a` and handoff/adjudication record the exact accepted artifact.

Add a faithful partial typing rule for paper variant introduction `t(\bar v) : \langle t_j(\bar A_j)\rangle` (manuscript `docs/yulang-operational-type-safety-ja.tex:219`) to the existing six indexed judgments. The rule must expose the matching tag in the output variant row, the corresponding ordered payload-type sequence, the actual payload typing derivation, and arity agreement. Add a genuine inversion result for a derivation of a raw variant value, recovering its matching row/tag/payload-type/arity evidence. Apply the new constructor case to the existing arbitrary simultaneous substitution theorem; preserve and audit all six transport conclusions.

Do not require a fixed ambient scope formation hypothesis that the judgment does not carry. Use only formation/membership evidence justified by the paper and the existing `VariantFormed` definition; keep row/tag uniqueness distinct from payload typing. Do not alter `PaperTypeFormation` or any frozen dependency.

The raw syntax constructor is `Value.variant (constructor : DeclarationId) (typeArguments : List Ty) (payload : List Value)`. The paper's variant-introduction line does not specify the meaning of this explicit raw `typeArguments` field. Preserve it byte-for-byte as syntax and under the existing `mapPaperValue` substitution mapping. Do not guess an equality, infer instance semantics, silently discard the field, or use an unproved premise to make the rule pass. If exact application of the paper rule requires an authority not present in the manuscript, stop with the specific mismatch and keep the variant parent premise OPEN.

## Authority, exact inputs and source correspondence

Governing manuscript `docs/yulang-operational-type-safety-ja.tex` lines 219, 232, 953–977, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; whole-paper typing table and substitution claim remain authoritative. Relevant existing type row: `Ty.variantCons` and `VariantFormed` (`PaperTypeSubstitution.lean`, `PaperTypeFormation.lean`). No semantic decision is granted by this packet.

Frozen direct dependency hashes:
- `PaperExecutionSyntax.lean`: `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`
- `PaperExecutionTypingSubstitution.lean`: `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`
- accepted `PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

Rust correspondence is read-only and secondary. Inspected `tools/inference-playground/src/runtime/program.rs:891` constructs `Instruction::Variant { tag, payloads }`; `machine.rs:729` evaluates the ordered payload list. The inspected path carries neither a declared variant-row typing proof nor raw type arguments. Record this gap; no Rust edit or code slice is safe for this proof-only packet (`NO_SAFE_CODE_SLICE`).

## Leases, lanes and resource bounds

One registered `lean_prover` owns only these outputs in detached worktree `/tmp/yulang-r18-variant` at the frozen baseline:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `.lake/R18Audit.lean`
- `tasks/agent-loop/inbox/paper-typing-subst-r18.md`

The same proof owner may continue related steps only within those files and this contract. Dependencies are read-only; worktree cache is dedicated. No implementation lane is admitted. Luna owns this contract, `current.json`, final calls 7–8, review, adjudication, integration and Git. After freeze, one fresh non-author source-only reviewer may inspect the changed proof seam and retained audits; the 8-call R18 ceiling cannot be exceeded for review.

Maximum 900 active seconds, 8 literal serial Lean/Lake processes and 120 checker seconds. Calls 1–6 construction; calls 7–8 primary final focused build/type/axiom audit. Every process counts, including failed, audit and cleanup calls; one at a time, use Lean `-j1 -M1024`, no reconnaissance/version-only invocation. No R17/R16 call transfers. Primary may not exceed calls 7–8. Keep actual checker time and unknown active-time telemetry honest.

## Success, falsifiers and stop conditions

Success requires: focused build of changed Syntax and TypingSubstitution; exact printed types and complete axiom audits for all six transport theorems, variant introduction/inversion, and a concrete non-head-tag example with ordered payload and exact arity; no `sorryAx`, project axiom, `sorry`, `admit`, or failed dependency; direct application to the original represented variant-introduction premise. The variant example must distinguish the selected tag from another row arm and show payload component order.

Falsifiers: absent/unmatched tag accepted; duplicate tag ambiguity; wrong payload type/order/arity accepted; payload or raw type arguments dropped/reordered under σ; transport restricted to a special substitution; an ambient scope assumption invented; or a proof constructor that changes existing cases or narrows any shared context. The syntax mapping for `.variant` must retain raw constructor identity and map every explicit type argument and payload under the same σ.

Stop immediately if the manuscript does not define how raw `typeArguments` relates to variant row/payload types and the rule cannot be justified without guessing, or if any new authority, dependency, lease, premise or semantic change is needed. Report exact counterexample/mismatch, preserve the failed diagnostics, and leave the full parent OPEN. Complete success closes only represented variant introduction/inversion plus transport support; nominal, switch, remaining paper rules, recursive graph guards, full typing/inference/executor, original A/B, source/native/Rust and production remain OPEN.
