# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r20 — union elimination

Status: ADMITTED by Luna after R19 acceptance and sprint-end selector consultation. Revision r1. Branch `research/simple-sub-intrusion`; frozen baseline `aafbc15f0f9595eabea2c5187fba75fff06c3d04`. Isolated proof candidate only; no production, semantic-adoption, Rust or source/native rights.

## Original parent and fixed outcome

The original goal remains Lean proofs of Yulang type inference/executor semantics, with the original full-paper simultaneous type-substitution theorem and all source scope unchanged. R16.2, R17.1 and R19 wrap are reviewed prerequisites. R18 remains separately stopped at `R18-VARIANT-TYPEARG-CORRESPONDENCE-1`; this packet does not resolve it.

Represent the paper's union elimination typing rule at `docs/yulang-operational-type-safety-ja.tex:233` in `PaperComputationTyped`, add genuine inversion for the raw `.unionCase`, compose the rule with existing `injectLeft` and `injectRight` typings, and add the constructor case to the existing arbitrary-σ substitution theorem. Exact rule:

```text
v : A ∨ B under Γ
left : C under A :: Γ
right : C under B :: Γ
-----------------------------------------------
unioncase(v, x.left, y.right) : C under Γ
```

Both branches share the same `D`, `Xi`, tail `Γ` and result type `C`; the left binder receives `A`, the right binder receives `B`. Preserve the exact result type equality through inversion. Typing an `injectLeft` or `injectRight` input must use the existing value constructor and the same two branch derivations. These are typing-composition lemmas only; make no claim that either branch executed.

Raw syntax is `Computation.unionCase (value : Value) (leftBinder : TermName) (left : Computation) (rightBinder : TermName) (right : Computation)` (`PaperExecutionSyntax.lean:76–77`). Its substitution mapping retains both binder names and maps the scrutinee and both branches under the same arbitrary σ (`PaperExecutionSyntax.lean:239–241`). Preserve that mapping and all previous typing cases.

## Authority, exact inputs and source correspondence

Governing manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; relevant union elimination line 233 and simultaneous-substitution claim lines 953–977. Existing union introductions are represented at `PaperExecutionSyntax.lean:698–705`; existing Call, force and remaining judgments remain unchanged.

Frozen direct dependency hashes:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `2192b5de98b9af217318dd95db93c6fd4b776e93266f62ec7e4e23402166acb3`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `6c41d59cf9326b2e94e612b62c02448991979d60658a88a001a4e7143bbfefdc`
- accepted `PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

No new semantic authority is needed for the cited rule. No Rust edit or runtime claim is authorized. Do not assume a proof about union typing closes executor/inference safety or source/native correspondence.

## Leases, lanes and resource bounds

One registered `lean_prover` owns only these outputs in detached worktree `/tmp/yulang-r20-unioncase` at the frozen baseline:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `notes/theory/lean/.lake/R20Audit.lean`
- `tasks/agent-loop/inbox/paper-typing-subst-r20.md`

Dependencies are read-only; the cache is dedicated. Luna owns this contract, `current.json`, final calls 5–6, one fresh independent review after freeze, adjudication, integration and Git. No implementation lane is admitted.

Maximum 600 active seconds, 6 literal serial Lean/Lake processes and 90 checker seconds. Calls 1–4 are construction; calls 5–6 primary final focused build/type/axiom audit. Every process counts, including failed, audit and cleanup calls. Use Lean `-j1 -M1024`, one process at a time, with no reconnaissance/version-only invocation. No earlier packet's calls transfer. Do not launch a checker until the worker has matched all frozen dependencies and Luna has recorded a fresh active receipt.

## Success, falsifiers and stop conditions

Success requires a focused build of the changed modules and complete printed type/axiom audits for all six transport theorems, unionCase constructor and inversion, and both injection-composition derivations. The audit must reject `sorryAx`, project axioms, `sorry`, `admit`, failed declarations/dependencies and axioms outside the existing standard allowlist.

Falsifiers include allowing different branch results, switching the left/right binder types, using different `D`, `Xi` or `Γ`, dropping either branch premise, reversing injection evidence, or restricting σ. Transport must preserve both raw binder names and map the scrutinee/branches together under arbitrary σ.

Stop if the exact paper rule requires new authority, a new premise/dependency/lease or a semantic/source-domain change. Preserve complete diagnostics and claim no proof after any checker failure. Do not revisit R18's variant correspondence here.

Success closes only represented union elimination/inversion, left/right injection typing composition and their arbitrary-substitution support. Variant, nominal, switch, remaining omitted forms, recursive graph guards, full paper typing/substitution, inference/executor, original A/B, source/native/Rust and production remain OPEN.
