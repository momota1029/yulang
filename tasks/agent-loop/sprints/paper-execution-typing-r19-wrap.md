# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r19 — wrap typing and transport

Status: ADMITTED by Luna after R18 source-correspondence adjudication and end-of-sprint selector consultation. Revision r1. Branch `research/simple-sub-intrusion`; frozen baseline `c5d41edcbd5689f0c4365a0b5330b709fed422ee`. Isolated proof candidate only; no production, semantic-adoption, Rust, or main-checkout Lean-source rights.

## Original parent and fixed outcome

The original goal remains Lean proofs of Yulang type inference/executor semantics; the mathematical parent remains the original full-paper simultaneous type-substitution theorem with unchanged scope. R16.2 and R17.1 remain accepted prerequisites. R18 is separately stopped at `R18-VARIANT-TYPEARG-CORRESPONDENCE-1`; this packet neither resolves nor consumes that OPEN premise.

Represent the paper's `wrap` value-introduction rule at `docs/yulang-operational-type-safety-ja.tex:224`, its genuine typing inversion, its direct application as the function of the existing `Call` judgment, and the new case of arbitrary simultaneous type-substitution transport. Preserve the paper's distinct adapter directions exactly:

```text
f : C(A,B) under Γ
a : A   under A' :: Γ
r : B'  under B  :: Γ
-----------------------------------------------
wrap(f,a,r) : C(A',B') under Γ
```

In the Lean de Bruijn environment, the argument adapter computation is typed in `A' :: Γ` with result `A`; the result adapter computation is typed in `B :: Γ` with result `B'`. The wrapped function is typed `callable A B`, and the wrapped value is `callable A' B'`. Do not reverse these endpoints or weaken/remove any premise. The existing `Call` case must apply the wrapped function to a thunk of `A'` and produce `B'`.

The raw syntax is `Value.wrap (function : Value) (argumentAdapter resultAdapter : Computation)` (`PaperExecutionSyntax.lean:53`). Its substitution mapping at lines 192–193 retains the function and maps both adapters by the same arbitrary σ. Preserve this syntax and mapping; no extra fields or semantic choices are authorized.

## Authority, exact inputs and source correspondence

Governing manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; relevant rule line 224, value/computation syntax lines 150–177, original simultaneous substitution claim lines 953–977. The existing Call rule is represented in `PaperExecutionSyntax.lean:731–736`.

Frozen direct dependency hashes:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`
- accepted `PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

Paper rule line 224 explicitly gives the function and both adapter premises, so this scope needs no new semantic authority. No Rust edit or source/native claim is authorized; source/native and production gates remain OPEN.

## Leases, lanes and resource bounds

One registered `lean_prover` owns only these outputs in detached worktree `/tmp/yulang-r19-wrap` at the frozen baseline:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `notes/theory/lean/.lake/R19Audit.lean`
- `tasks/agent-loop/inbox/paper-typing-subst-r19.md`

Dependencies are read-only; the worktree cache is dedicated. Luna owns this contract, `current.json`, final calls 7–8, one fresh independent review after freeze, adjudication, integration and Git. No implementation lane is admitted.

Maximum 900 active seconds, 8 literal serial Lean/Lake processes and 120 checker seconds. Calls 1–6 are construction; calls 7–8 primary final focused build/type/axiom audit. Every process counts, including failed, audit and cleanup calls. Use Lean `-j1 -M1024`, one process at a time, with no reconnaissance/version-only invocation. No earlier packet's calls transfer. Do not launch a call until the worker has matched these frozen dependencies and Luna has recorded a fresh active receipt.

## Success, falsifiers and stop conditions

Success requires a focused build of the changed modules and complete printed type/axiom audits for all six existing transport theorems, the wrap constructor and inversion, and the wrapped-Call derivation. No theorem may use `sorryAx`, a project axiom, `sorry`, `admit`, a failed declaration/dependency, or a narrowed shared context. Apply the new constructor to the original paper premises exactly.

Falsifiers include either adapter direction reversed, adapters typed under a different Γ or `Xi`, an untyped adapter accepted, Call accepting a thunk of `A` instead of `A'`, result type `B` instead of `B'`, or transport restricted to a special σ. The syntax substitution case must retain the wrapped function and map both computation adapters under the same arbitrary σ.

Stop if the exact paper rule requires an authority absent from the cited sources, any new premise/dependency/lease, or semantic/source-scope change. Preserve complete diagnostics for a checker failure and report it without claiming proof. Do not revisit the R18 variant mismatch in this packet.

Success closes only represented wrap introduction/inversion, the stated wrapped-Call derivation, and their transport support. Nominal, variant, switch, remaining manuscript typing rules, recursive graph guards, full typing/inference/executor, original A/B, source/native/Rust and production remain OPEN.
