# Sprint PAPER-TYPE-BETA-EXECUTION-20261026/r52

Status: RUNNING; bounded proof slice for the manuscript's explicit type-application beta step. This sprint does not adopt or invent language meaning. The user withdrew two unrelated semantic question bundles; no answer is requested or required.

Branch: `research/simple-sub-intrusion`  
Baseline: `9272dcffc59c7dd3830802772417b311829c8bed`  
Authority: `docs/yulang-operational-type-safety-ja.tex`, execution typing rules at lines 2063–2065 and the execution-type preservation proof at line 1101 (type application uses the simultaneous type-substitution lemma); corrected value/type substitution account in `notes/theory/2026-10-24-corrected-core-value-continuation.md`, V1(b). This packet formalizes only the explicitly written administrative reduction `(Λα.v)[A] → v[A/α]` in the existing represented judgment. It does not change the source language or claim whole-language correspondence.

## Original outcome and success evidence

Parent goal: complete proofs for Yulang inference and executor semantics, preserving original claims and source domain. Relevant bounded premise: a type-application beta step must preserve the existing `PaperValueTyped`/`PaperComputationTyped` judgments after capture-avoiding simultaneous type substitution.

Success evidence is an executable `typeBetaValue` on the existing raw constructors, a checked cancellation theorem for the exact shared contexts moved by type abstraction (`DeclarationTable`, graph environment, and type environment), and a checked applicability/preservation result derived from `PaperValueTyped.typeTransport`. The declaration-table result must include registered template bodies; environment list-map cancellation alone is insufficient. Also show `force ((Λα.delay M)[A])` as two reductions—type beta followed by force—and preserve typing for each step. Record full theorem types and complete axiom audits.

Preserve distinct type argument, body type, and result type quantifiers from the existing judgments. Do not assume context cancellation, restrict the theorem to an empty declaration table or closed value, introduce axioms/sorry, or identify the two reductions as one step. General owner renaming, missing scope/metadata laws, full machine correspondence, full executor preservation, inference A/B, and production remain OPEN.

## Fixed inputs

- `PaperExecutionBinderLaws.lean` SHA-256 `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `PaperExecutionTypingSubstitution.lean` SHA-256 `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `PaperTypeSubstitution.lean` SHA-256 `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `PaperExecutionSyntax.lean` SHA-256 `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `PaperTermSubstitution.lean` SHA-256 `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- `DeclSubst.lean` SHA-256 `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R49 `PaperPerformLetExecution.lean` SHA-256 `2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0`
- Lean toolchain: `leanprover/lean4:v4.35.0`; pinned project manifest/config must match the baseline. Source rule and corrected note are read-only inputs.

## Proof lane and method

Owner: one registered `lean_prover`, no descendants and no Astra lane. Work in isolated exact-baseline copy `/tmp/yulang-r52-type-beta`; primary verifies its HEAD and every input hash before launch. The new module is `YulangClosure.PaperTypeBetaExecution`. Reuse the existing simultaneous substitution and `Nat.strongRecOn`/common-size approach where applicable; generalize by binder depth. Prove cancellation structurally for raw value/computation syntax and every declaration-table member, including template body substitution under formal binders. Then apply the existing checked type transport theorem. Treat nested forall/μ shifts, ambient versus formal template binders, and all template bodies as required adversarial cases.

Exact worker outputs, all confined to `/tmp/yulang-r52-type-beta`: new module; `.lake/R52Audit.lean`; one optional probe; complete command/output files and worker log; `paper-type-beta-r52.md` handoff. Existing shared files and the repository worktree are read-only to the worker. No implementation lane is authorized (`NO_SAFE_CODE_SLICE`): inspected `program.rs`/`machine.rs` evidence does not establish an approved direct source correspondence for this paper rule.

## Resources, verification and stop conditions

Total new grant: **1800 active seconds, 14 literal Lean/Lake calls, 180 checker seconds**. Worker: **1200 s / 10 calls / 120 checker s**; Luna primary: **420 s / 4 calls / 60 checker s**; fresh independent reviewer: **180 s / zero checker calls**. Version queries count as calls. Each process uses project `-j1 -M1024`; worker must resolve Lake with `elan which lake`, invoke the resolved absolute Lake, and run `lake env lean --version`. Build dependencies before the direct strict audit. Include complete stdout/stderr, exact argv/cwd/exit, monotonic durations and hashes; use monotonic durations for resource accounting. At most two construction failures. Stop on failed pinned-input verification, build/audit failure after the allowed repair bound, cap, timeout, unexpected theorem premise, or authority mismatch; preserve all failed evidence and report the exact remaining premise.

Primary runs the strict declaration/type/axiom audit and root integration build within its separate grant. Fresh independent `compiler_referee` review checks the frozen proof against the stated paper rule, complete theorem statements, all cancellation cases including template bodies, and the exact audit before Luna integrates. Any BLOCKING/MAJOR finding stops integration; batch at most one repair only if remaining resources and contract allow. Tests are not in scope.

## Frozen seam and parent application

Only after reviewer CLEAN and Luna adjudication may the byte-identical module be copied to `notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean` and exactly one root import be added to `notes/theory/lean/YulangClosure.lean`. Run `python3 tools/agent_sprint.py check`, update compact current state and a primary integration receipt, then inspect the full outbound commit range before push. The theorem can close only this represented type-beta preservation slice. Source-to-Lean realization, broader V1, full state/graph metadata, administrative-step coverage for other constructors, handlers/effects, whole executor, inference A/B, and production remain OPEN. The withdrawn questions remain `WITHDRAWN_BY_USER`, excluded from Git staging, with their related gaps OPEN. Keep all eight legacy reservations quarantined.

Next dispatcher boundary: after the reviewed outcome, any genuine proof obstruction/counterexample, authority/dependency/lease change, or parent replanning. Internal lemmas and routine checker receipts do not trigger another dispatch.
