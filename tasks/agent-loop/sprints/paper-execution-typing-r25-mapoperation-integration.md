# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261026/r25 — mapOperation typing integration

Status: CANDIDATE; no writer/checker may act before exact contract hash, fresh runtime receipt, leases and committed acknowledgement.
Branch: research/simple-sub-intrusion
Baseline: 70c3d29f76fa54f209fe8271e2ca25f079f26acf (R24 accepted as reviewed prerequisite)
Contract revision: r2

## Parent and selected outcome

The unchanged parent is the original full-paper simultaneous type-substitution theorem at docs/yulang-operational-type-safety-ja.tex:953–977, followed by inference/executor semantics and original A/B obligations. R24 is an accepted prerequisite only for the separate operation mapper adapter evidence. R25 targets the missing connection from those adapters to the mapOperation computation-typing judgment.

Before semantic edits, audit the exact manuscript rule and source representation. Manuscript :694–719 fixes same-family/member source/target instances, payload direction P(source) → P(target), response direction Q(target) → Q(source), same mapper, and both actual code typings with matching operation signatures. Manuscript :1024 and :1109 treat mapop as preserving the normal result type while transporting operation instance/continuation types and composing payload/response code with ordinary let typing. The Computation.mapOperation body mapper raw syntax exists at PaperExecutionSyntax.lean:83,248; the partial PaperComputationTyped judgment has no mapOperation constructor. If the body result type or exact connection to the R24 relation is not source-justified, freeze the precise authority blocker and stop before editing accepted source modules.

## Fixed typing rule and proof outcomes

If that source gate passes, extend only the existing PaperComputationTyped judgment with one mapOperation constructor. It must preserve the body result type and require all of:

1. The body derivation PaperComputationTyped D Xi Gamma body resultType.
2. The exact R24 mapper premises: one resolved declaration; source and target witness lists each of declaration arity; full source and target equalities to that same declaration's instantiate results, retaining OperationInstance.typeArguments = argsSyntax witnesses; payload derivation under source.payloadType :: Gamma returning target.payloadType; response derivation under target.responseType :: Gamma returning source.responseType.
3. The same D, Xi, and captured Gamma in the body and both adapter derivations; only the adapter input formal is consed at the head of its code environment.

The new upper module YulangClosure.PaperMapOperationIntegration must import accepted R24 evidence after the revised Syntax and TypingSubstitution modules, without making either lower module import R24. Prove exact inversion and the following proposition, with unchanged resultType:

    PaperComputationTyped D Xi Gamma (.mapOperation body mapper) resultType ↔
      PaperComputationTyped D Xi Gamma body resultType ∧
      MapperPlanTyped D Xi Gamma mapper

Prove arbitrary-σ transport through the new constructor in the existing six-judgment substitution proof. The R24 relation's exact-instance premises must coincide with the new constructor's premises; do not weaken the iff to a one-way implication or use a different declaration/witness set in adapter evidence.

Preserve every existing transport theorem type and constructor/premise outside this one admitted mapOperation case. Re-audit the six judgments and their complete axiom reports, the R24 mapper relation/transport/polarity theorems, the new constructor/inversion/iff and both operation-instance substitution dependencies. No sorryAx, project axiom, failed declaration or narrowed substitution scope is permitted.

R25 does not prove one-step mapOperation execution preservation, request/frame/continuation composition, response plugging/freshening, term substitution, template-body caller embedding, R18 variant correspondence, full inference/executor, A/B, source/native/Rust or production readiness. No Rust or implementation change is authorized; NO_SAFE_CODE_SLICE remains.

## Success evidence and falsifiers

Success requires source-grounded body-result preservation and rule mapping; exact inversion and the bidirectional statement above; all six original arbitrary-σ theorem types unchanged and checked; the R24 results still type-check under the extended judgment; a focused build and complete axiom audit; a fresh independent M1 source/spec review with no blocking/major issue.

Falsifiers: different body result type; only one direction of the iff; adapter result/direction reversed; contexts not sharing D/Xi/Gamma; different operation declarations or dropped type-argument encoding; transport failing for arbitrary σ; any changed existing transport statement; unsound/unapproved axiom or mismatch with manuscript. Any ambiguity stops at a frozen handoff, not an invented premise.

## Leases and lanes

Only after an actual worker/session receipt and committed acknowledgement, one registered lean_prover may write in detached worktree /tmp/yulang-r25-mapop at this baseline:
- notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
- notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
- new notes/theory/lean/YulangClosure/PaperMapOperationIntegration.lean
- notes/theory/lean/.lake/R25Audit.lean
- notes/theory/lean/.lake/build (dedicated cache in this isolated worktree; worker owns it during construction, then stops and hands it to primary before final verification)
- tasks/agent-loop/inbox/paper-typing-subst-r25-worker-checks.txt
- tasks/agent-loop/inbox/paper-typing-subst-r25-primary-verification.txt
- tasks/agent-loop/inbox/paper-typing-subst-r25.md

R24 module and all other dependencies are read-only. Worker must source-audit first; if blocked, write only the handoff and stop. If the source gate passes, continue within this packet through the constructor, transport case, inversion/iff, exact audit source and handoff. No child agents.

Worker is the sole checker/cache owner during construction and may use the leased isolated .lake/build and worker-checks receipt within its 10-call cap. After a frozen handoff and actual STOP/cessation receipt, the primary takes sole ownership of that exact isolated cache path and a separate tasks/agent-loop/inbox/paper-typing-subst-r25-primary-verification.txt path for the final focused build and final exact audit (2 calls). Run these exact commands, serially, with the existing lakefile Lean options; do not pass Lean flags as Lake build options:

    lake build +YulangClosure.PaperMapOperationIntegration
    lake env lean -j1 -M1024 .lake/R25Audit.lean

One fresh non-author reviewer, only after freeze, may write tasks/agent-loop/inbox/paper-typing-subst-r25-review.md; reviewer runs no checker. No overlapping checker/cache owner.

## Inputs and frozen hashes

    docs/yulang-operational-type-safety-ja.tex  a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
    notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean  e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932
    notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean  3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41
    notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean  568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a
    notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean  175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77
    notes/theory/lean/YulangClosure/PaperTypeFormation.lean  29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13
    notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean  02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861
    notes/theory/lean/YulangClosure/DeclSubst.lean  f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258
    tasks/agent-loop/inbox/paper-typing-subst-r24-adjudication.md  0f8ef9853dfeb07a194b0bb74d4bcb3c9bea667225b1af856a831668ed28e4c5

The primary revalidates all input hashes in the isolated checkout before acknowledging worker launch. No dependency edits or new package imports.

## Resource and stop contract

Envelope: 1800 active seconds including source intake and review; 12 literal serial Lean/Lake invocations total, 180 checker seconds; worker cap 10 and primary reserves 2; one heavy build at a time, pinned Lean 4.35.0, LEAN_NUM_THREADS=1, Lean -j1 -M1024; any Lake/Lean version query counts as one invocation. No tests, default/full build, Rust build, dependency/network activity or generated cache shared with another owner. Failed commands count. Stop at the first source ambiguity, semantic choice, failed check, budget edge, authority/dependency/lease change, STOP or session end. Preserve R23/R18, the original parent and all other OPEN gates.

Review mode M1: one fresh non-author checks the frozen rule against manuscript, exact iff/inversion, recursive transport case, unchanged six statements, R24 relation correspondence, full audit output and remaining gates. Convergence requires no blocking/major finding or one bounded repair plus re-freeze and delta review.
