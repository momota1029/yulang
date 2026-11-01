# Sprint R220 — abstract Simple-sub literal generation and same-solution readout

Status: ADMITTED by Luna after resolving the source authority, exact output paths, dependencies, resource bounds, and cache ownership.
Branch / baseline: `yulang3` / `6f3656d9ae0214721df9e160e7ae69ba29ee773f`.
Authority: unchanged `Contracts.lean:128–130` `SourceProblem.InferenceSoundness`; R199 fixed abstract-model direction; R213 source-independent model inventory; adopted L1 literal semantics; user-approved abstract-first research plan.

## Original outcome and success evidence

The original root remains, without changing its source domain or quantifiers:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This sprint targets the first constructor premise in the literal induction edge. Construct a source-independent Simple-sub literal producer and an independent regular-solution interpretation. For all eight raw payloads, every assignment satisfying the generated Value and intrinsic Effect constraints must read back at the original site to the L1 descriptor/value/pure-Return facts, retaining the original root, event, scope and one shared witness. The producer cannot inspect `sourceJudgment`, `LiteralDeclaration`, `Kernel.atom`, solver output, or a chosen readout. The consumer cannot exchange the satisfying assignment for another one.

Use the existing structural term/store algebra and regular graph interpretation only where their exact definitions entail the needed result. Keep `synthesis` separate from `writtenTarget`; keep intrinsic empty Effect separate from contextual permission, inflow, residual, Call and future obligations. Do not narrow `supported`, replace original endpoints, add an axiom/assumed local law, or define source admission as generated satisfaction.

Success requires: (1) frozen equations for the independent literal generator and denotation, with all eight payload cases and endpoint map; (2) a kernel-checked theorem deriving the L1 local source facts from the same satisfying assignment, with printed theorem type and complete axiom audit; and (3) actual application of that theorem to the unchanged original soundness induction premise, reviewed against the source rule. Only (3) may reduce the parent count. If a concrete descriptor/root/event equation is missing, stop at that exact interface and report it without postulating a bridge.

Before state: parent-premise delta 0; roots 0/4; packages 0/5; hygiene theorem delta 0. After state is measured only by the reviewed original premise actually removed. A model note, conditional theorem, or local graph lemma alone leaves these values unchanged.

## Two continuing lanes

**Constructive core:** Astra proof lane, bounded to the actual abstract Value/Effect producer, regular denotation, literal same-solution implication, and parent application. Use existing approved structural and L1 definitions. No new semantics choice is authorized.

**Independent falsifier:** Sol/research lane on a separate handoff. Attack the exact generator/readout candidate for a satisfying assignment that loses atom identity, confuses an endpoint, changes the source row/witness, or erases contextual effects. Do not duplicate the constructive proof or edit its owned note/module.

After the candidate equations are frozen, a registered `lean_prover` owns the exact Lean module path and verifies the theorem with the pinned project and existing cache. Build/check ownership is singular and sequential. If the equations cannot connect to original descriptor/event/root fields, return the precise premise to Luna; do not prove only a renamed `Build`/`Kernel.atom` wrapper.

Implementation lane: R219's audited candidate-source/admission owners found `NO_SAFE_CODE_SLICE` for this mathematical gap. Reuse that result; no Rust edit, source lease, or repeated owner audit is admitted in R220. Rust correspondence remains later than the abstract proof.

No change to Call, contextual effects, annotation policy, source syntax, or accepted source alternatives. These remain represented in the unchanged parent and are not discharged by this literal edge.

## Permissions, resources and leases

Exact output leases, all on this branch and only for the named owners:

- `notes/theory/2026-11-02-abstract-generator-denotation-r220.md` — primary integration.
- `notes/theory/lean/YulangClosure/AbstractGeneratorDenotationR220.lean` — registered `lean_prover`, only after candidate equations are frozen.
- `tasks/agent-loop/inbox/abstract-generator-denotation-r220-proof.md` — Astra.
- `tasks/agent-loop/inbox/abstract-generator-denotation-r220-falsifier.md` — Sol/researcher.
- `tasks/agent-loop/history/20261102-abstract-generator-denotation-r220-outcome.md` — primary closeout.
- `tasks/agent-loop/current.json` — primary only.
- `notes/theory/lean/.lake/build` — primary build owner only; use the existing project cache path. The user explicitly authorized new cache generation. Do not create a second project/worktree/cache.

Dependencies are frozen by SHA-256: R199 model `33d0cd52fbbf07d7916804f8b8961c102b53cc1cf5e9260ac15d83de9f295aa0`; R213 model `17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e`; R219 result `a88fd7ec4c0e85850a384220776d6c32d1a480e3923ba8b278ac716aea1fbb18`; L1 adoption `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`; `Contracts.lean` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; `OriginalSourceSyntax.lean` `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`; `OriginalSourceGeneration.lean` `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`; `OriginalSourceInterpretation.lean` `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`; `SimpleSubConstraintSyntax.lean` `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`; `SimpleSubRegularSolutions.lean` `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`; `SimpleSubRegularPublication.lean` `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99`.

Resource bounds: Astra ≤900 seconds; falsifier ≤600 seconds; Lean construction/check ≤1800 seconds after frozen model admission; fresh independent review ≤600 seconds; one heavy process and one CPU/RAM owner at a time; no Cargo, tests, runtime experiment, worktree, or second cache. Total active assignment budget ≤3900 seconds. Record requested and observed model/effort separately; unknown metadata stays UNKNOWN.

Stop on successful reviewed parent application, exact missing original model equation, falsifying satisfying assignment, or budget/session/user stop. Preserve all unrelated dirty/quarantined files. No author may enlarge its paths or change source meaning.

## Frozen seam and integration

Freeze the candidate model and all direct dependency hashes before Lean checking. The independent reviewer must be fresh and not a constructive coauthor; review the generator for non-circularity, all eight cases, same-assignment readout, source endpoint/witness preservation, contextual-effect separation, parent application, theorem type and complete axiom audit.

The original soundness parent stays OPEN unless its literal premise is actually removed. Principality, termination, remaining source constructors/Call/effects, and Rust/native correspondence are separate OPEN gates. A reviewed R220 result updates only its actual parent-premise delta.

Checkpoint only the explicit R220 artifacts plus primary state. Run `python3 tools/agent_sprint.py check`; Lean checker/build is allowed only for the exact module and pinned project. No unit tests were requested. Next dispatcher consultation is at proof/model admission seam, genuine counterexample, authority/dependency/lease change, or sprint closeout.
