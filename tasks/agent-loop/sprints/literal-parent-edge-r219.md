# R219 — apply the literal equation to the original soundness parent

Status: admitted bounded research sprint. This continues the user's active goal
and adopts the parent-first plan: abstract Simple-sub soundness before
principality and termination, then source Call/effects and Rust correspondence.

## Fixed parent and accounting

The unchanged original target is

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The original source semantics, quantifiers, `supported` predicate, shared
witness, scopes, effect-hygiene policy, and all four root obligations remain
fixed. At admission: soundness, source-scoped coverage, principality, and
termination roots are 0/4 closed; packages 0/5; parent-premise delta 0.
Count progress only after a reviewed theorem is applied to an original
induction premise. A conditional model or generated formula alone changes no
count.

## Admission gate: reuse R214/R215

Before writing a theorem, incorporate these exact reviewed results:

- R214 rejected the one-sided `atom(typeCode τ(l)) ≤ var(q)` readout by a
  `.top` countermodel. It left the source descriptor/effect readout and same
  original endpoint coordinates open.
- R215 gave the stronger candidate pair
  `atom(code (literalType l)) ≤ var(q)` and
  `var(q) ≤ atom(code (literalType l))`, read as a regular-subtype equivalence
  class. This blocks R214's particular `.top` model, but does not establish an
  injective code, graph-to-source endpoint map, effect-coordinate equation,
  original `Descriptor`, `sameScoped`, or a parent case.

Frozen inputs and hashes:

```text
notes/theory/2026-11-02-literal-independent-equation-r214.md
  9c19d9422b47408a6ee944d04b04ddb22d58047684144dfc276bfa6e5d01c6e9
tasks/agent-loop/history/20261102-literal-independent-equation-r214-outcome.md
  fd1b7570a35d4590db2459d431123bfae649f98ee87a15ac1a3cbadb91d42c65
tasks/agent-loop/history/20261102-literal-independent-equation-r214-review.md
  52cb7663dfa27d71e6b5fce8dbe524764903f7b9cf93395fc82677761f6b4b4a
notes/theory/2026-11-02-source-solution-readout-r215.md
  c3044d07f4290b019e2a181b032e314501ddc1bc9e37e9d8725cec3898973866
tasks/agent-loop/history/20261102-source-solution-readout-r215-outcome.md
  f2cc1c8b57938c989dc9188bb202ba9a34f84f6da949cd9d23740f31db94ac60
tasks/agent-loop/history/20261102-source-solution-readout-r215-review.md
  265dec9f5f565e9e81034d92c261e4ecb5e8f54a5cc2753f65c8a73cf343b4e1
notes/design/2026-11-02-literal-l1-adoption.md
  f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8
notes/theory/lean/YulangClosure/Contracts.lean
  2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
  3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean
  126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean
  feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean
  a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6
notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean
  c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3
```

R214/R215 establish no theorem. Preserve the exact distinction between their
candidate equation and any equation this sprint can prove.

## Required Lean result

Construct an independently generated Value/Effect constraint for each of the
eight adopted raw literal forms, using the same raw payload and original
`(q,r,e₀,ξ,ω)`. Establish, or stop at the first exact missing owner equation:

1. The actual generated value clauses and their satisfaction condition, without
   assuming `LiteralAtom`, source judgment, `Kernel.atom`, or a chosen readout.
2. If using the two-sided R215 candidate, injectivity/agreement of the eight
   type codes with the adopted `PaperTypes.literalType`, and a proved
   regular-subtype readout from the *same* assignment to the original source
   descriptor coordinates. Do not claim graph-node identity from preorder.
3. The pure Return effect equation for the original event/root coordinate,
   with empty intrinsic performed effects and all contextual effects retained.
4. A constructive literal source derivation from every satisfying assignment,
   obtaining the payload value from source syntax and preserving the same
   `(q,r,e₀,ξ,ω)` witness. Apply that construction to the literal induction
   edge of the unchanged `InferenceSoundness` theorem.

The accepted source rule is fixed by the L1 adoption. Preserve all independent
checking, annotation, method and adapter alternatives. Keep synthesis separate
from `writtenTarget`; do not assume exact identity where only subtype bounds
exist. No narrowed source domain or new semantic choice.

A definition, source `Build` equation, theorem assuming `LiteralAtom`, arbitrary
`Kernel.atom`, assumed endpoint map, or conditional `sameScoped` hypothesis
fails the parent gate. If the current abstract problem does not provide an
independent generator/solution interface from which the literal implication
can be derived, stop with the exact missing equation and its semantic owner;
do not disguise it as a helper hypothesis.

## Exact outputs and leases

Primary owns and integrates:

- this contract;
- `notes/theory/2026-11-02-literal-parent-edge-r219.md`;
- `notes/theory/lean/YulangClosure/OriginalLiteralParentEdgeR219.lean`;
- `tasks/agent-loop/inbox/literal-parent-edge-r219-proof.md`;
- `tasks/agent-loop/inbox/literal-parent-edge-r219-source.md`;
- `tasks/agent-loop/history/20261102-literal-parent-edge-r219-outcome.md`;
- `tasks/agent-loop/current.json`.

The registered `lean_prover` may write only the Lean module and proof inbox.
A read-only Rust/source lane may write only the source inbox and may not edit
Rust or run Cargo. The independent `compiler_referee` reviews frozen exact
artifacts; no overlapping writers. No isolated checkout or new package/env.
Reuse the existing Lean project cache; authorized cache creation is allowed.

## Resources and stop boundary

- Primary packet: at most 1,800 seconds.
- Lean proof lane: at most 600 seconds, one CPU; checker and complete axiom
  audit for every accepted declaration.
- Rust/source correspondence lane: at most 600 seconds, read-only, no Cargo or
  Rust build.
- Fresh independent review: at most 600 seconds, read-only.
- Astra: 0 seconds. No semantic authority expansion or user decision is
  requested by this sprint.

Stop at the reviewed parent-premise reduction, exact missing source equation,
reviewed falsifier, or resource bound. Record literal parent delta separately
from root/package closure. Rust/native simulation remains a later bridge; no
production promotion in this sprint.
