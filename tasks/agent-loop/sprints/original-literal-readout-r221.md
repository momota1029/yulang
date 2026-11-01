# Sprint R221 — original literal interpretation from the same solved assignment

Status: ADMITTED by Luna after exact leases, hashes and resources were fixed.
Branch / baseline: `yulang3` / `d39ec2532e424526d8808dc6fd4ba13b95113766`.
User goal: abstract Simple-sub inference guarantees first; keep the original source domain, A/B claims and L1 literal decision unchanged.

## Parent and decisive outcome

Original target: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

R220 proved and independently reviewed only structural readout from the same
regular graph/reference assignment. Its parent-premise delta is 0. R221 must
construct the original literal interpretation from that same assignment and
apply it to the unchanged literal induction edge. Success is one reviewed
original literal premise removed, with its original source, site, context,
payload, root, event, scope, and shared witness preserved. A definition,
wrapper, or theorem assuming the desired `LiteralAtom` leaves the delta at 0.

## Fixed semantics and exact first interface

Retain Authoritative L1 at `notes/design/2026-11-02-literal-l1-adoption.md`:
all eight raw payloads; descriptor `Value(τ(l))`; value `v(l)`; original root
`r`; event `e₀`; pure `Comp(empty, τ(l))` Return; same scope and witness; all
enclosing checking and contextual-effect obligations. No alternative source
forms are removed.

The first source owner is `OriginalSourceInterpretation.lean`:
`SourceAssignment.row` reads descriptor/value/root at `⟨site, finalRoot⟩` and
retains the assignment Event; `LiteralAtom` consumes a supplied declaration,
ground descriptor and ground row. `OriginalSourceGeneration.sourceRules` emits
`literalDeclaration`. The source syntax distinguishes `synthesis`,
`finalRoot`, and `writtenTarget`; its annotated boundary connects synthesis to
writtenTarget. R220's checked fragment provides only an opaque constructor code
and intrinsic bottom at caller-chosen graph references.

The required equation must map the actual generated literal endpoints and the
same satisfying Simple-sub assignment into the existing original
Descriptor/Value/Root/Event interpretation, establish groundness/declaration
and pure Return, and preserve `q,r,e₀,ξ,ω`. Inspect consumers/callers before any
source-interpreter change. Do not alias ports, select a replacement assignment,
choose new source semantics, or add a law that assumes the desired readout.
Changes to `OriginalSourceInterpretation.lean` are allowed only if they are
definitionally/constructively justified by L1 and existing adopted model
meaning; no change to `Source`, `sourceRules`, accepted alternatives, or
`supported` is authorized.

If the existing carriers and equations cannot construct this readout, freeze
`NO_ADMITTED_CARRIER_INTERPRETATION` with the exact missing field/equation and
semantic owner. Do not call that semantic underdetermination or a
source-qualified counterexample without such evidence.

## Work lanes and exact leases

**Constructive proof (Sol/high, ≤900 seconds):**
- `notes/theory/2026-11-02-original-literal-readout-r221.md`
- `tasks/agent-loop/inbox/original-literal-readout-r221-proof.md`

Construct the actual carrier/endpoints and same-assignment readout from
existing meanings. Use R220's checked theorem and all eight original payloads.
Retain the full source judgement, not a literal-only replacement language.

**Primary source-owner integration (Luna/high, ≤600 seconds):**
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean`
- `tasks/agent-loop/history/20261102-original-literal-readout-r221-outcome.md`
- `tasks/agent-loop/current.json`
- `notes/theory/lean/.lake/build` (sole build/cache owner)

Inspect original interpreter consumers and endpoint callers against the frozen
candidate. Apply the result to the literal edge only if the same-solution
equation is established. No Rust edit or repeated implementation audit; retain
R219's reviewed `NO_SAFE_CODE_SLICE`.

**Lean verification (registered `lean_prover`, ≤1200 seconds):**
- `notes/theory/lean/YulangClosure/OriginalLiteralReadoutR221.lean`

Check the exact admitted module and every delivered theorem with pinned Lean
4.35.0, print complete types and axiom audits. Use the existing project/cache
only. No tests, Cargo, second project/worktree/cache, or `lake update`.

**Falsifier (researcher, ≤300 seconds), after equations freeze:**
- `tasks/agent-loop/inbox/original-literal-readout-r221-falsifier.md`

Hold the satisfying assignment fixed and attack payload/value, duplicate atom
indices, finalRoot versus synthesis/writtenTarget, root, event, annotation
target, Return and shared witness. Distinguish a source-qualified counterexample
from missing construction evidence.

**Fresh review (compiler_referee/spec_auditor, ≤600 seconds):**
- `tasks/agent-loop/inbox/original-literal-readout-r221-review.md`

Review the frozen construction, exact source equations, same-assignment
application, theorem types/axioms, and whether one literal parent premise is
actually removed. No producer or coauthor reviews the result.

## Dependencies, resources and stop conditions

R220 contract and all semantic pins are inherited unchanged; direct inputs are
rechecked before dispatch. Additional pins:

- R220 module: `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254`.
- R220 outcome: `eac0414232cd2afa93b2a10e7f2a6280db6e3489d026baccdb69dca3305c940a`.
- L1 adoption: `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`.
- `OriginalSourceInterpretation.lean`: `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.

Aggregate active assignment budget: 3600 seconds maximum (900 + 600 + 1200 +
300 + 600); no Astra assignment. One heavy process, one verification/cache
owner, `-j1 -M1024`; no budget reset or second cache. Preserve unrelated dirty,
question, UNKNOWN, and quarantined paths. Existing user authorization covers
cache output under the current Lean project.

Stop on reviewed parent application, actual source-qualified falsifier, or the
exact missing carrier/readout equation. Parent delta counts only the first
case. Keep soundness, coverage, principality, termination, full effects and
Rust/native simulation as distinct roots. Next dispatcher consultation is at
frozen model admission, genuine obstruction/counterexample, resource/dependency
change, or sprint closeout.
