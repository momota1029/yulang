# R201 — original literal equation construction

Status: READY FOR ONE READ-ONLY CONSTRUCTION ASSIGNMENT.
Branch / baseline: `yulang3` / `295de848bbd0da59a1df4cdf3dd751a0164412be`.
Primary: `/root` (Luna); model and Git authority stay with primary.

## Objective and parent

Construct the original literal ground/Return interpretation together with an
independent abstract Simple-sub literal generator and solution readout, or
identify the exact equation that cannot be derived from selected source
authority. The target parent remains `SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

No supported payload, scope, event, effect, Call field, or shared witness may
be narrowed. This packet is one model-construction step, not a parent proof or
semantic-adoption gate.

## Frozen inputs

```text
Candidate model: notes/theory/2026-11-01-abstract-inference-model-r199.md
  sha256 f60b89d98ced17cabf860c6dd65aa3929796c85a407c8f82af25607adf0017cb
R200 outcome: tasks/agent-loop/history/abstract-inference-model-r199-outcome.md
  sha256 7b7a3fc1d1a4960ed78dee5befdf9c305d0a02b70091243d4b59995838aec337
Contracts.lean: 2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e
OriginalSourceSyntax.lean: 3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
OriginalSourceGeneration.lean: 126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
OriginalSourceInterpretation.lean: feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef
SimpleSubConstraintSyntax.lean: a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6
PaperExecutionSyntax.lean: d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d
Selected Source-Generalize authority: 46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38
Selected Source-Generalize construction: e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240
Annotation/effect policy: a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18
```

## Required construction

Return one message with concrete definitions/equations for:

```text
GenerateLiteral(Γ, site, literal) = actual type/effect constraints and outputs
SolvesLiteral(d, a)                = independent constraint interpretation
ReadLiteral(Γ, site, literal, a)    = descriptor/value/root/event at same scope
```

Then derive, or stop at the first unjustified equation in:

```text
SolvesLiteral(GenerateLiteral(Γ, site, literal), a)
  → original LiteralDeclaration and ground formation
    ∧ original Return premise
    ∧ original contextual-effect premise
```

All clauses must use the same assignment, occurrence, scope, and event.
`LiteralDeclaration` and `inputs.ground` cannot remain unexplained predicates
whose assumed truth supplies the conclusion. Do not define solving through
`Kernel.atom`, `OriginalSource.Satisfies`, or the desired source judgment.
Reuse the R200 lossless payload map only as data; paper/Core literal typing
does not by itself select the original effectful source row.

Check the construction against literal `0` versus `1`, arbitrary Nat float
bits/bytes and arbitrary strings/paths, and the structural counterexample
`atom(literal) <: α` with `α = top`. These falsify incomplete readouts, not the
original theorem. State the exact connection to the literal induction case
and why the result still does or does not reduce that parent premise.

## Assignment, budget and boundaries

- Owner: one `architect`, read-only. Output is one message to Luna; no files
  are leased to the worker. Luna is the only model editor.
- Budget: at most 900 seconds; no descendants.
- No Lean/Lake, build, test, Rust/native source read, environment, cache,
  target, scratch directory, or changes to existing UNKNOWN/quarantined paths.
- Preserve all current dirty/untracked work and the pending typed-Union bundle.
- If an authentic original primitive/Return/effect law is absent, report its
  exact source equation and evidence. Do not invent new semantics or ask for a
  semantic vote unless a concrete competing accepted meaning is established.
- Any candidate equation that changes the source domain, effect meaning,
  Return behavior, witness, or source rule stops before adoption. A completed
  equation still requires fresh independent model and spec review before any
  theorem activation.

## Success and accounting

Success is either a concrete noncircular equation set with a same-assignment
derivation, or a precise first missing original law that changes the next
construction step. This does not pass the full model gate. Current accounting
remains **0/4 roots; 0/5 packages** until a reviewed theorem result is applied
to an unchanged parent. Principality, termination, source coverage and Rust
correspondence remain separate.
