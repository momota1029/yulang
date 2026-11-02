# R232 — original literal generation and arbitrary-solution readout

Status: ACTIVE, primary-owned model construction; theorem activation CLOSED.
Branch / baseline: `yulang3` / `05586b1473e3194b80fb5ce7b30c531875e27929`.
Authority: the unchanged original roots in `Contracts.lean:128–154`, the
adopted Simple-sub algorithm, and the user-approved
`notes/design/2026-11-02-literal-l1-adoption.md`.

## Fixed outcome

Construct the literal case of the fixed abstract generation/satisfaction /
readout model used by the unchanged `SourceProblem.InferenceSoundness` root:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

No source form, quantifier, original coordinate, annotation boundary,
contextual effect obligation, or shared witness may be removed. The result is
successful only if it supplies the actual literal induction premise from the
same arbitrary satisfying assignment and applies it to the unchanged parent.
Otherwise record the exact missing equation and parent delta 0.

## Fixed source meaning and candidate equation

The adopted source rule fixes, for each payload-preserving literal `l`,
`τ(l) = PaperTypes.literalType(p(l))` and
`v(l) = PaperTypes.Value.literal(p(l))`, with all eight constructors:
Unit, Bool, Int, Float, String, Bytes, Path and Char. At the original
`(q,r,e₀,ξ,ω)`, it fixes

```text
row = ⟨Value(τ(l)), v(l), r, e₀⟩
Return(row) = ⟨Comp(empty, τ(l)), v(l), r, e₀⟩.
```

The independent generator candidate must allocate value/effect coordinates
from source syntax and scope, before solving and without source typing. For a
fresh pair `(α(q,r,ξ), ε(q,r,ξ))`, the native-inspired structural candidate
is the reciprocal value pair

```text
α(q,r,ξ) ≤ atom(BaseCode(τ(l)))
atom(BaseCode(τ(l))) ≤ α(q,r,ξ)
```

and pure-effect pair

```text
bottom_effect ≤ ε(q,r,ξ)
ε(q,r,ξ) ≤ empty_effect.
```

The actual equation must use the approved abstract syntax and algorithm, not
assume these strings as a premise. It must specify an injective, scope-safe
coordinate allocator; the exact `Term` constructors for every base type and
empty effect; identity/noncollision conditions for any `atom` IDs; and the
literal's exact original ports. Equal constructor tags alone do not identify
payloads: the semantic value must remain `v(l)`.

The readout candidate takes an arbitrary satisfying valuation `ρ` of the
generated constraints and interprets it at the original occurrence. It must
derive from those constraints, not posit, that the read descriptor is
`Value(τ(l))`, that the row carries the syntax-fixed `v(l)`, that the root and
event are the original `r,e₀`, and that pure Return is
`Comp(empty,τ(l))` at the same scope and shared witness. Annotated literals
must still read synthesis and finalRoot separately and derive the original
boundary to writtenTarget. All enclosing permission, inflow, residual, Call,
guard, future and conversion obligations stay in the same judgment.

## Decisive model questions to resolve

1. Does the approved Simple-sub model contain a typed, injective interpretation
   of base-type atoms and empty effects into the original descriptor/effect
   carriers, with a `Sub` satisfaction theorem strong enough to recover exact
   literal equality from reciprocal bounds?
2. Is source-to-coordinate allocation already fixed by the abstract
   algorithm, including collision avoidance with arbitrary source atoms and
   distinct ports, or would this require a new algorithm/semantic choice?
3. Can every valuation of the generated constraints be read into the original
   `SourceAssignment` without assuming `LiteralAtom`, `sourceJudgment`, a
   chosen typing, or successful native readback?
4. Can the result derive the pure Return and same `(q,r,e₀,ξ,ω)` witness while
   preserving annotation and contextual boundaries?

If an answer depends on a source meaning that the current authority does not
fix, stop at its exact typed equation and owner. Do not add that equation as a
theorem hypothesis or silently extend the language.

## Frozen direct dependencies

| Source | SHA-256 |
|---|---|
| `notes/design/2026-11-02-literal-l1-adoption.md` | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `AbstractSimpleSubCore.lean` | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| `notes/theory/2026-11-02-root-first-simple-sub-plan.md` | `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16` |

## Leases and resource boundary

- Luna only: this contract, `notes/theory/2026-11-02-original-literal-equations-r232.md`,
  `tasks/agent-loop/inbox/original-literal-equations-r232-model.md`,
  `tasks/agent-loop/current.json`, and the outcome record.
- Fresh read-only reviewer only: `tasks/agent-loop/inbox/original-literal-equations-r232-review.md`.
- No Lean/Rust source output lease and no theorem activation.
- No builds, tests, Lean/Lake, Rust/Cargo, scratch files, worktrees or new
  caches for this model gate. Existing cache may be used only if the later
  approved proof packet requires a pinned Lean check; user has authorized its
  growth. No cache growth is needed here.
- Keep all existing UNKNOWN writers and quarantined paths unchanged.
- Primary work envelope: 1,800 seconds. Independent review: at most 600
  seconds. Zero Astra.

## Review, metric and stop condition

Freeze the construction and dependencies before fresh independent review.
Review must attack payload collisions, arbitrary valuations, atom identity,
coordinate/port allocation, annotated-literal boundaries, ground/readout
assumptions, Return incidence, and preservation of the enclosing witness.
Acceptance requires actual independent definitions and a derivation that does
not use `LiteralAtom`, source satisfaction, native solver success, or assumed
readout equations. A clean review of an incomplete finding does not activate a
proof.

Success metric: count a parent-premise reduction only after the reviewed result
is applied to the literal constructor in the unchanged `InferenceSoundness`
proof. If the original carrier embedding or allocation equation is absent,
finish as `MODEL-INCOMPLETE`, with the exact equation owner, no new premise,
and delta 0. Do not proceed to another equivalent local lemma.
