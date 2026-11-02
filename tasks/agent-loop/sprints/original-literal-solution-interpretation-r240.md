# Sprint R240 — original literal solution interpretation

Status: ADMITTED for primary model construction; proof-worker activation is
gated as specified below.
Baseline: `4f7e8348e03fc338467101b8bea09de08b483b5e` on `yulang3`.
Unchanged parent: `SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`.

## Fixed outcome and quantifiers

Construct and check the literal constructor bridge for all eight original
payload forms. The bridge must start from the adopted R237 generated result
and an arbitrary independent satisfying assignment, derive the original L1
literal declaration and intrinsic pure Return at the same original
occurrence/root/event/scope/shared witness, and consume that result at the
actual literal-rule application. Do not replace the parent root or its
quantifiers with this constructor theorem.

The abstract equation is adopted in
`notes/design/2026-11-02-canonical-literal-generation-adoption.md`.
The reviewed proposal hash is
`d5162f2cf08eda28455d0a086205811c12c26d2bf99dff92712ef87934bb3eab`.
Rust correspondence remains separate and unclaimed. The typed-Union question
remains untouched and pending.

## R239 gate adjustment, limited to this constructor

R239 prohibited proof activation before one complete concrete Yulang model.
For this sprint only, replace that activation condition with the following
constructor-level gate: Luna must first freeze (a) a generated literal result
whose equation is independent of source judgments and solver success, (b) an
independent satisfaction relation for arbitrary assignments, (c) a
noncircular interpretation of all result fields into the original carrier
row, and (d) the exact original literal-rule consumer and theorem type. The
consumer must preserve distinct synthesis, written-target and final-root
ports and must retain the enclosing contextual-effect obligations. A fresh
reviewer must pass this model seam before a proof worker is activated.

This versioned adjustment permits one actual source-constructor premise to be
proved and applied. It does not waive original source-domain, effect hygiene,
same-witness, review, root-quantifier or non-promotion boundaries. It does not
claim the full `SourceProblem` is instantiated.

## Success and parent accounting

Required checked theorem shape:

```text
adopted generated literal result + arbitrary independent solution a
  → original L1 declaration and pure Return under that same a
  → exact original literal-rule consumer at the same source coordinates
```

No `LiteralAtom`, source judgment, groundness/readout law, desired witness or
successful native run may be supplied as a premise in place of its
construction. The model must distinguish the source synthesis, written-target
and final-root endpoints. It must represent the literal's intrinsic empty
effect without erasing contextual permission, inflow, residual or Call
effects.

Parent-premise delta is zero until the checked constructor result is consumed
inside the unchanged parent proof. If the exact consumer cannot be inhabited
without identifying distinct ports or assuming a missing original law, stop
at that equation, report delta zero, and retain all eight literal forms.

## Exact output leases and owners

Luna owns the frozen constructor model:

- `notes/theory/lean/YulangClosure/OriginalLiteralSolutionModelR240.lean`

After the model gate passes, one registered `lean_prover` owns:

- `notes/theory/lean/YulangClosure/OriginalLiteralSolutionInterpretationR240.lean`
- `tasks/agent-loop/inbox/original-literal-solution-interpretation-r240.md`

Luna owns this contract, the authority record, `current.json`, verification
using the existing `notes/theory/lean/.lake`, independent reviewer assignment,
adjudication, staging and Git. No descendants. The two output paths were
absent before admission. No Rust write lease is issued; the bounded source
surface record remains evidence only. Do not touch the pending typed-Union
bundle or quarantined runtime files.

## Resources and checks

- Proof construction: at most 2,400 active seconds.
- Fresh source/model review: at most 600 seconds.
- Zero Astra; one proof worker; reserve review/integration capacity.
- Pinned Lean 4.35.0 / Lake 5.0.0; existing cache only, growth at most 64 MiB.
- At most two targeted Lean checks, run by Luna after frozen review.
- No tests, Rust builds, new cache paths, worktrees, environments, targets or
  scratch directories.

The pre-existing R209 capacity override is already applied to its exact 15
UNKNOWN identities. Do not apply it again or count its slots twice. All
UNKNOWN observations and quarantined paths remain intact. The live roster was
synchronized before this admission; no affected child or active coordinator
was RUNNING/WAITING at the roster check.

## Review seam and stop conditions

The independent reviewer checks the exact adopted authority, generated result,
independent satisfaction, carrier map, actual original consumer and all
coordinates. Reject Paper/original-carrier aliasing without an interpretation,
any `LiteralAtom`/source-typing assumption, lost checking alternatives,
contextual-effect reset, selected/principal/native-success substitution or
second witness. Primary verification includes complete theorem types and
axiom audits for the exact checked declarations.

Stop before proof-worker activation if the concrete carrier map or literal
consumer cannot be frozen without an additional semantic decision. Keep the
original root unchanged. Rust stays `NO_SAFE_CODE_SLICE` for this model gate.
