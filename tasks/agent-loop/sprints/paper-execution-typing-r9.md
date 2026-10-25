# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r9 — close all five transport motives

Status: issued by the primary for the continuing user proof goal.
Branch / baseline: `research/simple-sub-intrusion` at
`8e425bc4889b22ed1602b00d395bc69d98b69f40`.
Authority: `docs/yulang-operational-type-safety-ja.tex:953-977`, with record
rules `:217-231` and record code lemma `:724-749`. Preserve the original
arbitrary simultaneous substitution theorem and all downstream obligations.

## Fixed outcome

Produce a normally building `PaperExecutionTypingSubstitution.lean` that exports
transport for `ValuesTyped`, `ValuesAllTyped`, `RecordPayloadsTyped`,
`PaperValueTyped`, and `PaperComputationTyped` under arbitrary `σ : Nat → Ty`.
Keep labels, row presence, raw field tags, payloads, all declaration and graph
environments, and each theorem's existing quantifiers distinct. Do not add a
formation premise or strengthen assumptions. R8's checked scratch proof
`PaperValueTyped.subst_explicit` is a construction candidate only; R8 module
integration failed because the theorem name shadowed the type substitution
function and direct induction on the mutual computation family was unsupported.

Try a non-conflicting theorem name and a qualified type-substitution alias. For
computation transport, test deriving the IH by applying value transport to
`PaperValueTyped.delay derivation`, then invert the transported delay derivation
to recover the computation constructor. If this fails, preserve the exact Lean
error and do not mask it with stronger hypotheses or axioms. The list motives
may be proved by list induction using value transport. Apply every successful
helper immediately to the original five transport obligations.

## Exact work and leases

Primary `/root` owns the typing module, this contract, `current.json`, and the
final outcome record. Worker `/root/r9_computation_probe` owns only
`/tmp/yulang-r9-computation-probe/notes/theory/lean/.lake/R9ComputationProbe.lean`
and generated cache files below that isolated worktree's `.lake`. The worker
may read the R8 scratch proof and checked-in paper syntax, but must not edit
tracked sources, commit, or touch any other path. No other writer owns this
worktree. The R8 syntax input remains read-only at SHA-256
`8ad8bc4b1549eadaa73c743438b333c62b44be7bdff0346f690b7da9e6353a97`.

All historical/foreign UNKNOWN leases remain quarantined. There is one Lean/Lake
verification owner at a time. Sprint cap: 900 active seconds, 8 serial
Lean/Lake invocations, and 120 cumulative checker seconds; the worker may use at
most 3 invocations and 45 checker seconds. Root may use the remaining 5 calls.
Use `-j1 -M1024`, record actual receipts, and stop at the fixed bound, a hard
obstruction, source/authority change, or user STOP. No `sorry`, `admit`,
project axioms, tests, Rust/native builds, or compiler changes.

## Acceptance and open boundary

Success requires the focused module to build and the exact types plus complete
axiom audits for all five theorems and support lemmas, with no `sorryAx`, `_f`,
failed declaration dependency, or project axiom. Record source constructors
represented and omitted. A checked scratch lemma or isolated probe is not the
module result. Fresh independent review remains `NOT_RUN` unless a safe reviewer
slot is independently established. Full parent closure, inference/executor
soundness, A/B, source/native correspondence, and Rust bridges remain OPEN.
