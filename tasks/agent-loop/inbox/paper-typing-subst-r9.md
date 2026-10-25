# R9 handoff — partial paper typing substitution transport

Status: `SUCCESS_CHECKED_PARTIAL_MODULE`; not full paper theorem closure.
Baseline: `8e425bc4889b22ed1602b00d395bc69d98b69f40`.
Implementation: `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`.

## Result

The focused module now compiles and exposes arbitrary simultaneous type transport (`σ : Nat → Ty`) for all five represented judgments:

- `ValuesTyped.typeTransport`
- `ValuesAllTyped.typeTransport`
- `RecordPayloadsTyped.typeTransport`
- `PaperValueTyped.subst_explicit`
- `PaperComputationTyped.typeTransport`

Each theorem maps the declaration table, graph environment, type environment, syntax and result types consistently. `RecordPayloadsTyped` maps each payload value while preserving field label and raw `Presence`. The value recursor separately preserves record shape, duplicate-free actual labels, required-label inclusion, field witnesses and payload judgments. Required-only `field` and any-declared-label `lookup` constructors are transported by `RecordField.subst` without changing their quantifiers.

The computation theorem reuses the value theorem on `PaperValueTyped.delay derivation`, simplifies the mapped syntax/type equations, and inverts the resulting delay constructor. This avoids a second mutually recursive computation proof and keeps arbitrary σ.

## Verification receipt

Pinned Lean: 4.35.0, Lake commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Primary verification calls (serial):

1. `lake env lean -j1 -M1024 YulangClosure/PaperExecutionTypingSubstitution.lean` — exit 0, 0.50 s.
2. `lake build +YulangClosure.PaperExecutionTypingSubstitution` — exit 0, 0.63 s; imported syntax replay emitted only existing unused-variable warnings.
3. `lake env lean -j1 -M1024 .lake/R9Audit.lean` — exit 0, 0.12 s.

The isolated computation leaf used three calls: syntax build 20.03 s; initial `change` probe 0.60 s (failed because the mapping equations are not definitionally reducible); repaired probe 0.86 s. Total worker checker time 21.49 s, and the final computation result audited cleanly. Sprint aggregate: 6 serial calls, approximately 23.0 checker seconds; within 8 calls / 120 seconds. No Rust/native build or tests were run.

`#check @...` printed all five complete types with arbitrary `σ` and the mapped declarations, graph/type environments, syntax and results. `#print axioms` for all five transports and support lemmas reports only `[propext, Quot.sound]` where needed; `literalType_subst`, both lookup transports, `RecordShape.subst`, and `RecordField.subst` report no axioms. No `sorryAx`, `_f`, failed declaration dependency, or project axiom appears.

Worker artifact: `/tmp/yulang-r9-computation-probe/notes/theory/lean/.lake/R9ComputationProbe.lean`, SHA-256 `8bad2dafada61bc1a69d1a2d69e9848f6275d2542f8f81077763f3a4e9ce50ac`. The final theorem and axiom list were independently received from the leaf; the primary compiled and audited the integrated module.

## Scope and open premises

The file covers only constructors represented in `PaperExecutionSyntax.lean:609-716`. This is not the full paper substitution lemma at `docs/yulang-operational-type-safety-ja.tex:953-977`: type transport is proved for the modeled judgments, but term substitution, capture-avoiding renaming, all omitted typing rules (including variants, nominal tables, operations, handlers, graphs, primitives, templates, patterns and administrative forms), and source/native correspondence remain OPEN. Inference/executor soundness, original A/B claims, and Rust bridges remain OPEN. Independent review is `NOT_RUN`.

No compiler semantics or implementation changed. Exact source hash and commit are recorded in the primary sprint receipt.
