# R18 variant type-argument authority intake

Primary-owned bounded source intake following the R20 sprint-end dispatch.
This records inspected authority and source correspondence; it does not
adopt a variant rule or grant proof/implementation rights.

## Finding

**The existing governing material inspected here does not define the role of
the extra raw `Value.variant.typeArguments` field.** The R18 premise
`R18-VARIANT-TYPEARG-CORRESPONDENCE-1` remains OPEN. No candidate interpretation
is selected, and no raw value is accepted or rejected by this note.

The operational typing manuscript uses raw value form `t(\bar v)` at lines
150–155 and gives the variant rule at line 219: the tag selects a row arm, the
arity is correct, and each ordered payload has its corresponding component
type in that arm. The rule does not introduce a second list of type arguments
attached to the value. The general sentence at line 109 says family, nominal,
constructor and payload/response type arguments are retained, but it does not
map the Lean-only variant field to the row arm or to any source-level data.
The simultaneous substitution claim at lines 953–977 requires one σ to act on
all types and payloads; it does not determine what this extra field denotes.

Lean's raw syntax at `PaperExecutionSyntax.lean:46–47` has
`Value.variant constructor typeArguments payload`, and its map at lines 183–185
maps that list independently from payloads. `VariantFormed` in
`PaperTypeFormation.lean:63–67` validates row payload-type formation and unique
tags, but contains no raw value index and no connection to `typeArguments`.
Thus the current representation permits distinct lists beside the same tag
and ordered payloads, while no cited typing rule decides their relationship.

The inspected source path carries no analogous field: HIR
`LocalSourceForm::Variant` at `crates/yu-hir/src/module/local_source.rs:394`
contains a tag and ordered payload expressions. Solver generation at
`crates/yu-solver/src/candidate_source.rs:1928–1942` retains tag, payload
endpoints and effects. Runtime lowering at
`tools/inference-playground/src/runtime/program.rs:891–893` emits a tagged
variant with payload code only; `machine.rs:730–742` evaluates those payloads
in order and retains the tag. This is bounded inspected-path evidence, not a
claim about every compiler/backend or a source/native correctness theorem.

## Required authority and falsifier

An adopting owner must supply an approved, versioned source-to-raw
correspondence that preserves the original paper source scope and substitution
claim, states whether/how the additional list is determined, and accounts for
tag, row-instance arguments, payload component order and arity. It must decide
the two discriminator objects retained in the R18 handoff without conflating
row payload types with declaration type parameters. Possible metadata,
equality, declaration-instance, canonical-empty, removal, or other treatments
remain proposals only. Any representation/rule change needs its own authority,
dependency review and fresh contract revision before proof work.

Until then, no faithful `PaperValueTyped.variant` constructor, inversion,
transport case, mathematical counterexample, production change or source/native
closure is authorized by this intake. Independent packets whose rule meaning is
already explicit may continue.

## Frozen inputs

- `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256
  `678f84eb635c95392068887b834a4f79a1a754ad474b950097aa212a3b68032c`.
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`, SHA-256
  `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`.
- `crates/yu-hir/src/module/local_source.rs`, SHA-256
  `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`.
- `crates/yu-solver/src/candidate_source.rs`, SHA-256
  `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e`.
- `tools/inference-playground/src/runtime/program.rs`, SHA-256
  `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`.
- `tools/inference-playground/src/runtime/machine.rs`, SHA-256
  `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`.

No file under those source paths changed during intake. Read-only source
inspection only; no Lean/Lake, Cargo, tests, runtime execution, semantic
adoption, external contact, or Git operation. No active-time telemetry was
available. The source owner for any semantic adoption remains to be identified
by the project's authority process; Luna owns this intake and keeps the gate
OPEN.
