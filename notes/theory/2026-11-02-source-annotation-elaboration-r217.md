# R217 — fixed source annotation data and the remaining row mapping

Status: **candidate source data and one local Oracle value-bound equation
constructed; full annotation correspondence remains open.** The original soundness claim,
quantifiers and `supported` predicate are unchanged. This packet proves no
parent premise.

## The equation attempted

The candidate input separates a fixed signature from the solver assignment:

```text
Σ : List Declaration
u : (annotation id, owner, type scope, source-selected entry)
ρ : assignments to generated Simple-sub variables

resolve(Σ,u) : Option Declaration
```

`Declaration` stores the original annotation ID, owner, type scope and the
complete recursive annotation tree. The Lean tree retains all current Rust
`SourceAnnotationType` constructors and every row at its original node:
Unit/Int/Bool/Str, type variable, source-positioned hole, ordered Tuple and
Function. Concrete effect-family IDs and symbolic row variables are distinct.
The tuple constructor preserves nested per-element rows, even though current
formal candidate inference rejects that case. Function argument and result are
separate recursive children. Resolution requires matching annotation ID,
owner and type scope, and returns the declaration tree without consulting a
solution.

The focused Lean equations are in
`YulangClosure.SourceAnnotationElaborationR217`. Kernel-checked results:

```text
lookup_stable : lookup Σ u.annotation = some d →
  resolve Σ u = if d.owner = u.owner ∧ d.typeScope = u.typeScope then some d else none

resolved_source_identity : resolve Σ u = some d →
  d.owner = u.owner ∧ d.typeScope = u.typeScope
```

`lake env lean YulangClosure/SourceAnnotationElaborationR217.lean` passes using
the pinned project and existing `.lake/build`. Both `#print axioms` audits
report only `propext` and `Quot.sound`. These are lookup properties of the
candidate table; neither theorem says the original `Kernel.atom` or its
`supported` source uses this table.

## Exact coverage mismatch

The source parser recursively parses every `TypeExpression` inside a group,
then stores separated group elements as `SourceAnnotationValue::Tuple`.
Each child is a full `SourceAnnotationType`, so its `effects` row is retained.
Thus a parsed annotation shaped like `([E] int, bool)` has a concrete row on
Tuple element zero.

The current `candidate_formal_value_pair` Tuple branch returns `exhausted()`
when any immediate element has `effects.is_some()`. The current formal
construction therefore has no equation for that parser-produced tree.

The frozen Oracle supplies a relevant existing **value-bound equation**. Its
annotation builder recursively builds tuple children (`main` commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`crates/infer/src/annotation/builder.rs:265–277`). Its
`AnnConstraintLowerer::lower_value_bounds` erases an `Effectful { ret, .. }`
wrapper by recursing into `ret`, including when called for each tuple item
(`crates/infer/src/annotation/constraints.rs:334–347`). Therefore, in that
value-bound path, a tuple child's root effect row contributes no value bound.
Rows at immediate Function argument/result ports follow a distinct equation:
the Function case lowers both value children and both effect ports separately
(`constraints.rs:363–371`). This keeps the selected Function-port hygiene
distinction and separates row permission from actual inflow.

The new Lean `valueView` records a candidate projection. Its
`value_view_ignores_root_effects` theorem formalizes the cited local Oracle
rule: the root `Effectful` wrapper contributes no value bound. The recursive
Tuple clause applies that value projection to each element. This makes the
earlier “new semantic choice” claim premature for the tuple child's value
bound; no user choice is requested there.

The candidate's Function row mapping is **not** yet an Oracle correspondence.
Frozen `builder.rs:130–151` reads `arg_eff` from the `TypeRow` directly under
`TypeArrow`; it builds `param` separately from the left type head. For
`([E] int) -> int`, this yields `param = Effectful(E, Int)` and `arg_eff =
None`; `lower_value_bounds` strips the parameter wrapper. The current carrier
parser puts a prefix row on the Function's `argument.effects`, and candidate
`valueView` then records that row as the argument-effect port. These equations
differ. `candidate_function_view_records_child_root_rows` merely states what
the candidate definition stores; it is not a theorem about Oracle or the
selected hygiene policy. A faithful mapping must retain the distinction
between the arrow's argument-effect row and an Effectful value wrapper.

This Oracle equation still does not connect the current Rust carrier or
`valueView` to the original Lean `supported` source domain. The authoritative
whole-language note separates parser grammar from typed support, and the
original Lean source still stores annotations as `Nat`; it contains no
signature table or annotation AST. In particular, this local projection does
not prove that every carrier annotation is supported, that root entry effects
are handled by the same equation, or that all original source constructors
are represented by the current carrier. The remaining source-definition
obligation is to put the original annotation meaning into the source
interpretation/generation equation, map its exact row positions, and prove
coverage for its unchanged supported domain. Do not infer that correspondence
from the frozen Rust code alone.

## Parent connection and result

The unchanged parent obligation remains
`Contracts.SourceProblem.InferenceSoundness`. Its source argument has no
`Σ` field, the original source-generation Lambda rule forwards only the
annotation `Nat` and entry, and the parameterized `Kernel.atom` does not
connect to the candidate `resolve`. The new table can therefore not be
instantiated from the original source problem, and the candidate lookup
theorems cannot be applied to the Lambda induction premise. The value
projection is an independent equation, not that missing source-data equation.

R217 result: a concrete candidate source declaration/elaboration equation;
one parser-versus-candidate mismatch; the Oracle's value-wrapper erasure
formalized in Lean; an additional Function arrow-row mapping mismatch;
original source coverage and connection to `Kernel.atom` not established;
roots remain 0/4, packages 0/5, parent delta 0. Keep the candidate file
separate from the original parent theorem until the original source-data
equation and its coverage are proved.

## Pinned source facts

```text
docs/yulang-whole-language-semantics-ja.tex
  sha256 6246e7dc179a795b372603eac8cd64bf783ba69e9a4a733bcfc012ebd6869612
  § parser grammar vs frozen Oracle typed annotation support
crates/yu-hir/src/module/source_annotation.rs
  sha256 409ce491bc2166aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef
  parse_type_source / parse_group / SourceAnnotationType
crates/yu-solver/src/candidate_effect.rs
  sha256 4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15
  candidate_formal_value_pair Tuple branch
notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
  sha256 3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1
  Annotation := Nat; Formal retains annotation ID and outer entry bit
frozen main crates/infer/src/annotation/builder.rs
  sha256 baad6a964909eaee3e7822aa5445dca8cd2f70185bd5a1f2157e878a512ddf7b
frozen main crates/infer/src/annotation/constraints.rs
  sha256 3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db
```
