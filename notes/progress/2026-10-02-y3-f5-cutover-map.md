# Yulang3 Function inference cutover map

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: read-only implementation map; no replacement semantics or implementation authority

## Scope

This maps the eventual replacement seam for the F5 Function scheme path. It is
preparatory only: the SCC-intrusion charter retires F5 as the semantic target,
but requires reviewed and user-approved successor semantics before compiler
changes. No source files or tests were changed.

## Current public-to-solver path

- HIR's `ResolvedExpr::Lambda` is defined in
  `crates/yu-hir/src/module.rs:426`.
- `ConstraintBatch::collect(Arc<HirModule>)` is the solver collection entry in
  `crates/yu-solver/src/lib.rs:813`. Its current lambda source envelope is
  deliberately narrow: one parameter and integer, resolved-name, or
  parameter-name body (`:928-960`). Lambda recipes and parameter facts are
  recorded at `:1041-1049`; `emit_lambda` builds the associated facts at
  `:1555-1613`.
- `SolvedModule::solve` at `:15663` calls private session execution
  (`InferenceSession::run`, `:9729-9735`), which admits source facts, executes
  the SCC plan, and finalizes the result. Public root observations are
  `projection_for` (`:15691`) and `root_value_for` (`:15706`), the latter
  currently reading a closed scheme.
- Repository search found no Rust call sites for `ConstraintBatch::collect`
  or `SolvedModule::solve` outside `yu-solver`. This is repository evidence,
  not a claim about external consumers.

## Reusable SCC foundation

F0 immutable definition/use inventory, F1 static `SccPlan`, and F2 artifact-
checked component queries live in `crates/yu-solver/src/lib.rs` and
`crates/yu-solver/src/scc.rs`. F3's private session starts at `lib.rs:7198`.
F4's live bound and typed-constraint operations are in `:3699-3715`,
`:10445-10524`, and `:11048-11145`. Current execution routes internal uses
against live roots (`:12882-13010`) and installs all member schemes before
incoming uses (`:13890-13965`). The charter preserves this scheduling and
open-internal-use infrastructure within its declared scope; it does not make
the Function schemes authoritative.

## F5 coupling and eventual cutover seam

F5 is not one replaceable generalizer call:

- Session state includes live variables, levels/extrusion, bound rows, closed
  scheme slots, finalization and draft/instantiation scratch
  (`lib.rs:7198-7290`). Function constructors are at `:9658-9689`, extrusion
  at `:10656-10840`, and typed Function decomposition at `:11048-11200`.
- Production `component_generalization_draft` (`lib.rs:15160-15183`) calls
  `F5cGeneralizer`, whose expansion implementation is in
  `crates/yu-solver/src/f5c_generalization.rs`.
- The boxed production path builds and normalizes all member drafts, finalizes
  them through `yu-types`, and stages closed drafts
  (`lib.rs:13019-13327`). A flat alternative is `#[cfg(test)]` only.
- Incoming-use routing reads a closed scheme and allocates/restores Q/R rows
  (`lib.rs:14875-14995`, `:14525-14660`); internal uses instead connect to live
  roots (`:13983-14005`).
- `yu-types/src/lib.rs:585-684` owns polarized Function, quantified/recursive,
  union/intersection views, and `ClosedValueScheme`; finalization APIs are at
  `:2234` and `:2448-2457`.

The narrow eventual replacement boundary is therefore the complete component
lifecycle inside `execute_scc_plan_inner` (`lib.rs:12882-13970`): member
generalization/publication, the durable root result, and incoming-use
instantiation must move together. Replacing only `F5cGeneralizer` would leave
closed-scheme consumers and Q/R assumptions intact. F0-F4 may be reusable, but
their Function-facing operations still need an authority audit against the
successor source relation.

## Consumers and verification surfaces

Direct internal consumers include the `SolvedModule` scheme table/arena
(`lib.rs:7166-7175`), root observation (`:15706-15750`), incoming
instantiation (`:14875-14995`), and F5c-only scheme decoding in tests
(`:14107`). `yu-types` supplies scheme alpha equality and finalization views
(`:638-684`, `:756-774`). Relevant test sources include Function facts,
identity, constant, and productive recursion (`lib.rs:20278-20545`), F4 SCC
ordering/Integer cases (`:17498-18250`), F0-F2 structure (`:18800-19820`), and
`crates/yu-solver/src/tests/f5c_*.rs` transaction/replay/flat-walker/resource
suites. Tests are inventory only; no tests were run.

## Risks and next use

The replacement affects session representation, `yu-types` result shape,
member publication, incoming use, root observation, and rollback/resource
accounting. Current HIR reaches only a small source subset; the end-to-end
capability matrix records additional application, record, nominal, effect, and
diagnostic paths that must eventually be supplied to prove Oracle-level final
acceptance.

This map does not authorize F5 deletion, a new public result type, or a compiler
edit. Use it after the ordinary source/effect relation is reviewed and
approved, to plan one coherent replacement cutover that removes the F5
semantic dependency rather than wrapping it.
