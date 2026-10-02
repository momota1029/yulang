# Concrete compatibility boundaries and variable bound propagation

Status: Reviewed; records the user's 2026-10-03 semantic decision; operational rules and implementation authority remain open
Date: 2026-10-03
Scope: separate transitive variable-bound propagation from local concrete compatibility and adaptation resolution
Approved-by: user for the relation distinction and Oracle observations recorded in §1 only
Reviewed-by: compiler_referee and spec_auditor §§1–5, 2026-10-03; architect pre-write audit plus fresh compiler_referee/spec_auditor review of §5 found no findings within bounded scopes
Implementation authority: none
Supersedes: none; narrows source applicability of structural relation candidates without invalidating their fragment theorems

## 1. Governing semantic decision

The user's 2026-10-03 decision distinguishes two operations:

1. Bound propagation among type variables may use transitivity.
2. A comparison whose endpoints are concrete types is a local compatibility
   judgment. It may resolve a cast or adapter at that boundary. Its success is
   not an edge in a single transitive concrete subtype relation.

Optional Record comparisons are the discriminator. Oracle accepts each of

```text
{} <: {foo?: string}
{foo?: string} <: {}
{} <: {foo?: int}
```

and accepts the chain

```text
{} <: {foo?: string} <: {} <: {foo?: int}
```

while rejecting the direct comparison

```text
{foo?: string} <: {foo?: int}
```

Therefore local concrete compatibility is not closed under transitivity. In
particular, optional Record comparison must not be added to ordinary
structural subtyping and then transitively saturated.

The examples are user-supplied Oracle observations, not new successor source
fixtures or a complete operational account of the conversions. They do not
yet determine which fields are materialized, dropped, defaulted, or converted;
whether a concrete adapter is required at each site; or how ambiguous
adaptation is selected.

## 2. Candidate responsibility split

Keep these obligations distinct in any successor presentation:

```text
Eq(A, B)                         regular constructor equality
Bound(X, Y)                      variable-to-variable bound edge
Compat_j(A, B)                   local concrete compatibility query
Resolve(Compat_j(A, B))          selected conversion evidence / adapter
```

`Eq` identifies regular constructor unfoldings and retains its original
endpoints. Compatibility does not merge equality classes.

The bound graph may propagate a variable relation transitively. When a path
through variables exposes concrete endpoints, it generates a guarded local
`Compat_j(A, B)` obligation. The compatibility result and its conversion
evidence stay attached to that boundary query; they are not inserted back
into the variable reachability relation as a concrete edge. In particular,
successful `Compat_j(A, B)` and `Compat_k(B, C)` do not discharge
`Compat_l(A, C)`. Any composed conversion needs an independently justified
resolution and operational-validity argument.

The index `j` stands for the originating source boundary, lexical opening,
retained typed evidence and applicable scope context. Every derived query
still passes the selected generation-time scope guard before resolution.
This notation is a candidate separation, not a chosen data structure or a
proof that all source sites generate finitely many contexts.

For unresolved or variable endpoints, the solver may need to retain a
suspended compatibility obligation. Its endpoints, context and eventual
conversion evidence must remain correlated through aliases, replay,
generalization and SCC intrusion. The candidate mechanism and its finiteness
are open.

## 3. Relation to reviewed structural results

The following results remain valid within their declared mathematical
fragments:

- `2026-10-03-scoped-structural-projection.md` proves properties of a
  transitive greatest structural simulation over mandatory Records,
  Functions and declared-variance constructors. Its theorem does not model
  local cast/adaptation resolution or optional Record fields.
- `2026-10-03-scoped-constraint-solving.md` decides closed comparisons in
  that same structural fragment. Its regular equality quotient and permission
  propagation remain separately useful, provided adaptation compatibility
  does not stand for `Eq`.
- `2026-10-03-open-residual-factorization.md` proves a conditional
  factorization for bounds interpreted in the greatest structural relation.
  Its pair normalization and §4.1 equivalence cannot be applied to general
  concrete compatibility until preservation of both compatibility and
  conversion evidence is proved.
- `2026-10-02-typed-boundary-realization-draft.md` gives a conditional
  operational realization for fixed-shape Function/Thunk adapters. It is not
  a general concrete-compatibility oracle and does not cover optional Records.

These fragment theorems are not refuted. Their source applicability is
narrower than treating their `<=` as the one relation used at every concrete
boundary.

## 4. Current source evidence and limits

The current successor solver represents polarized Function terms and
variable bounds, but its term algebra has no Record or cast/adapter node:
`crates/yu-solver/src/term.rs::TermView` and
`crates/yu-solver/src/lib.rs::InferenceSession::constrain_live` are the
owning comparison surface. Closed types in `crates/yu-types/src/lib.rs`
likewise have no Record or adapter constructor. This is research/feasibility
evidence; the current task still authorizes no compiler implementation.

The successor HIR does not admit cast declarations into its resolved
expression envelope (`crates/yu-hir/src/module.rs`). The parser owns
`cast` declarations, and the stable-core example
`tests/contracts/stable-core/v0/run/vm/pass/example_cast/main.yu` demonstrates
implicit value casts in that contract corpus. The typed-computation design
also records frozen evidence for registered field casts, while explicitly
not establishing general whole-Record adaptation.

The frozen Oracle implementation has two distinct routes that a successor
could place behind one compatibility interface, but they should not be
conflated as existing evidence of one adapter mechanism:

- For Record-to-Record constraints,
  `a58eefc3:crates/infer/src/constraints/machine/propagate.rs` visits upper
  fields in `enqueue_record_fields`, skips absent lower fields, skips the
  lower-optional/upper-required case, and otherwise emits a field-type
  comparison. Frozen specialization separately rejects a missing *required*
  upper field and recursively checks matching fields at
  `a58eefc3:crates/specialize/src/specialize2/type_graph.rs`.
- For different nominal constructor paths, constraint propagation emits
  `NominalCastNeeded`. `AnalysisSession::constrain_nominal_cast` eagerly adds
  constraints for exact-path cast candidates; eligible source-boundary
  diagnostics later use `CastTable::resolve_value` to classify missing,
  unique, or ambiguous candidates. This route is implemented in the frozen
  `crates/infer/src/analysis/session/{generalize,ocast_activation}.rs` and
  `crates/infer/src/casts.rs`.

Consequently the optional-Record examples do not show that Oracle routes those
checks through its registered nominal cast table. They show why successor
concrete compatibility cannot be the transitive closure of every local
structural/adaptation success. The user-selected direction remains to
investigate one local compatibility/adaptation boundary; a candidate resolver
may dispatch to Record adaptation and nominal cast rules while retaining
distinct derivations and evidence. Whether that unification is sound and
operationally faithful is open; it must not silently turn Record checking into
registered nominal casts or compose boundary successes.

Successor named-Record type syntax currently requires `name: Type` fields;
the optional Record pattern syntax concerns pattern defaults and named
arguments, not optional fields in type declarations. Thus the user's
optional-Record observations are a semantic constraint on the successor
design, not evidence that this branch already parses or implements those
types.

## 5. Candidate Record-local checking derivation

The frozen concrete Record checker suggests a local presence-and-child
derivation for closed shapes. This is a candidate compatibility rule, not an
adopted source rule or a runtime adapter specification:

| Lower/actual field | Upper/expected field | Inference propagation | Concrete validation |
|---|---|---|---|
| absent | optional | no child comparison | absence is permitted |
| absent | required | no child comparison | reject missing required field |
| present, required | absent | no comparison | ignore extra lower field |
| present, optional | absent | no comparison | ignore extra lower field |
| present, required | present, optional | compare field types | validate child comparison |
| present, required | present, required | compare field types | validate child comparison |
| present, optional | present, optional | compare field types | validate child comparison |
| present, optional | present, required | defer the child comparison | validate child comparison; source-level acceptance and runtime presence guarantee remain unverified |

The last row matters: propagation skips the optional-to-required child pair,
but concrete specialization still checks matching field types. That skip is
not a permanent success. For the user-supplied discriminator, empty-to-optional
uses permitted absence, optional-to-empty has no upper fields to inspect, and
optional-string-to-optional-int reaches the incompatible child comparison.
This matches the stated pairwise outcomes without adding optional Records to
the transitive structural relation.

A candidate local derivation is:

```text
RecordCheck_j(L, R)
  = required-upper-name checks
    + one child Compat_(j, label)(L.label, R.label) for each shared label
```

Its evidence retains the original boundary, label correspondence, permitted
absence, ignored extra fields, deferred child obligations and every child
compatibility/conversion result. A compatibility dispatcher could return
distinct tagged derivations for Record checks, ordinary structural checks and
exact-path nominal cast resolution while preserving one boundary context.
At a shared Record field it can ask the same local child resolver, allowing a
registered conversion only when that child pair independently resolves. This
is a candidate API shape; it does not identify checking evidence with an
executable whole-Record adapter, nor show that Oracle routes optional Record
comparisons through its nominal cast table.

Executable Record realization remains a separate gate. In particular, evidence
is still missing for how omitted fields, extra fields and optional-to-required
fields behave at runtime, and whether a selected field adapter can be embedded
in an aggregate adapter. No composition law may be inferred from successful
boundary checks.

## 6. Next theorem gate

Before extending structural residual normalization, specify a local concrete
compatibility judgment and its Record-local evidence tree, while leaving the
candidate rows and missing runtime rules open until supported by
source/Oracle evidence. Then prove, in order:

1. the variable-only transitive propagation rule generates every required
   concrete boundary query and rechecks its scope guard;
2. compatibility normalization preserves the selected query outcome and
   adapter evidence, without composing independent successes transitively;
3. residual factorization preserves equality, bound provenance, conversion
   evidence and the joint symbolic coordinates under one assignment.

Only after those obligations close should the structural projection and
open-residual candidates be extended to general source inference. Effectful
interfaces, unknown Record shapes, source-wide evidence contexts, lifecycle,
and implementation remain open. No optional-Record grammar, acceptance
surface, conversion-selection policy, resource limit, or implementation
representation is approved here.
