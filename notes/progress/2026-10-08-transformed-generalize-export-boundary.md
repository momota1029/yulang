# Transformed Generalize export: current production boundary

Date: 2026-10-08
Status: bounded research audit; no semantics, design or implementation authority
Baseline: `fc6c7f769a4b6b582a8473838bb68434c84c3fa3`
Claim class: current implementation mapping plus conditional source-use discriminator
Scope: ordinary nonrecursive `id` and resolved `pick` export boundary

## 1. Selected public target

The approved `successor-generalize-root-policy/q1/a1` selects a transformed,
displayable scheme as the actual public target, together with only the
additional use information proved necessary. It explicitly rejects retaining
the complete source relation under another name as a substitute for that
target. The source Lambda root may be retained while constructing the result;
ordinary uses must be justified from the transformed export.

This choice does not specify the abstraction, its complete admission and
membership rules, or which additional fields suffice. It does not adopt a
resolver rule or authorize implementation. The first bounded source family
remains nonrecursive `id` and resolved `pick`; transformed/common exports,
recursive SCCs, complete Option 2 production containment, principality and
F5 cutover stay open.

## 2. Current production owner and payload

The current HIR retains an artifact-branded `DefinitionRootId` on each
`HirBinding` (`crates/yu-hir/src/module.rs`). Lambda lowering retains the
parameter and resolved body under that root. The production generalization
input is selected in `InferenceSession::component_generalization_draft`
(`crates/yu-solver/src/lib.rs`): it resolves the verified root's component,
translates it into the live solver row, and invokes
`F5cGeneralizer::build_component_with_bound_sidecar`. The finalizer installs
the resulting predicate and Q/R binders as a `ClosedValueScheme`
(`crates/yu-types/src/lib.rs`).

`ClosedValueScheme` stores an arena identity, quantifier count, recursive-bound
slice, and a designated positive predicate. Those are current solver objects;
the inspected type has no source Function membership/admission derivation,
original `xi`, or explicit immutable import/provider certificate. The current
standalone `SemanticImports` input is empty-only. This is a bounded mapping of
the examined HIR/type/solver owners, not a repository-wide absence claim and
not evidence that F5's predicate is the selected successor export.

The feature-gated shadow exporter borrows the current root scheme and keeps
the successor correspondence premises unresolved. It does not supply the
missing source rule or choose a transformed public export. Ordinary lowering,
collection, solving and publication still follow the current F5 route.

## 3. Why the retained-root query is insufficient

The reviewed PG-1 derivation establishes a conditional first Function query
for the retained root only when its `H-active`, `H-query`, and retained-root
`H-export` suppliers hold. The approved target instead requires a public
transformed root `R_A = alpha(R_L)`. A certificate for `R_L` does not establish
membership or a successful `Direct` query at `R_A`: the concrete Function
query is evaluated at the submitted root, with its own active membership,
admission, role, entry and consumer clauses. Concrete comparison success is
not transitive.

The selected invocation equations also rule out collapsing an export to its
body's printed effect. For resolved `pick y = z`, the body may have
`Comp(empty,b)`, while the complete Value-entry invocation first Forces the
received argument. Under the conditional premise that an independently typed
and admitted carrier `t` has

```text
Force(t) = Request(q,C,k),
```

the returned request retains the suffix that rebinds the response, returns the
original captured `z`, and completes the invocation. An abstraction that
retained only the body Result would lose this pending observation. The same
issue occurs for `id` with the rebound argument. This is a conditional
discriminator against body/call collapse, not a complete source-program
counterexample: no concrete operation declaration or admission derivation was
constructed here.

## 4. Exact next supplier

The smallest next construction is a candidate abstraction for `id` and
resolved `pick` that:

1. consumes the actual source Lambda and its occurrence-rooted construction
   evidence;
2. emits the transformed, displayable scheme as the designated public root;
3. exposes a finite, genuinely smaller set of use-time information, including
   any rigid captured/imported dependencies;
4. gives complete active membership/admission clauses and the actual ordinary
   use query at that transformed root; and
5. proves scoped freshening, invocation-prefix preservation, and coverage for
   the independently legal uses in this selected source family.

Each item is a proof obligation, not a new judgment assumed to hold. If the
concrete eligibility, membership or abstraction clause is not determined by
the approved sources, it needs its own reviewed decision before adoption. The
generalization/export candidate that retains the whole component is useful as
a conditional transport theorem, but does not discharge these obligations or
meet the approved public-target goal by itself.

## 5. Evidence and limits

Sources were read at the pinned baseline: the approved root-policy answer and
receipt; `2026-10-08-generalize-export-constructor-candidate.md` §§3–5.1;
`2026-10-08-pg1-generalize-direct-evidence.md` §§2–5; source contracts
§§2–3.7 and §5.3; current HIR, solver, shadow and type owners listed above.
Eight inspected production source files matched the pinned HEAD byte-for-byte.
The primary also read the exact source and PG-1 equations cited in this note.

No tests, builds, executable probes or production edits were part of this
audit. This note is its sole new path and has no independent review; it records
bounded source mapping and a conditional discriminator only. The required
active descriptor/admission inventory, actual transformed-root rule, complete
use-preservation theorem, recursive/generalized exports, exhaustive fixed
imports and production correspondence were not verified.
