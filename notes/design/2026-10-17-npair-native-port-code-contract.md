# NPAIR native negative-port producer contract

Status: Draft; unapplied and pending three fresh independent reviews. This
document grants no compiler-code or test lease.
Sprint: `npair-native-port-formation-20261017`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Decision proposed

Add one source-owned producer for negative formal effect ports, with two
separate outputs: the existing polar solver terms over one shared row, and
inert source Permission records. Do not encode concrete Permission atoms as a
row lower, upper cap, closed row, equality or subtraction instruction.

The candidate patch is confined to `candidate_effect.rs`. It changes the
recursive formal-pair builder to accumulate a temporary list of source
Permission records alongside its `(positive, negative)` terms. It reserves
that list to the already bounded annotation node count before recursion. Only
after the complete pair and both ordinary formal links (slots 43 and 44) have
been admitted does it append the records to the owning effect-algebra state.
The existing route transaction remains the publication and rollback boundary.

The source action already retains the annotation `Arc`, formal parameter,
lambda occurrence and `AnnotationScope`. The candidate record adds a typed
Function-child path to a concrete negative row occurrence. It points back to
the retained annotation for its operands instead of cloning atom strings:

```rust
enum FormalPortStep { Argument, Result }
struct FormalPermission {
    parameter: usize,
    occurrence: HirOccurrenceId,
    scope: AnnotationScope,
    path: Vec<FormalPortStep>,
}
struct FormalPairBuild {
    positive: Term,
    negative: Term,
    permissions: Vec<FormalPermission>,
}
```

These are proposed private types, not existing code. A lookup follows `path`
through the action's retained `SourceAnnotation`; it must verify that the
resolved row has the expected negative composed variance and concrete
operands. This record means only “the source annotation grants this local
handling permission.” It is not a `BoundAdmission`, `Contribution`, provider,
constraint occurrence or proof of `At(D,w,delta)`.

## Port construction and exact source cases

At each recursive Function child, preserve the current variance recursion and
all four children. For a negative written row with concrete operands and no
symbolic variables, the candidate producer allocates one fresh flexible row
at the formal's existing level, creates positive and negative live effect
terms over that same row, and appends one Permission path record. It creates
no row constraint from the concrete atoms. Both returned projections therefore
share one row, while distinct source occurrences get distinct fresh rows.

Existing behavior remains for omitted rows (one fresh shared row), singleton
symbolic rows (the existing scoped variable row), and positive explicit rows
(the existing signature views). In particular, argument variance reversal,
result variance preservation, the complete Function children, and slots
43/44 remain unchanged. The root computation-effect entry stays on
`FormalEntry` at slots 45/46 and is not collected as a nested Permission.

| Source shape at a negative nested port | Draft behavior | Status |
| --- | --- | --- |
| Omitted row | Existing fresh shared row | Existing behavior |
| No concrete atoms, exactly one symbol | Existing scoped shared symbol row | Existing behavior |
| Concrete operands, no symbols | Fresh shared row plus separate inert Permission path | Adopted concrete-only case |
| Concrete operands plus one symbol | Existing symbol is the whole-inflow row; concrete Permission is recorded | Adopted singleton connection; whole original `C_sym` applicability still needs source-owner evidence |
| Multiple symbols, with or without concrete operands | Preserve refusal | No join, split, equality or source restriction is selected; full `C_sym` is open |
| Explicit empty row | Preserve refusal | Literal N-Port-Intro shape does not establish source reachability/meaning |

The mixed singleton case is source-authority dependent: current native preflight
and pair guards refuse it, while the adopted interface names the symbol as
whole inflow. This Draft does not enable that case until the original
source-signature owner supplies the complete `C_sym` clauses and scope
correspondence. The exact implementation slice safe for a later code sprint is
therefore only the concrete-only negative case, with the current preflight
refusal left in place until source admission is separately authorized.

## Proposed code change sketch

This is the exact intended shape of the future patch, not an applied diff:

```diff
 struct EffectAlgebraState {
     ...
     formal_domains: HashMap<usize, Term>,
+    formal_permissions: Vec<FormalPermission>,
 }

- fn candidate_formal_pair(...) -> Result<(Term, Term), SolveAvailabilityError>
+ fn candidate_formal_pair(..., path: &mut Vec<FormalPortStep>,
+     permissions: &mut Vec<FormalPermission>)
+     -> Result<(Term, Term), SolveAvailabilityError>
```

The negative concrete-only branch in `candidate_formal_effect_port` would call
`fresh_effect_at_level(level)` once, derive both live polar terms from that
row, and push the current source path into the temporary permission vector.
The ordinary recursive branch pushes `Argument` or `Result` around each
existing recursive child call and pops it on both success and error. No
Function child constructor is removed. `candidate_formal_annotation` reserves
temporary permission capacity using the annotation's bounded node count,
builds the full result, admits both existing formal links, reserves retained
state and journal capacity with checked arithmetic, then publishes the
permissions. A fallible step before publication leaves no permission visible;
failure after either edge follows the existing enclosing route-transaction
rollback. The pair remains unpublished in `formal_domains` until both links
succeed, as today.

The retained vector belongs to `EffectAlgebraState`, because permission
outlives the temporary recursive builder and is source evidence attached to
the formal. It is not stored in `formal_domains` (which remains the solver's
negative value term) or in `candidate_context` (which owns contribution and
bound-admission evidence). `EffectAlgebraState::bytes`, `refresh_bytes`,
`EffectAlgebraUndo::bytes`, checkpoints and rollback must count/remove exactly
the appended records and each path's allocated capacity. The implementation
must reserve both state and undo bookkeeping before publication; use checked
byte arithmetic and return the existing exhaustion error on reserve failure.
On rollback, truncate to the checkpointed permission length. No new global
registry, ID counter, compiler API, or background consumer is introduced.

## Alternatives and rejected shortcuts

1. **Proposed: source Permission path records plus the shared row.** Keeps the
   adopted distinction, preserves the existing two solver edges and has one
   clear publication owner.
2. **Put concrete atoms into Support/Allowance signature views.** Rejected:
   those views create lower/cap behavior and do not implement negative
   Permission over a shared inflow row.
3. **Use the `FormalEntry` computation row or parameter domain as the port.**
   Rejected: root computation slots 45/46 and nested value/effect links 43/44
   have distinct roles and levels.
4. **Store Permission in `formal_domains` or bound-admission history.**
   Rejected: those structures respectively own a solver term and contribution
   derivations; Permission is neither.
5. **Enable all currently refused forms or infer an absent semantic case from
   preflight.** Rejected: multiple-symbolic `C_sym`, explicit empty reachability
   and source/native coverage remain open decisions.

## Authority, validation and parent boundary

The exact compiler owner is
`candidate_effect::candidate_formal_pair` /
`candidate_formal_effect_port` /
`candidate_formal_annotation`. The adjacent source gate is
`candidate_source::preflight` and Lambda registration. This sprint authorizes
only this unapplied design; source registration, preflight, error mapping and
all compiler code remain untouched. A later implementation sprint must receive
separate approval and exact path leases, and must retain both current refusal
behaviors until the source owner resolves admission.

The producer would establish a candidate row/Permission representation only.
It would not establish actual source acceptance, authentic `At`, provider
lineage, N-Ingress, transport, whole `rho_u`, J1/J2 future coverage, Catch or
other consumer authority, subtraction, N-Subtract-Elim, F1/FK1, source/native
adequacy, principality or production readiness. Retained FreshUse maps are
only structural crosswalk inputs and cannot supply this Permission or
contribution-derived evidence.

## Review contract and pins

Fresh sequential reviewers must inspect the frozen proof, this exact proposal
and the unchanged source pins. Compiler review checks all four Function
children, both formal edges, shared row identity, separate Permission,
failure behavior and error gates. Architecture review checks owner/lifetime,
capacity accounting and rollback. Specification review checks the adopted
source domain, open `C_sym`, separate computation effects, J1/J2 and unchanged
output scope. Any major finding returns to Luna; no reviewer may enlarge this
Draft into source or compiler authority.

Proof artifact SHA-256:
`a7be614af3b432e785fb64d2580ee30de30c448ba5d332e5c40162cb4578ce4f`.
Proof handoff SHA-256:
`b2d420b0b528f1a6776d6f6372542de5f6304208220d65abc4d052ea22afed45`.
Sprint contract SHA-256:
`3af4ef163a3555d037fa559db8abd2b4c741605dac64453589b7cbd5b69898e9`.
The four native source baseline pins and adopted-rule pins are recorded in the
sprint contract and frozen proof §7; they must be rechecked before independent
review. No tests, probes, builds, Cargo or compiler execution were run for this
Draft.

## Revision 2 — supersedes the producer sketch above

This section is append-only so the reviewed revision-1 bytes remain visible.
It controls wherever earlier prose conflicts with it. Revision 1 design SHA-256:
`2ebb6e4c629e520a1017a20fc5cd52f4e0bbfcdb621456e0927e1a639760dc73`.
Revision 1 compiler review STOPPED with two major findings: the earlier pair
refusal made the new port branch unreachable, and the proposed path handling
could record a parent node instead of the row occurrence.

### Current behavior and proposed future predicate

No repository code was changed. Today `candidate_formal_pair` rejects a
negative row before `candidate_formal_effect_port` when the row has concrete
operands or does not have exactly one symbolic variable. Independently,
`candidate_source::preflight_formal` rejects every negative concrete row,
including concrete-only rows, and explicit empty negative rows. The present
error outcomes remain `CandidateError::Unsupported` at source preflight and
`SolveAvailabilityError::IdentityExhausted` at the pair/port guard.

A future producer implementing only the bounded nonempty concrete-only case
must change the pair-level internal predicate as well as add the effect-port
branch. Its exact decision table is:

| Variance and row | Future pair guard | Future port construction |
| --- | --- | --- |
| Either variance, omitted row | Allow | Existing one fresh shared row |
| Negative, no concrete atoms and exactly one symbol | Allow | Existing scoped symbol row |
| Negative, one or more concrete atoms and zero symbols | Allow | One fresh shared row and separate Permission record |
| Negative, concrete plus one symbol | Refuse in this bounded patch | Adopted interface chooses the symbol as whole inflow, but original mixed `C_sym` coverage is not certified here |
| Negative, more than one symbol | Refuse | Full `C_sym` relation and scope obligations remain open |
| Negative, explicit empty row (`K=V=empty`) | Refuse | Reachability/meaning in the original source signature remains open |
| Positive, at most one symbol | Preserve existing predicate and port branch | Existing positive signature views where applicable |

Equivalently, for a written negative row this bounded internal predicate
accepts iff `(concrete.is_empty() && variables.len() == 1) ||
(!concrete.is_empty() && variables.is_empty())`; the existing outer
`variables.len() > 1` rejection remains. Omitted rows are handled before this
predicate. Positive behavior is unchanged. This changes only the future
internal pair constructor's accepted shape; it does **not** enable source
preflight, infer that refused source inputs are semantically unsupported, or
restrict the parent source domain. The concrete-only producer remains
unreachable through normal source collection until a separately authorized
source-admission decision.

### Exact path threading at all four Function children

A `FormalPortStep` path resolves the `SourceAnnotationType` child whose
computation row is being constructed. The current Function branch performs
argument value recursion, result value recursion, argument effect construction,
then result effect construction. Therefore the future patch must hold each
child path across both operations, not just around value recursion:

```text
base = path.len()
path.push(Argument)
argument_pair = candidate_formal_pair(argument, path, permissions)
argument_effects = candidate_formal_effect_port(argument.effects, path, permissions)
path.truncate(base)
propagate either error only after restoring path

base = path.len()
path.push(Result)
result_pair = candidate_formal_pair(result, path, permissions)
result_effects = candidate_formal_effect_port(result.effects, path, permissions)
path.truncate(base)
propagate either error only after restoring path

return the existing positive_function_term / negative_function_term using
argument_pair, argument_effects, result_effects
```

The actual implementation should put each pair of operations in a closure (or
an equivalent restoration guard) so `path.truncate(base)` runs on success and
error. It must preserve current constructor and allocation order. At the target
`f.result.value.Function.result.effects`, the path is `[Result, Result]`; an
argument-side port records the corresponding `Argument` child at its depth.
Nested descent appends another step and returns to the caller's prior length.
Permission construction reads the effect row of the exact child currently
named by `path`; it cannot use the parent annotation's row as a fallback.

### Self-contained retained Permission record

The earlier sketch omitted a durable owner for later path lookup. The future
record must be self-contained and must not depend on the temporary
`Action::FormalAnnotation` remaining alive:

```rust
struct FormalPermission {
    parameter: usize,
    occurrence: HirOccurrenceId,
    source_owner: SourceRootId,
    scope: AnnotationScope,
    path: Vec<FormalPortStep>,
    source_row: SourceNodeKey,
    concrete: Vec<SourceEffectId>,
}
```

Construction copies the concrete effect IDs and source row key from the exact
negative child row, and copies the already-available owner, occurrence and
scope from the formal action. The typed path retains the connection to the
original annotation shape even after collection. The record has no solver-row
mutation, provider, witness, contribution or `At` authority. Shared row
identity still comes only from the single fresh row used to construct both
polar terms; the Permission record never determines row equality.

Build records in a temporary vector reserved to the annotation's bounded node
count. Before publication, reserve the retained state vector and route-journal
undo capacity; checked byte arithmetic must include each path and concrete-ID
backing capacity plus owned record payload under the repository's existing
accounting rules. Shared declaration allocations are not charged twice when
only their shared handles are cloned. Add a checkpointed length to the
`EffectAlgebraUndo`; rollback truncates to that length. Publish only after the
complete pair and both links 43/44 succeed. A failure before publication
leaves no record visible; a later route failure removes all records created by
the route. Existing route transaction rollback remains responsible for edge
and domain state. If source/scope identity bytes lack an existing accountable
representation, stop the implementation and obtain an exact accounting design
before writing code.

This revision closes only the two compiler-review precision findings and
makes the record lifetime explicit. It remains an unapplied Draft. Revision 1
review does not certify this revision; fresh delta compiler review and complete
architect/spec review are required.

## Revision 2.1 — exact evaluation order correction

This append-only correction closes the revision-2 compiler-review minor. The
four operations preserve current construction order exactly:

```text
argument value at Argument path; restore caller path
result value at Result path; restore caller path
argument effect at Argument path; restore caller path
result effect at Result path; restore caller path
```

For each operation, save `base = path.len()`, push its child step, perform the
single operation inside a result-producing closure, truncate to `base`, then
propagate an error. Thus the existing allocation/constraint order remains
argument value, result value, argument effect, result effect; each effect row
still receives the same child path as its value recursion. This section
controls over the revision-2 pseudo-code's earlier grouped ordering. It changes
no other proposal text or authority. Fresh architecture and specification
review remain pending.
