# Finite guarded closure for variable bound replay

Status: Reviewed
Date: 2026-10-03
Scope: least closure of a fixed finite variable-bound graph with finite replay contexts
Approved-by: none; the user's approved relation distinction is recorded in §1 of `2026-10-03-concrete-compatibility-boundary.md`
Reviewed-by: architect pre-write audit; compiler_referee and spec_auditor review §§1–6 clean after primary closure of minor findings; fresh compiler_referee and spec_auditor review of §7 hypothesis; compiler_referee source-bridge and revised check-only contract-boundary deltas clean after major-finding repair; compiler_referee review of §8 clean after primary closure of one minor materialization-phase finding
Implementation authority: none
Supersedes: none

## 1. Purpose and limits

The [concrete compatibility boundary note](2026-10-03-concrete-compatibility-boundary.md)
records the user's distinction between transitive type-variable bound
propagation and local concrete compatibility. Its frozen-source audit found
that Oracle replays eligible lower/upper bound pairs stored at one variable,
retaining the pivot and both bound-record identities. This note isolates the
smallest finite closure theorem suggested by that route.

The theorem is about a fixed finite graph and fixed finite endpoint terms. It
proves termination, leastness and derivation preservation for the candidate
rules below. It does **not** prove that those rules are the successor source
typing judgment, that they preserve Oracle's complete source acceptance, that
the resulting constraints are principal, or that a generated conversion has
an executable source location. Those are separate open gates. The rules remain
candidates; no compiler change or new language behavior is authorized.

## 2. Fixed input and candidate closure rules

Fix:

- a finite variable set `V` and a finite directed `Bound` graph `E`;
- finite lower and upper payload identities `I_L` and `I_U`;
- for each lower payload `i`, a fixed endpoint term `A_i`; for each upper
  payload `u`, a fixed endpoint term `B_u`;
- a finite context carrier `C` that retains source identity, lexical binder
  identity and scope guard information; and
- finite context relations `Move_L`, `Move_U`, and `ReplayCtx`.

Every graph fact uses contexts from `C`; in particular,
`E ⊆ V × V × C`. The finite context relations have domains and codomains in
`C`.

An input lower state has shape `Lower(i, X, A_i, c)` and an input upper state
has shape `Upper(u, X, B_u, c)`, where `X ∈ V` and `c ∈ C`. A graph edge is
`Bound(X, Y, e)` with its own finite context `e`. The endpoint terms are nodes
in a fixed finite graph; the rules do not unfold them or allocate new endpoint
terms.

`Move_L(c,e,c')` and `Move_U(c,e,c')` say that the respective payload may
cross the edge under the resulting context. `ReplayCtx(c_L,c_U,X,c_R)` says
that the two contexts at one pivot admit a replay context. These relations are
explicit parameters of the theorem, not chosen guard-combination policies.
Their soundness and source definition remain open.

The candidate monotone rules are:

```text
Bound(X,Y,e) ∧ Lower(i,X,A,c) ∧ Move_L(c,e,c')
    ⇒ Lower(i,Y,A,c')

Bound(X,Y,e) ∧ Upper(u,Y,B,c) ∧ Move_U(c,e,c')
    ⇒ Upper(u,X,B,c')

Lower(i,X,A,c_L) ∧ Upper(u,X,B,c_U)
    ∧ ReplayCtx(c_L,c_U,X,c_R)
    ⇒ Replay(i,u,X,A,B,c_R)
```

The third rule creates a fresh `Compat` query after a bound-replay derivation.
When both endpoint terms are concrete, that query is resolved locally and may
select check/cast/adaptation evidence. If either endpoint is unresolved, the
query remains suspended for a later solving rule; this theorem specifies no
such rule. A successful local `Compat` result is not a premise to any of
these rules and is never entered into variable reachability. If a selected
compatibility derivation emits structural child obligations, those require a
separate finite closure argument with the replay query retained as their
parent; child generation is excluded from this theorem.

Original source boundaries are stored separately from these lower/upper
payloads. This package does not equate an original boundary with a lower or
upper payload, and does not decide whether a source boundary can supply either
kind of payload.

## 3. Finite least-closure theorem

Let `S_0` be any finite set of input lower and upper states. Let `R_Γ` be the
closure operator that adds every conclusion of the three rules in §2 using
fixed background facts `Γ` until no new state can be added. Context
transitions may be nondeterministic, but each relation is finite.

**Theorem (finite fixed-graph closure).** The closure process terminates after
finitely many state insertions and produces a unique least rule-closed state
set containing `S_0`. Every produced lower, upper or replay state has a finite
derivation from `S_0` and `Γ` (the fixed `Bound`, `Move_L`, `Move_U`, and
`ReplayCtx` facts). Conversely, every state with such a finite derivation is
present in the result. Any fair worklist schedule reaches the same least
closed set.

**Proof.** The universe of possible states is finite. If `n_L = |I_L|`,
`n_U = |I_U|`, `n_V = |V|` and `n_C = |C|`, then there are at most

```text
n_V² n_C
+ n_V (n_L + n_U) n_C
+ n_V n_L n_U n_C
```

canonical bound-edge, propagated-payload and replay states, respectively.
Endpoint terms are fixed by payload identity. A replay state's semantic key
contains its single result context; its lower and upper parent contexts are
premises in the finite provenance graph, not additional key coordinates. The
rules only add states, so each insertion strictly
increases a finite set and saturation terminates. Induction on insertion
round proves every inserted state has a finite derivation. Induction on the
height of a finite rule derivation proves completeness. The result is the
least fixed point of the monotone consequence operator, independent of fair
worklist order. A cyclic variable graph can produce alternate derivations but
cannot create infinitely many states when canonical keys and contexts remain
inside the fixed finite universe. ∎

This state bound does not count derivation paths. Keep a finite provenance
graph keyed by canonical states and immediate rule premises; do not allocate a
fresh semantic identity for every traversal of a cycle. If the system needs
path-specific guard behavior, that behavior must be represented in `C` and
proved equivalent for states sharing a key.

### 3.1 Conditional semantic conservation

The finite closure theorem alone says nothing about source meaning. Let `Γ` be
the fixed `Bound`, `Move_L`, `Move_U`, and `ReplayCtx` background facts, and let
`Models_Γ(S)` be the assignments satisfying `Γ` and state set `S` under a
separately defined bound judgment. If every candidate rule is sound for that
judgment—each conclusion is entailed by its premises under the same assignment
and `Γ`—then

```text
Models_Γ(S_0) = Models_Γ(R_Γ(S_0))
```

because closure only adds consequences and retains all original states. This
corollary is conditional. Defining `Models` to require every generated replay
query would make the equation immediate but would not prove that the source
typing judgment has that meaning. The successor/source bridge must establish
the premise independently.

## 4. Separation from concrete compatibility transitivity

The replay rule is a consequence rule over `Lower` and `Upper` payloads at a
shared pivot. It is not the rule

```text
Compat(A,B) ∧ Compat(B,C) ⇒ Compat(A,C)
```

The user's optional-Record observations refute that latter rule. Under the
separate bound judgment, a replay-generated `Compat(A,C)` is an additional
local query with lower/upper provenance; it must be resolved independently.
Its selected cast/check evidence stays on that replay identity and does not
become a general subtype edge. Runtime execution location and adapter
composition remain outside this theorem.

The suspended-obligation counterexample in the boundary note remains useful:
if a source meaning says that `Compat(A,X)` and `Compat(X,B)` are the entire
constraints, their success at `X={}` does not imply `Compat(A,B)`. Therefore
the semantic conservation premise cannot silently identify those independent
checks with `Lower(A,X)` and `Upper(X,B)`; the source must justify the stronger
bound judgment.

## 5. Why the finiteness premises matter

Fixed finite state keys are essential. If the context records an unbounded
edge history, even a one-node cycle can generate infinitely many contexts:

```text
Bound(X,X,e), Lower(i,X,A,c)
    ⇒ Lower(i,X,A,append(c,e))
    ⇒ Lower(i,X,A,append(append(c,e),e))
    ⇒ …
```

Likewise, if each replay traversal allocates a fresh boundary identity, a
single lower/upper pair can yield infinitely many distinct replay states.
These examples refute unconditional finiteness for those encodings; they do
not show that the successor source judgment requires either encoding.

This theorem also excludes dynamically generated variables, structural
decomposition that creates child bounds, changing equality quotients,
extrusion, recursive cast instantiation, generalization, freshening and SCC
intrusion. Each extension needs a finite-state and preservation argument of
its own. The full type-inference replacement objective remains active.

## 6. Frozen-source correspondence and unresolved bridge

At frozen commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`:

- `crates/infer/src/constraints/machine/propagate.rs::step_subtype` turns a
  variable-to-variable comparison into a lower bound on the target and an
  upper bound on the source, with the source constraint as derivation.
- `crates/infer/src/constraints/machine/bounds.rs::cpk_lower_bound_replay_actions`
  prepares routes from a new lower bound to existing uppers;
  `cpk_upper_bound_replay_actions` does the symmetric work. Eligible replay
  actions retain `BinaryReplayDerivation { pivot, lower, upper, rule }` and
  replay claim parents; routing can enqueue, deduplicate, or prefilter a route.
- `crates/infer/src/constraints/tests/case_01.rs::var_bound_addition_replays_against_opposite_bounds_with_union_weights`
  asserts a composed-weight lower/upper endpoint constraint. The neighboring
  `var_var_replay_materializes_transitive_edges` case asserts propagation of
  variable edges and a concrete lower bound along the chain.

These are source and test-contract evidence for the frozen operational route,
not proof that the candidate `Lower`/`Upper` judgment is successor semantics.
The frozen machinery additionally has constraint weights, route admission,
extrusion, incomplete/evidence-only replay and detailed provenance rules that
the finite theorem abstracts away. No tests were executed for this note.

Before extending structural residual factorization, close the following
successor obligations:

1. Define the meaning of `Bound`, `Lower`, and `Upper` independently of local
   `Compat` success, or show why the candidate factoring is wrong.
2. Prove each transport and replay rule sound for that source judgment under
   one shared assignment.
3. Define context/guard combination and prove equal canonical keys have equal
   guard and conversion-selection behavior.
4. Bridge original source boundaries and replay derivations to specialization
   queries without losing either logical provenance or the eventual execution
   site for a selected conversion.
5. Extend the finite carrier through recursive structural children, symbolic
   effects, generalization, freshening and SCC intrusion.

No source syntax, acceptance behavior, cast-selection policy, runtime adapter
rule, resource limit, or implementation representation is selected here.

## 7. Source-meaning obstruction and a conditional port hypothesis

A bounded architecture audit identified a necessary distinction for any
source-preservation proof. Suppose a lower and upper payload were interpreted
only as two independent suspended local checks:

```text
Lower(A, X) means Compat(A, X)
Upper(X, B) means Compat(X, B)
```

For `A = {foo?: string}`, `X = {}`, and `B = {foo?: int}`, both suspended
checks pass under the user's Oracle observations, but replay's `Compat(A, B)`
fails. Thus those two independent checks do not entail a replay query. This
does not contradict the frozen Oracle route; it rules out using independent
local-check satisfaction as its source justification.

One conditional explanation is to treat an inference variable as a
transparent interface port between producers and consumers. A lower payload
would retain a producer contract and its typed view at the port; an upper
payload would retain a consumer demand. Variable-bound transport would move
those contracts without inserting a conversion. If the port is transparent,
each admitted producer must safely reach each admitted consumer, so the
lower/upper replay becomes a separately resolved local compatibility query.
This can explain replay without composing successful conversions.

An actual source compatibility boundary might break transparent transport by
establishing a new consumer-facing contract, but need not emit a data
conversion. For example, a shape check could seal the exposed view to `{}`
while runtime preserves the original Record with its extra fields. Conversely,
a selected and emitted adapter could materialize a target-facing value. These
are separate questions: whether the source boundary starts a new typed
contract, and whether its runtime realization changes the value. A successful
`Compat` check at an arbitrary comparison does not by itself establish such a
contract boundary; nor does an emitted adapter by itself explain which source
obligations are discharged. In schematic form:

```text
producer A → transparent X → consumer B
    requires a justified local A-to-B query

producer A → source boundary exposing {} → producer-view {} → consumer B
    keeps the two boundary queries separate; realization may retain or adapt data
```

The common local resolver under consideration can resolve each justified
query, retaining Record-check, nominal-cast and adapter evidence as distinct
derivations. Its result must distinguish a successful check from selected
conversion evidence and from an adapter actually emitted. Source elaboration
must also say whether a particular check establishes a new consumer-facing
contract. The resolver cannot decide by itself whether a variable path is
transparent or whether a source operation created such a boundary. Execution
must preserve the producer view and place any selected conversion at the
correct consumer boundary; a check-only identity realization may still carry
a distinct typed view if the source contract requires it.

The frozen source provides a grounded transport example and a more precise
boundary locator. In `lowering/expr/block_local.rs::lower_local_binding_stmt`,
the local's public value is the body value; `connect_local_binding_annotation`
adds annotation constraints to that same value slot. During specialization,
`specialize2/task_solver/control.rs::local_let_binding_type` gives a
non-lambda local a fresh open variable, even when annotated. Its initializer
supplies lower information and a later consumer supplies upper information.
So a local annotation does not itself establish a converted port.

By contrast, `specialize2/task_solver.rs::apply_type` and
`consume_expr_value` record a function argument's actual/expected pair against
a materialized signature. When a registered cast is selected,
`specialize2/emit.rs::emit_expr_with_boundary` and
`boundary_expr_with_argument_contract` emit it at that argument expression
boundary through `cast_boundary_instance`. The emitted cast is evidence of
runtime conversion at that site, while the source comparison identity and
consumer view establish the logical boundary. This is frozen-source
characterization, not a successor rule: whether check-only Record boundaries
seal a typed view, and where optional-Record adapters execute, remain
unresolved.

This port account is an unverified hypothesis, not a source rule or approval.
Frozen bound replay establishes the operational route and its logical bound
parents; it does not establish that every eligible pair is a source-level
producer/consumer interaction. The hypothesis fails if substitution loses a
producer view, replay crosses a source boundary that seals a new
consumer-facing contract, or any generated rejecting pair lacks a
source-contract justification. Before adopting it,
trace supported producer-to-local-to-consumer and cast-at-consumer examples
through source generation, specialization and emission, including aliases,
multiple consumers and incompatible guards; then prove replay conservation in
both directions for the resulting source-bound and replay ledgers. A local
type annotation must not serve as the distinguishing example unless its
conversion behavior is separately established.

## 8. Partial frozen source-origin ledger

The ledger below is a bounded trace through the frozen implementation at the
commit named in §6. Its identities describe that implementation only; it does
not assert a successor representation.

| Stage | Evidence and identity | Established relation | Missing bridge |
|---|---|---|---|
| Literal producer | `lowering/expr/block_local.rs::lower_number` creates an expression and fresh `TypeVar`; `expr/constraints.rs::constrain_lower_with_origin` and `constrain_upper_with_origin` emit concrete-to-variable and variable-to-concrete constraints. | A source value can contribute concrete lower and upper payloads. | The origin is not a complete source-location identity for every payload. |
| Local binding and use | `lower_local_binding_stmt` keeps the initializer's value slot as the local public value. `lower_local_name` records a `RefId` targeting the local `DefId`; local references reuse that value unless scheme instantiation creates a fresh variable with witness routes. | Local transport and alias targets retain source binding identity. | Preservation of a semantic producer view across aliases, generalized uses and intrusion is unproved. |
| Local annotation | `connect_local_binding_annotation` reaches `annotation/constraints.rs::connect_value_detailed`, which constrains both directions between the annotation and the existing slot under annotation provenance. | Annotation contributes lower/upper constraints on the local value. | This alone does not show a new value slot, a runtime conversion, or a separately sealed consumer-facing contract. |
| Application demand | `make_source_app` allocates an `ApplicationArgument` `SourceBoundaryId` and source spans. `make_app_with_origins` relates the callee to a Function demand carrying the argument variable; Function decomposition derives the argument comparison. | The expected argument type has a source-owned application boundary and a derivation from the callee constraint. | The inferred constraint is not itself an executable cast placement. |
| Specialization local slot | `specialize2/task_solver/control.rs::local_let_binding_type` gives non-lambda locals a fresh `Type::OpenVar`; `block_type` consumes the initializer into it. `var_type` retrieves the stored slot for local uses. | A producer can flow through one specialization slot to multiple consumer expressions. | This reconstruction is separate from the inference `TypeVar` and does not itself prove which pairs are admissible for replay. |
| Materialized consumer | `consume_expr_value` constructs actual/expected materialized endpoints by looking up `TypeOccurrenceKey`s owned by the argument `ExprId`; `constrain_materialized_subtype` stores endpoint types with `SpecializeSubtypeProvenanceRecordId`s and available source anchors. Endpoints may still contain `Type::OpenVar`. Repeated semantic keys may merge positions and provenance. | Each argument comparison becomes a local root constraint; concrete compatibility resolution happens only if solving exposes concrete endpoints. Repeated uses can retain separate consumers. | Materialized record IDs do not map one-to-one to inference constraint or source-boundary IDs. Provenance may be incomplete. |
| Inference replay | `step_subtype` stores variable-edge and bound records. `cpk_lower_bound_replay_actions` / `cpk_upper_bound_replay_actions` pair same-pivot records; `BinaryReplayDerivation` retains the pivot plus both `BoundRecordId`s. | Frozen inference explicitly retains the logical replay parents. | Those parents do not identify where a selected runtime conversion executes. |
| Specialization replay | `TypeGraph::constrain_open_var_bound_pair` adds `OpenVarBound { parents }` with lower-side and upper-side positions from separate specialization records. | Specialization has a second replay route with whatever parent provenance is available. | Its record IDs are not the inference replay IDs; this carrier has no explicit pivot field, and some routes have incomplete provenance. |
| Cast emission | `emit_expr_with_boundary` wraps an application argument; `boundary_expr_with_argument_contract` selects through `cast_boundary_instance` using solved actual/expected types and emits an instance application around the argument expression. | A registered nominal cast can execute at the consuming argument. | Selection is endpoint/rule based, not keyed by the inference binary-replay identity. The exact discharged-constraint-to-emitted-cast link is absent from this trace. |

The frozen emitter also has an identity-style Record path: when
`same_record_boundary_shape` finds equal field counts and names,
`ensure_emitted_value_with_argument_contract` keeps the expression and changes
its computation metadata to the expected type. Separately, supported generic
`RecordFields` coercion can lower to a runtime alias. These paths show why a
consumer-facing typed view and a data adapter cannot share one evidence bit.
They do not establish that a check-only Record boundary seals transport or
that it discharges a later bound replay. The frozen specialization Record
branch checks required-field presence and matching child types, but does not
settle optional-Record runtime realization.

Accordingly, frozen source evidence currently connects source origins to
inference bounds, connects replay to its two logical parents, reconstructs
materialized consumer checks with separate provenance, and places nominal
casts at argument expressions. It does **not** provide a single identity chain
from an original source boundary through bound replay to the emitted
conversion, or a proof that the conversion discharges exactly that replay.
That cross-stage conservation relation is the next proof obligation. A
successor may choose a different topology, but it must establish the same
logical and execution correspondence before using replay to justify a local
resolver result.
