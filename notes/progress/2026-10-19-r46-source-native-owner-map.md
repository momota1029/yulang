# R46 source/native owner map — `q = loop y`

Status: primary read-only source/native map; frozen against R46 rev2 source pins
Sprint: `source-apply-owner-20261019-r46`, revision 2
Baseline: `55ed588e7`
Parent: unchanged full inference/evaluator theorem and Simple-sub A/B; **OPEN, 0 → 0**.

## Method and boundary

This map follows the HIR Apply occurrence forward into source inputs and native
ports, then backward from the typed Function-result consumer. The join key is
the source occurrence and its `ConstraintOccurrenceId`, not a call vector
position, solved endpoint shape, or matching spelling. All source files and
authorities are pinned in the R46 contract. Three source files are primary-owned
worktree overlays at those frozen hashes; overlay observations are not accepted
implementation behavior.

The map is static. No fixture was executed and no test/build/Cargo/runtime
command ran. Consequently, it identifies the exact construction chain and its
guards but does not claim an observed runtime admission for `q`.

## Forward source-to-native path

1. `yu-hir/src/module/local_source.rs` lowers a syntax application tail into
   `LocalSourceForm::Apply { callee, argument, source_form }` at a retained
   `HirOccurrenceId`. The callee and argument are child source slots. For
   `loop y`, the argument is the `Name(y)` slot; this is not the `Unit` slot
   used for a zero-argument application.
2. `yu-solver/src/candidate_source.rs` visits that Apply and records a
   `CandidateRelation::Apply` with callee/argument value endpoints, their
   effects, and result/application-effect endpoints. It creates
   `ApplySourceInput` with the same owner/expression/children, a checking
   occurrence derived from the Apply occurrence, matching source endpoints,
   and initially `native: None`, `introduction: None`. In scoped mode it also
   indexes the source input by occurrence.
3. Before admitting the candidate relation, `admit_candidate_fact` verifies
   that the source input names the same recipe and Apply occurrence and that
   the callee, argument, their effects, result and application effect agree
   with the retained recipe. This is a source-to-generated-relation identity
   check; it does not derive a source typing rule or output telescope.
4. `shadow_apply.rs::admit_candidate_fact` makes a negative Function demand
   from the original relation's argument, argument effect, fresh invocation
   effect, and result. It separately stores the application effect. The
   `NativeInterface` therefore retains callee, argument, callee/argument
   evaluation effects, result, demand, invocation effect/row, and application
   effect. The result component is selected from the checked relation only
   after the source-input equality guard above.
5. `candidate_call.rs::observe_inner` authenticates the exact Apply source
   children, source/checking occurrence, cause, HIR ownership and scopes. It
   checks the negative Function demand's argument, argument-effect,
   invocation-effect and result terms against `NativeInterface`, checks each
   native port's component kind/polarity, and checks the invocation row. It
   rejects malformed source/native joins. `PendingCallConstruction` still
   lists `OriginalGenCall0`, whole registration/interface, argument
   reification/carrier, and complete result/future suppliers among missing
   inputs where applicable. Observation is not a complete source Call
   derivation.

## Backward typed-result consumer path

The pinned typed-computation core distinguishes `Value(A)` from a source
computation judgment `Comp(E,A)` and requires an explicit source introduction
or elimination derivation at the selected typed path. Result data and
computation consumption are not inferred solely from a solved shape.

At the implementation boundary, a live positive Function versus negative
Function comparison is decomposed in `lib.rs` into typed argument,
argument-effect, result-effect and result child pairs. The Function dispatch
retains those four fields and sends each through `candidate_function_port_admit`
in `candidate_context.rs`. The argument fields use the Function argument
operation; Result and ResultEffect use `Preserve`. Result is a Value pair,
ResultEffect is an Effect pair. The relation is then enqueued as typed work.
This is a typed consumer path for an already constructed Function comparison;
it is not a source Application introduction and does not define `D_q`.

The source Generalize and Call authorities require an independently formed
input declaration/interface before they construct or consume later generalized
objects. R45's bounded audit plus the direct R46 pins identify no rule in this
implementation path that introduces the authentic ordinary-Application
`Desc(C_q, rho_A, ValueDescription, sigma_A, D_q)`. R46's independent proof
lane is still responsible for adjudicating exact law applicability at q.

## Occurrence/authentication seam

The overlay's scoped Apply admission calls `authenticate_scoped_apply`. For a
callee that resolves to a local Name, this requires a matching retained
`LocalCalleeRoute`, a `GraphState.local_route_by_occurrence` entry, and an
authentic `LocalFreshRoute`. The source scheduler separately emits `Action::Link`
for a local Name found in `active_initializers`. These are distinct source
events: a Link establishes the initializer endpoint equality; the code does not
thereby manufacture a FreshUse route. The exact applicability of this guard to
the designated recursive q occurrence remains under independent proof/source
review; no runtime failure is claimed here.

The working-tree test candidate adds a regression that checks the result port
and native demand for an ordinary source Apply and rejects substituted
occurrence/effect/result fields. It has not been run and is not evidence for a
semantic source law. No code change is proposed by this map.

## Result and remaining premise

The current source/native owners retain an occurrence-specific path from an
Apply syntax tail to a generated relation, a native Function demand, and typed
result/result-effect consumers. This narrows the implementation correspondence
question, but it supplies no authentic output `Desc`, its ordered dependency
telescope `D_q`, or a complete source Call interface. The first proof premise
still requiring an Authoritative owner is Application result-description
formation at the actual q occurrence, with independently authenticated operand
derivations and exact free dependencies. Complete provider/future/receiver/
return/pending/W/Z arms, two independent frames, alias sharing, and the
original theorem remain open.

Implementation status: **NO_SAFE_CODE_SLICE** under R46's read-only grant.
Source/native correspondence is partial and candidate-only; no production
promotion follows. Parent remains **OPEN, 0 → 0**.
