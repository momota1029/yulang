# R21 candidate field-root incidence bridge: two semantic options

Status: **two unadopted candidate rules**, for independent review and a later
semantic choice. Original `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`
remains **OPEN / closure 0** with its original source, provider, context, world,
occurrence, guard, continuation, Call, soundness, principality, and termination
quantifiers. A source-derived local rule cannot discharge F1 or the independent
FK1 foreign-continuation quantifier.

## Fixed notation and evidence that already exists

Fix the actual request owner `c`, typed field license `q`, callback body realizer
`c_outer`, and one retained `HandlerContinuationArgumentV1` `h_arg` from R6.
`h_arg` names the resolved response definition `d`, its exact callback body
operation/Apply, the selected Catch arm, binder `k`, and one `k response` Apply.
It does **not** say the Apply's result is the arm's final value. Keep the
retained source objects/IDs, including Arc identity, rather than rebuilding a
same-looking matcher result.

Let `m0 = AnnotationMember(v_body, 0)` be the actual native lower from that
callback operation, and `q^- = Allowance(v_q)` its separate licensed upper.
`FieldBoundV1` presently checks `m0 <: q^-` at callback slot 250; it is neither
a rooted response field nor a FreshUse acknowledgement. The response local
annotation at its exact source occurrence `a_d` constructs `L`, paired `A-`
and `A+`, and exposed root `R_d` using actual links `L <: A-` (slot 40) and
`A+ <: R_d` (slot 41), then installs `R_d`. The annotation's positive field
coordinate is `p` at its own source position; its negative checking coordinate
and `q`'s declaration field coordinate are distinct typed objects. In
particular, `candidate_signature_effect` constructs a positive
annotation-origin `Support`/`AnnotationMember` and a negative annotation-origin
`Allowance`; neither positive member is the callback-body `m0`. The
complete successful comparison and its per-child provenance must be retained;
the two top-level links alone do not prove that `m0` inhabits `R_d`.

At the argument Name of the selected `k response`, capture of the installed
response scheme and its actual FreshUse `u` produce value `S_u`. The resumption
constructor uses `negative_response` for the argument and has result ports
`R_ping+/R_ping-`; the Apply produces `R_k`. Existing checks include
`S_u <: negative_response` and `R_ping+ <: R_k-`. There is no type equality
`S_u = R_ping`. Every proposed witness below is a *source-and-native provenance
relation*, not value equality, a cast from permission to lower, or an ordinary
subtyping edge in the opposite direction.

Write `Own(v,f,o)` for a field witness attached to actual graph root `v`,
field coordinate `f`, and origin token `o=(c,q,c_outer,d,a_d,h_arg,m0)`.
`Own` is unavailable in the current solver. Its graph coordinates must be
captured before a use and mapped by that use's actual node-indexed FreshUse
maps; older nongeneric anchors remain shared. `UseOwn(u,...)` is an instance
with the exact Name occurrence, context_use, mapped member/allowance, scope,
and physical task/drain/ack. Neither family matching nor a global consumed
bit constructs it.

Both options also require the following **new, explicit result-map rule**.
It must be supplied by the source owner, not inferred from `h_arg` alone.
First define a least source value-origin judgment `Orig(x,y,D)` with only
these introduction clauses: (i) the selected raw `k` resumption binds the
actual argument value at `u` to the request-result binder named by `c`, using
its saved suffix, not a replacement expression; (ii) a source Name forwards
the value of its exact resolved binder; (iii) a `let` forwards an initializer
origin to its binder, and the block forwards the origin of its final
expression; (iv) the selected branch forwards its actual final expression;
(v) an Apply forwards an origin only if its actual source/Call result rule
derives that origin; and (vi) the Catch forwards the selected arm body's
origin through its actual slot-50 value constraint. Evaluation-effect edges,
type compatibility and mere lexical containment are **not** introduction
clauses. The least derivation carries its source edges, ordered suffix,
branch/provider/scope conditions and native endpoint counterparts; there is
no reflexive “anything of the same type” rule. This definition must itself
receive soundness review, especially its Call and foreign-continuation case.

```text
ResumeMap-intro
  selected Catch arm h_arg; actual resolved k Apply at e; actual argument Name u
  raw continuation of request c, with its full ordered suffix
  inductive Orig(S_u, request-result, D0) by selected resumption binding
  inductive Orig(request-result, e-result, D1) by actual suffix/Call clauses
  inductive Orig(e-result, arm.final, D2) by binding/final-value clauses
  actual Catch slot-50 link arm.final -> R_catch; actual Install(g)=R_catch
  all scope, handler, branch, provider and conflict conditions for D0,D1,D2 hold
  --------------------------------------------------------------------------
  ResultMap(c,h_arg,u,S_u,R_ping,R_k,R_catch,g,D0,D1,D2)

ResumeMap-elim
  UseOwn(u,f,o); ResultMap(...,u,...,D0,D1,D2)
  actual native positive result-child / arm slot-50 / install endpoints correspond
    to D0,D1,D2; dedicated mapped field tasks drain without conflict
  --------------------------------------------------------------------------
  Own(R_catch,f, (o,u,D0,D1,D2)) and, after actual Install(g), rooted g-origin f
```

The inductively built `D0,D1,D2` must account for the actual response substitution into the request result,
the raw suffix's value result, the actual `k` Apply result, and the arm's final
value. It is a composition of individually proven source edges, including the
appropriate variance/positive Function result child in native constraints.
The dedicated field tasks are new candidate native consumers: they must use
the source-derived endpoints for each hop, retain the same origin token and
FreshUse identity, and publish the Catch/g witness only after their own typed
drains succeed. Any conflict rolls back the affected task and dependent
witness; an existing value subtype success by itself is insufficient.
The path may run through ordinary source bindings: `let tmp = k response;
tmp` retains the exact value origin, while `let tmp = k response;
other_response` does not. Being syntactically last is neither necessary nor
sufficient. For the forwarding block, the native trace must include the
actual tmp Install/Name/FreshUse, the Block Finish Group from its
`final_expression` (`candidate_source.rs:1428–1441`,
`shadow_apply.rs:1791–1795`), then the arm endpoint used by Catch slot 50.
Those ordinary value edges alone still need the proposed field-origin rule;
they cannot substitute another definition's or use's witness. Where the suffix
returns a different value, or the arm discards
`k response`, there is no `ResultMap` and this elimination is inapplicable. A branch join
retains its selected alternative; a foreign/opaque continuation requires an
independent derivation. The rule does not turn the `R_ping+ <: R_k-` check into
an origin proof. Catch has a separate scrutinee-to-result link only in its
actual no-value-arm case; a selected operation arm uses its own slot-50 value
link. Field transfer never follows a bare type-compatible upper bound.

This result-map rule is a proposed semantic addition common to both options.
Its complete source derivation is presently missing even for the fixed specimen.
`admit_candidate_fact` owns the authenticated Apply endpoints and ordinary
four-port demand; `candidate_catch_operation_inner` owns the continuation
interfaces; `candidate_source` owns arm result and Catch slot-50 links. A native
trace through all three plus Install(g) must witness the same path. F1/FK1,
nonlocal providers and complete Call remain independent proof obligations.

### Bounded direct-source audit; D1 remains open

For the R20 admitted direct shape, the scrutinee is exactly the resolved
`signal::ping()` Apply, the selected operation arm's final expression is the
resolved Apply `k response`, and `my g` installs the Catch result. The following
is a **candidate source/native slice**, not a completed `ResultMap` or
field-transport derivation:

1. `operation_v1_catch_source` (`candidate_source.rs:705–755`) authenticates
   the scrutinee's operation Apply and retained `h_arg`: same request `c`,
   selected declaration/arm, binder `k`, exact argument Name resolution to
   `d`, and callback body `m0`. The `response` Install action constructs its
   annotated `R_d`; the argument Name action takes the exact local scheme's
   capture/FreshUse, yielding `S_u`. Neither step equates S_u with a
   continuation result.
2. `candidate_catch_operation_inner` (`candidate_effect.rs:932–1033`)
   constructs `k+ = Fun+(negative_response, entry-, returned+, R_ping+)`
   and the paired negative Function at the same actual scrutinee endpoint.
   `admit_candidate_fact` for this precise `k response` (`shadow_apply.rs:1763`
   onward) checks `S_u <: negative_response` and its positive result-child
   `R_ping+ <: R_k-`. These typed comparisons locate the candidate map's
   endpoints, but do not supply its value origin or equate them.
3. The direct scrutinee syntax suggests an empty raw suffix, but the pinned
   source constructor retains `original = endpoints[scrutinee]` and `h_arg`,
   not an authenticated suffix boundary or a source return constructor.
   `candidate_catch_operation_inner` puts `original_positive` at the
   continuation's positive result port; this is a type interface, not a
   value-origin introduction from `S_u` to `R_ping` and then `R_k`.
   Consequently the proposed least `Orig` clauses **cannot derive D1**, even
   for this fixed direct source. No empty-suffix identity/return rule is added
   without its source owner and native correspondence. D0's source
   substitution origin and the actual D1 return map remain OPEN.
4. The direct arm final expression is this same `k` Apply. If the arm is a
   Block, its `final_expression` is that Apply and `candidate_source.rs:1428–1441`
   emits a `CandidateRelation::Group`; `shadow_apply.rs:1791–1795` links the
   actual Apply child to the arm's result endpoint. This supports the local
   D2 arm-value leg, with
   no source-spelling shortcut. `candidate_source.rs:1148–1168` adds the
   selected arm's actual value endpoint to `R_catch` at slot 50; the
   `Work::Install(g)` path installs that exact Catch endpoint/root. A later
   g Name takes a *new* capture/FreshUse. The candidate field witness can
   follow this chain only via the new per-hop mapped typed field drains above.

For `{ my tmp = k response; tmp }`, `D2` instead passes the tmp initializer
Install, exact resolved tmp Name's capture/FreshUse, and Block Finish Group
before Catch slot 50. Each hop needs its own source ownership and mapped
field task; this is not covered by the direct D2 proof. For `{ my tmp = k
response; other_response }`, the Block Group child is `other_response`, so
the inductive `Orig(R_k,arm.final,_)` has no derivation. The source matcher
may still retain h_arg because it finds a nested Apply, but no
`ResumeMap-elim` may transfer response's field to g. The alternative program
is a candidate construction whose HIR admission/native run is unverified.
The fixed direct slice leaves `ResultMap` OPEN and says nothing about arbitrary returned Functions,
nonidentity raw suffixes, branch joins, general Call, or FK1 continuations;
those remain OPEN.

### Proposed prefix scheduling rule shared by A and B

The pinned scheduler currently appends `Action::FieldBoundV1` *after* all
ordinary traversal actions (`candidate_source.rs:1448`); the current
`Action::LocalAnnotation` also constructs and installs in one action
(`candidate_effect.rs:1542–1606`, `candidate_source.rs:1687`). Thus neither
option's pre-capture field use can run by merely moving a proof line.
Propose a **new candidate action order**, at the exact response
`Work::Install(d)` position, with the retained original `h_arg` carried
from source collection:

```text
all callback Operation/Apply/Lambda actions, CatchOperation/q preparation
  -> response initializer effects and complete annotation comparison/drains
  -> construct exposed R_d, retain its checked annotation derivation
  -> EarlyFieldBoundV1(c,q,h_arg,m0,R_d) and A Own / B Pending payload
  -> PublishLocal(response)=R_d
  -> first response Name capture/FreshUse
```

This splits the present LocalAnnotation action into construct/check and
publication actions; no current source action already has this order.
`EarlyFieldBoundV1` carries the **same retained** h_arg/Arc evidence and
the actual callback member, not a second matcher run. Source collection
reserves `(callback-body Apply occurrence, slot 250)` once and checks it
against the *complete* ordinary action/recipe schedule and every competing
field producer before execution. A successful prefix comparison alone does
not establish slot uniqueness. The final post-traversal
`Action::FieldBoundV1` for that exact key is suppressed, not executed twice;
an unmatched key keeps its ordinary disposition rather than borrowing this
early record.

The early record, its q/member task, and A's staged rooted witness or B's rooted
Pending payload remain private candidate evidence. The typed field task must
drain without conflict before local publication or capture. `PublishLocal`
consumes A's staged witness only after those prefix checks succeed and installs
the root with its payload; it does not manufacture a successful final candidate
receipt. A later conflict,
resource failure, duplicate key, annotation failure or solve failure rolls
back the record/edge/root payload and suppresses all dependent final
consumer/runtime/publication receipts, including earlier use-local claims.
Full-candidate conflict-free publication remains a separate final gate; an
early private success is not a proof or externally successful receipt. The
root payload must already be reachable by actual Graph capture before the
first response Name; no post-capture global attachment repairs a missed
prefix. This proposed scheduling rule needs source/native review and an
implementation lease before any code change.

## Option A — carry the successful local annotation derivation

### Introduction

Add `AnnCarry-A` in the proposed `EarlyFieldBoundV1` action after
`construct_candidate_local_annotation` has completed its full check and
formed `R_d`, and before the split `PublishLocal(d)`. The current
`Work::Install(d)` is its intended source position. Its premises are all
independently produced facts:

1. `h_arg` and R6's complete `q,m0,c_outer` source derivations identify the
   same resolved definition `d`, exact callback body occurrence/member, and
   licensed family/field ordinal. The response annotation at `d` has the
   corresponding positive `p`, verified by complete signature traversal.
2. The actual Lambda/body derivation connects `m0` to `L`'s result-effect
   child. The *successful complete* `L <: A-` comparison has a retained
   child-by-child route showing that this particular `m0` was checked against
   the annotation's distinct negative field allowance. The route retains source slots,
   polarity, row variables, scopes and typed native endpoints; a top-level
   success flag or equal annotation spelling is insufficient.
3. The matching positive `A+` field is produced by the same local annotation
   construction/environment, and the actual slot-41 link exposes it at `R_d`.
   This correspondence remains a proof relation between differently originated
   members and never identifies the callback `m0` with the annotation's
   positive `Support`/`AnnotationMember`. The q-indexed negative response allowance remains separate; its R6
   `FieldBoundV1` task has drained without conflict.
4. The callback, initializer, computation-effect and complete annotation
   comparison actions have drained without conflict/resource failure;
   exposed `R_d` is constructed with its positive field coordinate. The
   typed early q/member task has drained and a rooted payload is staged
   provisionally. `PublishLocal(d)` is still withheld. The source slot and
   field identity are unique across the complete schedule.

```text
AnnCarry-A-stage: premises 1–4
  --------------------------------------------------------------
  StagedOwn(R_d,p,(c,q,c_outer,d,a_d,h_arg,m0,D_ann))

PublishLocal-A: StagedOwn(...); all prefix checks/drains successful
  --------------------------------------------------------------
  private installed Own(R_d,p,(c,q,c_outer,d,a_d,h_arg,m0,D_ann))
```

`StagedOwn` is a private rooted payload, not a published scheme, completed
local publication, or externally successful candidate receipt. `PublishLocal`
must consume it before the first response capture; final candidate validation
remains a later gate and can still roll back all dependent records. `D_ann` is the retained exact derivation, including negative check and positive
exposure. This is the **new semantic step**: it declares that one checked
initializer field may be carried as owned evidence through the paired
annotation interface. Existing `L <: A-` and `A+ <: R_d` do not compose to
that result. It carries a field witness; it does not add `m0 <: A+`, equate
`L=A+`, or assert every initializer lower is an annotation lower. Its soundness
requires a simulation showing that this tagged field remains valid under the
annotation's variance, symbolic rows and later mutations/aliases.

### Elimination and actual Catch case

At each captured Name use `u` of `d`, `AnnUse-A` requires `Own(R_d,...)` to
be in the actual root's graph before capture. Map its retained node-indexed
value/effect/member/allowance/scope coordinates using that exact FreshUse;
preserve shared anchors and source IDs. Only after the mapped field's typed
edge is admitted, physically drained and acknowledged with `u`'s
`context_use` does it yield `UseOwn(u,p,o)`. Any missing coordinate, foreign
source owner, conflict, or failed drain aborts/rolls back the use and yields no
ack. A later global FieldBound consumed flag cannot stand in for the use ack.

Apply `ResumeMap-elim` only if the actual raw continuation and selected arm
derive the result map. For the direct `k response` arm whose raw suffix returns
the substituted request value, it can carry the witness through `R_ping`,
`R_k`, the selected arm's slot-50 link, `R_catch` and actual Install(g).
The exact g Name then needs its own capture/FreshUse and mapped typed drain.
If the arm instead binds/ignores `k response` and returns `other_response`,
this option yields no g field from `response` even though `h_arg` still names
the nested Apply. Thus A can derive both missing incidences **conditional on**
the new `AnnCarry-A` semantics and a genuine `ResultMap`; it cannot derive the
second incidence from currently implemented links alone.

### Scope and cost

This rule is local to the exact annotation occurrence/definition, q license,
request, retained h_arg, successful candidate route, and use. It should not
be a global same-type or same-family propagation rule. It preserves ordinary
Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion, and generalization. It retains the complete annotation
proof and mapped field coordinates across Graph capture, so memory and replay
work grow with captured fields/uses; finite resource accounting and termination
must include those records. Publication must be transactional with the
annotation/install and later uses; a conflict invalidates the witness and all
dependent receipts. A field witness is evidence about a particular value
origin, not a new row permission or a subtraction of residual effects.

## Option B — independently expose a response presentation

### Introduction

Add `Present-B` at the same proposed pre-publication action, and publish its
payload atomically with successful response annotation publication. The positive
annotation independently declares a *field presentation* for `R_d`; the
initializer is not yet declared to realize that field. Its premises are the
exact annotation-positive `p`, actual slot-41 exposure/Install(d), complete
source license `q` and retained `h_arg` identifying `d`, and conflict-free
publication. It creates a suspended obligation keyed to the actual definition
and initializer, rather than importing `m0` through the paired annotation:

```text
Present-B: positive p, q/h_arg/d, actual R_d publication
  ---------------------------------------------------------
  Pending(R_d,p,q,d,h_arg,initializer-id)
```

`Pending` is neither `Own`, `UseOwn`, a lower bound, nor a proof that the body
has `outer`. Equal annotations of two different definitions produce distinct
pending records. The source introduction must retain the exact graph-root
coordinate and a source-addressed realization recipe; a post-capture global
record keyed only by family cannot supply this.

### Elimination and realization

For an actual Name use `u`, `Realize-B` first captures/maps `Pending` with the
root's actual Graph/FreshUse and the Name's resolved definition identity. It
then follows the retained initializer source derivation to the actual callback
body `m0`, proves `m0` belongs to that initializer's value and its licensed
`q` field, and constructs the mapped typed member-to-q allowance task in this
use. Its independent premises include the complete successful initializer
comparison `L <: A-`, the positive presentation's declared field coordinate,
the authentic `FieldBoundV1` source/typed drain, exact mapped node coordinates,
and absence of conflicts. The positive presentation uses its own
annotation-origin member. `Realize-B` must record a typed, source-owned
correspondence from the callback-body `m0` through the initializer check to
that independent presentation; it cannot remap, rename or identify those
members merely because their families match. Those inputs are *checked now*, rather than used by
`Present-B` to transfer a field at publication.

```text
Realize-B: Pending(R_d,p,q,d,h_arg,i); actual FreshUse(d,u,S_u,M_u)
           source body(i) yields exact m0; full check(i,A-) succeeds
           M_u maps captured root, m0 and q coordinates; use task drains/acks
  --------------------------------------------------------------------------
  UseOwn(u,p,(c,q,c_outer,d,a_d,h_arg,m0,i,M_u))
```

The consequent is use indexed. At the exposed root before use, B supplies
only a suspended source obligation; it **does not prove the stronger immediate
`Own(R_d,...)` statement** that A proposes. Thus B closes the first gap only
under a revised meaning of “rooted incidence” as a root-owned realizable
presentation; if the original parent demands an already realized field at
Install(d), B alone is insufficient and that exact premise stays OPEN.
This is a material semantic difference for the user to choose, not a renamed
proof of A. If a use occurs after the initializer has changed or outside its
valid scope, `Realize-B` refuses instead of borrowing another initializer's
field. A successful use can then apply the same exact `ResultMap-elim` as A;
discarding the k result or returning another provider yields no g field.

### Scope and cost

B preserves the annotation-positive declared permission without treating it
as actual effect inflow. It demands a new root-owned pending representation,
per-use source/native realization and failure handling. Publication of the
annotation can succeed while this field's realization remains pending; a
dependent g-field claim can publish only after each relevant use's realization,
typed drain/ack and result map succeed. The use transaction must roll back its
pending/realized records and edge together on conflict. Source scope, q owner,
selected handler and provider, field ordinal, annotation occurrence, and
FreshUse context must remain distinct. Finite termination/resource accounting
must charge the delayed recipe and each use; no unbounded retry or recursive
re-formation of the same obligation is licensed.

**B remains BLOCKED for selection:** the pinned Graph capture traversal does
not yet provide a source-rooted payload carrying q/h_arg/m0 and the
independent annotation presentation into the response capture. The proposed
Pending constructor must not be implemented by a global field lookup or an
attachment after capture. This document states the required shape, not its
source/native construction proof.

## Decision and parent application

A gives the direct `initializer -> exposed root` statement, but requires a new
soundness theorem for carrying checked negative initializer provenance across
the paired positive annotation. B keeps the annotation exposure independent
and checks the body when a particular use needs it; it requires a suspended
root field and weakens what can be claimed at publication. Both require the
same separately justified continuation/arm result map and own-use replay.
The direct fixed specimen is a possible local application of either rule only
after those new premises are proved and implemented. Neither is current
language meaning; neither establishes the original universal parent or any
downstream soundness/principality/Call/termination theorem.

Falsifiers for independent review: swap the initializer while preserving its
annotation; use two distinct response Names and borrow the first use's ack;
share an old nongeneric anchor but rename its source owner; alter scope or
provider; make `k response` a nested ignored Apply and return
`other_response`. The last is a **candidate source construction**, not a
verified source-qualified counterexample; the source matcher accepts a nested
Apply shape, but full HIR admission and constraints have not been checked for
that constructed program. R20's 18/18 target receipt backs its baseline
specimen only. In each case a false `UseOwn` or g-field result
refutes the proposed rule/implementation. A source trace, rather than an
assumed transition or green test, is required to establish positive coverage.

Primary evidence: R21 contract SHA `c763210ccedb886930aff02fe064d9963ae6fb9cb3a33b2baa43c2a7d74f7b96`,
R20 CLEAN reviewed prefix/use note SHA `1ab75dd2b5210068ce272de81e41ee42d38c57d41a3b8d193d11b4f1b3387ddd`,
R6 design SHA `276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`.
Current native source pins matched the R21 contract: `candidate_source.rs`
`66b8f88b...`, `candidate_effect.rs` `6112343b...`, `candidate_scheme.rs`
`03b44d0f...`, `shadow_apply.rs` `5bbcf27d...`; the full pins are in the
contract. Checks here were read/search/hash and manual rule/source audit only.
