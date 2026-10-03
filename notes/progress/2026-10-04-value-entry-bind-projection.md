# Value-entry request projection under the shared callback fiber

Date: 2026-10-04
Branch: `research/simple-sub-intrusion`
Status: proof-only conditional lemma; no source rule or implementation authority

## Scope and authority

This lemma uses the user-selected §21 Value-entry schedule, inert whole-
argument construction, callback slot as typed invocation view, and role-first
Function elaboration. It does not give `never`, `Any`, or an empty effect row
an effect meaning. It does not compare effect ports independently, compose
successful concrete inequalities, or define a total subtraction algebra.

The lemma isolates one consequence of the already recorded source equation
`Force(D) >>= B`. It strengthens the informal support statement in §9 of
`notes/design/2026-10-02-typed-computation-core-elaboration.md`: it states the
required quantification over current state and resumption histories explicitly.

## Conditional statement

Fix one inequality query `q`, one assignment `ν`, and one joint typed-family
fiber with the same `K,D` identities throughout. Let `D` be the inert argument
carrier received by an actual Value-entry invocation. In the receiver's source
execution, let `F_D` denote its designated one-layer execution followed by
rebind, and let `B` denote the body and its designated result consumer. The
complete call uses the state-threaded composition

```text
J = F_D >>= B
```

inside the actual complete callback `CallView`; receipt remains before `F_D`.
For a retained-computation entry this equation is inapplicable unless the
body explicitly consumes the carrier.

For each compatible current configuration and every finite legal response,
resumption, alias/store transition, and repeated raw-resumption history
reachable in `J`, suppose:

1. every typed request emitted while executing `F_D` is admitted by row
   descriptor `d` at its original typed occurrence and under the same
   `ν,K,D`;
2. every typed request emitted by `B` or the designated result consumer is
   admitted by descriptor `b` at its original typed occurrence and under the
   same `ν,K,D`;
3. every request-emitting transition in the complete `CallView` belongs to
   one of those two source segments, or is already included in the bound for
   the segment containing it. No request origin, operation instance,
   response dependency, or handler authority is introduced by flattening the
   descriptors.
4. for each occurrence from either segment that is observed at the complete
   call boundary, the source derivation supplies its event-specific `Flow`
   and `Observe` correspondence to that boundary, with the same occurrence,
   handler configuration, and `ν,K,D` fiber. These correspondences are
   admissible independently of the result of `q`.
5. the source-derived linked component-combination evidence maps those
   corresponding observations into `[b,d]` at the common output profile.
   This is a premise of this projection corollary, not a generic row-union
   law and not a consequence of merely sharing `ν,K,D`.

Then each request observed in the complete call is admitted by the same-fiber
combined view `[b,d]`:

```text
Obs(J, q, ν, K, D) ⊆ Row([b,d], ν, K, D)
```

Here `Obs` is the request observation at the complete source `CallView`, not
the union of independently solved port marginals. The bracket denotes the
user-selected linked effect-lifting presentation in its common fiber; it
does not assert a new general row-union judgment. Canonical flat-row
normalization may combine the visible components, while their source
correlation remains in existing constraint/evidence relations. Without
premises 4–5, the operational argument below proves only that each emitted
request has an argument-entry or body/result source origin; it does not prove
transport to the output occurrence or membership in `[b,d]`.

## Proof sketch

Mark each emitted request occurrence by the source transition that emits it.
In the `Return` clause of state-threaded bind, `F_D` has completed at its
current state and control enters `B`; requests in that suffix therefore carry
the second premise. In the `Request` clause, bind preserves the exact request,
origin, typed payload, operation instance, and live `K,D`, and attaches the
remaining suffix to the original continuation. The request is therefore
covered by the first premise, while any later suffix request is covered by
the premise for the segment that emits it.

Apply this argument after every legal resumption. The continuation receives
the current resumed state and retains its original caller lineage; the proof
does not restore an earlier store, identify separate operation instances, or
replay receipt. Multi-shot resumption can revisit either segment in a changed
state, which is why premises 1 and 2 quantify over every compatible state and
history, not just the initial call. Induction over each finite interaction
prefix proves that every observed request occurrence has one of the two
source origins. Premise 4 then transports those same event occurrences to
their complete-call observation positions. Premise 5 supplies exactly the
joint component rule needed to place those observations in `[b,d]`. Neither
transport nor combination follows from common `ν,K,D` alone.

The claim is only about requests in this immediate complete call relation.
Returned latent interfaces keep their own typed paths and require the
existing future-use obligations; this proof does not flatten them into
`[b,d]`. The theorem is query-local: it gives no rule for composing concrete
comparison successes from different queries.

## What it does not establish

The source schedule and callback slot view justify the operational shape, but
the source premises remain to be derived for a Function inequality. In
particular this lemma does not prove that `d` is the callback slot's admitted
argument descriptor, that `b` is the actual body's complete descriptor, that
the rows denote the whole admission domains, or that
`D_checked(q) ⊆ D_actual(q)`. It does not establish endpoint adequacy for
`T_P`, either universal clause of the complete Function comparison, or a
finite principal presentation.

Thus this is not yet a proof of
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)`. The bind argument supplies only
the source-origin factorization. Its typed-profile corollary additionally
requires the still-unproved occurrence maps and joint component rule in
premises 4–5. Neither step interprets effect-position `never`.

The next proof must construct these segment bounds and the complete checked
challenge domain independently of comparison success, then derive the
occurrence maps and linked combination at the output profile and relate the
actual Pure endpoint to its source description over all legal histories. State-slot
runtime transitions and opaque first-class-reference imports remain separate
source bridges; this lemma assumes compatible state/history premises and
does not construct them.

## Review and remaining gate

The first compiler-referee review found a major gap: source-origin coverage
and common `ν,K,D` did not entail event-specific `Flow`/`Observe` transport to
the complete call output or the linked component-combination rule. The
statement was repaired to make both explicit premises. A focused fresh
compiler-referee delta review found the finding closed with no further issue.
Accordingly, the proved content is the conditional bind/source-origin
factorization; typed transport and `[b,d]` membership remain unproved source
obligations. No source semantics, solver carrier, API, or implementation is
approved by this note.

Next: derive or refute those occurrence maps and combination evidence from
the already approved slot invocation view and source-owned `Rel_C`, `K,D`,
`Flow`/`Observe`, `Path`, and incidence. Then derive the checked challenge
domain and actual Pure endpoint correspondence over the same complete
histories. No comparison success may be a premise for admission.

## Source-path derivation attempt

The user-selected facts fix the intended path endpoints and operational
middle for the bounded identity callback, but whether they entail the typed
maps remains open. Let `β` be the original callback-slot profile, with the
linked component `d` at its signed argument position and positive complete-
call contribution. The slot is a typed invocation view, so a call through it
uses `β` for the whole call. Under §21 Value entry, the callback invocation
receives the inert whole carrier `D` at `J_arg` and then executes
`Force(D) >>= B` inside its complete view. A request occurrence `o` emitted
by `Force(D)` retains its operation identity, payload, response dependency and
`K,D` through bind. Under the same concrete callback contract, while the
corresponding receiver boundary is active and before dispatch, the selected
visibility rule makes that Force-exposed request eligible like a direct
callback request. A live slot alone does not establish admission; an escaped
later call needs its own transported view and active-owner proof.

For a call through a supplied formal callback slot, identity lookup preserves
its typed invocation view. Ordinary application relates the whole inert
argument carrier to the formal parameter interface; the separate argument
receipt and §21 Value entry then execute that same carrier once. Thus the
formal-side structural path from `β.p_d⁻` to `J_arg` follows **if** `p_d⁻`
already denotes the argument computation position. If it denotes only a row
component occurrence, identifying it with that computation position is still
part of the open component interpretation.

The execution/observation part of the intended correspondence is:

```text
J_arg --separate argument Receive / Value entry--> Force(D) emits q
  --existing Observe in active complete slot CallView--> p_call
```

The outer receiver separately obtains the callback value through
`Receive(r, callback_slot, V_slot, M_slot)`. The inner
`Receive(u, arg, V_arg, ...)` is the callback invocation's receipt of `D`;
it cannot stand in for the slot owner's receipt of `f`. The slot-view
decision supplies the preserved complete profile; source application and
§21 entry supply the argument-carrier path and receipt conditional on the
component already denoting that argument position. The rules also supply the
complete executing view and preserve the Force event.

`Observe` needs no new event-routing rule: once source elaboration establishes
the correct complete `View(V_slot,p_call,...)`, the existing emission-context
definition makes the Force-emitted event observable at its complete call
position. But `p_call` and the original positive row-component occurrence
`d⁺` are different objects. `Observe` alone proves neither annotation
satisfaction nor membership in the linked `[b,d]` output contribution. The
remaining source lemma must interpret `d⁺` at that position, preserve the
contribution through canonical flat-row normalization, and establish the
inclusion under the same nonempty `Rel_C` fiber. Existing `Path`,
`Flow`/`Observe`, `Inc_C`, and directed-weight/subtraction evidence can record
and check that correspondence; subtraction cannot create the forward
component interpretation. The output `[b,d]` still follows the selected
linked profile rule, not independent port subtyping or row-set union.

This remains a derivation attempt, not a proved result. Formal-slot
application derives the execution and whole-call observation skeleton, but
does not admit an arbitrary existing Pure actual value. Nor does it identify
the positive `d⁺` row member with the observed complete-call position. The
diagram does not settle callback argument admission, actual endpoint
adequacy, universal domain/observation inclusion, or evidence generation in
the solver. The unresolved `Q`, distinct slot-value and argument receipts,
same live receiver before dispatch, complete `CallView`, and linked-component
projection remain separate obligations; success of `Q` must not create any
edge in the diagram.

## Candidate formal-slot profile rule

The smallest candidate that could close the positive projection is scoped to
an application of a known formal callback slot. Let `x` be that formal,
`β` its preserved profile, and `d⁻` / `d⁺` the original linked component
occurrences in the slot's already elaborated interface. Lookup through the
slot view, ordinary application, inert argument construction, actual §21
Value entry, and the complete call view give this structural skeleton:

```text
Γ ⊢ x : CallbackView(β, F_cb)
Γ ⊢ e : I_e                       D = Delay(X[e])
----------------------------------------------------
CallView(β, Receive(u, arg, D), Force(D) >>= B >>= result-consumer)
```

`I_e` is the argument expression's full synthesized interface. It may be
computation-producing or effectful; the application still constructs the
whole carrier inertly, and Value entry performs the force after receipt.
This candidate traces an actual callable whose introduction role is Pure and
whose own parameter syntax selects Value entry. Those facts come from that
callable's source derivation, not from the slot view; a retained-entry value
uses a different execution path. Plugging this candidate actual into the
formal slot leaves `Q` unresolved and makes no claim that the source program
has already passed its type check.

Its candidate evidence obligations, all generated independently of
`Q = T_P <: F_cb`, are:

1. The `d⁻` occurrence is interpreted at the formal's whole-argument
   computation position. Its typed path reaches `J_arg`; the inner argument
   receipt is distinct from the outer slot-value receipt.
2. For each request event emitted during `Force(D)` while the complete call
   view is active under the same concrete slot contract, the same event
   occurrence is observed at `p_call` by the existing pre-dispatch
   emission-context rule. This does not require the event to survive a nested
   handler image; that image may consume it after `Observe` is determined,
   and its arms may emit separate events. Source bind/handler-image evidence
   must retain event origins and response/resumption dependencies under
   shared `ν,K,D`. An escaped later invocation needs its own transported view
   and active-owner evidence.
3. The original positive occurrence `d⁺` denotes that linked
   argument-origin contribution at `p_call`; `b⁺` denotes body and designated
   result-consumer contributions over every compatible post-force state,
   response, and resumption history. The component combination is
   interpreted in the same nonempty `Rel_C` fiber with shared `ν,K,D`, rather
   than by taking independent port marginals.
4. Canonical flat normalization preserves those component occurrences,
   their co-occurrence/correlation evidence, and their joint solution fiber.

Only the execution edge and whole-call `Observe` skeleton follow from the
already selected formal-slot, application, and Value-entry rules. The
`d⁻`-to-argument row-component interpretation, clause (3), and clause (4) are
the missing bridge, not results of the rule as currently specified. In
particular, putting clause (3) in the rule as an axiom would restate the
desired linked lift rather than prove that source elaboration realizes it.
This candidate adds no carrier and imports no subtraction semantics; it
proposes a derivation shape to audit. If the clauses cannot be derived from
the selected linked lift and ordinary source application without a new
semantic choice, this candidate must remain unapproved and the precise
missing choice must be returned for approval.

Even if validated, the rule covers only formal-slot obligations. It does not
admit a preconstructed Pure actual, establish the nonempty checked/actual
challenge domains, or prove either universal clause of the complete
inequality. Those still require the separate `Q` theorem.

## Conditional flat-row transport lemma

One part of candidate clause 4 can be isolated without deciding the component
denotation. Fix one assignment `ν` and one nonempty `Rel_C` fiber, with the
original component occurrences already mapped to their complete views by
existing source-owned typed paths. Let `Flat(R)` recursively concatenate
nested covariant row constructors while retaining every original leaf
occurrence and its existing owner/dependency references. Assume row
combination is interpreted by joining those component views in the same
assignment, and all shared `K,D` conditions are conjoined before projecting
support. Then reassociation/flattening preserves:

- the component occurrence references and their typed paths;
- the shared assignment and nonempty joint fiber;
- each original owner and its incidence/dependency constraints;
- the resulting complete support projection.

The proof is structural on row constructors: a nested row contributes the
same leaf occurrences before and after concatenation, up to a canonical
permutation that carries their references. Since owners, paths, `K,D`, and
`ν` are unchanged, the joint relation before support projection is identical.
Only then does the derived support projection coincide. This is not a proof
that the premises hold for Yulang source rows:
component-to-view construction, row-combination semantics, and normalization
that preserves source identities remain to be established. In particular,
co-occurrence cannot silently quotient distinct terms; if a canonicalizer
consolidates them, its existing evidence must retain the original incidence
and every shared constraint. No row tree, separate marginal product, or new
provenance carrier is part of this conditional lemma.

## Astra audit: source occurrence-to-profile entailment

An Astra audit of the exact source entailment gap confirms that the existing
role, entry, application, Force, complete-`CallView`, and observation rules do
not construct the missing occurrence interpretation. They can derive the
negative path conditional on `d⁻` already denoting the argument computation
position, and they can observe Force-emitted events at the complete slot view.
They do not establish that an original positive `d⁺` row occurrence denotes
the linked argument-origin contribution at that call position. Core §9
explicitly assumes supplied typed-profile/path entries, while callback-context
delivery §2 leaves complete interface formation as an obligation. This is a
non-entailment from the displayed rules, not a counterexample to the selected
linked lift or a proposal to reinterpret effects. The next source proof must
define role-indexed complete Function-interface elaboration before inequality
resolution and derive the `d⁻`/`d⁺` occurrence mapping using existing profile,
path, flow, incidence and shared-fiber evidence. No new carrier is indicated.

### Minimal bounded port-map candidate

For the approved known callback-slot path, a minimal source clause to review
is to construct the profile mapping while elaborating the known callback-slot
Function interface, before resolving the existing value's concrete
inequality. The known instantiated slot interface supplies expected context
to an unannotated callback literal before body constraints; the literal then
forms its own interface under Handler role and compares it to the slot,
rather than copying the slot interface. This clause does not re-elaborate an
existing Pure value. Let the checked slot's target occurrences be
`d⁻`, `b⁺`, and `d⁺` inside flat `[b,d]`. Preserve their separate source
occurrence identities and their common symbolic coordinates under `ν`.
Construct only these correspondences:

```text
d⁻  ↦ (callback formal's whole argument-computation position, J_arg)
d⁺  ↦ (the same Force-origin event occurrences, observed at J_call)
b⁺  ↦ (body/result-consumer events at their reached post-force states, J_call)
```

`J_arg` and `J_call` are the ordinary ports already defined by typed-core §9;
`J_call` is the single state-threaded invocation `Force(D) >>= B`, not an
independent body-only row. The identity callback-slot view supplies the
typed boundary and `CallView` only for invocation through this slot; it does
not change the existing callable's Pure role or its §21 `Value(A)` entry. The
required signed profile paths are distinct:

```text
β.p_d⁻ → V_force.p_force
β.p_d⁺ → V_call.p_call
```

These are source-elaboration obligations, not facts created by the concrete
comparison's success. In particular, they must be constructed independently
of `Q = T_P <: F_cb`; successful resolution cannot supply a missing path or
receipt.

For a Force-emitted event `q`, `Observe(q,V_call,p_call)` locates the event at
the complete call position. `Path` must join the original-profile-to-position
correspondence, that `Observe`, and the matching `Receive` of the callback
slot's live owner in the same activation. Typed `Flow` transports value,
profile, and dependency correspondence; it does not transport an event
between effect rows. The callback-value receipt and inner argument receipt
remain distinct. Row flattening preserves the original occurrence
references; `Rel_C`, `K,D`, and `ν` stay joint until the covariant support
projection.

The three displayed occurrence arrows are required source correspondences
awaiting derivation; they are not established by this note. This candidate
commits to no type-variable-equality shortcut: the two `d` occurrences share
a symbolic coordinate, but the source derivation must produce a typed
profile correspondence between their distinct signed paths. It is bounded to
an existing Pure actual, known instantiated callback contract, identity
argument/result transport, and §21 `Value(A)` entry. It does not cover a
retained computation parameter or other adapters, and it does not prove
`D_checked ⊆ D_actual` or complete observation inclusion. In particular,
`Force(D)` explains the operational event link only after this profile rule
identifies its endpoints. This is a candidate operationalization of the
user-selected linked lift, not a claim that the link follows from existing
application/Force rules alone; no API/phase, solver relation, or carrier is
added.

### Astra audit of the bounded port-map candidate

Astra's bounded semantic audit confirms that none of the three arrows is
entailed by the presently approved premises. Application plus §21 Value entry
and Force determine execution of the whole inert argument; they imply the
negative `J_arg` direction only after `d⁻` has already been identified with
that computation position. Stateful bind and `Observe` locate Force-origin
events at a supplied complete slot `CallView`, but shared `ν(d)` alone does
not identify the distinct positive `d⁺` occurrence with that contribution or
provide its signed path and event incidence. Likewise, body/result execution
at reached post-force states does not map the original `b⁺` occurrence to
their complete bound across compatible histories. `Result(I_body)` supplies
an execution skeleton, not this row-component interpretation.

The exact next gate is a bounded role-indexed complete Function-interface
elaboration judgment, before resolving `Q`, deriving original occurrence to
position judgments for the known instantiated callback formal while retaining
distinct signed paths, receipts, and one joint `Rel_C`/`ν,K,D` fiber. The
linked contribution law follows that mapping; complete checked/actual domain
and observation inclusion remains subsequent. A source derivation must stop
and return for approval if it requires changing the actual Pure value's
role/entry, deriving paths from comparison success, merging distinct
receipts, or assuming an unapproved row-contribution premise. This audit found
no representation obstruction and selects no API or compiler phase. It does
not establish a counterexample or settle whether the missing elaboration can
be derived without an additional semantic premise.
