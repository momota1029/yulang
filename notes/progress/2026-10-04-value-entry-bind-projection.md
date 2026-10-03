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

The intended correspondence is the following candidate obligation diagram,
not yet a constructed `Path`:

```text
β.p_d⁻ --typed slot-to-argument map--> J_arg
  --separate argument Receive / Value entry--> Force(D)
  --same event at active CallView / event-specific Observe--> β.p_d⁺ in J_call
```

The outer receiver separately obtains the callback value through
`Receive(r, callback_slot, V_slot, M_slot)`. The inner
`Receive(u, arg, V_arg, ...)` is the callback invocation's receipt of `D`;
it cannot stand in for the slot owner's receipt of `f`. The user's linked-
lifting decision fixes the intended relation between the negative argument
contribution and positive `d` contribution. The slot-view decision supplies
the preserved profile. The operational rules supply the receipt/Force order
and event preservation. The source derivation must still construct both
receipts, the typed slot-to-argument map, the whole-call executing view, and
the component projection into the linked positive output contribution.

`Observe` needs no new event-routing rule: once source elaboration establishes
the correct complete `View(V_slot,p_call,...)`, the existing emission-context
definition makes the Force-emitted event observable in that executing view.
That fact does not itself prove annotation satisfaction or membership in the
linked `[b,d]` output component. The source maps and component projection must
still be recorded with existing `Path`, `Flow`/`Observe`, `Inc_C`, and
directed-weight/subtraction evidence before resolving `Q = T_P <: F_cb`.
The output `[b,d]` still requires the selected linked profile rule, not
independent port subtyping or row-set union.

This remains a derivation attempt, not a proved result. The exact question is
whether “typed invocation view” plus the selected linked lift entails the
displayed source-path correspondence, or merely fixes its endpoints while a
more explicit source application rule is needed. The diagram does not settle
callback argument admission, actual endpoint adequacy, universal
domain/observation inclusion, or evidence generation in the solver. Review
must check the unresolved `Q`, distinct slot-value and argument receipts,
same live receiver before dispatch, complete `CallView`, and linked-component
projection; success of `Q` must not create any edge in the diagram.
