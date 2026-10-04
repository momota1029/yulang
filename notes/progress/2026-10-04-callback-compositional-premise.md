# Callback theorem under a source-checkable recipe premise

Date: 2026-10-04
Status: conditional proof record; no new semantic authority
Scope: Pure-value callback / Function adequacy main gate
Depends on: Authoritative callback-context-delivery §§2–2.1, typed-core §9,
source-interface-adequacy §4, and the direct main-gate attacks

## Result

The failed direct proof localizes the missing assumption to one finite,
source-checkable property of endpoint generation: **compositional endpoint
recipe realization (CERR)**. CERR is a structural check on the generator's
output constructors, not a claim that a regular solution exists and not the
desired observation inclusion restated.

For each callback invocation, CERR requires the generated complete endpoint
to be assembled from the existing entry/argument, typed rebind, body/result,
and designated result-consumer constructors by the ordinary state-threaded
bind equations. The graph must:

1. link the independently generated segment endpoints to those constructors;
2. for this bounded fragment only, the slot's checked argument descriptor
   and the actual Pure value's §21 Value-entry descriptor are the same
   source-owned endpoint; this is a syntactic endpoint-identity restriction,
   not an equality imposed by adapting a value;
3. carry one `ν` and the existing `K,D`, occurrence/incidence, receipt,
   `Flow`/`Observe`, and subtraction evidence through every edge;
4. close every bound-permitted return, request, and typed resumption under
   rebind and the next segment, including conservative slack successors; and
5. preserve the generated value roots and return members at each constructor;
   in this bounded fragment these are first-order data, with no latent
   callable/thunk future-use obligation; and
6. introduce no independent complete-call bound leaf.

The finite recipe and shared endpoint identities are checked from the
endpoint-generation clauses and their constructor references; universal
closure is then proved by induction on those clauses. They retain slack in
segment bounds and do not require exact segment presentations. Universal
closure is essential:
the existing adequacy bind lemma covers successors admitted by the bounds,
whereas source-reached successors alone do not cover conservative slack.

The endpoint-identity restriction gives `D_checked = D_actual` in this
fragment directly from their common source-owned argument descriptor and
shared `ν`; it does not use comparison success. This deliberately limits the
conditional theorem to calls whose argument profile is already shared by
construction. It makes no claim for distinct parameter endpoints related by
variance or adaptation.

**Conditional theorem.** For the bounded first-order Value-entry callback
fragment, if CERR holds, then `D_checked = D_actual` and the generated
complete endpoint covers every
actual finite legal invocation history and returned first-order value root
in the same `ν,K,D` fiber, and every actual request observation factors
through the argument-entry, rebind, body/result-consumer recipe into the
linked `[b,d]` view. Hence both `D_checked ⊆ D_actual` and
`P_actual ⊆ P_checked` hold for this fragment's complete call/value
observations.

**Proof.** The common source-owned argument endpoint gives domain equality
under the shared `ν`. Induct on the finite bind history. At entry, use the
segment `Flow`/`Observe` evidence. A return continues along the
generated rebind/body edge. A request preserves its existing continuation;
on every permitted resumption CERR supplies the next edge at the same fiber.
The body and result-consumer cases repeat the same argument. Each observed
request therefore comes from one of the linked segment constructors, and
the existing linked-port map places it in `[b,d]`. No row-union inference,
exact segment presentation, new carrier, or concrete-comparison transitivity
is used.

The theorem is deliberately bounded: it does not cover nested escaping
closures, latent future behavior, arbitrary higher-order challenge values,
or State/import worlds. Extending it requires applying the same recipe check
recursively to their existing typed constructors, not assuming the whole
Function theorem.

## Separate source-generation result

The authoritative B contract does **not currently entail CERR**. B requires
independent parameter/body/result synthesis and one final `F_lit <: F_cb`,
but callback design §2.1 step 6 leaves formation of the completed interface
as an obligation. Typed-core §9 supplies the operational `J_call` image for a
resolved ordinary semantic interface and expressly does not construct a
finite presentation for every caller. Source-interface-adequacy §4 proves
bind lifting for a supplied adequate interface; it does not identify the
syntax-generated endpoint with that interface.

This is an underdetermination theorem about the current written generation
contract: a generator completion that builds the endpoint from the listed
bind constructors can satisfy CERR; a completion that independently adds a
conservative complete-call bound leaf still satisfies B's stated endpoint
independence and final inequality ordering, but can admit an observation
without segment factorization. The current documents specify neither
completion. Therefore no theorem that complete Yulang generation satisfies
CERR follows yet, and no Yulang source counterexample follows either.

The exact unresolved item is the endpoint-emission rule after B step 5: it
must define a finite constructor recipe for step 6 and prove its all-bound-
successor closure. This is a missing source rule/premise, not a user semantic
choice and not a reason to add new evidence machinery. Until that rule is
specified, the Pure-value callback/Function adequacy gate remains open.

No code, tests, or semantic authority changed.
