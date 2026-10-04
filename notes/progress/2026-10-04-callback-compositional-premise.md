# Callback theorem under a source-checkable recipe premise

Date: 2026-10-04
Status: conditional proof record; no new semantic authority
Scope: Pure-value callback / Function adequacy main gate
Depends on: Authoritative callback-context-delivery §§2–2.1, typed-core §9,
source-interface-adequacy §4, and the direct main-gate attacks

## Result

One non-tautological, source-checkable sufficient premise isolated by the
failed direct proof is **compositional endpoint recipe realization (CERR)**.
CERR is a structural check on the generator's output constructors, not a claim
that a regular solution exists and not the desired observation inclusion
restated. The current evidence does not prove CERR is weakest or necessary;
its minimality remains open.

For each callback invocation, CERR requires the generated complete endpoint
to be assembled from the existing entry/argument, typed rebind, body/result,
and designated result-consumer constructors by the ordinary state-threaded
bind equations. For the stated conditional theorem, its atomic segment nodes
also need a local adequacy check; constructor shape alone is insufficient.
The checkable conditions are:

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
6. each argument, body, and result-consumer endpoint covers its own source
   segment's finite observations and returned first-order values in the same
   fiber; and
7. the canonical flat output row `[b,d]` retains each component descriptor
   and its `ν,K,D` references from the `d⁺` and `b⁺` occurrences, with the
   existing occurrence/path links; it does not reconstruct, filter, or
   independently approximate those components; and
8. every return admitted by an argument-segment bound is a valid input to the
   generated typed rebind/body continuation, including after each permitted
   resumption; and
9. introduce no independent complete-call bound leaf.

The finite recipe and shared endpoint identities are checked from the
endpoint-generation clauses and their constructor references. The local
segment bounds may retain conservative slack and need not be exact. The
typed-return condition is essential:
the existing adequacy bind lemma covers successors admitted by the bounds,
whereas source-reached successors alone do not cover conservative slack.
`Flow`/`Observe` transport and locate evidence but do not establish local
segment adequacy or the component-preserving row inclusion by themselves.

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

This is a deliberately restricted sufficient fragment, not a minimum-
assumption theorem for general Function adaptation. In particular, the shared
argument endpoint excludes distinct parameter endpoints related only by
variance/adaptation. No necessity claim is made for this restriction.

**Proof.** The common source-owned argument endpoint gives domain equality
under the shared `ν`. Each source entry/body/result observation belongs to its
local segment bound by condition 6. Induct on the finite bind history. At
entry, use the typed rebind condition and segment `Flow`/`Observe` evidence.
A return continues along the generated rebind/body edge. A request preserves
its existing continuation; on every permitted resumption CERR supplies the
next edge at the same fiber. The body and result-consumer cases repeat the
same argument. For conservative slack admitted by a segment bound, condition
7 preserves the exact row component that admits it, together with its
dependencies and occurrence path, in the canonical flat target row. Thus
every member admitted through those segment components remains admitted by
the linked target bound. No row-union inference,
exact segment presentation, new carrier, or concrete-comparison transitivity
is used.

The theorem is deliberately bounded: it does not cover nested escaping
closures, latent future behavior, arbitrary higher-order challenge values,
or State/import worlds. Extending it requires applying the same recipe check
recursively to their existing typed constructors, not assuming the whole
Function theorem.

## Separate source-generation result

There are two generators here and they must not be conflated. Typed-core §9
does give a source-level **operational graph** construction: for every
resolved ordinary core callable, allocate its carrier port and link the
actual entry, bind, body, result consumer, and return delimiters; recursive
references reuse graph nodes. The ordinary source code graph therefore has
the constructor shape needed for the operational bind argument. This proves
the source operational-graph shape property, not finite endpoint generation.

It does not prove that the finite **inference endpoint** has that shape or
bounds the operational graph. §9 explicitly leaves the symbolic complete
image as an inference obligation. The conditional theorem above concerns
that finite endpoint, so the operational graph theorem cannot discharge it.

The authoritative B contract does **not currently entail CERR or its local
adequacy checks**. B requires
independent parameter/body/result synthesis and one final `F_lit <: F_cb`,
but callback design §2.1 step 6 leaves formation of the completed interface
as an obligation. Typed-core §9 supplies the operational `J_call` image for a
resolved ordinary semantic interface and expressly does not construct a
finite presentation for every caller. Source-interface-adequacy §4 proves
bind lifting for a supplied adequate interface; it does not identify the
syntax-generated endpoint with that interface.

This is an underdetermination theorem about the finite endpoint-generation
contract: a finite abstraction that maps the operational links to the same
entry/rebind/body/result constructors, locally covers each source segment,
and preserves their joint bound can satisfy the premise; a completion that
independently adds a conservative
complete-call bound leaf still satisfies B's stated endpoint independence
and final inequality ordering, but can admit an observation without segment
factorization. The current documents specify neither finite abstraction.
Therefore no theorem that the finite Yulang inference endpoint satisfies
CERR follows yet, and no Yulang source counterexample follows either.

The exact unresolved item is the bridge from the §9 operational graph to
the finite endpoint emitted after B step 5. Its step-6 rule must define the
existing-constructor abstraction and establish local typed closure for every
bound-permitted successor. This is a missing finite-generation rule/premise,
not a user semantic choice and not a reason to add new evidence machinery.
Until that bridge is proved, the Pure-value callback/Function adequacy gate
remains open.

No code, tests, or semantic authority changed.
