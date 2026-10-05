# Public notation candidate for releasing handler protection

Date: 2026-10-05; corrected 2026-10-05
Status: Draft / Exploratory; records the user's selected local meaning of `?`; slot attribution/elaboration, grammar, broader source projection, and implementation remain open
Scope: candidate public meaning of postfix `?` on an effect component in a Function type
Governing sources: [ordinary computation semantics](2026-10-02-ordinary-computation-semantics-package.md), [typed-boundary realization](2026-10-02-typed-boundary-realization-draft.md), [callback context delivery](2026-10-03-callback-context-delivery.md), [concrete compatibility](2026-10-03-concrete-compatibility-boundary.md), [production callback endpoint generation](2026-10-04-production-callback-endpoint-generation-draft.md), and the [SCC-intrusion redesign charter](2026-09-29-scc-intrusion-redesign-charter.md)
Implementation authority: none
Supersedes: none; withdraws this draft's prior optional-provenance-edge interpretation of `'e?`

This note records the user's selected local meaning for `'e?` and identifies
the remaining source-to-public interpretation work. That local reading is
settled: `?` releases the protection associated with the marked slot while
preserving provenance and membership. The note does not yet define general
source attribution/elaboration, grammar, or implementation. The earlier edge
interpretation in this draft is withdrawn. Its finite probe remains an
independent provenance/support characterization only; it is not evidence for
the meaning of `'e?`.

## Motivation

Handler hygiene can protect an effect contribution associated with an input
component from being handled while it passes through a particular typed slot.
Some Function interfaces need to say where that protection stops applying.
The proposed notation is:

```text
'a ['e, foo] -> ['e?, 'f] 'b
```

The `?` marks a change in **handler protection** for contributions attributed
to `'e` as they pass through the output slot. Their provenance remains `'e`.
The notation says nothing about whether a contribution flows, whether an
effect row contains a member, or whether a provenance edge exists.

## Intended reading

Read `'e?` as:

> For an `'e`-derived effect contribution leaving this slot, stop protecting
> that contribution from handlers.

The proposed transition is:

```text
contribution q
  provenance/source component: 'e
  handler protection: active
       -- passes through the 'e? slot -->
contribution q
  provenance/source component: 'e
  handler protection from this slot: released
```

The contribution retains its source component, event identity, family and
arguments, typed paths, origin/lineage, and the existing `K,D` dependencies.
Only its protection status changes. Once released, later handling follows the
ordinary handler search and eligibility rules. Release does not itself select
a handler, guarantee consumption, erase the contribution, or authorize a
handler whose ordinary source rules do not apply.

In the example, the input's concrete `foo` capture contract and the output
marker answer different questions. The concrete contract can make a matching
contribution eligible for the receiver-local handler under the existing
source rules. `'e?` says that the protection associated with the `'e` slot is
released when that contribution leaves this slot. It does not copy `foo` into
`'f`, and it does not make `'f` equal to `'e`.

Thus:

```text
['e?, 'f]  -- same 'e-derived contributions, with slot protection released
['e,  'f]  -- ordinary unmodified row components; no release is stated
```

The difference is protection state, not row membership or provenance. `?` is
not an optional-flow quantifier.

## Small-step / relational interpretation candidate

Use existing source observations and event evidence to identify a contribution
`q` at a typed slot `s`. Let `Prov(q)` stand for its already established
provenance, including its source component; let `Prot(q,s)` mean that source
evidence associates handler protection at slot `s` with `q`. Let `Ord(q)` be
the ordinary event contribution, without changing its identity or type.
These are metatheoretic names for this candidate, not new compiler fields.
Attribution and protection are premises supplied by their own source/evidence
rules; event identity, lineage, path, and provenance do not define the meaning
of `?`.

The proposed local release rule is:

```text
MarkedReleaseSlot(s, 'e)  and  AttributedTo(q, 'e, s)  and  Prot(q, s)
-----------------------------------------------------------------------
ReleaseProtection(q, s) = (Ord(q), release Prot(q, s))
```

`AttributedTo` must be established by the existing source/occurrence/path
evidence. The marker does not create that attribution; unrelated
contributions in the same output row do not satisfy this rule merely because
they share a family.

Its frame condition is essential:

```text
Prov(after) = Prov(before)
FamilyAndArguments(after) = FamilyAndArguments(before)
EventAndOrigin(after) = EventAndOrigin(before)
TypedPathAndDependencies(after) = TypedPathAndDependencies(before)
RowSupport(after) = RowSupport(before)
OnlyProtectionForThisSlot(after) differs
```

If no contribution from `'e` is present in a particular source observation,
the rule has nothing to transform. That absence does not make `'e` membership
optional and is not encoded by `?`.

After release, the contribution is considered by the usual active-handler
search and source-defined eligibility judgment. `PassQuestion` neither
performs subtraction nor changes a handler image or residual support. Any
interaction with shallow/deep handling, attached subtraction, or row support
must follow from a separate theorem connecting those existing judgments.

For nested boundaries, the candidate target is the protection associated
with the slot where `?` appears. Other independently justified protections
must remain distinguishable in the existing scope/path/evidence relation. A
single marker should not be read as a counter that counts protection layers;
the exact attribution and composition rule must be established before this
candidate can claim that `??` is unnecessary in every case.

## Relation to current directed-weight machinery

The available design material has different authority levels. Callback
expected-context delivery and the Pure-value invocation-view rule are
Authoritative. The ordinary-computation and typed-boundary packages are
reviewed Draft source candidates. Frozen Oracle weights are characterization
evidence only under the SCC charter.

| Needed fact | Existing candidate evidence | Limit |
|---|---|---|
| Which contribution came through `'e` | Source event/origin, typed `Flow`/`Observe`, `Path`, occurrence/incidence, shared `Rel_C` and `K,D` | Family equality and row support alone cannot identify this contribution. |
| Whether it is protected at this slot | Callback boundary, typed boundary/profile transport, active scope, receipt and occurrence evidence | Current source material does not yet define the complete annotation-to-output-slot protection judgment. |
| Where protection is released | The public slot bearing `?` in this candidate | Source typing/elaboration has not shown how that marker maps to the source slot or to nested/latent views. |
| What happens afterward | Existing ordered handler search and source eligibility | Release does not itself grant a capture contract or consume an event. |
| What stays invariant | Existing event identity, origin, typed path, attachment, and `K,D` evidence | No theorem yet proves the frame condition through every Function endpoint transformation. |

Frozen Oracle uses `PWeight(L,T)` and `NWeight(R,T)` for projected positive
and negative occurrences. Directed left weights can retain ordered `pop` and
active `take(F)` steps; right weights retain pure pops. The historical weight
spec uses `@u[Empty]` for an active `take(Empty)` push with zero consumable
family budget. Frozen public-reference prose uses occurrence-local
`#id[Empty]` for protected/non-subtractable evidence. `AllExcept(S)` records a
residual family filter. These are subtraction/weight facts; none alone means
“release handler protection while retaining provenance.” They are not
successor semantics.

The current Yulang3 production crates have no live `PWeight`, `NWeight`,
`StackWeight`, `SubtractId`, or `AllExcept` carrier. That implementation fact
does not show that a new carrier is needed. First test whether the release
operation is a public projection of `Rel_C`, typed paths, occurrence/incidence,
attachment, and existing source protection evidence. Do not duplicate the
regional, attachment, or provenance machinery under new names.

## Examples

These examples are semantic probes for the candidate, not accepted programs
or new typing rules.

### Higher-order callback

```text
run : 'a ['e, foo] -> ['e?, 'f] 'b
```

A `foo` contribution attributed to `'e` may be handled at the input boundary
when the concrete contract and ordinary dispatch permit it. If that same
contribution reaches the output slot, its provenance remains `'e` and its
protection from this slot is released. An unrelated body contribution in
`'f` is unchanged. No input-to-output flow is asserted, and `'f` receives no
`'e` provenance by this notation.

### Nested handlers

If an `'e`-derived contribution crosses the marked output slot while inner and
outer handlers are active, `?` does not choose either handler. It releases the
protection associated with this slot; then the normal ordered search and
eligibility rules decide whether an active handler can handle the contribution.
Any distinct protection from another boundary must remain represented by its
own existing scope/path evidence. The marker does not remove a family from the
handler image.

### Shallow handler and resumed continuation

A shallow handler may handle one `foo` event and resume its raw continuation,
which may produce another `foo` event. `'e?` does not merge these events or
delete either one. For each event, existing provenance evidence decides
whether it is an `'e` contribution; only then can the slot release rule apply
to its protection. The handler's subtraction/residual result is computed by
the separate shallow-handler semantics.

### Deep handler

The marker is not a deep-handler rule. If a deep handler recursively handles
requests, the source handler semantics determines which requests it handles.
The `?` marker only changes the protection state of an `'e`-derived
contribution at its typed output slot; it does not express attached
subtraction, deep re-entry, or row-support projection.

### Recursive handler

Repeated recursive entries may produce many dynamic events of one family.
Each event retains its event identity, origin and `'e` attribution where
established. The marker changes protection for qualifying contributions at
the slot, not event multiplicity, recursive behavior, or family membership.

### Existing Pure value in a Handler callback slot

An existing Pure function passed through a Handler callback slot keeps its
underlying Pure role and original entry semantics. The slot's typed invocation
view remains governed by the Authoritative callback-context contract. If the
view carries an `'e?` output slot, the candidate release applies to its
`'e`-attributed contributions there; it does not rewrite the stored value or
turn it into a Handler.

### Same family, distinct origins

Suppose `q₁` is attributed to `'e` and `q₂` is an independent local `foo`
event. Shared family support does not merge them. At the marked slot the
release can affect `q₁` only if the existing source evidence attributes it to
`'e`; it does not change `q₂` merely because `family(q₁) = family(q₂)`. Both
events still contribute to ordinary family support according to the source
execution.

## Counterexamples / ambiguity tests

1. **Optional-membership mutant:** read `'e?` as a row member that may be
   absent. This changes membership rather than protection.
2. **May-flow mutant:** read `?` as “some contribution may flow from `'e` to
   `'f`.” No such edge or flow fact is stated.
3. **Provenance-erasure mutant:** delete the `'e` origin after release. This
   violates the frame condition.
4. **Family-wide release mutant:** release every `foo` event because one
   `'e`-derived `foo` was released. Same-family origins remain distinct.
5. **Subtraction mutant:** remove a handled event from output support merely
   because it passed through `?`. Protection release is not handler
   subtraction.
6. **Handler-selection mutant:** interpret `?` as selecting the next active
   handler or guaranteeing consumption. Ordinary ordered search remains in
   control.
7. **Role-rewrite mutant:** use the marker to convert an existing Pure value
   into a Handler. The callback slot only supplies its typed invocation view.
8. **Sticky-protection mutant:** retain the protection released at this slot
   as if `?` described provenance rather than its protection state.
9. **Layer-count mutant:** require `??` to release two nested protections.
   The candidate instead assigns the one marker to its typed slot; whether
   current evidence identifies that slot-local protection is an open proof
   obligation, not permission to add repeated punctuation.

## Principal-type implications

`'e?` changes a protection annotation, not the set of effect-family members
and not the contribution's source identity. Therefore principal comparison
must compare the accepted protection behavior along with ordinary row
membership and the complete typed observations. It cannot order schemes by
adding or deleting may-flow edges.

Potentially, the marker can be projected away when a theorem proves that the
released and unreleased protections yield identical ordinary handler
eligibility and downstream observations for every admitted source execution.
That condition is not established by equal family support. Projection is
unsafe if it lets a handler consume a contribution that the unreleased scheme
protects, blocks a handler that the released scheme permits, merges same-family
origins, or changes a later typed dependency. No principal-scheme order for
protection annotations is selected here.

## What this notation does not mean

`'e?` does not mean:

- optional membership of `'e`;
- a may-flow or provenance edge from `'e` to `'f`;
- loss, creation, or relabeling of `'e` provenance;
- automatic subtraction from an effect row or handler image;
- a new shallow/deep handler rule;
- automatic handler selection or guaranteed event consumption;
- a change to the underlying Pure/Handler role of a callback value;
- a special meaning for `never`, `Any`, an empty effect row, or a polarized
  solver bound; or
- authorization to add a solver carrier or change production inference.

## Open questions

1. What exact source relation says that a dynamic contribution leaving this
   slot is attributed to `'e`, across higher-order values and typed latent
   paths?
2. What is the precise source step at which the slot releases protection,
   especially if a returned latent value is invoked again while an enclosing
   receiver remains active?
3. How does a released contribution re-enter ordinary ordered handler search
   without treating release as a capture grant or subtraction?
4. Across nested, shallow, deep, recursive and resumed executions, which
   protection belongs to this slot, and how are other independent protections
   preserved?
5. Can the required attribution and protection state be derived from existing
   `Rel_C`, occurrence/incidence, typed paths, attachments, and evidence, or
   is a specific source fact missing? No missing fact is established yet.
6. Can one slot-local `?` express release when multiple boundaries overlap,
   without a `??` syntax? If not, show the smallest source case that loses a
   distinction before considering richer internal representation.
7. Does the protection marker survive in the final public scheme, or can it
   be projected away while preserving every handler observation and principal
   solution?
8. What principal generality order compares schemes that differ only in
   protection state?
9. How should postfix `?` be tokenized in type context without changing its
   meaning?

## Syntax observation

The type reference admits `SigilIdentifier` as a type atom. The apostrophe
sigil scanner delegates to `scan_identifier`, which consumes one optional
trailing `?` or `!`. Thus `'e?` is currently one sigil identifier token, not
an identifier followed by a distinct type-level suffix. The effect-row
introducer `'[` is a separate adjacent-token grammar and does not resolve
this collision. A future syntax gate must choose token ownership/precedence or
another spelling. Syntax preference cannot redefine the protection-release
semantics recorded here.

## Recommendation

Treat `'e?` as a **protection-release annotation candidate** on an effect
component. The corrected meaning is coherent with the general idea that
protection is attached to typed slot paths while provenance and event identity
are retained independently. Existing `Rel_C`, occurrence/incidence, typed
path and attachment evidence are the first projection substrate to inspect;
no duplicate carrier is justified by current evidence.

The current source packages do not yet define the complete slot-to-event
attribution relation or prove that one `?` releases exactly the intended
protection while preserving all other source observations. The candidate is
therefore **(B) additional semantic organization is needed, but the direction
is promising**. The minimal missing result is a source-to-public projection
theorem for slot-local protection release, including nested/latent lifetime,
ordinary post-release eligibility, and the frame condition preserving
provenance, row support, and `K,D`.
