# Public notation candidate for handler hygiene provenance

Date: 2026-10-05
Status: Draft / Exploratory; no semantic, syntax, or implementation authority
Scope: candidate public type notation for a capture contract and optional
effect-provenance flow across a Function boundary
Governing sources: [ordinary computation semantics](2026-10-02-ordinary-computation-semantics-package.md),
[callback context delivery](2026-10-03-callback-context-delivery.md),
[concrete compatibility boundary](2026-10-03-concrete-compatibility-boundary.md),
[production callback endpoint generation](2026-10-04-production-callback-endpoint-generation-draft.md),
and the [SCC-intrusion redesign charter](2026-09-29-scc-intrusion-redesign-charter.md)
Implementation authority: none
Supersedes: none

This note records a surface-notation candidate. It does not revise the
governing source semantics, select a new solver carrier, or authorize changes
to parsing, inference, or the production path. The governing documents remain
authoritative within their stated scope; this note is a projection question
for future design review.

## Motivation

Handler hygiene distinguishes an effect's family from the source path that
made a particular contribution visible to a handler. A concrete callback
capture contract may authorize a receiver-local handler to consume matching
requests while that receiver is active. That authority expires with the
receiver. If a request contribution also reaches a result effect, the result
effect is ordinary output at its new boundary; the input annotation must not
remain a permanent restriction on later handlers.

The candidate notation is:

```text
'a ['e, foo] -> ['e?, 'f] 'b
```

The design question is whether `'e?` can expose the optional provenance
connection from input component `'e` to result component `'f`, while keeping
the capture permission attached only to the input boundary. This is motivated
by a boundary-lifetime fact, not by a need to make effect-row membership
optional.

## Intended reading

The intended reading of the example is:

- The input side supplies component `'e` under a capture contract that admits
  `foo` at this boundary.
- At this boundary, a request contributed through `'e` may be subtracted when
  the source handler and its existing subtraction evidence justify it.
- The output marker `'e?` proposes an optional provenance edge from the input
  component to output component `'f`.
- The edge does not require `'e` to contribute at all. If a contribution from
  `'e` does reach this result position, it is accounted for in ordinary output
  component `'f`.
- The capture permission attached to `'e` ends at the boundary. A contribution
  represented in `'f` has ordinary output eligibility; any later handler uses
  its own active boundary, contract, and ordered search.

The intended distinction is therefore:

```text
['e?, 'f]  -- optional source-provenance edge into f
['e,  'f]  -- two ordinary effect-row members/components
```

The first is not shorthand for the second. The punctuation is evidence about
possible flow, not an optional-membership operator on the row variable.

The prior sketch `'f ['e]` could be read as attaching a lasting capture
authority to `'f` or as saying that `'f` can capture `'e`. The proposed `'e?`
placement instead names the source endpoint of a possible flow edge and makes
the intended authority cutoff at the result position easier to state. This
comparison is about candidate readings only; neither spelling has selected
semantics.

The user has separately selected a polarity-sensitive mixed-row fragment for
a deep handler: the shared abstract component may appear contravariantly and
covariantly, with the targeted concrete contribution removed at the shared
covariant position when the complete source image and attachment evidence
justify it. That decision is recorded in the
[concrete-compatibility addendum](2026-10-03-concrete-compatibility-boundary.md#9-user-directed-mixed-effect-row-fragment-2026-10-05).
It does not select `'e?`, define its optional-edge quantifier, or prove that
this spelling projects that mixed-row relation. The tentative shallow-handler
scheme remains only a candidate.

## Small-step / relational interpretation candidate

The following is one candidate relation for discussing the notation. It is
not a new implementation carrier or a replacement for the existing source
relations.

Let `q` range over distinct request events, `fam(q)` be the operation family
of `q`, `e` and `f` be source effect components, and `b` be the active
receiver boundary. Under one fixed source assignment `ν` and one admissible
source execution, define:

```text
AtInput(q, e)       q is contributed through the input component e
Capture_b(q)        b's contract admits fam(q), and q is connected to b
                    by the source's typed flow/observation evidence
Active_b(t)         receiver b is active at source step t
FlowsTo(q, f, t)    q's contribution reaches output component f by step t
```

Candidate local rule:

```text
AtInput(q,e) ∧ Active_b(t) ∧ Capture_b(q)
  => a handler installed by b may subtract q at t,
     but only when ordinary ordered dispatch and existing subtraction
     evidence select that handler.
```

Candidate provenance-edge reading:

```text
Edgeν(e,f)
  iff under this fixed admissible assignment ν, there is a source execution
      and evidence path in which some q satisfies AtInput(q,e) and later
      FlowsTo(q,f,t).
```

The `?` is a candidate way to expose that a path witnessing `Edgeν(e,f)` may
exist; it does not make a row member present-or-absent, and it does not assert
that every execution takes the edge. If `q` is represented in `f`,
`Capture_b(q)` is not copied to `f`.
After the source step that exits `b`, `Active_b` is false, and any subsequent
handler eligibility is computed from the then-current ordinary source
context. The output component retains its type/effect contribution, not the
expired permission.

This fixed-`ν` relation is only a local candidate. The public scheme still
needs a quantifier across admitted assignments: for example, whether its edge
means a may-flow in some admitted assignment, a permission available in every
assignment, or an exact relation indexed by the assignment. It also remains
open whether the public edge denotes an upper-bound permission or an exact
may-flow fact. Those choices affect scheme generality and are not resolved by
the punctuation itself.

There is also a boundary-alignment obligation. The ordinary-computation
candidate defines callback capture relative to an active receiver and carries
the typed boundary profile along corresponding result paths to later latent
views while that receiver remains active. The proposed public reading instead
says that a contribution represented in output component `'f` is ordinary
there and no longer carries the input capture restriction. These statements
agree when `'f` denotes a result outside the capture boundary (for example,
after the receiver returns). They do not yet establish that merely reaching a
result-typed path cuts capture authority if that path is still observed inside
the active receiver. Thus the projection theorem must say whether the public
`'f` endpoint denotes boundary exit, or prove that materialization at that
endpoint itself ends the callback incidence. This note preserves the user's
intended cutoff as the candidate surface reading; it does not silently amend
the reviewed source-machine rule.

The candidate must be interpreted per event and path. It cannot replace
`q`, `ν`, typed `Flow`, `Observe`, `Path`, occurrence/incidence, or the shared
`K,D` witnesses by a family-set test. In particular, two requests with the
same family may have different source origins and different capture
incidences.

## Relation to current directed-weight machinery

The source contract is split across authority levels: callback-context
delivery and the Pure-value invocation-view rule are Authoritative; the
ordinary computation/capture package is a reviewed Draft source candidate;
the SCC charter makes frozen Oracle weights characterization evidence only.
The current theory provides a plausible evidence substrate, but no proven
public projection theorem:

| Needed fact | Existing source/evidence candidate | Limit of current result |
|---|---|---|
| A particular input contribution is visible at a boundary | `Flow`, `Observe`, `Path`, occurrence/incidence, and the common `ν,K,D` relation | Family equality or row support alone does not establish incidence. |
| A handler may consume that contribution | Active receiver/handler scope, the concrete capture contract, ordered shallow dispatch, and existing directed-weight/subtraction evidence | A weight is not by itself the source rule; each transformation needs a meaning-preservation argument. |
| A contribution may reach a result | Source result/consumer relation and its `d⁺` / `b⁺` occurrences, with typed paths and shared witnesses | Current production endpoint generation has not completed this source-to-endpoint correspondence. |
| Capture authority expires | Source activation/receiver exit in the ordinary semantics | A public row variable alone has no lifetime or activation identity. |
| Same-family origins stay distinct | Event IDs, source origins, occurrence/incidence and `K,D` | Canonical row support intentionally may collapse repeated family membership. |

Frozen Oracle observations and retained research notes use names such as
`StackWeight`, `SubtractId`, `All`, `AllExcept(...)`, weighted
`PosId`/`TypeVar` bounds, and split/residual records. A historical Oracle
trace records residual weights such as `AllExcept(signal)` and
`SubtractId(0)`. These are characterization evidence, not successor
semantics. Repository search finds no live Yulang3 production carrier named
`PWeight`, `AllExcept`, `#u[Empty]`, or `StackWeight`; `StackWeight`,
`SubtractId`, and `AllExcept` occur in historical research records, while the
exact spellings `PWeight` and `#u[Empty]` are not present in this checkout.
This note therefore does not assign those last two spellings an internal
meaning, interpret `#u[Empty]` as an optional edge, or identify it with
public absence.

The directed-weight/subtraction work may account for a *witnessed local
subtraction* and its attachment. It does not presently prove that it can
project the complete relation `Edgeν(e,f)`, quantify the optionality
over all admitted source assignments, or distinguish all same-family source
origins after row normalization. The concrete compatibility design expressly
requires a source/component-to-existing-evidence bridge before treating the
frozen weight rules as successor evidence. No duplicated regional,
attachment, or provenance ledger is proposed here.

The repository layers must also stay distinct when describing this possible
reuse. The SCC charter and the Oracle investigation record directed left/right
weight routing and `StackWeight`/`SubtractId` as frozen-Oracle
characterization; they explicitly do not grant those transformations a
successor denotation. `AllExcept(S)` can characterize a residual family
filter in those traces, but by itself it says neither that an input
contribution reached a result nor when a receiver's authority expired. The
spellings `PWeight` and `#u[Empty]` do not occur in this checkout, so this
note cannot map them to a current Yulang3 object or infer their meaning.

The current Yulang3 solver is a separate fact: its `TermView` exposes
positive/negative Function nodes with four endpoints, while F5 generalization
recognizes only its existing pure-effect endpoint forms. The current code has
no carrier named `StackWeight`, `SubtractId`, `PWeight`, or `AllExcept`, and
no source-level input-to-result provenance edge. These facts describe the
implementation boundary only. They do not make four Function ports
independent effect subtyping judgments, nor establish that a new carrier is
needed: the successor projection should first be derived from `Rel_C`,
`K,D`, typed paths, occurrence/incidence, and existing witnessed subtraction
evidence.

The most economical candidate is to derive `'e?` as a public view over
existing source evidence when that evidence already determines the edge. If
there is a production case where the edge is required but not recoverable
from current `Rel_C`, `K,D`, occurrence/incidence, typed paths, and existing
subtraction evidence, that exact lost fact must be shown before considering
any richer internal representation.

## Examples

These sketches illustrate questions for the candidate relation. They are not
accepted source programs or new typing rules.

The approved mixed-row fragment distinguishes a deep-handler removal from
primitive shallow resumption. It does not settle the public provenance edge in
the examples below; each `'e?` reading remains exploratory, and targeted
removal still requires the complete source image rather than family-wide
cancellation.

### Higher-order callback

```text
run : 'a ['e, foo] -> ['e?, 'f] 'b
```

The receiver may subtract an eligible `foo` event during this invocation.
Another event from `'e` may flow to `'f`; if so, it is ordinary output at the
result boundary. A later handler may consume it under its own normal contract.
The notation does not say that the callback always emits, that all of `'e`
flows, or that `'f` inherits permission to subtract `foo`. This example assumes
the `'f` endpoint lies beyond the capture boundary. If the corresponding
returned latent value is executed again while the receiver remains active,
the current reviewed source candidate retains incidence along that matching
result path; whether the public scheme marks that as the same `'e?` edge, a
second edge, or an already ordinary `'f` contribution is unresolved.

### Nested handlers

Suppose an outer receiver has capture permission for `foo`, and an inner
handler is installed while the outer receiver remains active. The inner
handler's eligibility is decided by ordinary ordered dispatch and the
incidence for that event. If a matching event escapes the inner handler and
reaches the outer result, the outer capture relation may remain active only
while the outer receiver remains active. Once the result is represented by
`'f` outside that boundary, neither inner nor expired outer capture permission
is carried by the output marker.

This case needs the event's boundary path. A single family entry `foo` cannot
say whether the event was captured by the inner contract, the outer contract,
or neither.

### Shallow handler and resumed continuation

A handler may consume a request and resume its raw continuation outside that
selected activation. The continuation may emit a distinct event of the same
family. That later event can reach `'f`, but it is not automatically evidence
for an edge from `'e`: the candidate relation above requires input and output
incidence for the same event `q`. The edge may cover the later event only if
the existing typed-flow/provenance evidence independently connects it to the
input component. Causal succession or family equality alone does not provide
that connection. This is a discriminating case for the projection theorem:
either the public edge summarizes a broader source contribution lineage than
one event, with that lineage already recoverable from current evidence, or
this example lies outside what one `'e?` can express. The note selects neither
interpretation.

### Recursive handler

A recursive callback can produce several distinct `foo` events on successive
entries. The candidate edge is about possible provenance from `'e` to `'f`,
not multiplicity. If the public effect row is set-like, repeated family
membership may collapse in `'f`, while event IDs and source paths remain
distinct in the derivation. The surface marker cannot claim that one event,
all events, or a fixed number of recursive iterations contributes.

### Existing Pure value in a Handler callback slot

An already constructed Pure function passed to a Handler-capable slot keeps
its underlying Pure role and original entry semantics. The slot provides a
typed invocation view, as fixed by the Authoritative callback-context design.
Any input/output provenance edge must be derived for that view and its
invocation evidence; `'e?` cannot rewrite the stored Pure scheme or turn the
value into a Handler. Capture authority ends at the slot's receiver boundary
according to the source execution, not at a permanent property of the value.

## Counterexamples / ambiguity tests

The following tests separate the candidate from tempting readings:

1. **Optional membership mutant:** interpret `'e?` as “the row may omit `e`.”
   This changes the row domain and fails to say whether any `e`-origin event
   reached `'f`.
2. **Mandatory-flow mutant:** interpret `'e?` as “`e` must occur in output.”
   This rejects the intended no-contribution execution.
3. **Ordinary-union mutant:** replace `['e?, 'f]` with `['e, 'f]`. This turns
   provenance into unconditional row membership and erases the boundary
   relation.
4. **Sticky-authority mutant:** carry the input `foo` capture permission into
   `'f`. This allows a later handler to use an expired receiver's contract.
5. **Family-set mutant:** merge two `foo` events from different origins and
   let one event borrow the other's capture incidence. Existing hygiene rules
   reject family equality as authority.
6. **Shallow-resumption mutant:** remove `foo` from output merely because one
   event was handled. A resumed raw continuation may emit a distinct `foo`
   event after the selected handler.
7. **Role-rewrite mutant:** use the marker to convert an existing Pure value
   into a Handler value. This violates the slot-view/underlying-value
   distinction.
8. **Persistent-edge mutant:** interpret `'f ['e]` as a standing right for
   future handlers to capture `'e`. That is not the proposed cutoff behavior.

For overlapping scopes, a surface spelling such as `e??` should not be
introduced merely to count boundaries. The candidate would instead derive
the path through the existing nested source scopes and emit one `'e?` only if
the public type boundary exposes one unambiguous source component and result
component. If two independent paths from the same `'e` to `'f` have different
capture histories, one unindexed marker cannot state which path the edge
summarizes. This is a genuine ambiguity to test, not a license to add a
second marker or carrier preemptively.

## Principal-type implications

Let a public scheme denote a set of admitted source/evidence models, ordered
by reverse constraint strength: a scheme is more general when its
interpretation admits every model admitted by the other scheme. Under one
candidate reading, an optional edge records a *may-flow allowance*. Adding
an edge then admits additional provenance paths and is at least as general;
removing an edge is valid only when those paths are impossible or observationally
irrelevant at the public boundary. The effect row itself remains subject to
its ordinary row constraints.

That order is not yet established. If the marker instead asserts an exact
possible-flow fact or summarizes existential witnesses over solver models,
adding/removing it may change the constraint rather than merely widen an
allowance. Principal-scheme comparison therefore needs a defined edge
interpretation and quantification before it can compare schemes containing
different edge sets.

Projection to an ordinary row variable may be possible when removing the edge
preserves both the set of public instantiations and every downstream
handler-eligibility judgment. A sufficient candidate condition is that all
admitted models agree that the edge is unreachable, or that the edge is
unobservable after its authority has expired and all downstream decisions
depend only on ordinary effect membership. This is not yet a proven
criterion. Projection is unsafe if it merges two same-family origins before
their local capture decisions or erases a correlation required by the
complete Function inequality or generalization.

The input capture list and the output provenance edge answer different
questions: the former restricts which contribution may be consumed at the
current boundary; the latter describes whether an input contribution can
reach a result. Neither can be inferred from the other by ordinary row
inclusion. In particular, shared spelling of an effect variable across
ports does not establish an edge or capture permission.

## What this notation does not mean

`'e?` does not mean:

- that `'e` is an optional type/effect variable;
- that `'e` may or may not be a member of an effect row;
- that `'e` necessarily appears in the output;
- that `['e?, 'f]` is equivalent to `['e, 'f]`;
- that a capture restriction attached to `'e` is copied into `'f`;
- that every event of the named family has the same origin or eligibility;
- that `Force`, a shared type variable, family equality, or a public row
  creates capture authority;
- that `never`, `Any`, an empty effect row, polarized solver bounds, or an
  Oracle fallback has any special role in this notation;
- that Function effect ports are independent structural subtype checks; or
- that a new solver relation/carrier is selected.

## Open questions

1. What is the quantifier for “may flow”: executions, source assignments,
   valid solver solutions, or a combination?
2. Does an omitted edge mean impossible flow, untracked flow, or an edge
   erased by a proved projection? These meanings have different principal
   orders.
3. Can the edge be projected from existing `Rel_C`, `K,D`, source segments,
   operand tuples, binder scopes, occurrence/incidence, `Flow`/`Observe`,
   directed weights, and subtraction evidence for every required source case?
4. What exact source position is the boundary in the higher-order type, and
   how does it compose with an explicit annotation and expected callback
   boundary when both are present?
5. Does reaching the public result component `'f` itself end capture authority,
   or does the edge denote only flows that have crossed the receiver's
   source-level exit? How should a returned latent value invoked again while
   the receiver is still active be projected?
6. How are two independent same-family contributions represented when one
   is captured and the other is not, especially after canonical flat-row
   normalization?
7. When two capture scopes overlap on one input/output component pair, can
   the existing source path relation distinguish them without a public
   multiplicity marker? If not, what is the smallest source example showing
   the lost fact?
8. Under which exact principal-scheme equivalence can `'e?` be erased to an
   ordinary row variable?
9. What parser precedence and token ownership should apply to postfix `?`, if
   the notation proceeds beyond a design candidate?

## Syntax observation

The syntax reference defines effect rows with the adjacent opener `'[ ... ]`
and standalone `'e` as a sigil identifier. The lexer delegates the sigil's
suffix to `scan_identifier`, which consumes an optional trailing `?` or `!`.
Therefore `'e?` currently collides lexically with an existing sigil-identifier
spelling; the `?` is not a separate token in this form. The type-expression
grammar admits `SigilIdentifier` as a type atom but defines no separate
provenance suffix. The expression grammar's dynamic suffix operators are an
additional contextual use of suffix punctuation, not a resolution of this
type-level ownership. A future syntax gate must decide whether the sigil
identifier suffix is reinterpreted, escaped, or replaced in type context, and
inspect tokenization, operator-table interaction, and adjacent type forms.
That syntax decision must not infer or alter the relational meaning of the
optional provenance edge. This is confirmed by the current lexer
(`crates/yu-syntax/src/lexical/lexer.rs`, `scan_identifier` and
`scan_identifier_suffix`) and type-starter scan in
`crates/yu-syntax/src/declaration/type_decl.rs`; this note does not select a
grammar workaround.

## Recommendation

Treat `'e?` as a useful **public-projection candidate**, not as a new effect
algebra. Its intended boundary-lifetime reading is compatible in shape with
the existing event-specific hygiene theory: capture permission is local to an
active receiver, while typed paths and event evidence may relate an input
contribution to a result. The existing evidence avoids a reason to add a
parallel carrier at this stage.

The user's later polarity-sensitive deep-handler decision narrows one
mixed-row case and is recorded in the governing compatibility addendum. It
does not close the separate question of whether an optional provenance marker
is a public projection of that case, especially while the receiver remains
active along a returned latent path.

However, the current work has not proved that the edge is derivable from the
existing evidence across higher-order, nested, shallow, recursive, and
generalized cases. Nor is the edge's quantifier or principal order fixed.
The appropriate assessment is **(B) additional semantic organization is
needed, but the candidate is promising**. The narrow missing result is a
source-to-public-projection theorem that maps the optional input-to-result
contribution relation to `'e?`, proves capture authority expires at the
declared boundary, and preserves the scheme solution set without merging
same-family origins. Only a concrete counterexample to that mapping would
justify proposing additional internal evidence.
