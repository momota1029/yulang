# Conservative continuation-summary effect candidate

Date: 2026-10-01
Status: exploratory candidate; not selected or authoritative
Scope: ordinary shallow effects and handler residuals; no weight encoding yet
Implementation authority: none
Reviewed-by: architect, compiler_referee (multiple delta reviews), spec_auditor (multiple delta reviews)

## User constraint on precision and principality

The user has explicitly ruled out exact continuation-sensitive effect inference
as a successor requirement when it would require linear/affine continuation
typing, usage tracking, or a substantially richer type system without an
independent language-design justification. Exact trace semantics remains the
semantic reference for soundness. The inference language may choose a
conservative compositional abstraction, and principality must be defined
relative to the solutions expressible in that chosen abstraction. This does
not waive soundness or justify dropping effects; it permits a sound
over-approximation when exact trace support is not expressible. The shallow
one-request/resume example is evidence that Oracle rows over-approximate exact
trace support, not a requirement to make successor rows exact.

## Question

Can a sound compositional effect abstraction conservatively account for
shallow resumption without exact continuation-sensitive inference or
linear/affine continuation typing?

The candidate below is a response to that question, not a successor rule. Its
main unresolved dependency is provider/capture eligibility: a family row does
not say which handler may consume a request.

## Candidate abstract judgment

Let `Fam` be the finite set of operation families relevant to a checked module
and its imported interfaces. A computation has an abstract immediate effect
`E ⊆ Fam`. Functions, callbacks, thunks, and continuation values also retain a
latent effect set, which an ordinary call or force adds to the immediate
effect. Sequential composition and control-flow joins use set union.

For an operation request in family `f`, the immediate effect contains `f`.
In a shallow catch with scrutinee effect `E`, let `M` contain only those
families for which every operation that can contribute that family to `E` is
both covered by an arm and eligible for this handler under a separate
provider/capture relation. The candidate handler rule is:

```text
effect(catch e with H) = (E \ M) ∪ effect(value arm) ∪ ⋃ effect(operation arms)
```

Each operation arm receives its continuation `k` with the whole pre-handler
effect `E` as `k`'s latent effect. Invoking `k` therefore contributes `E` by
ordinary application typing. Passing or returning `k` must preserve that
latent effect in the resulting function/value type. The operation arm runs
outside this shallow catch, so its own effect is not implicitly filtered by
`M`. Incomplete coverage, unknown eligibility, or any uncovered operation
keeps its family in `E \ M`.

This rule is intentionally coarse. Exact continuation-sensitive effect
inference is not a successor requirement if it needs linear/affine
continuation typing, usage tracking, or a substantially richer type system.
Exact traces remain the semantic reference for soundness; the inference
language may conservatively approximate their support. Principality is
relative to the chosen expressible compositional effect abstraction, not to
exact trace support. In the one-request-and-resume fixture,
`k` receives `[choose]` even though its concrete suffix is pure, so the
abstract result may retain `[choose]`. That annotation behavior is a precision
choice in this candidate, not a claim that the exact trace contains a request.
The finite set domain alone does not justify principality: the empty set is
expressible and is the least exact trace bound in that fixture. Any
principality theorem must be stated for the explicit compositional abstract
judgment above, whose continuation summary deliberately forgets suffix
correlation, and prove its least derivable solution property.

No linear or affine usage accounting is needed for this transfer: an arm that
does not invoke or export `k` does not incur its latent effect through ordinary
function application. Every actual invocation, force, or later invocation of
an exported closure must continue to carry that latent effect. Whether the
language's existing typing constructs preserve this property is unproved.

## Soundness sketch and conditions

Relative to the shallow trace transformer in
`2026-09-30-intrusion-shallow-handler-trace-calculus.md`, a candidate
induction has three cases:

1. An unmatched or ineligible request remains in `E \ M`; the trace forwards
   it and reapplies the catch to the forwarded continuation.
2. A covered, eligible request invokes its arm. The arm's own effects are in
   the arm-effect union. If it resumes the raw continuation, `k`'s latent `E`
   covers every family on every suffix path, including another request in
   family `M`.
3. A non-resuming arm has no suffix execution through `k`; its arm effects
   remain, while an input family may be removed only when coverage and
   eligibility are complete for every request that could produce it.

This is only a sketch for direct request trees. It does not establish the
provider/capture relation, effect soundness through higher-order subtype and
scheme instantiation, or a source/runtime correspondence theorem. In
particular, equal `[choose]` rows can have different handler visibility; rows
alone cannot justify `M`.

## Relative principality target for the finite effect core

The selected abstraction should have a least-solution theorem, rather than
claiming that finite rows are principal by themselves. A first target fixes a
source program and its annotation contracts, with finite family set `Fam`, a
finite set `Slots` of static immediate and latent effect positions, and fixed
provenance/eligibility input:

```text
L = (P(Fam))^Slots
```

Order assignments componentwise by subset. Generate a lower-bound constraint
operator `F : L -> L` from the compositional rules. Operation nodes contribute
their family; sequencing, calls, and thunk forcing use union with operand and
latent effects; a shallow catch uses `(E \ Drop) ∪ arm_bounds`, with each raw
continuation assigned the whole scrutinee `E`. `Drop` and callback contracts
are fixed inputs for this judgment, so these transfers are monotone. Define
abstract solutions as the pre-fixed points `Sol(F) = {ρ | F(ρ) ≤ ρ}`. Derivability
must be defined by, or proved equivalent to, these generated inequalities
before calling the least solution principal.

For each handler/family pair, let `Origins(H,f)` be a sound over-approximation
of request-occurrence and handler-activation/provenance configurations offered
to that handler by shallow evaluation. It must cover every activation,
environment, use-site instantiation, recursive unfolding, closure/thunk
invocation, operation result, and forwarded continuation suffix relevant to
the static handler slot. A matched operation's raw continuation is not resumed
under this handler: its suffix is instead covered by the whole-scrutinee
latent effect assigned to `k` when the arm invokes or exports it. A forwarded
unmatched request is different: if an outer context resumes it, this handler
is re-applied to the forwarded suffix, so those configurations belong in
`Origins`. A finite `Slots` set does not make these dynamic configurations
finite; constructing a sound finite quotient or symbolic summary is a separate
proof obligation. Define `Drop(H)` only from families whose every configuration
in this handler-offered over-approximation is covered and eligible at that
activation. Unknown configurations are treated as ineligible and prevent
subtraction. `Origins` and `Drop` must be valid uniformly for all admissible
assignments and configurations in the claimed soundness domain, not only
snapshots visited by Kleene iteration. If eligibility depends on inferred
effect slots, monotonicity must be proved again rather than assumed. In
addition, each family in a scrutinee row must have a corresponding request
fact in `Origins` or an explicit unknown fact; otherwise a missing origin
could make the coverage check vacuously succeed.

### Finite may-block provenance domain (conditional construction)

A possible finite quotient keeps effect rows coarse while tracking only enough
information to justify a handler drop. For one static handler slot, abstract
request facts can have the form:

```text
ReqFact = (family, exact_operation | UnknownOp,
           origin_site | UnknownOrigin, may_blockers)
may_blockers ⊆ BoundarySite ∪ {UnknownMask}
```

The abstract request set joins by union. `Drop(H,f)` is permitted only when
there is positive evidence that `H` is active, every fact for `f` names an
operation covered by an exact arm, and every fact has no possible blocker.
`UnknownOp`, `UnknownOrigin`, `UnknownMask`, or an absent family-to-origin
fact prevents the drop. Static sites name possible origins and boundaries;
equal site labels do not prove equal dynamic activations. A concrete callback
contract may discharge a blocker only when a separate scope proof establishes
that the handler activation is inside the receiving activation introduced by
that contract. Helper calls, force, return, closure escape, scheme
instantiation, recursive re-entry, and forwarded-continuation resumption need
explicit monotone transfer rules. Any transfer that cannot establish the
activation relation adds `UnknownMask`.

This is a finite-domain candidate, not a construction theorem. Its simulation
must prove that all concrete request/handler configurations map to abstract
facts, including requests carried through closures and requests reached after
forwarding. Its row/provenance coupling must prove that every family in each
scrutinee row has an abstract request fact or unknown fact. The unknown
fallback is sound only under those coverage premises and can reduce final
acceptance; its precision over the supported envelope remains unmeasured. The
least-bound argument above assumes `Drop` and callback contracts are fixed
inputs. One possible phase order is to compute a sound may-block summary first
and then solve effect rows. If origin discovery depends on inferred rows, or
the two analyses run together, monotonicity of the combined operator must be
proved; the separate finite-lattice theorem does not establish it.

### Proposed provenance transfers (unproved)

The following table is a candidate transfer contract for checking against the
source request-tree semantics. It does not adopt Oracle weights or runtime
guard routing. `Lineage` is ordered and preserves callback-boundary evidence;
`Block(H,q)` is a sound over-approximation of the boundaries that may prevent
handler `H` from receiving request `q`.

| Source transition | Candidate provenance transfer | Required proof obligation |
|---|---|---|
| Direct operation request | Add an exact `(family, operation, origin-site)` fact; retain current lineage. | Every evaluated request has a fact, including operation results and recursive calls. |
| Enter a catch activation `H` | Mark this dynamic activation active while evaluating its scrutinee and forwarded suffixes. | Activation identity and delimiter lifetime are explicit, including recursive/re-entrant calls. |
| Enter a callback receiving boundary `b` | Append the fresh boundary instance to the lineage; compute possible blockers relative to the receiving handler activations. | Dynamic nesting and the provider of the callback are preserved across the call. |
| Concrete callback argument contract `[F]` | Record a candidate grant `(b,F)`; it can discharge blocker `b` only for family `f ∈ F` and a handler proved inside this receiving activation. | Contract ownership and scope are stable under helper calls and do not become a family-wide grant. |
| Concrete empty, absent, wildcard, or wildcard-by-skeleton annotation | Preserve the exact annotation form and its row-side constraint separately from explicit grant metadata; do not collapse the forms. | Frozen Oracle uses distinct row-side constraints (`take(Empty)`, `take(All)`, or omitted) and concrete heads alone generate explicit runtime contract metadata. Their successor visibility meaning is open; unknown meaning cannot prove a drop. |
| Ordinary helper call | Preserve existing request origin and lineage, append any newly crossed receiving boundary, then recompute handler-relative blockers for newly entered activations. Add `UnknownMask` if context prevents proving those relations. | Compositionality across argument passing, helper entry/return, and any handler entered by the helper. |
| Thunk force or closure invocation | Preserve latent request facts, then relate the current handler activation to every captured boundary; unknown relation adds `UnknownMask`. | Return/force and re-entry preserve effects and do not widen grant scope. |
| Closure return or storage | Carry latent row and provenance with the value; do not convert grants into transferable permission. | Later invocation reconstructs a sound receiving/activation relation, or conservatively becomes unknown. |
| Scheme instantiation | Freshen identities owned by local static binders while preserving imported/outer provider identities; transport request facts consistently. Dynamic receiving activation identities are allocated later, at calls. | Static binder ownership, use-site substitution, and later dynamic activation are separate; unresolved ownership adds `UnknownMask`. |
| Handler value arm or matching operation arm begins | Remove the current shallow handler activation from the active stack while evaluating the arm; arm-originated requests are analyzed against outer active handlers. | Arm execution does not accidentally reuse `H`'s eligibility or hide arm effects from outer handlers. |
| Matched request resumes raw `k` | Execute the suffix without automatically reinstating this matching `H`; retain its request lineage and analyze it under whatever outer handlers are active. | This agrees with the shallow trace transformer; effects remain covered by `k : May(C)`, and any separately installed/re-entered handler gets its own provenance analysis. |
| Forwarded request resumed by an outer context | Preserve request provenance and re-enter the forwarded handler transformer under its captured `H` activation identity. If an abstract implementation uses a successor identity, prove it equivalent for visibility. | Every such successor configuration is represented in `Offered`; arbitrary finite resumes remain covered. |
| Handler arm returns or aborts | `H` remains inactive after arm entry; finalize that same suspended scope without popping `H` or disturbing outer handlers a second time. Unwind arm-local activations normally. | Delimiter scope ends on every arm exit path and its captured identity cannot leak to unrelated calls. |

For a handler/family pair, a blocker can be removed only after exact operation
coverage and active-handler status are established, and either (a) a proof
shows this handler activation is outside the receiving activation represented
by that boundary, or (b) a matching concrete grant is in scope for this
handler. Possible-but-unproved scope is not treated as outside; it maps to
`UnknownMask`. Join of control-flow paths unions request facts and possible
blockers. This is designed to lose precision monotonically: adding a possible
path cannot create a new `Drop` proof.

The transfer table is not yet a finite abstract interpreter. In particular,
the rule for determining whether a handler is inside a receiving activation
cannot use source-site equality: recursive calls and escaped closures can
re-enter one site under distinct dynamic activations. Fresh dynamic identities
must also be distinguished from static boundary binders freshened during
scheme instantiation. A finite activation quotient and simulation theorem are
still needed. If the quotient or callback facts depend on inferred effect
rows, the combined origin/effect analysis must also establish monotonicity;
otherwise the fixed-`Drop` leastness theorem does not apply.

### Bounded dynamic-scope quotient candidate (unselected)

Independent architecture and semantic review suggests a finite, deliberately
conservative route. A concrete state `κ` would carry unique dynamic handler
and receiving-boundary identities, their ordered active delimiter stack,
request lineage, contract grants, and the provenance snapshots carried by
closures, thunks, and continuations. For a fixed finite program and an
analysis parameter `K`, an abstract state can retain only the top `K` stack
frames, each tagged by frame kind and source site, plus an `UnknownOlder`
summary for frames below that suffix. Request lineage can use the same bounded
ordered representation and an `UnknownOlder` tail. This gives a finite domain
for fixed `K`; it is an analysis precision parameter, not yet a selected input
limit or compatibility boundary. To keep the carried-value component finite,
closure/thunk/continuation provenance would be joined by static allocation
site or a finite set of instantiated value slots; if recursive specialization
can create an unbounded slot universe, it must use allocation-site summaries
or `Unknown`. Grant families and paired-snapshot references must range over
finite source sites, annotation heads, bounded abstract frame positions/value
slots, or `Unknown`; they cannot use fresh dynamic counters. `UnknownOlder`
must be a finite flag or subset of finite site/kind labels, not an unbounded
count or list. Recursive stored-value depth and repeated grant instances join
at allocation sites/value slots, with multiplicity discarded. A merge may add
possible scopes but must never turn uncertainty into proof of visibility.

The abstract identity of a frame is its position in the currently retained
stack snapshot, never its source site or a position reused after pop. Such
positions cannot escape as durable identity: a closure/thunk/continuation may
carry a paired snapshot only while a proof ties it to the same live dynamic
frame. A join of equal site/position shapes with different dynamic identities
must destroy that correlation; a later transfer cannot reconstruct
`InsideGranted` from shape equality. At escape, truncation, merge, or re-entry
where identity is ambiguous, the carried relation degrades to `Unknown`. This
prevents a recursive activation or reused stack slot from inheriting another
activation's grant.

For each offered request, handler, and boundary represented in its lineage,
the abstract scope relation is a set of possible classes:

```text
ScopeClass = Outside | InsideGranted | InsideDenied | Unknown
```

`InsideGranted` requires proof that the handler is nested under the same live
receiving activation and that its concrete grant covers the request family.
`Outside` requires proof that the handler is not nested under that activation,
including a proof that the carried boundary has expired; treating expiry this
way remains a source-level hypothesis to validate. Any hidden stack
frame, mixed dynamic activation, unmatched snapshot, or uncertain grant adds
`Unknown`. The finite relation uses union at joins. A family may enter
`Drop(H)` only if every represented operation is covered and every possible
scope class for every boundary is either `Outside` or `InsideGranted`; any
`InsideDenied` or `Unknown` prevents subtraction. This universal condition is
important: a static handler site may denote one activation inside an ungranted
boundary and another outside it. The outside activation cannot clear the
inside activation's blocker.

The target step-simulation obligation is:

```text
α(step(κ)) ⊑ step#(α(κ))
```

for every concrete source-semantics step, including call/return, force,
closure escape/re-entry, scheme instantiation, handler arm entry/exit,
forwarded resumption, and multi-shot continuation invocation. Forwarded
resumption restores its captured handler context; matched raw `k` does not
automatically restore the matching shallow handler. Multiple resumes join
their abstract outcomes and require no usage count. A row/provenance coupling
lemma must additionally map each family in a scrutinee row to a represented
request fact or `Unknown`. Step simulation alone does not justify `Drop`; also
prove the following observation/refinement invariant, including at the initial
state:

1. Every concrete request `q` offered to dynamic handler `H` has a covering
   abstract request fact at the corresponding static handler slot.
2. For every receiving-boundary identity and other active mask on `q`'s
   concrete lineage, that fact's possible `ScopeClass` set contains the
   concrete relation for this exact `(H,q,boundary)` activation tuple.
3. Per-concrete-pair classification is sound, and exact operation coverage is
   checked separately. Only when the entire possible-class set for every
   relevant boundary/mask is a subset of `{Outside, InsideGranted}` does the
   abstract fact imply visibility eligibility for every represented pair. Any
   `InsideDenied` or `Unknown` prevents `Drop`; a joined `{Outside,
   InsideDenied}` cannot pass just because one possibility is outside.
4. Closure/thunk/continuation summaries preserve latent effect rows and these
   scope relations. Boundary expiry means `Outside` only after proving the
   source semantics cannot restore that receiving scope through a carried
   value; a lexical return or stack pop alone is insufficient.

Then every family admitted to `Drop(H)` is covered and eligible for every
concrete request represented by its abstract facts. Without this implication,
the abstract scope test is not a sound subtraction certificate.

This is not yet a finite-quotient theorem. The concrete activation semantics,
abstract join/transfer soundness, and effect of truncation on the supported
final-acceptance envelope all remain open. Recursive or escaped-callback
cases may become `Unknown` and therefore lose acceptance precision. No value
of `K` is selected. Any useful precision/acceptance claim requires explicit
fixtures and proof over the resulting abstraction; exact trace support remains
the soundness reference, not a continuation-usage inference requirement.

Concrete callback annotations are part of the fixed source-contract input and
can change `Drop` and therefore `F`; this theorem compares solutions only for
the same annotated program. Concrete result annotations are separate upper
filter checks `ρ(slot) ⊆ U`, not operations that clip or alter `F`.

Under monotonicity, the finite lattice gives a least fixed point
`lfp(F) = ⋃ₙ Fⁿ(⊥)`. For every `ρ ∈ Sol(F)`, `lfp(F) ≤ ρ`; therefore, if any
solution satisfies a separate concrete result filter `ρ(slot) ⊆ U`, the least
solution satisfies it too. This establishes principality only if derivations
of the selected effect core are exactly characterized by `Sol(F)` and its
separate filters. Principality here means least derivable finite-family bounds
for this effect core. It does not mean least exact trace support, and it does
not establish principal value types, higher-order subtyping, scheme/SCC
generalization, or final program acceptance for the full language. If the
request-configuration summary is coarse, the result may retain extra families
and lose acceptance precision; soundness additionally requires complete
configuration coverage, correct eligibility, sound transfer simulation, and
latent-effect preservation.

This fixed-point argument is a proof target, not yet a theorem for the current
candidate: source-origin completeness, handler-scope stability, and the full
construct interpretation still require proof and independent review.

## Worked least bounds for the shallow witnesses

Take `Fam = {choose}`, one fixed handler activation, and a closed direct
request tree with no other effects. For both one-request cases, and for the
first request of the two-request case, every request offered to the handler is
covered and eligible, so `Drop = {choose}`. The second request in the
two-request case is in the raw continuation: it does not reach this handler,
but invoking `k` has latent bound `E = {choose}`, so the arm bound restores
`choose`. In the final case a reachable, uncovered `choose` operation is
offered to the handler, so `Drop = ∅`. Each scrutinee has bound
`E = {choose}`.

| Witness | Exact trace support after the catch | `Drop` | Arm bound with `k : E` | Candidate result `(E \ Drop) ∪ arms` | Least row |
|---|---:|---:|---:|---:|---:|
| One request, arm ignores `k` | `∅` | `{choose}` | `∅` | `∅` | `∅` |
| One request, arm invokes `k` once | `∅` | `{choose}` | `{choose}` | `{choose}` | `{choose}` |
| Two requests, arm resumes first request | `{choose}` | `{choose}` | `{choose}` | `{choose}` | `{choose}` |
| Reachable uncovered `choose` operation | `{choose}` | `∅` | `∅` | `{choose}` | `{choose}` |

In the non-resuming case, merely giving `k` latent bound `E` adds no effect;
ordinary application contributes `E` only when the arm invokes it. In the
one-request resuming case, the abstract least bound intentionally retains
`choose` although the exact suffix is pure. In the two-request case that same
bound also covers the second request that escapes shallow resumption. The
last row illustrates that an uncovered reachable operation contributing to
`E` prevents family subtraction; an omitted operation that cannot occur does
not. These equations establish leastness for the fixed
one-family witnesses under the candidate transfer rules; they do not prove
that source lowering, provider analysis, or the general constraint operator
meets those rules.

## Adversarial review result

Independent architect and compiler-referee reviews agree on the following:

- **Blocking for a general rule:** define provider identity and handler
  eligibility independently of family labels. The candidate now separates
  request provenance, ordered boundary instances, handler activations, and
  grants; a family may be removed only when every reachable configuration is
  covered and eligible, otherwise retain it conservatively. The activation
  transport and source/runtime correspondence remain unproved.
- **Major, narrowed:** the finite-core candidate now states principality as
  leastness among pre-fixed solutions of explicit compositional lower-bound
  constraints, with result filters checked separately. Independent review
  confirms the finite-lattice step under those premises. A finite powerset
  codomain alone is insufficient: derivation correspondence, complete dynamic
  origin summaries, higher-order subtyping, SCC schemes, and final acceptance
  remain outside the proved result.
- **Major:** incomplete handlers and residual operations must remain in the
  bound. Non-resumption removes a family only under complete eligible
  coverage. Nested outer handlers and callback ownership need explicit rules.
- No direct-fragment counterexample was found to the whole-scrutinee `k`
  effect, provided ordinary application and escaped closures preserve latent
  effects. This is review evidence, not a completed proof.

## Next characterization and proof matrix

Before considering any weight representation, define and prove the
provider/capture eligibility judgment, then check the effect abstraction
against:

- one request with resume, two sequential requests with resume, and no resume;
- complete coverage, an incomplete family handler, and one uncovered
  operation in an otherwise handled family;
- nested handlers with distinct and repeated families;
- outer-owned versus inner-owned callback under a same-family inner handler;
- delayed thunk forced under a handler;
- repeated callback calls sharing one frame pop;
- residual effects that are passed through and later handled by an outer
  eligible handler.

Only after this matrix should a weight be assigned a denotation. Every proposed
left/right transfer then needs a preservation argument against this abstract
judgment. Method selection, roles, and implementation resolution stay in the
mandatory later gate from the redesign charter unless this proof exposes a
concrete dependency.

No implementation, Oracle weight rule, or equivalence claim is authorized by
this candidate.

## Provider/capture eligibility remains open

The frozen reference directly states these principles:

- callback-origin effects supplied by an outer caller are protected from an
  inner same-family handler unless the receiving boundary exposes them;
- a concrete callback argument row grants matching-family visibility to
  handlers inside that receiving function;
- wildcard surface rows do not erase unrelated hygiene evidence; and
- a shallow operation arm receives the raw continuation.

The nested-provider probes in
`2026-09-30-intrusion-weight-routing-counterexample-search.md` characterize the
first two behaviors as outer result `[1]` without the concrete contract and
inner result `[2]` with `[choose]`. The helper witness records a further Oracle
conflict: its pure `invoke` scheme drops an effect that its callback call can
perform. The successor must propagate that effect and conservatively retain it
when shallow resumption can reach another request. These observations do not
define a provider identity or grant lifetime.

A source semantics will need at least distinct operation-family, request
provenance, callback-boundary, and active-handler identities. Candidate
eligibility notation is:

```text
eligible(request, handler) iff
    handler is active
    and handler covers request.operation
    and visibility evidence authorizes this request at this activation
```

The last condition is intentionally unspecified. Treating a capture contract
as a transferable Boolean attached to a family is unsafe: if that bit escapes
in a returned closure, it could authorize an unrelated inner handler outside
the introducing receiving scope. The converse shortcut—dropping every grant
at a helper return—could prevent an explicitly permitted nested handler from
working. The evidence must therefore be scoped to its introducing boundary
and active handler, and its call, force, closure-escape, and scheme-instantiation
transport must be proved without widening its scope. This is a challenge
example, not an established Oracle behavior or a selected successor rule.

Annotation syntax also cannot be collapsed to one “has a contract” bit.
Absent annotations, concrete nonempty rows, concrete empty rows, wildcard
`[_]`, and any effect-only skeleton position with wildcard behavior may impose
different constraints. The frozen effect specification characterizes several
of these paths, while its weight operations remain non-authoritative. The
successor must define the semantic meaning of each supported annotation form
before deriving any encoding.

Independent architect, compiler-referee, and spec-auditor reviews agree that
provider provenance must remain separate from family identity and that the
family-removal side condition must quantify over every possible request path:
each contributing operation must be covered and eligible at the handler
activation being modeled. The references establish the visibility principle,
not the provenance assignment, grant lifetime, closure-escape rule, or
inference/runtime correspondence theorem. Consequently, the notation above is
only a proof target. It does not close the blocker or authorize a data
representation.

The next proof artifact should define a source request-tree judgment with this
eligibility relation and prove a one-step handler simulation: covered eligible
requests enter the matching arm; incomplete, uncovered, or ineligible requests
forward with provenance intact; and any raw-continuation resumption preserves
the whole pre-handler effect bound. Include the callback/hygiene pair,
helper-call composition, delayed thunk force, closure escape, and repeated
callback request before relating the judgment to a runtime representation or
weight calculation.

### Candidate provenance relation (unselected)

A useful proof target keeps these identities separate:

```text
request q = (operation, family, origin, ordered_boundary_lineage)
handler h = (activation_id, covered_operations)
grant g = (introducing_boundary, family_set, scope)
```

A source-grounded candidate eligibility clause can be stated as:

```text
eligible(q, h) iff
    active(h)
    and exact_operation_covered(h, q.operation)
    and for every boundary b in q.ordered_boundary_lineage:
          outside(h, b) or matching_grant(b, q.family, h)
    and no_other_active_boundary_masks(q, h)
```

`outside(h,b)` means handler activation `h` is not dynamically nested within
the particular receiving activation represented by boundary instance `b`.
It is activation-specific, not a lexical test on where a closure was created.
A crossed callback boundary does not by itself block an outer handler.
`matching_grant` requires an explicit contract at that boundary for the family
and a scope proof that includes this activation. How this receiving scope is
represented and transported across closure re-entry remains a proof
obligation. Other active guards may also mask a request even when the handler
is outside this grant scope. Thus the escaped-callback
inference is conditional: the caller may handle the request if its exact arm
matches, it is outside the maker grant scope, no other carried/active boundary
masks it, and the source/runtime correspondence preserves that eligibility.
This clause is a source-grounded candidate, not a selected successor rule.

The eligibility judgment must require an active handler, exact operation-arm
coverage, and a derivation that every callback boundary on the request's path
to that handler permits this family at this activation. Family equality alone
cannot discharge the last premise. A request with no callback boundary uses
the direct shallow rule. Handler subtraction is allowed only if this judgment
holds for every reachable request contributing that family, including each
suffix reached by resuming a forwarded continuation. The lineage is an ordered
sequence of boundary instances, not a set: repeated pushes, re-entry, and one
shared pop must retain their order and multiplicity until a preservation
theorem justifies normalization.

The frozen source documentation motivates, but does not complete, a candidate
grant rule: a concrete callback argument contract exposes its listed families
to handlers inside its receiving function. The candidate should identify the
receiving activation and handler activations explicitly; it must not turn the
grant into a family-wide Boolean. Passing the callback through a helper must
preserve its origin and boundary lineage. A returned closure must preserve its
latent effect and provenance. A source-grounded scope hypothesis is that the
grant authorizes matching handlers inside the receiving function activation;
it is not a transferable permission for unrelated later handlers. Thus the
`caller` catch in the `maker` closure probe is outside `maker` and need not
inherit `maker`'s grant to handle a request that escapes the returned closure,
provided no other active boundary masks it. The marker spec's own-family
`add_id` rule is compatible with this interpretation at that boundary, but
does not establish eligibility at a later caller activation. The no-contract
outer-handler control is also only adjacent evidence; it does not prove the
concrete-contract closure-return path. This escaped-closure conclusion is an
inference, not an explicit frozen source rule. Formal activation scope,
helper composition, and the relation between returned-value markers and
handler eligibility still need proof. They must not be inferred from
`StackWeight` or runtime marker code; that code conflicts with the marker spec
on own-path coloring.

Until those scope rules are proved, the conservative effect abstraction
retains the family whenever eligibility is unknown. This is compatible with
the user's precision decision: the bound may over-approximate exact trace
support, while its principal-solution theorem is stated over the chosen
compositional abstraction. The following annotation forms remain distinct
proof cases: absent callback annotation, concrete nonempty row, concrete empty
row, wildcard row, and result-position filter. Frozen documentation describes
different roles for these forms, but their successor grant and filter
semantics have not been selected. This relation is only a proof target and
does not resolve the frozen marker code/spec conflict.

The frozen contract-metadata design sharpens this distinction: only concrete
heads in root function-parameter annotations generate argument-contract
markers; wildcard and row tails do not. A root computation annotation is a
separate static subtraction contract, not argument metadata. The frozen effect
reference describes a result-position concrete row as a static escape filter.
These are representation/lowering facts, not authority for successor weight
semantics. See
`/tmp/yulang-intrusion-oracle/notes/design/2026-06-24-explicit-effect-contract-metadata.md:65-81,111-128`,
`/tmp/yulang-intrusion-oracle/web/docs/reference/effects.md:243-263`, and
`/tmp/yulang-intrusion-oracle/spec/2026-05-31-effect-variable-subtractable.md:254-274`.

### Frozen-Oracle closure-escape probe

A new source characterization tests callback effect transport through a
returned closure:

```yu
act choose:
  our reject: () -> int

my rejecter() = choose::reject()
my maker(f: () -> [choose] int) = \_ -> f()
my delayed = maker(rejecter)
my caller(): [] int = catch delayed(0):
  choose::reject(), k -> k 3
  v -> v

caller()
```

The frozen Oracle `check` accepts this program. Its `--poly-raw` dump gives
`maker`'s returned function, `delayed`, and `caller` pure (`Bot`) return-effect
slots. Both interpreter and evidence VM instead report an unhandled
`choose::reject`. Thus callback effect information is lost across this
closure-return path before the pure caller annotation is checked. The
successor's sound effect abstraction must retain `choose` in the returned
function's latent effect. Handler eligibility for the escaped request remains
open, but the current coarse whole-scrutinee continuation candidate predicts
that the explicit `[]` annotation is rejected either way: if the handler is
ineligible, the scrutinee effect remains; if eligible, invoking `k` contributes
the whole pre-handler effect through the unfiltered arm. The derivation and
compatibility consequence are stated below. The Oracle accepts the annotation
while both runtimes leave the request unhandled; this is a concrete
accepted-but-failing Oracle case, not yet a selected successor rule.

A direct-closure control with `delayed = \_ -> choose::reject()` retains
`[choose]` in the delayed function and caller schemes; the inferred caller
returns `3`, while an explicit pure annotation is rejected with an effect
filter mismatch. The contrast localizes the missing static effect to the
callback/closure transport path. It does not decide whether the callback's
later request is eligible for the caller catch; the minimum successor rule is
that it cannot be erased from the returned function's effect.

The same source was checked with the `maker` callback contract changed while
the pure caller annotation was removed. With no contract, wildcard `[_]`, and
concrete empty `[]`, each inferred `caller` retains `[choose]`, and the
interpreter's caller handler returns `[3]`. With concrete `[choose]`, the
inferred `maker` result, `delayed`, and `caller` instead have `Bot` return
effects, and both runtimes report unhandled `choose::reject`. Thus these
annotation forms differ on this exact closure-escape path. The annotation-
dependent effect loss is consistent with the concrete capture grant affecting
analysis beyond the receiving function's inner handlers, but does not
establish the Oracle mechanism or a general grant-lifetime rule. The successor
must preserve the unconsumed callback effect in the returned closure; capture
evidence transport across returned functions remains open. Frozen runtime
guard notes describe result-marker propagation across returned functions, so
an unconditional rule that closes every grant at function return would be
premature. A source-derived symbolic marker trace for the returning-callback
control is recorded below; it characterizes frozen implementation code but
does not choose the successor's boundary rule.

The frozen runtime IR narrows the mechanism without settling the source rule.
The concrete-contract variant lowers the callback argument with
`arg[add_id[1, choose, own, resume-own]]`; the returned closure's maker adapter
has `body[add_id[1, choose, own]]`. At the caller, the concrete variant has a
plain `catch (delayed 0)`, while the absent, wildcard, and concrete-empty
variants retain a `thunk[[choose], int]` and lower to a marked
`catch marker[choose](force-thunk ...)`. These are compiler-lowered marker
plans, not an instrumented trace of runtime `GuardId` values. The frozen
runtime rules say returned functions carry markers and later calls re-enter
their marker frame; the concrete variant's two runtimes report the resulting
request unhandled. This shows that effect-row erasure and runtime marker
routing coexist in this case, but does not prove whether the caller handler is
eligible in the successor's declarative semantics.

The frozen runtime source gives a conditional route derivation for the plain
caller catch, but its own-path coloring condition conflicts with the frozen
runtime marker specification. The implementation's `mark_request` path can,
under its `guard_own_path` condition, record a guard and `CarriedGuard`
exposure snapshot for an own-path request; adapter marker frames then pop
while `guard_ids` and `carried_guards` remain on the forwarded request. A
plain `Catch` adds no handler frame, and the missing-handler route can use a
carried guard to skip its arm. However, the frozen marker specification says
that `add_id[0,path,id]` colors a request only when the marker path is not a
prefix of the request path; it therefore requires an own-path request to
remain readable at that boundary. The code-derived route is characterization
of the frozen implementation and a code/spec conflict, not a normative rule
for the successor. It needs an approved specification resolution before any
semantic adoption. The relevant implementation rules are in
`crates/mono-runtime/src/lib.rs:471-484`,
`crates/mono-runtime/src/runtime/flow.rs:135-180,296-376,391-412,438-553`,
and `crates/mono-runtime/src/runtime/eval.rs:360-380,449-477` in the frozen
checkout; the conflicting path-prefix condition is in
`spec/2026-06-13-runtime-guard-markers.md:117-130`. A source-derived symbolic
execution of the nested adapter/value-marker composition is recorded below,
but no dynamic request-state instrumentation was performed. The exact
implementation route does not resolve the normative code/spec conflict or
define successor source semantics.

The source-derived allocation trace accounts for adapter calls during
top-level `m0`: A (the outer `m0` adapter) allocates G0/G1 for argument depths
1/2; C (the `maker` adapter) allocates G2/G3 for body depths 0/1, then G4/G5
for argument depths 1/2; B (the callback adapter invoked by `d6()`) allocates
G6/G7 for argument depths 1/2. `apply_adapter` allocates markers before
marking the argument value, so G6/G7 are consumed even though scalar `()` does
not retain them. After the callback returns its closure, the relevant carried
markers are G0-G5. Calls decrement positive depths; forcing the marked effect
thunk re-enters marker frames, and frame exit preserves request guard and
carried-guard data in the implementation. The initial carried G0 exposure
snapshot is empty in this root; later snapshots reflect guards active before
each marker frame, rather than every previously allocated ID. Re-entry of an
existing marker does not allocate a new ID. The plain catch has no marker
frame, so the frozen implementation's missing-handler path selects a carried
guard and skips the arm; the root host then reports the unhandled request.
This is source-derived symbolic execution, not an instrumented runtime log,
and the own-path skip remains in conflict with the marker specification.
Independent source audit confirmed the G6/G7 allocation and that outer
marker stripping does not remove markers nested inside returned adapters or
thunks. The trace is limited to frozen mono-runtime; it proves neither VM
parity nor declarative handler eligibility.

A second control makes the callback itself return the effectful closure:

```yu
my make_rejecter() = \_ -> choose::reject()
my maker(f: () -> [choose] (int -> [choose] int)) = f()
my delayed = maker(make_rejecter)
my caller(): [] int = catch delayed(0):
  choose::reject(), k -> k 3
  v -> v
```

The frozen checker accepts it; `--poly-raw` again gives `maker`, `delayed`,
and `caller` pure result-effect slots, and the interpreter reports an
unhandled `choose::reject`. Its runtime IR shows callback markers at depths 1
and 2, plus returned maker-body markers at depths 0 and 1. This is a
distinguishing lowering control for callback-result transport, not yet a
runtime log of marker ids, frame exits, resumption, and catch skipping. The
successor's dynamic eligibility remains unresolved; the coarse effect
candidate's pure-annotation rejection does not depend on that choice.

The matched absent-contract control rejects the explicit pure caller with an
effect-filter mismatch. With the caller annotation inferred instead, the
absent-contract program retains `[choose]` in `delayed` and `caller`, and the
caller handler returns `[3]`. The concrete-contract version with the caller
annotation inferred has `Bot` result effects and fails at runtime with the
unhandled request. These outcomes isolate the contract-dependent difference
on this returned-callback shape; they still do not choose the successor's
handler-eligibility rule.

Compatibility consequence: the successor cannot adopt Oracle's complete
combination of pure returned-closure effects and pure caller acceptance as a
validated rule. If `choose` escapes the receiving function, the returned
closure's latent effect must retain it. Whether the surrounding pure caller is
then rejected is no longer dependent on the unresolved eligibility rule for
the current coarse candidate. Its shallow handler assigns the whole
pre-handler effect `E` to `k`; the arm `k 3` therefore contributes `choose` to
the arm-effect union, which runs outside the same shallow catch. If the request
is ineligible, `choose` also remains in `E \ M`; if eligible, the resumed
continuation summary still contributes it through the arm. Thus this candidate
rejects the pure caller annotation under either eligibility outcome. This is
a conservative approximation choice, not a claim that the exact one-request
trace contains an outward request or that the Oracle program is semantically
well-typed. The candidate acceptance delta is concrete: Oracle `check`
accepts the pure caller, while the proposed compositional bound rejects it;
Oracle's runtimes report the request unhandled. Whether a more precise
abstraction can soundly accept it remains open. No final successor rule is
selected until soundness and least-derivability relative to the chosen
abstraction are proved.

Focused commands used the frozen checkout's prebuilt CLI and sources in
`/tmp/yulang-intrusion-*`:

```text
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-capture-escape.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-direct-closure-control.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-direct-closure-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-absent-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-absent-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-absent-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-absent-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-wildcard-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-empty-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-empty-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-empty-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-empty-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-capture-escape-concrete-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-control.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-control.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-control.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-control.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-absent.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-absent-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-absent-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-absent-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-absent-inferred.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu --runtime-ir
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-returning-callback-concrete-inferred.yu
```

The callback/closure fixture's check and dump exit 0; both runtime commands
exit 1 with `yulang.unhandled-effect`. The direct pure-annotation control exits
1 with an effect filter mismatch; its inferred control exits 0 and returns
`[3]`. Each no-contract/wildcard/empty inferred variant checks successfully
and returns `[3]`; the concrete `[choose]` inferred variant checks but both
runtimes fail with `yulang.unhandled-effect`. This is Oracle characterization,
not an implementation test.

## Parameterized one-step soundness lemma

The coarse row rule can be isolated from the still-open hygiene semantics by
parameterizing the handler transformer with two independent predicates:

```text
Covered(H, activation, operation)
Visible(request, H, activation)
```

`Visible` must refer to the request's provenance and the active handler
activation. It is not defined by family equality. A configuration `κ` records
the active activation and relevant provenance/guard state. Keep the exact
request occurrence on each trace path; do not aggregate different paths that
share a family into one node-local visibility value.

For a request tree `C`, write `May(C)` for a sound family-set upper bound on
the union of supports of all finite traces through `C`, including every
continuation suffix for every operation result. This finite-trace definition
also applies when recursion makes the request tree infinite. Assume each arm
judgment soundly summarizes its immediate execution for arbitrary calls to
raw `k`, with `k` assigned latent row `May(C)`. If an arm returns a callable
or thunk that captures `k`, its result-value typing must separately preserve
that latent row. The following simulation targets immediate trace effects:

The source-grounded eligibility hypothesis above decomposes the predicates:

```text
Eligible(q, H, κ) = Active(H, κ)
                    and Covered(H, κ, q.operation)
                    and Visible(q, H, κ)

Visible(q, H, κ) =
    for every boundary b in q.ordered_boundary_lineage:
        outside(H.activation, b, κ)
        or matching_grant(b, q.family, H.activation, κ)
    and no_other_active_boundary_masks(q, H, κ)
```

Here `κ` must contain the active handler identities, the specific receiving
activation and its nesting relation to each handler, the ordered request
lineage, and explicit contract evidence. `outside` is evaluated at the
request's current activation, including closure re-entry; it is not inferred
from the source location where a closure was created. These predicates remain
conditional because the successor's scope transport and runtime correspondence
are unproved. If any premise cannot be established, `Visible` is false for
subtraction purposes and the family remains in the bound.

```text
T_{H,κ}(Return(v)) = value_arm(v)

T_{H,κ}(Request(q, k)) = operation_arm(q, k)
    if Eligible(q, H, κ)

T_{H,κ}(Request(q, k)) = Request(q, x -> T_{H,κ'}(k(x)))
    otherwise
```

In the forwarded case, `κ'` ranges over the successor configurations allowed
when that request is resumed by its surrounding context. Those transitions
are part of the still-open source semantics.

Let `Reach(H, C, κ0)` contain every request/activation/provenance
configuration reachable from the initial configuration `κ0` while evaluating
the transformed tree, including arm execution, raw-continuation calls, tails
reached after any allowed operation result, and handler re-entry induced by
forwarding. Let `Offered(H, C, κ0)` be the subset of request configurations
actually offered to this handler while evaluating the scrutinee: include the
initial scrutinee path and suffixes revisited after a forwarded request is
resumed, but exclude raw-continuation suffixes executed by a matching operation
arm because that continuation is not wrapped by this handler. Let `A(H, C,
κ0)` be one uniform upper bound for value and operation arm effects across
every applicable handler configuration in `Reach(H, C, κ0)`, with raw `k`
assigned latent `May(C)`. Let `Drop(H, C, κ0)` be a proof-carrying set of
families, not a function of the family row alone. A family `f` may enter
`Drop(H, C, κ0)` only if every configuration in `Offered(H, C, κ0)` for a
request of family `f` is covered and visible at that activation, with positive
evidence that the handler is active. This quantification must account for
forwarding: an outer handler may resume a forwarded continuation zero, one,
or multiple times, producing different configurations. A row/provenance
coupling premise must ensure each family in `May(C)` has a corresponding
request fact in `Offered` or is conservatively retained as unknown. The
abstract result is:

```text
(May(C) \ Drop(H, C, κ0))
    ∪ A(H, C, κ0)
```

### Conditional statement

Assume:

1. `May(C)` includes the request at each node and all suffix requests for every
   operation result, with the bound valid for every finite trace.
2. The arm judgments soundly bound immediate arm execution with raw `k` typed
   at latent effect `May(C)`, including any finite number of invocations.
3. `Drop(H, C, κ0)` excludes every family that occurs at any uncovered or
   ineligible request configuration in `Offered(H, C, κ0)`, including
   configurations reached after forwarding and outer resumption. Requests in
   raw-continuation suffixes of matched operations are instead bounded through
   `May(C)` at `k` whenever an arm calls or exports it.

Then every immediate family on every finite trace of `T_{H,κ0}(C)` is in the
abstract result above. This statement covers recursive/infinite request trees
by considering each finite trace prefix. It is conditional: it does not prove
`Visible`, validity or existence of `Drop` certificates, sound arm judgments,
least derivability, or principal schemes. To extend this immediate-trace
result to higher-order soundness, prove separately that every returned
callable/thunk capturing `k` preserves its latent row and visibility evidence
in its result value type.

### Proof sketch

Induct on finite trace length with the uniform invariant that every reachable
transformed suffix from `Reach(H,C,κ0)` is bounded by the original result
`May(C) \ Drop(H,C,κ0) ∪ A(H,C,κ0)`.

- For `Return(v)`, the transformed trace evaluates the value arm, whose
  immediate families are in the value-arm term of the abstract result.
- For an uncovered or ineligible request `q` of family `f`, premise 3 gives
  `f ∉ Drop(H,C,κ0)`. The forwarded request itself is in
  `May(C) \ Drop(H,C,κ0)`. Its continuation resumes in a configuration in
  `Reach(H,C,κ0)`; the remaining finite trace is shorter, so the induction
  hypothesis using the same original global bound covers its later families.
- For a covered and eligible request, the transformed trace evaluates the
  matching operation arm. The uniform arm judgment in `A(H,C,κ0)` bounds its
  immediate effects, including any raw `k` calls. Every suffix reached by
  such a call is bounded by `May(C)` under premise 1 and included through
  `k`'s latent effect in the same arm summary. The shallow rule does not apply
  `H` again to that raw continuation.

The compiler-referee delta review found no finite-trace counterexample under
these conditions. It noted that the induction must retain the original global
bound and arm union across every reachable suffix, rather than recomputing a
new bound for each suffix. The sketch now states that uniform invariant and
quantifies arm bounds over all reachable activations. This is a wording-level
repair, not a proof certification. In particular, a returned closure's later
invocation needs the separate value-correspondence proof; immediate trace
inclusion alone does not establish higher-order soundness. Nor does this proof
establish a least-solution property or principal schemes.

The quantifier in `Drop` exposes an important limitation: a family-set row
alone cannot prove that *all* contributing requests are visible. A solver
would need to retain enough occurrence/path evidence to justify a drop, or
conservatively leave the family residual whenever that evidence is absent.
This is an abstract proof requirement, not a choice of graph representation.
The unresolved closure-escape and helper-composition cases determine whether
such evidence can be transported soundly.
