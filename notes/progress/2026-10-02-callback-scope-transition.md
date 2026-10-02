# Callback-scope transition characterization

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: preserve semantics selected; proof and implementation gates remain open

## Question

Does a nested concrete callback receiver preserve or shadow an enclosing
receiver's capture incidence while the nested `CallView` adapts the callback
result? The question is about one clause in the common activation-context
relation, not a reason to add a callback selector or a new row obligation.

## Frozen characterization

The witness is `/tmp/yulang-helper-capture-concrete.yu`:

```yu
pub act choose:
  pub get: () -> unit

pub invoke(f: () -> [choose] ()) = f()
pub handle(f: () -> [choose] ()) = catch invoke(f):
  choose::get, k -> k ()
  v -> v
pub result = handle(\() -> choose::get())
```

The frozen CLI `check --no-prelude --no-cache` accepts it. `dump --poly-raw`
reports `ret_eff=Bot` for `invoke` and `handle`; `dump --mono` places the
callback-result force inside `invoke`; `run --interpreter` then reports an
unhandled `choose::get`. Wildcard-helper and direct-receiver controls succeed.
This is a checker/runtime mismatch, not authority for either runtime routing
or a successor rule. In particular, the Oracle's empty row is not to be copied
if it erases a request that the successor execution relation leaves outward.

## Candidate clauses in the same theory

1. Preserve the enclosing capture incidence through nested call and adaptation.
   This is the compositional context-extension candidate. The outer handler can
   consume the request only if the complete source transition and universal
   handler-image proof establish visibility, coverage, and typed compatibility.
   It fits the documented receiving-function capture promise, but has not been
   shown by the witness or frozen runtime.
2. Suspend derivability of the enclosing incidence across a competing inner
   concrete receiver. Retain the ordered frame, request, and symbolic `K,D`;
   family equality alone cannot define competition. This may reject an
   outer-handler program accepted by Oracle and needs a source-level precedence
   rule. A larger row is not by itself a principality failure; principality is
   relative to this selected source semantics and its expressible abstraction.

Both clauses use the same ordered context, source-owned request incidence,
typed-family formula, `CallView`/`Adapt`, and whole-computation handler image.
The incidence is a derivability fact of that source relation, not a stored
permission or an additional solver predicate. This keeps `Sel_s`, `Demand`,
route records, and transport maps as derived views or proof bookkeeping.
Candidate 1 is conceptually cheaper if source simulation proves it; candidate 2
cannot be chosen merely to fit the frozen route. The author has not selected
either clause.

The frozen source reference gives candidate 1 some positive, but incomplete,
support: it says a concrete callback argument contract lets handlers inside
the receiving function consume matching callback-origin effects. In the
witness, `handle` is such a receiver and its `catch` is in the function body;
`invoke` itself has no handler, so its `[choose]` annotation alone does not
explain consumption. This favors preserving the enclosing incidence through
the nested call as the simpler reading. It does not specify how two concrete
receiver contracts compose, or formally establish that all generated
`CallView` adaptations execute inside the enclosing catch. Treat it as a
source-backed hypothesis, not a selected rule or proof of soundness.

## Reviews

- **architect**: the witness cannot select either candidate; keep the
  concrete-on-concrete relation open within the common ordered context.
- **compiler_referee**: candidate 1 needs a source/runtime simulation across
  argument adaptation, call, result adaptation, origin eligibility, shallow
  resumption, and symbolic `K,D` transport. Candidate 2 must retain all
  unconsumed support. A family match alone must not capture an unrelated
  caller-owned request.
- **spec_auditor**: frozen public references establish a scoped capture
  promise, not nested-contract precedence or universal sticky composition;
  runtime markers specify lineage persistence/re-entry but do not select the
  disputed source eligibility rule. No source rule or implementation approval
  follows.

The three reviews converge: this is a genuine source-semantic decision, not an
Oracle implementation fact. The exact request lifetime and caller-handler
eligibility remain unresolved. The later method/roles/impl-resolution gate is
unchanged and must wait until ordinary effect/handler semantics is settled.

Follow-up review clarified the support quantifier: handler soundness is stated
over reachable outputs of the complete image. It does not retain every input
may-request except selected heads, because an aborting arm can make a suffix
unreachable. Raw resumption and arm execution can also expose requests missed
by set subtraction. Output support is projected after the image; symbolic
family predicates and `K,D` stay attached to every dependent output view.
The architect and compiler-referee recommendations fit this single transition
carrier; finite presentation and source adequacy remain open. A spec-auditor
delta review closed the support, competition, derivability-versus-storage, and
unproved-soundness wording with no remaining blocking or major finding. Review
closure applies only to these clauses and records; it selects neither policy
or authorizes implementation.

The conditional nested-receiver calculation was corrected after adversarial
review. Keeping the request occurrence, owner incidence, capture relation,
and outer frame does not entail that `Visible` remains derivable: its ordered
context rule may include negative premises such as the absence of an
intervening competing boundary. The preserve candidate therefore needs a
transport proof for the complete visibility derivation, including all
contextual premises, across its declared helper class. The witness alone does
not prove monotonicity.

Under explicit premises covering that complete visibility derivation, the
entire `CallView` and force placement, one exact request, one raw resumption,
request-free arm/suffix behavior, operation compatibility, and shared
symbolic `K,D`, the closed witness yields empty immediate request support after
the whole handler image. The conclusion is only a support projection: it does
not claim singleton `Return(unit)`, termination, or a nonempty image. It also
does not establish finite presentation or pure generalized inference for
`handle`. The generic callback contract admits two sequential requests, so a
row-only abstraction must conservatively retain `choose` after shallow raw
resumption. A finite presentation that recovers the closed witness's pure
result, and any final-acceptance difference if it cannot, remain open. A
spec-auditor delta review closed the correction with no remaining findings.
Neither preserve nor suspend is selected.

## Handler-relative visibility repair

A later adversarial audit found a separate formal issue in the candidate
notation: `Visible(q,κ)` was existential over all active frames, while ordered
search could test that same fact at each frame. With
`κ = [h_inner,h_outer]`, a request connected only to `h_outer` would make the
global fact true and could therefore be stolen by a same-family `h_inner`.
That contradicts the documented caller-hygiene rule.

The draft now uses the handler-relative judgment `Visible(q,h,κ)`. Search
checks request origin and capture incidence against each candidate `h`; it
does not distribute an outer handler's evidence to other frames. The concrete
counterexample and revised signature are in the coupled-interface draft's
visibility section. A compiler-referee delta review closed this quantifier
finding. The reviewer also confirmed that the deeper certification blocker
remains: source rules for contract incidence through nested boundaries,
concrete/concrete propagation, and handler eligibility of escaped values are
still absent. Runtime lineage transport itself is specified; it must not be
conflated with the unresolved source permission calculus.

Architecture and source-spec audits agree that an origin-indexed relation over
ordered boundary transitions is the most economical candidate carrier. The
public source contract supports capture by handlers inside a concrete
receiving function and protection of uncontracted callback effects. The
authoritative Yulang3 architecture and frozen runtime guard specification fix
that activation-specific lineage travels with closures, thunks and
continuations and is reinstalled on resume. They do not uniquely settle
nested concrete receiver propagation or which source handler may consume an
escaped request. Preserve/composition is the simpler hypothesis; a visibility
cut would need a source-defined boundary rule beyond family equality. Neither
is approved. A concrete user decision remains before that source rule can be
selected; finite symbolic presentation and principality follow as separate
proof gates.

## Next proof gate

Define one source call/handler transition over ordered activation contexts and
request origins, derive both candidate clauses from that relation, and compare
their final well-typed-program acceptance. Preserve symbolic typed-family
argument invariance through solving, residualization, call, force, handler
image, generalization, fresh instantiation, and intrusion at the same
assignment. Do not begin method,
role, or impl-resolution work before ordinary effect/handler semantics closes,
unless a proved dependency requires it earlier. No compiler code or tests were
changed or run. `git diff --check` is the only mechanical check for this
record/design slice.

## 2026-10-02 authority split: annotation contract vs runtime lineage

A source-spec audit checked the exact frozen annotation contract and the
Yulang3 runtime-hygiene authority. This narrows, but does not select, the
nested-receiver policy.

The frozen source contract distinguishes annotation position and form:

| Source position/form | Contract fixed by the reference | Successor-relation reading |
|---|---|---|
| Unannotated callback argument | Grants no new capture contract; callback-origin effects remain hygienic at that boundary | No new visibility derivation follows from this boundary |
| Wildcard callback argument | Exposes inferred surface effects but does not erase other hygiene evidence | Preserve other lineage/visibility facts in the same relation |
| Concrete callback computation argument | Lets handlers inside the receiving function consume only the named family from that argument computation | Preserve is selected for an already-derived receiver/handler incidence across nested `CallView`; source derivation and proof remain open |
| Covariant result | A concrete row statically filters escaping effects; omission/wildcard remains open | A result filter is checked at the result view and is not a runtime capture marker |

These are source-level distinctions in annotation syntax and polarity. They
can be clauses of the same source typing/interface relation; they do not
justify separate effect-obligation stores, selectors, or route rules. In
particular, a concrete result filter must not be confused with a contravariant
callback capture contract.

Runtime activation lineage has a firmer authority boundary than the prior
record suggested. The approved Yulang3 architecture requires fresh
activation-specific scope identities to travel with closures, thunks, and
continuations and to be reinstated on resume. This is an approved runtime
hygiene invariant. The frozen guard-marker specification characterizes
shape-directed transport through force, call, projection, adapters, unwind,
and re-entry, but its concrete marker transformations are not independently
selected semantic rules: the successor must derive and prove the corresponding
transitions from source semantics. Neither source fixes whether a particular
escaped request remains eligible for a particular handler after nested
concrete contracts. Static identity, runtime fresh identity, and source
visibility therefore remain separate coordinates of one relation.

The nested `handle`/`invoke` witness has positive source-text support for the
preserve hypothesis: its catch lies inside a concrete callback receiver, and
the nested `invoke` contains no handler that could consume the request. The
contract says such an inner handler may consume the named family. However, the
text does not explicitly specify the transport of that permission through the
second concrete argument boundary and all generated adaptations/forces. The
At the time of that audit, preserve versus suspend remained unresolved; the
frozen runtime trace and Oracle's empty row could not choose it. The immediate proof
target is to define the common typed call/handler transition so that source
capture clauses and the specified runtime lineage transport compose, then
check the witness against the complete transition. No implementation or test
expectation change follows from this record.

Source anchors: frozen Yulang2 `a58eefc31`, `web/docs/reference/effects.md`,
“Effect annotations and visibility,” lines 244–265; frozen
`web/docs/reference/type-theory.md`, “What Effect Annotations Mean,” lines
154–177; frozen `spec/2026-06-13-runtime-guard-markers.md`, §§ runtime
elements, marker, add_id, function guard marker, and dynamic unwind; current
`docs/yulang3-architecture.md:710`.

Independent source-spec audit: the three annotation forms/positions above and
the high-level activation-identity transport invariant are fixed by these
sources. Exact nested concrete permission propagation and per-handler
eligibility after escape are not. No policy was selected. The reviewer delta
closed after narrowing the frozen marker spec to characterization evidence;
this does not approve its routing algorithm or any successor source rule.

### User-selected preserve semantics (2026-10-02)

The user selected preservation as the intended source semantics: a concrete
callback receiver's capture entitlement remains derivable through a nested
concrete receiver's call/adaptation transition unless the source language
independently defines a semantic boundary that invalidates that entitlement.
No such invalidating boundary is currently defined for this transition.
Suspension/shadowing must not be introduced to reproduce the frozen Oracle
runtime route. This is a semantic choice, not implementation approval.

The formal clause belongs to the existing handler-relative
`Visible(q,h,κ)` judgment. If the same request origin and capture incidence
enter a nested call while the candidate handler remains active, the complete
visibility derivation transports to the extended ordered context (with the
new frame prepended because `κ` is written nearest-handler first). This must
preserve negative as well as positive premises. It covers callee/argument
evaluation, both `CallView` adaptations, callback execution, and any force
before handler dispatch. Exact operation identity, request origin, and
candidate handler remain distinct; equal family heads alone never grant
visibility. A handler arm receives the raw continuation outside its shallow
frame, and repeated suffix requests remain subject to the ordinary outer
search.

Required proof gate: prove source/runtime simulation for that entire
transition; caller hygiene for unrelated same-family origins; raw-resumption
and ordered-search soundness; symbolic typed-family formula and `K,D`
preservation at one assignment through residualization, generalization,
freshening, and intrusion; and soundness/principality of the finite
abstraction. If that proof yields a genuine source-level counterexample,
return the choice for reconsideration rather than adding an ad hoc exception.
Escaped-value entitlement after return remains a separate open question;
runtime activation lineage transport/re-entry itself is fixed by the
Authoritative Yulang3 architecture. No compiler implementation or tests are
authorized by this decision. Review must assess the proof gate before this
clause can become implementation-ready.

### Follow-up source decision audit

A focused architect review compared only the frozen annotation/handler text
and the current Yulang3 runtime-lineage authority. It confirmed that the
reference grants capture at each concrete receiving-function boundary but
does not define composition when an outer handler surrounds a second concrete
receiver whose result adaptation forces the callback. The missing rule is one
boundary-crossing clause in the existing origin-indexed `Visible(q,h,κ)`
relation: whether an enclosing incidence remains derivable across that nested
`CallView`. No additional selector or obligation kind is needed to state the
choice.

This audit established that the source docs did not themselves select nested
precedence. The user subsequently made that choice: preserve the enclosing
entitlement through the nested concrete receiver, absent an independently
defined source invalidator. The audit remains evidence for why this is an
explicit source decision rather than a rule inferred from Oracle internals.
The preserve rule still requires complete-call simulation and principality
proofs; source economy cannot substitute for soundness.

Escape/re-entry is only partly open. Authoritative architecture already
requires activation-specific lineage to travel through closures, thunks, and
continuations and to be reinstated on resume. The unresolved question is
which receiver entitlement that transported lineage represents when an
escaped value later runs; deleting all lineage on return is not admissible.
No runtime-marker routing rule is used as semantic authority. The nested
preserve/suspend decision is now resolved by the user's explicit choice;
escaped-value entitlement remains separately open. Exact locators: frozen
`web/docs/reference/effects.md:127–151,
153–204, 244–265`; frozen `web/docs/reference/type-theory.md:154–179`; current
`docs/yulang3-architecture.md:702–718`; draft §§1240, 1281, 1321. No source
implementation or tests changed.

### Conditional one-request reduction and symbolic handler image (2026-10-02)

The common-interface draft now records a conditional `handle`/`invoke`
reduction. It premises initial handler-specific visibility, source-derived
result-force timing, preserved callback origin, no earlier eligible handler,
operation compatibility, and a request-free raw suffix. Under those premises,
the selected preserve clause plus nearest-first ordered search sends the
request to the catch; one raw resumption returns normally with empty immediate
request support. These premises are not all derived from the current source
typing relation, so this is not yet a source-adequacy theorem.

The compiler-referee review closed two overclaims in the first version: the
request-origin/force premises are now explicit, and operational handling no
longer implies successor final-check acceptance. The frozen checker accepts
the witness, but a finite successor presentation has not yet been shown to
derive that acceptance. A final narrow review confirmed nearest-first context
extension and ordered search are consistent, and the “no earlier eligible
handler” premise prevents the outer handler from incorrectly bypassing a
nearer eligible one.

For any predicate `K(ν)` already in an input relation, the whole handler image
preserves its assignment `ν`; selection changes the request observation, not
the assignment. Therefore output pairs still satisfy `K(ν)`. Formula-to-view
incidence `D` must continue to identify dependent surviving views; this is a
presentation obligation, not implied merely by the same-ν equation. The result
is conditional preservation at the handler-image algebra step, not proof that
the source rules or concrete solver produce/preserve the right `K,D` throughout
the entire lifecycle. Soundness, finite principality, and intrusion quotient
adequacy remain open. No tests were run.

The follow-up compiler-referee review found that the first preservation/search
decomposition had replaced the existing stateful ordered `Search_H` with a
simplified visibility-and-operation-coverage test, omitting pattern rejection,
guards, and guard effects. The draft now treats preservation solely as
transport of candidate-specific visibility and delegates actual selection to
the existing `Search_H` relation, including its source-order state and effects.
The review also corrected raw-resumption wording: the selected shallow
activation is absent after handling, while an independent outer activation
may handle a later request only through its own visibility derivation and
ordered search. The compiler-referee delta review closed both findings with no
remaining issue in this decomposition. This does not close the source-stage
transport premises or the global soundness/principality gate.

### Conditional frame-extension derivation (2026-10-02)

The coupled-interface draft now factors handler-relative visibility into the
active candidate identity, exact operation compatibility, and
origin-indexed `Capture_ν(o,h)` incidence. Under a nested `CallView`, each
stage must either preserve those coordinates at the same assignment or apply
one equivariant capture-avoiding transport uniformly to request endpoints,
`K`, and `D`, while fixing imported outer binders and preserving `h`'s
activation. Under those premises, induction over the finite call/adaptation/
force sequence proves
`Visible_ν(q,h,κ) ⇒ Visible_{θν}(θ(q),h,b::κ)`.

The derivation separates entitlement from dispatch: stateful ordered `Search_H`
still evaluates nearer patterns and guards against evolving state, and only
that relation selects an arm. After `h` handles a request, its shallow arm is
outside `h` and gets the raw continuation, so the frame-extension lemma does
not apply to a resumed suffix unless a separate source step re-enters `h`.
For a different caller origin `o'`, context extension cannot produce the
missing `Capture_ν(o',h)` premise. The symbolic family formula survives only
when the same transport maps its dependent `K,D` incidence.

This closes a conditional derivability argument for the selected clause, not
the actual source premises: annotation adaptation, callback-origin mapping,
force placement, and source incidence equivariance still need derivation from
the successor source rules. It is not whole-language type soundness or
principality; in particular the least finite interface for the stateful
handler and raw-continuation image is open.

A compiler-referee delta review found and closed one precision issue: the first
lemma wording did not explicitly require exhaustive factorization of
`Visible`'s positive and negative ordered-context premises. The current text
now premises that exhaustiveness, preservation of every remaining premise,
and absence of an independent source invalidator. The reviewer found no other
issue in this conditional lemma; closure does not extend to the source-stage
premises, concrete `K,D` transport, soundness, finite inference, or
principality.

### Adaptation-origin transport and shallow cutoff (2026-10-02)

The draft now case-analyzes the existing `Adapt` equations. Under an
origin-preservation premise for the value-boundary relation, identity
adaptation leaves origin unchanged; forcing a thunk exposes the forcee's
origin; wrapping as a thunk retains the origin and `K,D` incidence latently;
thunk-to-thunk adaptation composes force and result adaptation. The
`CallView` composition then transports callback-origin `Visible` across
argument adaptation, call, and result adaptation under the composed type map.
Requests independently produced by conversions need their own source
incidence; family equality alone does not grant them the callback's capture.

Adversarial review found an essential cutoff: if `h` itself handles an earlier
request during the still-running `CallView`, shallow semantics removes `h`
before resuming the raw continuation. A later suffix request cannot inherit
that activation's entitlement. The theorem now applies only along prefixes
where `h` remains active and no independent invalidator occurs; an independent
outer handler must use its own visibility derivation. This is not a
counterexample to the user's preservation decision because selecting `h` is
an independently specified shallow-handler boundary. The review also corrected
the force wording so it distinguishes source origin and restored re-entry
lineage from boundary-specific allocation of fresh dynamic identity. Both
findings closed under compiler-referee delta review.

This closes only the conditional `Adapt`/`CallView` decomposition. The
successor source rules still must prove origin and `K,D` preservation for each
adaptation/force, typed compatibility before dispatch, and complete handler
image behavior across repeated requests. Global soundness, finite
representation, and principality remain open.

### Returned thunk: callback lineage versus caller lineage

The proof now has a same-family caller-hygiene discriminator at result
adaptation. A thunk carrying the callback computation lineage may preserve its
existing `Capture(o_cb,h)` through force and nested adaptation, with `K,D`
transported uniformly while `h` remains active. A thunk merely returned or
forwarded by the callback but carrying caller lineage `o_caller` cannot borrow
that entitlement from family/payload equality; it needs its own independent
visibility derivation. Compiler-referee review found no issue with this
conditional distinction, and identified the remaining source proof cases:
callback-created wrappers that force caller-owned thunks, thunks containing
requests from both origins, and forwarding/resumption with activation restore.
Origin must attach to each exposed request, not one whole thunk. Each origin's
own `K,D` incidence must use the same symbolic transport; immediate empty
support does not discharge it. The source value/force relation must establish
these cases, so this remains a conditional distinction, not a source rule or
global proof.

The next derivation reuses the draft's stateful bind equation. Once an observed
request is labeled `q[o]`, `Request(q[o],c,k) >>= F` changes only its saved
continuation to `λr. k(r) >>= F`; it cannot relabel that already observed
caller request as callback-origin. Requests later emitted by `k` or `F` retain
their own source labels. This closes a local label-stability lemma inside the
candidate resumable relation, but not the source rule that assigns labels when
a thunk is created, forwarded, or forced.

Compiler-referee delta review closed this local lemma. Its scope is request
label stability only: bind preserves an already observed `q[o]` and rewrites
its saved continuation, but does not prove reachability of every later request
under stateful multi-shot resumption, handler visibility, or full `K,D`
incidence preservation. Those remain separate source and interface-composition
obligations.

Substituting the three nonidentity `Adapt` equations into that bind lemma gives
conditional cases: force-to-concrete preserves already observed labels and
appends result adaptation to their continuations; concrete-to-thunk dispatches
nothing at wrap time and exposes the latent relation only at a later force;
thunk-to-thunk delays `Force(v) >>= Adapt(A,B)`, preserving prior request labels
and giving later conversion requests their own source labels. Review caught
that appended adaptation is not guaranteed to execute: a shallow arm may
abort, or resumption may not return. The wording now says it runs outside the
selected activation only if reached through raw resumption, unless an
independent source transition re-enters that activation. Delta review closed
this correction. The equations still require source provenance and symbolic
`K,D` transport premises.

The first-dispatch force/catch cut now has an origin-indexed refinement. A
thunk's latent interface retains each request origin before force; force
exposes the same first request origin before active ordered dispatch; after a
non-forcing value arm returns and unwinds the handler, a later forced request
retains its own source origin but cannot use the departed handler without an
independent re-entry transition. A shallow-selected handler remains absent
from its raw suffix, with independently specified re-entry allowed. Adversarial
review required that qualification and then closed the wording. The `Visible`
capture derivation, `K,D` transport, and source Force/value rules remain open.

The transport notation is now aligned with the general injective `Tr_θ`
action: type maps act on typed endpoints/`K`; owned-occurrence maps act on
source/request-owner labels and `D`; boundary maps reindex compile-time
handler-binder metadata. The callback-origin case fixes already concrete
dynamic request and activation IDs, while a later execution can allocate fresh
dynamic instances. Compiler-referee review found this identity split consistent
with the general equivariance theorem after explicitly identifying it as the
runtime-ID-fixing specialization. This is identity bookkeeping only; it does
not prove source lineage generation or non-injective intrusion preservation.

The origin-labeled bind equation is recorded as the request clause of the
existing `Tr_θ`/bind commutation proof. Review confirmed it transports the
request, origin coordinate, configuration, and continuation together while
fixing concrete runtime IDs. Its conclusion is conditional on source `Capture`
equivariance and the existing injective transport assumptions; source label
generation, complete solution-fiber preservation, and non-injective parent
quotients remain open.

The general parent-quotient observation criterion now has a specific
caller-hygiene stress case. Same-family, same-payload requests can still have
different complete handler observations when one origin is captured and the
caller origin is not. Merging their owner labels and replacing edge evidence
with one node-local capture bit cannot preserve both routes. Independent
review confirmed this only rejects that evidence-collapsing quotient; a
type-only parent map may keep owner/boundary identities and request edges
distinct, subject to the full solution-fiber test. This does not prove the
actual successor source owns the hypothesized events.

The candidate source derivation for `Capture_ν(o,h)` now binds `h` to the
ordinary source relation's exact receiver activation and argument-contract
boundary. Compiler-referee review found that dynamic containment alone could
incorrectly let an outer concrete callback contract capture through a nested
receiver's handler. The text now excludes that inference; a nested handler
needs its own source-derived contract connection. Review otherwise accepted
the per-request caller-owned-thunk distinction and found no new selector or
obligation. This remains a projection candidate: source ownership rules and
their soundness/principality proof are open.

The `Capture` projection is now expressed as one join in the common source
relation: request/value-flow ownership, handler installation under the exact
receiver activation and argument contract, and typed operation compatibility
at the same assignment. These are proof coordinates, not separate solver
predicates. Nested `CallView` preserves an already-derived outer incidence but
does not copy it to a newly installed nested handler. Compiler-referee and
spec-auditor delta reviews found no remaining findings and confirmed that
preservation stays selected, dynamic containment alone grants nothing, and
escaped-handler eligibility remains open.

Alternating implementation review rechecked the current HIR, solver, core, VM,
and native surfaces. Resolved expressions still lack calls, Force, requests, or
handlers; core and backend entrypoints remain documentation-only, and current
effect substitution has no origin transport. This rule cannot be prototyped
without major front-end, solver/scheme, and runtime work, before the source
relation is settled. The next theory gate is to derive the call/value/handler
incidences compositionally, including wrapper/forwarding and escaped
closure/re-entry cases; repeat feasibility review after that gate.

A conditional closure-value transport lemma now specializes the existing
`Tr_θ`/bind equivariance to Lambda construction and later `ApplyValue`. Under
source `Run`, captured-environment, and lineage-reentry equivariance, injective
freshening maps code, captured environment, `K,D`, origin, and compile-time
boundary evidence together while fixing runtime event/activation identities and
store. The lemma neither snapshots the live handler stack nor proves that an
escaped request is visible to a later handler. Compiler-referee review closed
this statement with no findings; source closure/re-entry adequacy,
non-injective intrusion, and full solution-fiber preservation remain open.

The escape analysis now separates retained `Capture_ν(o,h)` incidence from
the active-frame premise of `Visible`. If ordinary return removes `h` from
`κ`, that old activation is no longer eligible even though the closure retains
its latent request and symbolic `K,D`; continuation resume may restore the
same `h`, while a newly installed `h'` needs its own source join. This is the
ordinary activation exit consequence, not suspension at a nested receiver.
Compiler-referee review confirmed it is consistent with selected preservation
and runtime guard-lineage transport, without treating a guard marker as a
handler activation.

An escape-scope audit found the remaining caller-handler question cannot be
inferred from the selected nested-preservation clause. The actual `maker`
witness has no handler to remove; its returned closure retains a callback
request and mandatory activation lineage, while the fresh caller handler's
eligibility is unspecified by the frozen source docs and current architecture.
Receiver-local `Capture` proves that `maker`'s grant is not transferred by
family equality, but does not prove the caller handler is ineligible by every
ordinary source rule. Architect, compiler-referee, and spec-auditor reviews
converge on this boundary. The design now records two unselected rules:
ordinary caller handling when the complete source relation permits it, or a
source-justified carried-boundary mask. Both retain latent effects and runtime
lineage; neither may be selected from frozen runtime routing. Exact pure-caller
acceptance still depends on the finite handler-image abstraction. The user's
subsequent ordinary-caller preference resolves the semantic direction below;
it does not supply the missing source-adequacy derivation.

### Escaped callback eligibility: ordinary caller default (2026-10-02)

The user selected ordinary caller handling as the default for an escaped
callback. A later caller handler may handle its request only when the ordinary
current source relation, handler-relative `Visible`, ordered search, and
`OpCompat` derive that result. The maker's callback-capture authority belongs
to its receiver activation and cannot transfer to a fresh handler by family
equality. Normal return ends that activation, but does not erase the returned
closure's latent effects, request origins, symbolic typed-family constraints,
`K,D` incidence, or required runtime lineage. Lineage transport alone is
neither a fresh grant nor a persistent mask. No independent source-language
reason for a carried mask has been established; do not add one to reproduce
frozen runtime routing.

The requested discriminators were checked against the common relational
presentation:

1. **Escaped callback:** the `maker(f) = \_ -> f()` witness installs no
   handler in `maker`, so expiring a maker handler cannot settle the fresh
   caller's eligibility. The request must remain on the returned function;
   caller handling is a new `Visible` derivation, not a transfer of maker's
   grant. This is consistent with the relational model but the ordinary
   closure/application rule that joins the escaped origin to the fresh handler
   remains to be derived.
2. **Mixed origin:** a closure that forces a caller-owned thunk and then issues
   a callback-origin request must retain two request events and their distinct
   origins and `K,D`, even if both share one family instance. Neither an
   origin-level owner bit nor family equality may lend maker capture to the
   caller request. The separate imported-Force A/B policy remains unresolved.
3. **Ordinary effectful closure:** the direct `\_ -> choose::reject()` control
   retains `[choose]` and its ordinary caller handler returns `3`; its pure
   caller annotation is rejected by the frozen checker. The direct and
   escaped closures should use the same current-handler relation whenever
   their complete source visibility derivations coincide. This equivalence is
   still a source-adequacy obligation, not a proved identity of origins.
4. **Repeated request and shallow resume:** consuming the first request does
   not subtract a whole latent family when a later request in the raw suffix
   runs outside the shallow handler. The complete stateful handler image must
   account for the suffix.
5. **Ordered selection and compatibility:** ordered search selects by source
   visibility and order. Every actually selected arm must satisfy universal
   `OpCompat`; an incompatible selected arm rejects typing rather than being
   reclassified as forwarding to an outer compatible arm.

These cases show that ordinary caller handling is the preferred semantic
direction without a new callback-only selector or sticky boundary construct.
They do not yet prove the fresh-handler/source-origin join, full source
adequacy for closure and Force transport, soundness of the complete handler
image, or principality of its finite abstraction. If deriving ordinary
visibility produces a genuine source-level counterexample, return that
counterexample for reconsideration; do not patch it with an ad hoc mask. The
compatibility record and the precise conditional rule are in the
coupled-effect draft, “Candidate and open boundary lifetime for callback
capture contracts.”

The alternating implementation-feasibility check remains negative: current
resolved HIR has no call, Force, request, or handler execution rules, and
current effect substitution has no origin/`K,D` transport. Core and backend
entrypoints are still stubs. This semantic slice has no bounded production
prototype until those interfaces exist, so continue the source relation before
another implementation audit. No implementation, tests, or builds were run.

### Next bounded source theorem after preservation selection

An independent compiler-referee audit identified the next proof obligation as
source adequacy of per-request provenance through thunk adaptation. Fix one
assignment `ω`, one receiver argument boundary `(r,a,E)`, and an already-derived
`Capture_ω(o,h)`. For each finite prefix of argument adaptation, the call, and
result adaptation in `CallView`, derive from the ordinary value/Force/application
rules that each exposed request retains its own origin and dependent symbolic
`K,D` incidence. Therefore `Capture_ω(o,h)` remains derivable at that request
while `h` remains active, unless an independently specified source transition
invalidates it. A distinct caller-owned request must not gain the incidence by
family equality. Start with forwarded thunks, callback wrappers forcing caller
thunks, and mixed-origin computations; stop at selection/removal of `h` and do
not settle post-return caller-handler eligibility in this theorem.

The current draft proves only conditional composition: its source ownership,
Force-origin, and complete-interface transport premises are not yet derived
from source rules. A stress case is a callback returning
`Delay(Force(u_caller) >>= callback_request)` where both requests share one
symbolic family `F<α>`: whole-wrapper ownership would wrongly grant the caller
request, while dropping incidence at the wrapper would lose the callback
request's `K_F(α),D`. Stagewise witnesses are insufficient; both requests and
all incidence must inhabit the same assignment and joined interface. This is
a blocking gap for claiming source-theorem closure, not a contradiction of the
selected preservation rule. No implementation claim follows until the source
correspondence is proved; then run a targeted feasibility audit against the
derived carrier instead of repeating only the current broad surface inventory.

### CallView origin-composition lemma (proved conditionally)

There is a smaller composition result that does not depend on choosing any
source-site selector. Write each transition as a relation on the **complete**
interface at one assignment:

```text
Tᵢ,ν : Iᵢ ⇝ Iᵢ₊₁
```

Each `I` jointly contains the request occurrences, per-request origin
incidences, symbolic family formulas `K`, occurrence incidences `D`, and their
shared-binder predicates. Assume each source transition has three properties:

1. **Fiber and predicate preservation:** one derivation relates its input and
   output using the same complete assignment `ν`, and preserves the joint
   `K,D`/shared-binder predicate for every surviving request and every
   dependent residual or value view. It does not choose separate witnesses for
   request payloads and their constraints. A predicate may be projected only
   when the source transition proves it irrelevant to every remaining view.
2. **Per-request factorization:** every output request is either inherited
   through an input computation/value lineage, with its origin and all
   dependent `K,D` incidence transported together, or generated by this
   transition's own source derivation with its own origin premise. A force may
   expose a new dynamic event from an inherited latent lineage; event identity
   is not conflated with source origin. Inherited requests do not acquire an
   origin merely from another request's family or owner.
3. **Witnessed disappearance:** if a request occurrence is absent from an
   output prefix, that absence has a source-transition witness (for example,
   the represented execution prefix has not emitted it, or a source operation
   consumed it). It is not silently dropped by the interface map; any formula
   still constraining another view remains in the joint predicate.

Then relational composition preserves these three premises. For a surviving
request with inherited lineage, follow its lineage and incidence witnesses
through the intermediate complete interfaces; intermediate source-flow
relations compose even when force allocates a new dynamic event identity, while
the common `ν` is preserved by each relation. For a generated
request, its generating stage supplies the origin; every later stage either
transports it under the inherited clause or records its disappearance under
the witnessed-disappearance premise. The full predicate premise retains
dependent typed-family information across either case. Thus no later stage can
relabel it by family equality. Induction gives the result for any finite chain, including
the three `CallView` stages `Adapt(argument); Call; Adapt(result)` and the
structural force/bind steps inside each adaptation.

The mixed-thunk stress case follows **if** the source rules establish its
premises: the forced caller request enters with inherited caller lineage, while the
wrapper's operation is separately generated; every observed request remains
in the same `I` and assignment, each with its own origin and `K,D`. A
wrapper-level owner bit or
separate marginal projections violate per-request factorization. This proves
closure under composition, not that source evaluation, Force, application, or
conversion satisfies the three premises. The missing source-adequacy lemma is
therefore narrowed to proving those local transition premises for the ordinary
value/Force rules, including helper calls and captured executable values. No
dispatch or escaped-handler rule is added here.

Independent compiler-referee and spec-auditor review found two proof-contract
gaps in the first statement: it allowed vacuous disappearance of a request and
did not require dependent `K,D` predicates to survive when a request left the
immediate output. The premises now require a source witness for disappearance
and preservation of every predicate that still constrains a residual or value
view. Delta review closed both findings. The result remains conditional and
proves only compositional closure; it does not derive the local premises from
source semantics or establish handler soundness/principality.
