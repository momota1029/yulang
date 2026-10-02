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
| Concrete callback computation argument | Lets handlers inside the receiving function consume only the named family from that argument computation | A source capture relation is required for that receiver scope; its transport through a nested concrete receiver remains open |
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
