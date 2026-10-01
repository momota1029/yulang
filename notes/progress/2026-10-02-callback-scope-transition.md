# Callback-scope transition characterization

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: design investigation; no source rule selected

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
  runtime markers characterize re-entry only. No source rule or implementation
  approval follows.

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
concrete/concrete propagation, and escaped-value lineage are still absent.

Architecture and source-spec audits agree that an origin-indexed relation over
ordered boundary transitions is the most economical candidate carrier. The
public source contract supports capture by handlers inside a concrete
receiving function and protection of uncontracted callback effects. It does
not uniquely settle nested concrete receiver propagation or escaped-value
lifetime. Preserve/composition is the simpler hypothesis; a visibility cut
would need a source-defined boundary rule beyond family equality. Neither is
approved. A concrete user decision remains before that source rule can be
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
