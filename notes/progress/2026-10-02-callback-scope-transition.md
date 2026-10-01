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
