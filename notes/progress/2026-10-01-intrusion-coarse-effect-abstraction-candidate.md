# Conservative continuation-summary effect candidate

Date: 2026-10-01
Status: exploratory candidate; not selected or authoritative
Scope: ordinary shallow effects and handler residuals; no weight encoding yet
Implementation authority: none
Reviewed-by: architect, compiler_referee (multiple delta reviews), spec_auditor (multiple delta reviews)

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

## Adversarial review result

Independent architect and compiler-referee reviews agree on the following:

- **Blocking for a general rule:** define provider identity and handler
  eligibility independently of family labels. A family may be removed only
  when each possible request in it is covered and eligible; otherwise retain
  it conservatively. Prove that source inference and runtime handler search
  implement the same relation.
- **Major:** state principality as a least-solution property of explicit
  compositional rules with the whole-scrutinee continuation summary. A finite
  powerset codomain by itself does not make the coarse one-request result
  principal. Open rows, higher-order subtyping, SCC schemes, and final
  acceptance remain outside the present argument.
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
as a transferable Boolean attached to a family is unsafe: if it escapes in a
returned closure, a later handler without a matching receiving-boundary
contract may steal the request. The converse shortcut—dropping every grant at
a helper return—could prevent a contract that composes through a helper from
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
function's latent effect. Whether the enclosing caller's explicit `[]`
annotation must be rejected depends on the still-open declarative eligibility
of that caller handler. The Oracle accepts the annotation while both runtimes
leave the request unhandled; this is a concrete accepted-but-failing Oracle
case, while the successor's final acceptance delta remains unsettled until
handler eligibility and source/runtime correspondence are defined.

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
premature. A returning-callback control is documented below; a dynamic
request/marker trace is still needed before choosing that boundary rule.

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
eligible/ineligible-caller ambiguity therefore remains.

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
then rejected or its handler may soundly consume the request remains open
until provider eligibility and source/runtime correspondence are defined.
Thus the accepted-but-unhandled Oracle behavior is recorded, while its final
well-typed-program acceptance delta is not yet selected.

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

```text
T_{H,κ}(Return(v)) = value_arm(v)

T_{H,κ}(Request(q, k)) = operation_arm(q, k)
    if Covered(H, κ, q.operation) and Visible(q, H, κ)

T_{H,κ}(Request(q, k)) = Request(q, x -> T_{H,κ'}(k(x)))
    otherwise
```

In the forwarded case, `κ'` ranges over the successor configurations allowed
when that request is resumed by its surrounding context. Those transitions
are part of the still-open source semantics.

Let `Reach(H, C, κ0)` contain every request/activation/provenance
configuration reachable from the initial configuration `κ0` while evaluating
the transformed tree, including tails reached after any allowed operation
result and any handler re-entry induced by forwarding. Let `A(H, C, κ0)` be
one uniform upper bound for value and operation arm effects across every
configuration in `Reach(H, C, κ0)`, with raw `k` assigned latent `May(C)`. Let
`Drop(H, C, κ0)` be a proof-carrying set of families, not a
function of the family row alone. A family `f` may enter `Drop(H, C, κ0)` only if
every reachable configuration in `Reach(H, C, κ0)` for a request of family
`f` is covered and visible at that activation. This quantification must
account for forwarding: an outer handler may resume a forwarded continuation
zero, one, or multiple times, producing different configurations. The
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
3. `Drop(H, C, κ0)` excludes every family that occurs at any reachable
   uncovered/ineligible request configuration, including configurations
   reached after forwarding and outer resumption.

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
