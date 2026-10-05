# `id 1`: a source-reference Initial certificate and production seam

Date: 2026-10-06 (assigned artifact date)
Status: frozen unreviewed conditional source derivation and bounded artifact map
Baseline: `885939a8202190fb2d0d8ffe20cea16a17d16d56`
Exclusive lease: this file only
Implementation authority: none
Method: instantiate existing source-certificate rules, then map their operands

## 1. Result and exact premise

Theorem C §3's **Initial** rule supplies one source-reference inlet subcase
for `id 1`: synthesize a literal Int result port, pass its whole delayed
computation, and use the actual Value-entry result/rebind path. The reference
rule does not require inventing
`Check(Computation(empty,Int),Value(Int))` or assuming a pending Function
comparison. Thus the generic missing production cross-form interpretation is
not an additional premise of this already specified reference rule.

This result is conditional on the independently supplied decorated
source-context witnesses that Theorem C §2.1 explicitly takes as input. Literal
synthesis does **not** generate a receiver activation, receipt, profile or
typed path. The complete certificate cannot be reconstructed from the current
production `id`/literal facts alone. In particular, this note does not prove
raw-source typing or production admission of `id 1`.

The constructive gain is precise: the reference inlet has a rule to
instantiate; its remaining local production premise is formation/interpretation
of the original decorated call/carrier/result incidence and its retained
contracts. No exhaustive production inlet rule or Option 2 membership grammar
is selected.

## 2. Pinned inputs and governing sections

Only committed source at the assigned baseline was consumed. The three
approved answers were read directly and their blobs independently checked.
The prior M1 note is historical research, not an authority premise here.

| Input | Exact scope used | Git blob |
| --- | --- | --- |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | d1 decisions 1–5: independent broad contexts, direct whole-carrier/callable holes, preserved evidence, no comparison premise | `e3c0dada3036e23c2929c5af9775e7490998a210` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | d1 decisions 1–5: complete original `Rel_C` fiber, independent constraints/admission, concrete rules open | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | d1 decisions 1–4: Option 2 extras allowed without uniform source witnesses; Theorem C remains a source result | `fb4a169a2d748422490cc74c026338587290e90c` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | §§16–17 whole-carrier invocation/reification; §21 unannotated Value-entry authority | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | §§2–3 supplied derivation and delay translation; §6 literal/result/parameter rules; §9 actual entry paths | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
| `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | §§2.1–2.3 decorated input/primitive/generator; §3 Initial/Response and nonempty example; §4 Theorem C | `ab212217cd404991cded2b8fd529a1e731a806b3` |
| `notes/design/2026-10-04-source-indexed-callback-realization.md` | §§3.1–3.2 literal/result/reify/call and entry; §4 reference-domain admission | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
| `crates/yu-hir/src/module.rs` | `HirParameter`, `ResolvedExpr`, `lower_plan`, `lower_simple_chain` | `668d1b6f82fb17a96178a2353543d288c32e2762` |
| `crates/yu-solver/src/lib.rs` | `LambdaRecipe`, `emit_integer`, `emit_lambda`, `admit_lambda_fact`, `SolvedModule` retained owners | `fa118b726ebbfdc7d32b617373b4e2cb04e84682` |

The core/reference packages retain their conditional scope and no
implementation authority. The charter's selected role/scheduling decisions
are used within that scope. No uncommitted replacement is a dependency.
Previously read research/design-authority/Git-concurrency rules govern this
disjoint research lease; no shared record or prior artifact was edited.

## 3. Minimal independently supplied context

Keep one original binder environment and fiber `xi=(nu,K,D)`. Do not erase
`K,D`, change their scopes, or choose witnesses separately per segment.
Instantiate the identity's common value coordinate at Int consistently with
its original local constraints. The actual source is `my id x = x`, with an
unannotated parameter and actual Pure introduction, not a synthesized Handler
wrapper.

Take a punctured finite context with a declared callable hole `H`, a direct
argument-carrier hole, a terminal Int result consumer, and no other free
values. For the reference checked challenge, it has the instantiated known
slot/view `beta` of Theorem C §3; for the actual challenge, its entry/result
correspondence is the actual identity's Value entry. The hole declaration may
describe how the context uses `H`. It contains no proof that the filling
already satisfies the declared Function contract or tested query `Q`.

The supplied decorated witness `chi` must contain, before `Q`:

- the carrier's original designated computation/result port and typed Int
  result path;
- the actual receiver context, receipt/Flow correspondence, source scope and
  applicable view/profile contracts at that port;
- the original immutable lexical realization and joint `xi`, with all local
  constraints valid independently of `Q`;
- any slot/view authority required by that source context, with no invented
  grant, and its compatible current configuration.

These are the existing theorem's independent kernel inputs. They are not a
new predicate “the desired inlet comparison succeeds.” Their construction
from raw source/current F5 is **not** claimed here. If one has only a scalar
Int fact and no such independent typed correspondence, this derivation stops
before Initial; adding an assumed cross-form inequality would not repair it.

No ambient operation handler, request, response provider, raw handle, mutable
cell or latent returned provider is needed for this smallest source subcase.
The initial history is empty. Absence of those extensions does not remove
the receiver/path/context premises in `chi`.

## 4. Literal synthesis and whole-carrier certificate

Use the exact independently typed scalar local relation for literal `1`.
Choosing an exact scalar relation is within Theorem C §2.2; no conservative
extra is needed for this witness. The finite proof graph is:

```text
literal rule:       d_1 = literal(1) : Value(Int)
normalization:      c_1 = result(d_1) : Comp(empty,Int)
call translation:  t_1 = Delay(X[c_1], original lexical references)
designated port:   the c_1 port retained in chi, with result interface Value(Int).
```

The first two steps instantiate typed-core §6's literal and
`Result(Value(A))` rules. The third is exactly §3's call translation
`let t = Delay(X[c_a], lexical references)`; it does not execute a prefix of
`c_1`. The last identifies the independently supplied source port rather
than inferring a force path from a solved runtime representation.

The callable side is independently synthesized under the parameter binding:

```text
P = Value(A); Gamma(x) = Value(A)
body data = name(x); body computation = result(name(x))
lambda data = lambda(P, result(name(x)))
at the original Int assignment: A = Int.
```

These are the existing §6 name/lambda/parameter rules. They determine the
identity's actual entry and body interface without an expected-endpoint
assignment. This source graph and the punctured certificate are prepared
separately; filling `H` with the callable is direct and does not add that
callable to the other semantic environment.

Now apply Theorem C §3's existing Initial rule:

```text
locally typed whole carrier t_1 from c_1
declared result port Value(Int), profile and path from chi
independent punctured source context, original xi and local constraints
-------------------------------------------------------------------- Initial
empty history for this source-reference challenge is admitted.
```

Source-indexed realization §4 explicitly uses the same carrier and
result/rebind path in the actual Value inlet. Its rule supplies the reference
carrier-to-entry connection. The application relation then receives this
whole carrier and uses the actual receiver's single designated Value-entry
demand/rebind; that is the selected charter §21/typed-core §9 behavior.
There is no proof-only cross-tag conversion, extra wrapper invocation or
pre-entry force in this certificate.

This is an instantiation of the already specified source-reference rule,
analogous to Theorem C §3's nonempty Unit example using the exact Int literal
relation. It does not infer a fully typed raw application from literal
synthesis alone. In particular, the unrestricted §6 application constraint
and its missing production endpoint interpretation have not been replaced
with this restricted certificate rule.

**Response rule check.** For the exact literal carrier and identity source
relation, this certificate exposes no request to which Response could apply.
No response or raw-handle premise is manufactured; the empty history uses
Initial only. If the carrier were replaced by a request-producing source
derivation, Response would require its actually exposed request, original
operation witness, response port and current continuation context. This note
neither repeats that request trace nor constructs that larger certificate.

The conditional claim is therefore:

> Given the original independently valid decorated context `chi` and exact
> literal/identity source relations at `xi`, the existing reference Initial
> rule admits the `id 1` source challenge independently of `Q`.

It is not `Adm_prod(id,1)` inferred from F5 scalar/Function facts.

## 5. Exact current HIR/F5 object map

The following mapping was rechecked against actual committed source, rather
than treating a model's labels as compiler objects. It is a bounded code-path
read; no parser/collector execution was performed.

| Certificate operand | Available production object and exact location | Remaining correspondence |
| --- | --- | --- |
| Identity callable source | `ResolvedExpr::Lambda` retains occurrence, parameter id, body and range (`module.rs:426`). `lower_plan` wraps the resolved parameter body in that Lambda (`:1200`). | No runtime closure activation or complete invocation image is generated by this object. Actual role/entry interpretation is a source correspondence, not a stored invocation receipt. |
| Lexical `x` and identity result | `NameResolution` includes `Parameter(HirParameterId)` (`:397`); `lower_simple_chain` resolves parameter names through the current scope (`:1443`). | This is genuine binder identity, not by itself a demand/result typed Flow path. |
| Retained parameter/body/effect linkage | `LambdaRecipe` records occurrence, parameter position, root, optional body value component, body effect, lambda effect and insertion position (`yu-solver/lib.rs:689`). The own-parameter case sets body value to `None` and records the body effect (`:1557`). | This encodes the shared structural parameter/result recipe, not a received whole carrier. |
| Live Function provider | `admit_lambda_fact` uses one parameter live ordinal for negative argument and positive result when body value is `None`; attaches actual body-effect term and negative EmptyEffect, then records the Function-to-root fact/provenance (`:10539`). | No call operand, `t_1`, designated computation port, `chi`, `Rel_C` Initial predicate or actual receiver receipt is supplied by this fact. |
| Literal `1` source | A separately admitted integer leaf retains occurrence, spelling and range in `ResolvedExpr::Integer` (`module.rs:1427`). | The argument leaf inside `id 1` does not reach a resolved caller expression on this production path. A separately admitted literal is not proof of a carrier-use path to `id`. |
| Literal type/effect facts | `emit_integer` creates value/effect components and Int lower/upper plus bottom/empty-effect facts (`yu-solver/lib.rs:1454`). | Those facts establish the structural leaf constraints, not `Delay(c_1)` or a source computation elimination correspondence. |
| Call/delay and whole argument | `ResolvedExpr` has Lambda/Integer/Name/Error only (`module.rs:426–450`); `lower_simple_chain` admits only childless associated values (`:1422`). An associated application is unsupported. | There is no resolved `Apply(id,1)`, whole-carrier recipe, call-owned typed path or invocation receipt for this production source case. This is a generation boundary, not a semantic rejection rule for the approved domain. |
| Post-solve evidence owner | `SolvedModule` retains `Arc<HirModule>`, store, schemes and closed arena (`yu-solver/lib.rs:7168`); public `hir()` and `store()` expose the first two (`:15668`, `:15677`). | Retention permits a future proved reconstruction. It does not prove that the missing decorated context has already been reconstructed. |

For a source such as `my use = id 1`, the non-leaf associated application
hits the quoted lowering guard. This is derived from source inspection,
not a new executed compiler-result claim. A name's definition-use/type
instantiation is not the execution of that callable; no call certificate
may be assigned to it merely because the referenced scheme is the identity.

## 6. Production boundary, comparison independence and next obligation

The source-reference derivation consumes no successful whole-Function query,
no desired inclusion and no presumed satisfaction by the hole filling.
All witnesses stay under the same original `xi`. Source labels are finite
proof bookkeeping; no solver carrier or grant is added.

Option 2 is preserved: neither `Adm_prod` nor complete production membership
is defined as this source certificate. Additional independently licensed
production observations remain possible. Theorem C's source-reference
containment result can use this certificate in its exact linked-lift envelope;
one admitted source challenge does not show domain coverage for every
production context or containment for non-source observations.

The next local proof obligation is **decoration/conformance for this exact
Initial certificate**: derive or independently justify `chi`'s original
carrier/result/receiver paths and contracts, and establish their active
interpretation at the retained production endpoint. Current source inspection
maps the callable/literal ingredients and exposes the absent call-generation
seam; it supplies no proof of that obligation. If closing it requires the
generic production cross-form clause or a new durable interpretation, stop
there and return that specific clause to the primary's design gate.

The prior scalar-only M1 analysis remains valid for the exhaustive production
rule. This note narrows its source-reference subcase: Initial already provides
a conditional source rule, so no new cross-form check is needed **within that
reference framework with independently supplied decorations**.

## 7. Checks, omissions, resources and review

Commands: committed `git show BASE:path` section/range reads; narrow `rg -n`
locators for HIR/solver owners; a read-only Python
`git rev-parse BASE:path` pass checking all nine direct dependency blobs.
The three approved answer blobs and prior core/Theorem C pins matched.
Output lease absence, final output scope/hash and committed dependency
recheck are recorded at handoff. No Git index/ref mutation occurred.

No executable oracle, model, seed/range search, mutation, test, build,
formatter or benchmark was used. Existing source-certificate and primitive
relations are explicit shared premises of the derivation and Theorem C;
reading them is not independent proof of those source rules. The code-path
map is independent of a hand-supplied checker transition system but remains
bounded source inspection, not execution or complete implementation review.

Omitted: construction of `chi` from raw syntax/current F5; production Apply
or carrier generation; exhaustive contexts; non-source Option 2 extras;
request histories; latent returned providers; arbitrary adaptations,
annotations, mutable state or handler images; source soundness/principality
and production observation containment. No undecidability, carrier
insufficiency or implementation authority is claimed.

Resources: one producer, no children or heavyweight process. Lightweight
captured commands each completed below one second. Aggregate reasoning wall
time, CPU and peak memory were not instrumented; no incomplete enumeration
exists. Independent review is pending. The leased file is frozen before
submission; previous artifacts/shared records remain untouched.

Recommended next action: have the primary target the missing independent
decorated `chi` formation/endpoint-conformance proof for this existing Initial
certificate, keeping it separate from exhaustive production membership.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-function-id-literal-inlet-source-subcase.md` only.
- Baseline SHA: `885939a8202190fb2d0d8ffe20cea16a17d16d56`.
- Changed dependency hashes: none at baseline verification; all nine direct Git blobs are pinned in §2 and rechecked at handoff.
- Claim/review status: frozen, research-only, unreviewed conditional reference Initial derivation plus bounded current-source artifact map; no production gate closure.
- Checks already run: committed governing/code reads, nine dependency identities, lease absence and final scope/hash/dependency recheck; zero tests/builds/models.
- Proposed one-line checkpoint commit message: `research: instantiate literal identity source inlet certificate`.
- Shared-record deltas intentionally deferred to primary/curator: record that reference Initial covers this decorated literal subcase without a new cross-form check; retain raw decoration/current-production conformance and exhaustive admission as open. No task/index/theory/authority/question file was changed.
