# Descriptor admission: the retained Function inlet incidence

Date: 2026-10-05
Status: independently reviewed source/code correspondence and conditional local bridge obligation
Baseline: `dfd49d1b14a9aba922bb0278ca7c1bfac8061058`
Branch: `research/simple-sub-intrusion`
Scope: one ordinary unannotated lambda's retained Function fact and one separately supplied typed invocation; no production context-domain quantifier
Implementation authority: none

## 1. Result and authority

The next useful bridge is narrower than a complete descriptor denotation:
interpret the **actual negative argument-effect child**,
`EmptyEffectNegative`, at the source lambda's inlet while preserving the
argument Force contribution at its complete invocation. The current solver
always places that leaf in the positive Function emitted for an ordinary
lambda. The selected source rule still forces an effectful or divergent
whole argument inside Value entry. The spelling of this leaf therefore
cannot supply an admission rule without a source-incidence interpretation.

This note establishes the exact retained code incidence, derives a
discriminator from the source entry equation, and states one pointwise
bridge proposition. It does not prove that proposition, define exhaustive
production admission or membership, or identify a production counterexample.
It does not choose which contexts production quantifies over.

The committed approvals govern:

- [Denotation A](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
  selects the original complete `Rel_C` at the same `xi=(nu,K,D)` and
  original scopes, with independently interpreted endpoint/role/path/origin/
  continuation/authority/dependency conditions. Admission is separate and
  independent of the pending comparison.
- [Option 2](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
  permits production observations without source-constructor witnesses. It
  does not select the exhaustive additional-member rule.
- [Charter §21](../design/2026-09-29-scc-intrusion-redesign-charter.md#21-user-decision-parameter-roles-follow-the-outer-source-annotation-2026-10-03)
  records the user-selected unannotated parameter role `Value(A)`, inert
  whole-argument construction, and same-receiver force/rebind before the body.
  Its general research header is not implementation approval.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3, 6, 9 supplies the conditional structural translation and the
  `J_arg/J_body/J_call` entry correspondence.
- [Production callback draft](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
  §3 requires distinct `d-`, `d+`, and `b+` source incidences before querying;
  §4 keeps production endpoint interpretation open.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2.2 requires semantically active retained clauses. Section 3.7's conditional
  `W/Z` grammar is neither selected nor used here.

Both committed approved answers embed their matching committed drafts and
record explicit `OK` approval. Their receipts identify integration commits
`0b6f326ae` and `74eab8661`. Reads in this derivation use `git show` at the
stated baseline; concurrent working documents supply no premises.

## 2. What the current code actually retains

The owning locations below are at the baseline.

| Owner | Exact retained information | Semantic limit |
|---|---|---|
| `crates/yu-solver/src/lib.rs:689`, `LambdaRecipe` | Lambda occurrence, formal-parameter recipe position, root component, body value/effect component positions, lambda construction-effect position | No runtime receiver, entry Force, or complete invocation receipt/path |
| `lib.rs:1557`, `emit_lambda` | For `id x = x`, the parameter-body case uses no separate body-value component; its body-effect component is bounded between `EffectBottomPositive` and `EmptyEffectNegative`; closure construction has separate pure-effect facts | These are retained polarized constraints, not complete argument or call histories |
| `lib.rs:10539`, `admit_lambda_fact` | Function lower fact, root upper fact, lambda-occurrence slot 2, cause and provenance | Fact insertion is not challenge admission |
| `crates/yu-solver/src/term.rs:1122`, `positive_function` | Child lineage, component kind and polarity checked before interning | No source admission/receipt/Force semantics is checked |
| `lib.rs:2858`, `AdmissionReceipt` | Store token, serial, constraint occurrence, cause, fact and accepted/duplicate delta | This is a store-transaction receipt, not an invocation's source receipt |
| `lib.rs:2881`, `ProvenanceEdge`; `lib.rs:2894`, `SemanticFact` | Cause-to-fact edges; fact ID and ordered lower/upper terms | Useful original-source references, without an independently interpreted whole-history clause |
| `crates/yu-types/src/lib.rs:585`, `PositiveValueView`; `:599`, `NegativeValueView` | Four typed Function children | No role/entry or receipt tag; effect observations at `:614`/`:618` are only `Bottom`/`Empty` in the present pure API |

The line numbers locate owners; the formulas below use the inspected function
bodies rather than field names as semantic assumptions.

For the identity recipe, write `p` for its session-allocated parameter ordinal,
`e_body` for its body-effect ordinal, and `r` for its definition root. The
actual emitted term/fact is exactly:

```text
F_id = PositiveFunction {
    argument       = LiveValue(Negative,p),
    argument_effect= Leaf(EmptyEffectNegative),
    result_effect  = LiveEffect(Positive,e_body),
    result         = LiveValue(Positive,p)
}

SemanticFact(lower=F_id, upper=Component(r))
source occurrence = (lambda occurrence, slot 2)
```

`admit_lambda_fact` obtains the formal ordinal from
`parameter_live_base + recipe.parameter_position`; its special identity case
uses that same ordinal for the result. Thus the value-port sharing is an
actual source/code fact. The argument-effect leaf is not the body's
effect component, and the body's effect component is not the lambda's
construction-effect component. No `d+` operand is added by this constructor.

This extraction is not a new assertion that negative effect `Empty` means
an empty request set. Nor does it identify `e_body` with the complete
`J_call`: the inspected code links it to the body component.

The `AdmissionReceipt` distinction matters: a successful store transaction
only establishes that a constraint fact and its provenance were admitted.
Converting that token into a proof that a source caller was admitted would
cross two different judgments. The token contains no received carrier,
actual receiver activation or response/resumption configuration.

## 3. A pointwise source discriminator

Use the typed core, not current raw/HIR application support. Supply a valid
declaration and its existing local typed certificate for an operation
`op: Unit -> [E]Int`, with a selected nonempty request contribution. Let

```text
id = lambda(Value(Int), result(name x))
c_op = call(result(operation op), result(Unit))
invocation = call(result(id), c_op)
```

`Unit` here is the supplied typed-core primitive, not a claim that current
error-free production HIR emits it. The known source typing/consumer
certificate is an input; no operation, payload, grant or response is inferred
from matching endpoint types.

The actual source expansion supplies `t=Delay(X[c_op])` to `id`, after
constructing it inertly. At the same original fiber and scopes:

```text
actual receiver and source receipt;
Force(t) >>= (a,C1).
    RebindResultPath(t,a,C1);
    Return(a,C1) >>= ReturnFromInvocation
```

The body has `Result(Value(Int))=Comp(empty,Int)`. Nevertheless an
independently legal finite entry prefix can expose the original `op`
request, before the body is reached. Typed core §3 explicitly includes the
operation's declaration-derived result consumer; §9 distinguishes this
entry contribution from the body result. In an ambient configuration with
no eligible handler, the exposed request is observable. With a handler,
the original pre-dispatch request still requires its typed incidence and
authority conditions.

For a response/resumption development covered by the supplied certificate,
the state-threaded bind equation is:

```text
Request(q,C,k) >>= suffix
 = Request(q,C, lambda(response,C'). k(response,C') >>= suffix)
```

It preserves the original operation instance, origin, response endpoint and
`K,D`; it appends rebind/body/return and does not replay the source receipt.
No termination or return observation is required for the initial prefix.

Consequently the proposed shortcut

```text
argument_effect = EmptyEffectNegative
    ==> admitted Force(t) has empty request support
```

has no source derivation. If a proposed production domain includes this
particular certified challenge, that shortcut rejects its entry request,
contrary to the source entry image. If it also equates `result_effect` to
the complete call's body-only support, it loses the same request at `d+`.

This is a conditional falsifier of the shortcut, not of the approved
production semantics. Whether this challenge belongs to the eventual
production domain is not asserted. The derivation does not choose a domain,
and neither current HIR nor the current four-port term is claimed to emit
this full operation call.

## 4. One minimal bridge proposition

Fix one ordinary source lambda root `rho`, its actual retained Function fact
`F_rho`, one original `xi=(nu,K,D)` satisfying the retained source constraints,
and one independently supplied typed punctured-context challenge `h`.
Assume the challenge's provider/path/operation certificates are valid at
those original scopes; this premise says nothing about the pending Function
comparison or the class of all production contexts.

The missing proposition is **inlet-incidence adequacy**:

> There is a source-derived incidence map `mu` from this Function fact's
> argument and argument-effect children to the lambda's designated received
> carrier/entry demand, such that an independently interpreted local inlet
> predicate `In_F(argument,argument_effect;h,xi,mu)` agrees with the source
> entry's typed carrier/rebind obligations for that same challenge. The map
> preserves the actual receiver/receipt, original argument/provider identity,
> binder scope and `K,D`, and carries the same Force contribution to `d+`
> without identifying it with `b+`.

This is a local proposition about a supplied challenge, not exhaustive
production admission. `In_F` is a named missing judgment, not a definition by
source execution, successful resolution, or desired containment. In
particular its clause for the actual `EmptyEffectNegative` child must be
given and justified; the name `Empty` does not discharge it. If a local
interpretation cannot agree for a proposed admitted challenge, the bridge
fails for that challenge and the mismatch is explicit.

The conditional reduction is precise. The source §21 role gives Value entry
before body synthesis. The retained formal-parameter/source occurrence map
identifies its argument/value endpoint. The source entry equation identifies
the carrier, Force, receipt and rebind. With inlet-incidence adequacy, the
descriptor's local input obligations can then be evaluated on that same
tuple without querying the pending inequality. The reference entry/bind
equations carry each certified request/resumption development through the
same suffix. This discharges **only the descriptor inlet portion** of an
admission check for `h`; surrounding context typing, provider future-use
rules and exhaustive production membership remain separate.

Nothing in this reduction defines production membership as the source image.
Option 2's permitted non-source members must eventually satisfy the separately
completed exhaustive interpretation. No `W/Z` rule, new carrier, total effect
subtraction, or comparison-composition law is introduced.

The current code establishes the first retained endpoint/source lookup and
the exact leaf incidence. It does not establish `mu`'s semantic path/receipt
part or the independent inlet predicate. The missing premise is therefore
the interpretation of a specific existing negative leaf at a specific
source inlet, not another request for the unresolved global context quantifier.

## 5. Next evidence, checks and checkpoint packet

The next useful research artifact is a source/code certificate for this one
incidence. Its structural part should recover the lambda occurrence,
parameter recipe/ordinal, exact Function lower fact and source-role entry;
its semantic part should state what `EmptyEffectNegative` constrains at
`J_arg`. It should account for a separately supplied request-free carrier,
the effectful prefix above, and an empty-support divergent carrier, with
their source certificates. These cases discriminate an actual inlet
interpretation; enlarging a toy membership search does not.

Such a checker may return an explicit unproved semantic obligation. It must
not report admission from store `AdmissionReceipt`, four-child equality,
F4 `SolvedEffect::Empty`, or a pending Function query. Current raw/HIR lacks
the production Apply/operation trace needed to derive these certificates
from source text. Executable certificate work needs a separately authorized
lease; this note changes no compiler or checker.

Verification performed: committed source/owner inspection, exact committed
draft embedding and explicit approval-marker comparison for both answer
bundles, and output-only whitespace checking of this note. Independent
`compiler_referee` review found no blocking, major, or minor findings. Review
verified the code incidence, pointwise Value-entry discriminator, approval
identity, and authority boundary. Exhaustive production membership/admission,
callback containment, and principality remain outside review. Tests, builds,
executable searches and measurements: zero.
No Git mutations or shared-record writes were performed.

Frozen direct dependency SHA-256 values:

```text
crates/yu-solver/src/lib.rs
  a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59
crates/yu-solver/src/term.rs
  12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611
crates/yu-types/src/lib.rs
  a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5
notes/design/2026-10-02-typed-computation-core-elaboration.md
  0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e
notes/design/2026-10-04-production-callback-endpoint-generation-draft.md
  f619eef1c4f3363737033a91380a029cdf48bb40b6101a11573cc117942e6698
notes/design/2026-10-05-source-contracts-and-common-allowance.md
  1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186
questions/2026-10-05-production-function-denotation/approved-answer.md
  7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a
questions/2026-10-05-production-function-bound-membership/approved-answer.md
  d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179
```

Checkpoint path: this note only. Claim status: independently reviewed
research, exact code incidence plus conditional local proposition/shortcut
falsifier; no gate closure. Proposed commit message: `Isolate retained
Function inlet admission bridge`.
No frozen dependency was modified by this lane. Primary integration should
recheck those dependencies before checkpointing. Shared changes to
`tasks/current.md`, design/index/theory records are intentionally deferred to
the primary; their useful delta is the named inlet-incidence obligation and
its request-prefix discriminator. Production context quantification,
exhaustive membership/admission, complete callback containment,
generalization/use transport and principality remain open.
