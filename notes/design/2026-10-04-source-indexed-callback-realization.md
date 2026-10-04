# Source-indexed callback endpoint realization

Status: Reviewed limited mathematical construction; production conformance open
Date: 2026-10-04
Scope: constructive reference endpoint interpretation and its complete-bound crosswalk for the reviewed finite decorated immutable source envelope
Implementation authority: none
Supersedes: none

## 1. Result and its exact status

This note constructs a source-associated interpretation of an ordinary
Function endpoint and proves its correspondence with the reviewed
[source-generated callback theorem](2026-10-04-source-generated-callback-structural-theorems.md)
(Theorem C). The actual-bound membership inversion and checked-bound
embedding are consequences of finite constructor rules for this
**reference interpretation**. They are not assumed endpoint-adequacy
certificates.

The construction completes a candidate interpretation, rather than proving
that today's production endpoints already have that interpretation.
[Concrete compatibility](2026-10-03-concrete-compatibility-boundary.md),
under "Candidate abstract component as a same-fiber view," permits this reuse
shape but does not select a complete endpoint denotation. The
[production callback draft](2026-10-04-production-callback-endpoint-generation-draft.md)
likewise distinguishes a source graph from production complete-bound
membership. No earlier complete denotation is replaced here. In particular,
these rules are not a new rejection rule for the current compiler.

There are three separate conclusions:

1. Whole-observation typed projection preserves Theorem C, including every
   finite latent/future-use/resumption history.
2. A finite source-associated reference interpretation realizes the
   generated actual and checked bounds exactly at that observation boundary.
3. Conformance of current production generation and endpoint interpretation
   to these rules remains unproved. The unrestricted production bridge and
   principal effect-scheme gates are not declared closed.

The reference stays in the existing `Rel_C` carrier. It retains the ordinary
descriptor, original source occurrence, source derivation and residual;
there is no extra runtime representation, type constructor, provenance
store, or implementation proposal.

## 2. Input and preserved coordinates

Use exactly Theorem C §§2.1–3's source envelope:

- a finite decorated typed source graph with monomorphic recursive references;
- immutable lexical roots and source-labelled closure, delay, operation and
  designated result-consumer providers;
- independently supplied valid local source/primitive relations, typed paths,
  owner/view kernel, receipts, operation witnesses and existing attachments;
- finite separately supplied client/provider graphs, without a bound on the
  number or length of their finite future interactions;
- no mutable cells, opaque semantic imports, implicit adapters, or offered
  handler-image nodes inside this envelope.

For the linked Pure-value lift, the actual callable is an existing Pure value
with its actual Value entry. The checked template retains that same callable,
body, result and local relations. An unrelated annotation is not covered.
The inline B literal path is considered separately in §6.

Fix one original joint fiber `xi = (nu,K,D)`. Write `C_old` for the original
residual, including its inequalities, permissions, guards and all other live
dependencies. Neither construction removes `C_old`. The tuple `X` includes
every shared source root, endpoint, argument, body/result, continuation and
owner/view coordinate needed by a surviving view. A genuinely local witness
is hidden only at its original scope. A witness shared by two segments is
bound once around their joint formula, not once per segment.

Rigid operation binders keep their original quantifier positions. In
particular the construction does not interchange a rigid universal binder
and an existential witness that depends on it. Numeric labels may be
consistently renamed; original sharing and authority must be preserved.

This is the joint-hiding discipline of Theorem C §2.4 and
[parametric component linking](2026-10-02-parametric-component-linking.md)
§3. It is metatheoretic witness binding, not existential source types.

## 3. Finite reference interpretation

Preallocate the source labels, lexical binders, callable/delay body labels,
consumer labels and operand references. A back edge points to a registered
label. For each source occurrence, associate its existing ordinary endpoint
with the following finite constructor trace. This association is an
interpretation of the endpoint in its retained source context; the printed
four children alone are not the complete interpretation.

### 3.1 Values and computations

| Constructor | Reference membership clause |
| --- | --- |
| Literal or local primitive | Use its original whole-tuple relation. Exact source relations suffice; independently certified conservative local relations are also allowed, as in Theorem C §2.2. |
| Name | Read the same lexical root or parameter binder, retaining its descriptor and dependent roots. |
| Lambda | Return the inert closure descriptor with its source label, actual introduction role, actual entry, body/consumer and captured roots. |
| Operation | Return its declared producer and designated consumer, retaining the declaration-instance operands and native delimiter. |
| Reify | Return the inert delay reference to the source computation and roots. |
| `result(d)` | Generate the data descriptor and return it in the current configuration. |
| `eliminate_p(d)` | Execute exactly the source-designated one-layer port and its existing consumer. |
| `bind(x,c1,c2)` | Compose at the same returned descriptor and state, preserving the original binder; a request retains its original continuation with the same suffix appended. |
| `call(cf,ca)` | Evaluate the callee; pass the whole reified argument inertly; establish actual receiver and receipt; use that producer's entry, body and designated consumer; return from that invocation. |

The bind equations are the source equations, with current resumed state
explicit:

```text
Return(v,C) >>= S = S(v,C)

Request(q,C,k) >>= S
  = Request(q,C, lambda (response,C'). k(response,C') >>= S).
```

The request's operation witness, source origin, response port and pending
suffix remain the same. Reentry does not replay receipt or reopen its rigid
binder. The designated consumer for an operation is its declaration-derived
consumer after native invocation return; native return is not identified
with the declared completed result.

### 3.2 Entry and future interaction

Expand entry from the actual callable's source parameter form, using
[typed core](2026-10-02-typed-computation-core-elaboration.md) §§6 and 9.
Value entry receives the whole carrier, executes its designated Force port
once, rebinds the result at its typed source path, and continues with the
body and result consumer. Retained computation entry binds that same carrier
without an entry force. Its body's explicit consumers remain effective.

Introduction role and entry mode are separate. A Pure value offered at a
callback slot keeps its actual role and entry. The slot supplies the typed
invocation view; it does not rewrite the value's executable behavior.

A returned closure or delay retains the source label and roots used to
justify a later interaction. A certified future use unfolds the corresponding
constructor. A response or raw resumption uses the retained request's
continuation at the current decorated configuration. No clause revives an
expired callback or shallow-handler activation.

These are finite positive recursive relation templates. Their behavioral
denotation consists of finite observation derivations, including finite
prefixes. Recursive references do not assert termination or an infinite
liveness property. Divergence is not discarded on account of empty support.

### 3.3 The root rule and typed erasure

Let `Der_ref(e,h;xi,w)` mean that a finite derivation of these rules at source
endpoint occurrence `e` and challenge `h` has full joint witness `w`. Its
observation contains the existing typed interaction and latent-interface
structure. Define the reference complete bound by the root rule

```text
Der_ref(e,h;xi,w)  and  Obar = Pi_xi(Obs(w))
------------------------------------------------
Obar in P_ref(e,h;xi).
```

There is no additional root rule admitting arbitrary latent behavior solely
because its four port types fit. Every membership has a constructor witness.
Local conservative alternatives remain allowed when their original local
relation supplies that witness.

`Pi_xi` is one projection at the
[approved typed observation boundary](../../questions/2026-10-04-function-bound-value-observation/approved-answer.md).
It erases concrete data-value identity and concrete input/output data-value
correlation from the compared observation. It retains value types, typed
events/requests, continuation and origin/authority relationships, and live
`nu,K,D` dependencies. Internal source labels and data values may remain in
the hidden derivation witness to explain a latent observation; they are not
thereby added as publicly observable value identities.

Apply this projection to the complete joined observation. Do not project
argument, body and returned-value marginals separately and reconstruct their
product. Nothing requires erasure to commute with such local composition.
The approved decision does not project challenge admission down to a test of
value types alone.

## 4. Query-independent domains

The reference domains are generated by punctured source certificates with a
callable hole, as concrete finite rules, before testing the pending query.

An initial checked certificate supplies the instantiated known slot, a
source-derived whole carrier at the declared result interface, its `d`
constraints, independent lexical/provider roots, current compatible owner/view
context, original typed paths, and the same `nu,K,D`. The actual inlet uses
the same carrier, result/rebind path and source-context premises required by
the actual Value entry. It has no incoming support test inferred from Pure
introduction or the spelling `never`.

History extension has exactly these cases:

1. Supply a typed response at a request actually exposed in the retained
   joint history, under its original operation witness and current context.
2. Resume through a raw handle already associated with such a request.
3. Supply a future call/force provider at a returned source descriptor's
   original typed port, in its current compatible context.

The surrounding punctured context is checked independently; no case assumes
that the filling satisfies the pending callback query. A response certificate
does not become available merely because another history has a response of
the same value type. A divergent carrier is admitted by its source
certificate, without requiring a produced observation.

These are the same local source rules as Theorem C §3, now specified as the
reference endpoint's admission rules. Their equality with the generated
domains is a derivation correspondence proved below. No acceptance of an
otherwise invalid annotation is inferred from an empty domain or fiber.

## 5. Theorems

### 5.1 Whole-observation projected transport

Under Theorem C's hypotheses, write `P_GA` and `P_GC` for its generated bounds.
Then, for every `h in D_GC(xi)`,

```text
Pi_xi[P_GA(h;xi)] subset Pi_xi[P_GC(h;xi)].
```

**Proof.** Choose `Obar` in the left image and its original whole witness
`w`. Theorem C copies `w` to a checked witness `w+`, preserving all old
coordinates and `Obs(w+) = Obs(w)`. Apply the same `Pi_xi` once to those
equal observations. The image is therefore in the right bound. Theorem C's
copying applies to every finite future/latent/resumption extension, so the
same argument covers each such extension. Domain certificates are unchanged.
No new commutation or higher-order value-saturation premise is used. QED.

### 5.2 Constructive endpoint realization

Generate actual and linked checked reference presentations using §§3–4.
The checked trace copies the entire actual tuple, scope structure and local
relations and adds only Theorem C §2.6's total fresh-coordinate definitions:

```text
F_ref,C(X,Z,W) = F_ref,A(X,Z) and Def_T(W;X,Z).
```

This equation describes the copied observation graph at a common admitted
challenge; checked admission still carries its independent additional
constraints. Externally fixed `b,c,d`, original source occurrences, operation
witnesses and `nu,K,D` are old coordinates, never reassigned by `Def_T`.
The lift adds no target-bound predicate on an old segment.

Let `G_A,G_C` use the same source primitives and evidence. Then

```text
D_C^ref = D_GC subset D_GA = D_A^ref

P_A^ref(h;xi) = Pi_xi[P_GA(h;xi)]
P_C^ref(h;xi) = Pi_xi[P_GC(h;xi)]       for h in D_C^ref.
```

Consequently `D_C^ref subset D_A^ref` and
`P_A^ref(h;xi) subset P_C^ref(h;xi)` for every checked challenge.

**Proof.** First construct a finite trace correspondence. Each row of §3.1
has the same constructor tag, operands, source label, local relation and
scope as Theorem C §2.3. Entry and designated consumption agree by §3.2.
Preallocated recursive references correspond without unfolding. This step
only constructs the static correspondence; it is not yet behavioral
adequacy.

Translate a finite admission certificate in both directions by induction
on its derivation. Initial, response, resumption and future-use clauses have
identical premises and keep the same source/provider witness. This proves
the two domain equalities. Forgetting the checked inlet's extra `d`
constraints proves the middle inclusion, exactly as in Theorem C §4.

Now choose an arbitrary membership `Obar in P_A^ref(h;xi)`. The root rule
supplies a full witness and a finite constructor derivation. Induct on that
derivation. A local leaf keeps its whole-tuple witness. Lookup keeps its
lexical root. Lambda and reify keep their latent descriptor; they do not
execute it. Return and elimination keep their designated result/consumer.
A bind return enters the same typed suffix; a bind request retains the
same request and suffix. A call uses the same actual receipt, entry, body
and consumer. A finite future use or resumption unfolds the corresponding
retained label/continuation at the same current context. Every case thus
produces a `G_A` derivation with the same full observation, scopes and
`xi`. Its image is `Obar`. This proves actual-side membership realization
for arbitrary local conservative alternatives as well as exact executions.

The reverse constructor induction gives the other actual-bound inclusion.
For the checked graph, use the same induction and the identical total
coordinate definitions, evaluated on the old tuple. Forward translation
gives checked embedding; reverse translation gives equality. Scope-preserving
joint hiding and the same final projection preserve these equalities.

Finally apply §5.1 to a checked challenge and use both bound equalities.
This proves complete containment for one direct Function query without
composing successes of concrete comparisons. QED.

### 5.3 Finite presentation

Each source node emits a bounded constructor template and references its
existing children. Local primitive relations and certificate/profile/path
descriptions are inputs whose sizes must be counted. With those sizes
included, construction is linear in the finite decorated graph. Cycles share
registered labels. The full witness language and set of future clients may
still be infinite.

This proves an intensional finite presentation. It does not prove effective
elimination into a four-port descriptor, a finite-state behavioral model,
decidable complete Function inclusion, or principal inference. The pure
[structural FMP theorem](2026-10-04-structural-fmp-fence-completion.md)
is not a premise and does not supply those missing claims.

## 6. Role-first B and its separate generation boundary

For an unannotated literal at a known callback slot, use the selected order
of the
[callback context delivery contract](2026-10-03-callback-context-delivery.md)
and the production draft:

```text
known expected boundary -> Handler role -> own parameter and entry
 -> independently synthesized body and Result(I_body)
 -> latent invocation trace -> completed F_lit -> one F_lit <: F_cb.
```

The outer application and latent invocation keep distinct source tuples.
The latent trace selects three original occurrences: `d-` at the designated
argument Force path, `d+` for that Force-origin contribution in complete
`J_call`, and `b+` for body/designated-consumer contributions in `J_call`.
The linked output display is the existing canonical flat `[b+,d+]` view of
that one relation. Distinct occurrences keep their common original
coordinates; flattening is not a product of independently hidden marginals.

Contravariant component classification and concrete attachments use the
original supplied descriptor and subtraction evidence. The construction
does not derive an attachment from a row equality or introduce total reverse
addition. Expected context does not copy `F_cb`'s value endpoints into the
literal's independently synthesized endpoints.

Given valid finite source/evidence inputs resolving these projections and
attachments, the construction terminates and emits the completed query.
This is conditional **generation totality**. It does not prove the query
succeeds, nor that every raw literal already supplies these inputs. Theorem
C and §5.2 apply to the linked prebuilt Pure-value path, not to arbitrary B
queries. Annotation/callback overlap remains outside this bounded contract.

## 7. Production conformance is still a real obligation

The construction removes the abstract endpoint-realization premise for
`P_ref`; it does not remove it for an independently chosen production
interpretation `P_prod`. A compiler must be shown to retain or reconstruct
the constructor trace, domain rules, local bounds, scopes, occurrence maps
and total checked extension above. An interpretation admitting extra root
observations needs a corresponding certified constructor witness.

Current owners expose a concrete limit. `crates/yu-hir/src/module.rs`,
`ResolvedExpr` and `lower_simple_chain`, do not supply application source
derivations. `crates/yu-solver/src/lib.rs`, `LambdaRecipe`, `emit_lambda`,
`admit_lambda_fact` and `ConstraintStore`, retain source/endpoint identity
but do not define this complete membership relation. `TermView::PositiveFunction`
and `TermView::NegativeFunction` in `crates/yu-solver/src/term.rs` retain four
children, which are useful
inputs but not a constructor interpretation. These are inspected owner
facts, not a proof that a new carrier is necessary.

The higher-order warning is specific: under an *endpoint-only* interpretation,
two same-typed source functions can share a bound although one returns its
supplied quiet closure and another returns an effectful captured closure.
Future invocation distinguishes them by a typed request even after concrete
data erasure. Thus the approved projection alone cannot justify replacing
all production memberships by the exact source recipe. The reference avoids
that inference by retaining each latent source witness; it does not refute
all conservative endpoint interpretations.

No additional observation choice is needed for the theorems here. Selecting
or implementing the reference as production semantics is a separate design
and conformance step. General abstract-component interpretation, common
allowance, State/opaque providers, unrelated annotations and compiler
implementation remain outside the closed claims.

## 8. Review record

Independent read-only compiler-referee and specification-auditor reviews
(M3, 2026-10-04) found no blocking or major defect in the stated reference
construction. The specification review found no conformance defects. The
compiler review's minor production enum-name correction was applied and
verified against `crates/yu-solver/src/term.rs` by the primary.

Both reviewers expressly retained the production conformance gate. This
review certifies the limited mathematical construction, not production
completion or selection of the reference as authoritative semantics. The
[follow-up record](../progress/2026-10-04-callback-principality-direct-followup.md)
records the combined result.
