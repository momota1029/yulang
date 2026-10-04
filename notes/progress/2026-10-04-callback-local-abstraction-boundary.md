# Callback bounds must account for erased value dependence locally

Date: 2026-10-04
Status: Reviewed obstruction and bounded projected construction
Scope: the source-to-complete-Function-endpoint proof obligation
Base: `research/simple-sub-intrusion` at `eb7bc50d`
Implementation authority: none
Reviewed-by: independent compiler_referee, 2026-10-04; no blocking/major findings; two minor wording repairs incorporated

## 1. Result

The remaining callback bridge has a more specific abstraction obligation than
operational composition alone. If a Function bound is interpreted solely
from its grounded ports, it can forget a dependency retained by a source
name/rebind relation. In that case its full bound cannot generally be inverted
through the exact source relation, even on an integer identity with no
integer literal in its body.

This is an obstruction to an exact-recipe factorization premise, not a
counterexample to the intended callback inequality. Actual and checked type
bounds can both allow the same extra output. A locally abstracted source
recipe can account for that output without independent complete-call
widening.

The note proves the obstruction under an explicit endpoint-only hypothesis,
then constructs a finite local abstraction for grounded integer bodies and
proves its projected first-order callback lift. It does not identify that
construction with production F5, settle higher-order complete observations,
or change source execution. The exact/full and abstract/projected contracts
are kept distinct throughout.

Governing sources are
[callback B](../design/2026-10-03-callback-context-delivery.md) §§2–2.1,
[typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6,9,
[source adequacy](../design/2026-10-02-source-interface-adequacy-theorem.md) §§2–4,
and [Theorem C](../design/2026-10-04-source-generated-callback-structural-theorems.md)
§§2.3–4. This result does not supersede their source-role, receipt, scope,
joint-fiber, or independent-endpoint requirements.

## 2. Endpoint-only erasure obstruction

### Explicit hypothesis

Call a proposed interpretation endpoint-only when its observable bound, for
a fixed admitted carrier and decorated context, depends only on interpreted
Function ports and actual receiver/entry mode. It does not inspect retained
body HIR, lexical dependence, or the source-labelled relation graph.
Private occurrence/receipt names may be consistently renamed when comparing
the two independent source definitions.

Use the first-order observation projection that retains integer return
values and visible event histories. This projection can erase private source
names; it does not erase a difference between returning `0` and returning
`1`.

The existing repository does not require endpoint-only interpretation.
In particular, retaining HIR and the store can distinguish the following
sources. The proposition tests a possible shortcut for the missing bridge,
not an asserted denotation of current production code.

### Grounded witness

Consider two separately introduced ordinary Pure values:

```text
id x = x
zero x = 0
```

Fix a fiber assigning their parameter and result value ports `Int`, with
corresponding common pure-body effect-port assignments and the same actual
Value-entry mode. No polarized sentinel is identified with an effect row by
this statement. The two values then have the same interpreted four-port
shape for purposes of the endpoint-only hypothesis.

Supply the same independently certified challenge whose argument relation
returns exactly integer `1` without an event. Its source-core notation is
`result(1)`. The singleton argument relation is held fixed in this argument;
it is not merely the guarantee that an unspecified integer may return. A
current production application is not claimed: HIR does not yet lower those
call sites.

The exact Value-entry execution of `id` forces `1`, rebinds it, and its name
body returns that value. The execution of `zero` instead returns `0`.
Both use the existing receipt/entry/body/result-consumer schedule.

**Proposition E.** If an endpoint-only interpretation is source-adequate for
both definitions on this challenge, the observable bound of `id` admits a
return of `0`. It therefore does not factor through the exact identity body
recipe with that fixed argument relation.

**Proof.** Adequacy for `zero` puts its actual return of `0` in its bound.
Endpoint-only invariance identifies the observable bounds, so the same
return belongs to the bound of `id`. In the exact identity recipe, forcing
the supplied argument returns `1`, and lookup returns the same rebound
lexical value. That recipe cannot return `0`. QED.

Saturating literal nodes in the body does not repair this instance: the
identity body has no literal node. Widening the independently fixed argument
relation would remove the premise of this instance and is a different
abstraction. This observation localizes the issue to value dependence lost
by the proposed endpoint interpretation.

Proposition E does not refute `P_actual ⊆ P_checked`. A checked type bound
with the same result guarantee can also contain `0`. Nor does it refute
Theorem C: that theorem specifies its own graph-derived complete bound and
does not identify every port-only interpretation with the exact name graph.

## 3. What the current owners preserve

The evidence is already carried by existing owners:

- `crates/yu-solver/src/lib.rs`, `LambdaRecipe` records the optional body
  value component, the parameter position, body-effect component, and source
  occurrence.
- `admit_lambda_fact` uses the parameter in both value ports for an
  own-parameter body; otherwise it uses the separate body component for the
  result. Its generated Function has both effect children and provenance.
- `emit_integer` constrains an integer body through `Int` facts; those
  facts do not encode the numeral spelling.
- `crates/yu-hir/src/module.rs`, `ResolvedExpr::Integer`, retains that
  spelling, and `ResolvedExpr::Name` retains lexical resolution.
- `SolvedModule` retains HIR as well as the `ConstraintStore`.

Consequently this result does not justify a parallel carrier or extra
evidence machinery. The missing theorem must explain which retained facts
enter complete-bound denotation and where an abstraction drops a dependency.
The existing [effect-linkage audit](2026-10-04-production-hir-empty-record-shadow.md)
does not decide that denotation.

## 4. Finite abstraction at an owning atomic body

Here is a constructive response for a specified bounded interpretation.
It is a mathematical generator, not an approved successor implementation.

Take a Pure Value-entry lambda with an own-parameter or integer-literal body,
and fix parameter/result `Int`. Return values have no latent callable,
receipt, path, handler, or capture-bearing content. The ambient decorated
context is retained. An independently supplied argument relation can still
expose certified requests and finite response/resumption histories.

At body occurrence `j`, use a source-owned abstract result coordinate `v`
distinct from its lexical input/read coordinate `a`, and define

```text
Sat_j(a,v,C,C') := Int(a) and Int(v) and C'=C.
```

The read/root identity remains an operand and provenance fact. There is no
assertion that the output is the very same value root holding `a`. This
abstract relation forgets the numerical dependency locally. The exact
identity pairs `(a,a,C,C)` and exact literal pairs `(a,n,C,C)`, for the
body's integer literal `n`, map into it. It changes no configuration and
cannot produce an event or a capability.

For this paragraph, observations retain scalar values and visible events,
and forget equality of the concrete input and output value roots. If a
complete observation retains that equality, only the projected theorem below
applies; `Sat_j` must not be called a conservative extension of an unchanged
exact name-root equation. This qualification is essential when connecting to
Theorem C's old tuple.

Generate the complete abstract recipe by the existing operations:

```text
actual receiver and receipt;
Force(argument_relation) >>= (a,C).
    typed rebind;
    Sat_j(a,v,C,C');
    designated Value(Int) result consumer;
    return v from this invocation.
```

This graph has a fixed finite number of local nodes and a reference to the
supplied argument graph. `Int` membership is a symbolic relation; no integer
enumeration is used. There is no independent complete-call bound leaf.

Actual and checked generation copy this same locally abstracted graph,
including its full tuple, metadata, `Sat_j` leaf, and hidden-variable scope.
They add only the total fresh-coordinate definitions already specified by
the linked lift. The selected `d+` projection retains the original argument
contribution. The abstract scalar body creates no request, so it introduces
no body event into `b+`. This is a property of `Sat_j`, not of a sentinel's
name or a generic empty-support assumption.

## 5. Projected lift and independent admission

**Theorem L.** For the explicitly constructed abstract recipes of §4,
independent typed challenge certificates give

```text
D_checked(nu,K,D) subset D_actual(nu,K,D),

P_sat,actual(h;nu,K,D) subset P_sat,checked(h;nu,K,D)
    for each independently admitted checked challenge h.
```

The second line is about the first-order abstract observation contract just
specified. It includes all its permitted scalar slack and certified finite
resumption histories. It is not an identification of an F5 complete bound
with either side.

**Admission.** Before the pending Function query, the carrier/provider rules
certify that every permitted return tuple has result `Int`, and retain each
exposed request's original response port, witness, owner/path premises, and
raw continuation. All these operands stay in one `nu,K,D` fiber. Actual
Value entry receives and forces that carrier with the same premises; Pure
introduction adds no separate incoming support-row gate. Thus each checked
certificate supplies an actual inlet certificate. Neither certificate cites
the success of the Function query. The fixed `result(1)` challenge witnesses
nonempty admission independently.

**Full abstract-bound inversion.** An abstract-bound witness is, by the
generator, a witness of the displayed composition. Before a force return it
has the common receiver/receipt/entry prefix followed by the same argument
prefix or request. After a force return, it consists of
the original `(a,C)` tuple, a `Sat_j` witness, and the designated consumer
and return witnesses. Bind retains an exposed request and appends the same
suffix to its continuation; it does not replay receipt or freshen a request
witness. Induction on a finite legal response/resumption history gives the
same decomposition after every resumption.

Checked generation copies each of these whole witnesses. Its additional
coordinates are total functions of the old tuple, so they impose no new
condition on it. Joint existential hiding occurs after composition, keeping
shared witnesses together. Every abstract actual observation therefore has
the same checked observation and linked contribution projection. QED.

This now accounts for the abstract return of `0` by an identity given `1`:
it is a witness of `Sat_j`, rather than an unexplained extra complete-call
observation. The exact runtime identity continues to return `1`.

Divergent carriers remain admissible if independently well-typed; they need
not reach the scalar body. Empty event support is not used as a termination
claim. Arbitrary higher-order values cannot use this product saturation:
that would invent latent behavior or authority without a source certificate.

## 6. Consequence for the unrestricted bridge

The finite source-generation rule needed for this route is more precise:

> Specify the whole-tuple abstract relation of each value-producing source
> constructor before assembling the complete endpoint. A dependency erased
> by the endpoint abstraction must be erased at an owning constructor with
> a local well-formedness and capability certificate. Actual and checked
> generation use the same certified relation and tuple. Complete bounds
> are formed by their joint composition and scope-correct hiding; challenge
> admission is generated separately.

An exact source-indexed interpretation can instead retain the dependency.
Neither route is selected here as production policy. The obstruction shows
why a port-only interpretation cannot be silently equated with the exact
source recipe; the construction shows that local abstraction is sufficient
for the bounded scalar case.

The next theorem must connect the actual finite successor endpoint to its
chosen local relations, including latent values, higher-order inputs,
resumed witnesses and arbitrary target annotations. Current B step 6 and
the retained F5 evidence do not yet establish that connection. There is no
new source-program counterexample, no proof that State exclusion is enough,
and no unrestricted callback closure in this note.

## 7. Verification

The HIR and solver owners above were read at the stated base revision.
The work changes no production code, expectation, or authority. A separate
compiler_referee received the submitted artifact and governing source
locators without the producer's report or parent conversation history. It
independently checked Proposition E, the exact argument relation, Theorem L,
root projection, typed admission, same-fiber transport, and the cited
HIR/solver owners. It found no blocking or major defect. Two minor wording
findings were accepted and repaired: the literal example now quantifies over
the body's integer `n`, and the prefix proof explicitly includes the common
receiver/receipt/entry prefix. These change neither the theorem nor its
observation contract and closed by primary diff inspection.

The reviewer expressly did not certify a production complete-bound
denotation, the entire solver, the full callback theorem, or the structural
submission. The primary checked local Markdown targets and `git diff --check`.
No compiler test, build, benchmark, or Oracle execution was needed for this
proof-only slice. The sibling structural result and its separate executable
checks are recorded in
[the structural review record](2026-10-04-preclosed-structural-witness-review.md).
The task used M3 with two independent semantic reviewers across the two
proof domains; no extra review round or measurement campaign ran.
