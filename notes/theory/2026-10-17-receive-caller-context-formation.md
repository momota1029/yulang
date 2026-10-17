# Receive first-Call punctured context: construction boundary and candidate bridge

Date: 2026-10-17  
Status: Draft, conditional source analysis for independent review; no rule adoption or compiler authority.  
Sprint: `receive-caller-context-formation-20261017`, contract revision 1.  
Parent: type inference and executor with proofs remains OPEN.

## 1. Fixed claim and question

Keep the original selected fragment and its original shared indices:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

The reviewed two-Call derivation reaches a first unprovided source premise:
an independently satisfying punctured caller context for `c1` at the same
`A1,E1,xi=(nu,K,D)`, including hypothetical `g:Value(A1)` and its real `c2`
obligations. The direct source route has no supplied `T` containing this
context. The native route separately lacks one anchored full MODEL.

This note tests whether the selected constructors already produce the missing
context, then states the narrowest candidate bridge found. It does not claim
the candidate is proved or adopted.

## 2. What the selected rules provide

The selected Unit-arrow rule forms a complete challenge from an independently
typed compatible punctured context, other valid bindings, the actual
registered callable/carrier holes, the whole-carrier proof, and original
context/path/role formulas. It forms that challenge before provider
acceptance or execution. Its context formulas retain the hypothetical result
binder and pending `g()` suffix. Therefore it has no premise of actual `c1`
Return, actual `g` installation, or successful execution of the plugged
continuation.

The source challenge-ownership construction explains where the data come
from: source syntax/reference graph and a checking derivation. The graph
records the original first Call hole, `Bind` suffix, hypothetical
`g:Value(A1)`, `c2`, and the full shared tuple. Its context and checking
proofs are description-scoped logical fields. That record construction does
not prove that the independent context predicate `Phi_B^H` holds.

The first-Call forward theorem consequently treats the independently
satisfying punctured context as an input premise. Its Unit inlet construction
then assembles the challenge and only afterward eliminates the same supplied
`f` membership. The independently reviewed source input realization gives a
noncircular two-hole challenge constructor, but it likewise takes the
independent context witness as input. No selected rule among these sources
turns the syntax graph alone into an inhabitant of `Phi_B^H`.

## 3. Candidate ResultBind context rule

The missing bridge can be stated without assuming actual `c1` acceptance or
output. For an original result position `A1`, separate the open suffix from
the punctured context. Let `S_g` be the source expression `g(Unit)` checked
under the original hypothetical result binder, and let `K` be the source
context `let g = [hole] in S_g`, with its original scopes, provider
references, world/path data, effects, and request/response/future suffix.
The `g` in `S_g` is bound by the ResultBind continuation; an outer `g` is not
used to justify or replace that binder. A candidate rule is:

```text
CTX-RESULTBIND-PUNCTURE (candidate, not selected)

1. The source-owned ResultBind/Call constructor identifies this exact hole,
   result position A1, binder g, context K, and shared xi.
2. At the same original xi and scopes, an independently checked open-suffix
   derivation types S_g under the original hypothetical binder
   `g:Value(A1)`. For this fragment its c2 judgment is derived from the
   original A1 interface and Call/Name/Unit constructors; it cannot inspect
   a returned value z or a dynamic receipt from c1.
3. The source ResultBind/context plug constructor maps that staged suffix
   derivation, context K, and the original other-binding/world/profile
   witnesses into the independent punctured-context predicate, retaining
   its whole dependent telescope. The result binder is discharged only by
   the actual Return when K runs; it is hypothetical while the challenge is
   formed.
4. The original result, effect, path, role, scope, authority, response,
   Resume and FutureUse premises are proved at their original incidences on
   one tuple. No coordinate is reconstructed from endpoint equality.

----------------------------------------------------------------

Phi_B^H(K; A1,E1,xi) at c1, with the original g suffix and all c2
obligations retained.
```

The proposed rule is noncircular only if premise 2 is an open source typing
derivation of the *suffix* under the hypothetical binder and premise 3 is a
source ResultBind/context introduction law. It must not use c1's actual Function-membership elimination,
actual receipt/entry, successful first Return, `W_z`, or actual environment
extension. Those facts occur after the challenge and cannot justify its own
formation.

This is not yet a derivation of premise 3. Current selected artifacts provide
the context as an independently checked input and describe the syntax-to-
context ownership, but no frozen theorem was found in the pinned scope that
maps an arbitrary open continuation derivation to the full `Phi_B^H` witness
with all original world/authority/provider/future fields. So the result is a
precise conditional bridge candidate, not a claim that `T` now exists.

## 4. Required preservation law and falsifiers

Any accepted form of `CTX-RESULTBIND-PUNCTURE` must preserve:

- the original `A1,E1,xi`, source occurrence, scopes and source instance;
- the direct callable and whole-carrier holes and their registered
  incidences;
- the entire independent compatible context domain, not a successful-call
  subset or a finite list of clients;
- the hypothetical `g:Value(A1)` binder, `c2` and its dependent suffix;
- original effect/context/path/role constraints and same-tuple dependencies;
- current world, other values, profiles, authority and raw continuation
  obligations;
- staging: no `g` value, receipt, execution result, or first-call safety
  premise before actual Return.

It is falsified if the derivation uses `c1` admission to validate `Phi_B^H`,
uses actual `W_z` to type the hypothetical binder, changes xi or world between
the `c1` and `c2` clauses, drops pending/future obligations, derives
`Phi_B^H` from generated syntax without checking its independent guards, or
narrows the domain to contexts that make the invocation succeed.

## 5. Direct-source and native limits

If the source owner supplies the open-continuation-to-context theorem and its
premises, the direct source route can apply it at this `c1` without depending
on actual `c1` completion. The selected Application checked-result
constructor then retains both tagged Return inputs and the actual `b_g`
rebind. This still needs every other source premise, including the actual
second-Call input obligations, and does not close the original theorem.

The native route additionally requires one fixed anchored full MODEL over the
original `alpha,A1,E1,xi` and all incident constraints. The context bridge
does not produce that model, imply solver success establishes it, or repair
native/source correspondence. F5, Catch, NPAIR, subtraction, principality,
soundness and production gates remain separate and OPEN.

## 6. Exact next evidence

The source context/Bind owner must supply either:

1. the frozen original rule and a reviewed derivation of premise 3 for this
   exact open `g(Unit)` continuation, including every independent guard; or
2. a counterexample/owner explanation showing that the context predicate is
   not generated from this source continuation and must remain an external
   premise for this fragment.

Until then, `T` remains OPEN. The candidate rule is submitted for
independent review under this sprint; no semantic adoption, code edit, test,
build, probe, source admission, or production change follows from this note.
