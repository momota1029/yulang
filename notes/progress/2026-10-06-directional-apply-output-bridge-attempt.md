# Ordinary Apply: bridge to a directional output-effect occurrence

Date: 2026-10-06
Baseline: `b26087ce26bc2e77f41709a1e7b58bc4c73c2db6`
Status: frozen conditional research result; compiler-referee reviewed with no findings
Method: one bounded constructive source-section derivation
Claim class: conditional local static bridge using an already reviewed Call constructor
Semantic/implementation authority: none
Exclusive lease: this note only

## Objective and exact result

For the selected component

```text
my apply f = { my step x = f x; step }
```

the reviewed source-call construction generates an unsolved upper Function
demand on the same original `f` endpoint, its immediate complete-invocation
output-effect address, and their common original formal/contract root and
scope. These records instantiate the directional rule **given the selected
protected-variable witness at this exposure**. Neither satisfying the demand
nor a solved Function shape is a premise of their generation.

This proves a local static bridge. It identifies the original profile's
**root**, not a completed original profile or an event's membership in that
profile. The latter inversion stops at source-call construction §7 P and the
directional addendum §2's contribution/typed-incidence/receipt/live-receiver
obligations. No source-valid counterexample, source-wide completeness,
soundness, principality, source acceptance or production result is claimed.

## Governing dependencies and hypotheses

The exact governing sections are:

- [Directional user decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§1–6: protected-variable to original upper output occurrence; no reverse
  protection of an existing lower provider; separate event interpretation.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5, especially §§2–4: shared original root, annotation absence, one joint
  `xi=(nu,K,D)`, Q independence and retained actual provider role/entry.
- [Nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: resolved outer `f`, inner `x`, capture and return of `step`.
- [Typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3, 6, 7, 9: Value parameter/Name/Result construction, same-value checking,
  complete invocation and its output direction.
- [Reviewed Call construction](2026-10-06-source-call-generation-construction.md)
  §§3–5, §7 P and its [review](2026-10-06-source-call-generation-review.md),
  “Compiler-referee assessment”, “Exact-conformance assessment” and
  “Primary adjudication and closed scope”. These establish the bounded
  static schema and supplied-decorated constraint envelope, not complete P/A.
- [Current directional derivation](2026-10-06-directional-protection-source-generation.md)
  §§2–3: retained seed-at-exposure premise and scope-indexed local producer.
  Its finite checker is not used as evidence for source generation here.

Explicit hypotheses:

1. Work on this exact resolved ordinary component, with `u_f -> d_f`,
   `u_x -> d_x`, `c=Apply(u_f,u_x)` and the selected nested source skeleton.
   Current production parsing/typechecking of those bytes is not assumed.
2. Use the ordinary representation-preserving generation envelope of the
   reviewed Call constructor, with `Gamma(d_f)=Value(A_f)` and
   `Gamma(d_x)=Value(A_x)` after their Value entries. General conversion
   completeness and arbitrary source annotation resolution are not assumed.
3. The actual unannotated formal supplies `k` protecting `v=A_f` while it
   remains inferred, at this original exposure. This is the directly selected
   local seed treatment, not a seed inferred from Name annotation absence,
   later solution, arbitrary SCC ordering or late-seed replay.
4. All generated dependent records retain the same original scope `sigma`
   and parameterized whole `xi=(nu,K,D)`. A well-formed realization of `F_c`
   gives the generated addresses their observation-port sort; existence of
   such a satisfying realization is not a generation premise or conclusion.

There is no candidate new language assumption. The result is conditional on
these existing selected/reviewed premises; their extension beyond this
component remains unverified.

## Derivation for the one resolved Apply

**Names and capture.** Nested-block §2 fixes `d_f` as the outer formal.
Typed-core §6 generates Value bindings and Name/Return images. Thus the
callee image `J_f` reads the same endpoint `v=A_f`; the actual argument image
`J_x` returns the already rebound `A_x`. The call retains `J_x`, not just its
printed `Comp(empty,A_x)`. Source-call §§3, 4.4 retain the capture identity and
original-scope correspondence. No fresh independent provider is substituted
for the captured endpoint.

**Upper orientation before solving.** Source-call §4.2 introduces one
dependent complete Function variable `F_c` at `R_f`. Section 5 emits

```text
exists_sigma(F_c,e).
  WF_Dec(F_c;xi)
  & VIncl(A_f,F_c;xi,e_value)
  & WholeArgCompatible(J_x,CarrierContract(F_c);xi,e_arg)
  & CIncl(ExecuteCallableImage(J_f,Delay(J_x),F_c,e;xi),
          Comp(E_c,A_c);xi,e_result)
  & TypedCallCert_Dec(c,F_c,e;xi)
  & canonical Gen-Call-0 records and Role_0
```

The displayed `VIncl` is the generated same-value constraint with `A_f` on
the left and the demanded complete Function view on the right. Let `u_c`
name this original checking occurrence and let `U_c=F_c`. In this local
bridge, `SourceUpperUse(u_c,v,U_c,sigma)` abbreviates that emitted constraint
occurrence **together with its Gen-Call-0 source certificate**. It does not
abbreviate the proposition that `VIncl` is true. The full conjunction can be
empty. Its supplied decorated certificate does not supply raw-source P/A.

This naming introduces no new Call rule: the emitting rule and its semantic
orientation are exactly source-call §§4.2, 5 and typed-core §§6–7. Discarding
the source occurrence and reconstructing it from successful checking would
invalidate the bridge.

**Exact typed output occurrence.** The same Gen-Call-0 constructor emits

```text
beta = (original d_f, R_f)
p_0 = (beta, call.effect)
p_out(c) = complete-invocation effect address of c
ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c))
```

Its interpretation identifies the signature's immediate complete invocation
effect position before the result's latent structure is known. Define
`outEff(U_c)` to be this occurrence of `U_c` at `p_0`; the effect field there
is the symbolic `'c` in the user's upper-view notation. The port is supplied
by the Function-elimination constructor, not by inspecting the solved value
of `A_f` or `A_c`. Under a well-formed realization it has the required sort.
Typed-core §9 derives the complete invocation/result port's output direction
from invocation; its argument-carrier port has the reversed direction.

Consequently this is the covariant output occurrence required by the local
directional rule. It is neither the input effect nor a latent descendant of
the returned value. It is also not merely a closure-body row: complete
invocation includes actual entry and designated result consumers. The source
address correspondence does not assert equality of independently represented
outward rows, runtime `Flow`, actual receipt or event contribution.

**One original dependency family.** `R_f`, `F_c`, `beta`, `p_0`, `u_c` and
`ElimOrigin` are generated from the same `c,d_f,A_f,sigma`. The variable-stage
seed names that `v` and original formal. The textual scope of the inner Name
does not replace the original scope: the selected capture and §4.4's dependent
identity-address schema retain its witness. Each record is dependent on the
same `F_c` and whole `xi`; no port chooses a separate `nu`, `K`, `D`, provider
or continuation. Generalizing `step` does not quantify captured `A_f` into an
independent provider. This is the reviewed static scope-preservation result,
not a full generalization theorem.

**Apply the selected rule.** With hypothesis 3 and the generated records:

```text
ProtectedVarAt(k,v,sigma,u_c)
SourceUpperUse(u_c,v,U_c,sigma)
outEff(U_c) is its generated complete-invocation output occurrence p_0
---------------------------------------------------------------- Dir-Protect
NewProtection(k,beta,u_c,sigma,p_0)
```

This is the requested bounded witness. An existing `L <: v` has the opposite
orientation and does not discharge `SourceUpperUse`. Preserve its provider
effect and all independently inherited evidence even if its denotation equals
the upper effect. No lower-bound satisfaction or direction-erasing equality
is used in this derivation.

## Exact inversion stop and failure conditions

The static bridge succeeds through `NewProtection`. Trying to conclude
`Gamma_original(beta;xi)`, exact `Slots_original(beta;xi)`, a contribution
classification or protection of a concrete provider event then stops.
Source-call §7 P still asks for the original contribution/path interpretation
and seed-to-refined receiving-view normalization at this generated root.
Actual packets, receipts, live receivers and pre-dispatch observations require
their independently typed source evidence. A lexical capture or the static
`ElimOrigin` schema cannot supply them. Full independent admission is also not
derived by this attempt.

The local result fails if the use lacks its original upper-constraint
certificate, if a known external Name is substituted for the unannotated
formal seed, if the seed-at-exposure/original-scope witness is absent, or if
upper and lower occurrences are collapsed by endpoint equality. An admitted
executable conversion outside the same-value fragment needs its separate
source rule. An unsatisfiable `G_call` leaves generated static records but
gives no executable well-typed instance. Applying the record to every event
from a lower provider would cross the remaining P/receipt/observation cut.

## Checks, coverage and frozen handoff

Pinned reads used `git show b26087ce26bc2e77f41709a1e7b58bc4c73c2db6:<path>`;
the selected sections were inspected constructively. Dependency stability
was checked by `git diff b26087ce26bc2e77f41709a1e7b58bc4c73c2db6 --` followed
by the seven dependency paths below; it returned no changes. SHA-256 values
were obtained with `sha256sum` on those same paths. The note's narrow link and
whitespace checks are reported in the producer handoff.

| Dependency | SHA-256 at this submission |
| --- | --- |
| directional addendum | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| nested-block addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| typed computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| source-call construction | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| source-call review | `237b99131476e9f7876c3b3d52d05cae3613483d0b46e9be51dd3a2c54616417` |
| directional source derivation | `3702eb2ea5108eba1adc8ab7a557542abb9993cee09f70b738e2999a05a2d185` |

No Oracle evidence or run, executable reference/checker, solver result,
enumeration, mutations, random seed, range search, compiler test/build or
performance experiment is involved. This argument shares the stated source
and reviewed decorated-constructor premises; it is not independent review of
those premises or of this producer's note. Coverage is one source-section
derivation for one selected ordinary Apply. CPU/RAM and total wall time were
not measured; no compute search or heavyweight process ran. Initial policy
loading launched three lightweight `cat` reads together, exceeding the assigned
single-process budget for that read; subsequent commands ran sequentially.
Inspection output
was bounded; broad document captures were truncated, and exact relevant
sections were reread. Other core/source cases were not exhaustively searched.

Recommended next action: construct the event-to-upper-occurrence contribution
clause at the generated root with actual typed receipt and live observation.
Do not re-solve the already selected directional meaning.

## Independent review

A compiler referee reviewed the complete note against the directional,
call-view, nested-block, source-call and typed-core sources. No blocking, major
or minor findings were reported. The review confirms this conditional bridge
from the emitted `VIncl` occurrence and exact complete-invocation output port
to `NewProtection` under the seed-at-exposure premise, and confirms the stop
before original profile completion, event contribution, typed receipt/live
receiver and independent admission. Source-wide exposure, conversions,
arbitrary generalization and production behavior were not reviewed or closed.

Commit packet: only
`notes/progress/2026-10-06-directional-apply-output-bridge-attempt.md`;
baseline `b26087ce26bc2e77f41709a1e7b58bc4c73c2db6`; changed dependency hashes:
none; review status: unreviewed, frozen research submission; checks: pinned
section inspection, dependency diff/hash checks and note-only link/whitespace
inspection; proposed message: `research: derive the ordinary Apply directional output bridge`.
Shared-record deltas left for the primary/curator: record only the conditional
static bridge and retain full original-profile/contribution/receipt/admission
gates. No shared task/index/theory or question-board file was changed.
