# JOF output-owner rule for ordinary Applications — R44 draft

Status: **Draft; selected recommendation, not yet Authoritative.**
Sprint: `call-output-owner-jof-20261019-r44`, revision 1
Parent: unchanged full inference/evaluator theorem and Simple-sub A/B, **OPEN,
0 → 0**.
User delegation: 2026-10-19, “そういう判断はおすすめを自動的に選んでもらっていいですよ．駄目だったら変えればいいので”.
Selection by Luna: advance JOF as the best concrete design candidate; do not
claim the user approved this exact signature or that old/new preservation is
proved.
Direct evidence: R41 proposal `faf3c347909a59acafabf78d77f0597a5b48c033ec3fb5ce957681000ff675da`,
R42 dependency-order decision `fd51992ded8fd106d2c7ff5790c33864efbbffd4a655b9c0c2c0ae384e60d83c`,
R43 bounded source audit `50c8499da6b441980953868e007fc8f22446a8cea19d1015d7ad8affedeb5c61`.

## 1. Recommendation and exact scope

I recommend advancing **Joint Output Formation (JOF)** as the candidate
completion rule for the original ordinary Application/Call output owner. Its
target instance is `q = Application(Name(loop), Name(y))`, the body of the
local recursive helper in:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

The candidate makes the output description an owned, typed source parameter
before any Call header whose type refers to that output is formed. It uses the
whole already formed source context as its ordered dependency telescope. This
is one general source-formation rule for the ordinary Application owner family;
`loop` and `y` are not semantic names, and q is not a special compiler branch.
Any existing narrower authoritative Application case remains governed by its
own owner and must not receive a duplicate JOF output owner. R43 established
only that the selected bounded Name/Int and literal-child cases do not
authenticate q's old Name/Name/Keep output owner; it did not establish a
repository-wide absence theorem.

JOF is selected because it gives a concrete acyclic formation order that can
be checked against the actual Complete Call and Generalize consumers. Waiting
for an unavailable source-owner record makes no progress; claiming that JOF
preserves old accepted programs is also unsupported. This draft chooses the
design-and-proof route while keeping adoption and production cutover behind
independent review and explicit evidence.

## 2. Candidate formation rule

Let `Γ_q` be the actual ordered typed source context after independently
forming the callee and whole-argument child schemas for an ordinary
Application. The context carries each entry's original owner, class, source
sort, scope and predecessor dependencies. It is not inferred from the native
solver level, a lexical-name scan or a solved row.

The proposed order is:

```text
Γ_q ⊢ f : F_q       Γ_q ⊢ a : T_q
------------------------------------------------ operands
Γ_q ⊢ q = Application(f,a) : operand schemas

ρ_A := (C_q, q, output-value-description)
Desc(C_q, ρ_A, ValueDescription, σ_q, Δ_A)
Δ_A := Γ_q                          (identity typed inclusion, in source order)

Γ_q ; A_q:ValueDescription
  ⊢ E_q : original-Application-effect-at-q
  ⊢ each complete original Call header, clause and reference at q
      under its actual ordered dependent telescope
      with output-value coordinate A_q
------------------------------------------------ JOF candidate
Q_q : original complete Call relation
Comp(E_q, A_q) : synthesized computation interface
Code(q) = reify(call(Code(f), Code(a)))
```

`A_q` is one fresh flexible ordinary `Desc`, not a provider, a receiver result,
a runtime value, a `Shared` field, an event witness or a solved output. It is
introduced after both operand schemas and before every q-local output-indexed
header. `E_q` remains the Application's original effect coordinate, formed by
its actual effect owner and kept distinct from the callee effect, receiver
invocation effect, whole-argument effect, provider and returned world. This
candidate does not choose an effect rule or identify any of those fields with
`E_q`.

The schema above is deliberately a rule shape, not yet an instantiated q
derivation. The exact `σ_q`, the actual `Γ_q` entries and their types, effect
formation, header substitutions and every `Q_q` arm must be supplied without
using `Q_q` as a premise. A schematic `OriginalCallHeader` name or an already
formed `Q_q` is insufficient.

## 3. Complete Call obligations

Every original structural and alternative clause remains in `Q_q`: callee
then receiver Bind; whole argument; callee and receiver pending continuations
with their original raw continuation and resumed world; the once-only receipt;
the actual receiver role and designated consumer; the complete result and
provider-indexed future; all original W, Z, receiver-local, callee-local and
nested arms. Every arm retains its actual binder order, type, source owner,
guard, license, provider/admission law, future and substitution. Opaque
predicates may stay opaque; their typed interfaces and references may not be
omitted. No structural return is treated as a complete Call by itself.

Synthesis A remains unchanged: the Application synthesizes
`Computation(E_q,A_q)` and `reify(call(f,a))`. The closure body's Result, the
helper's invocation result, the loop's final `helper x` endpoint, the Call
result, and the actual returned provider/world stay distinct. JOF creates no
new execution step, implicit Force, cast, eager constraint solution or
successful-query premise.

## 4. Candidate Generalize interpretation

Because `Δ_A := Γ_q`, the declaration is available only under the typed map
that retains the entire original ordered context. Generalize may not treat
this as a minimal free-variable set, erase unused entries, reorder dependent
entries, or reconstruct the telescope from native levels. Its existing L1–L5
classification and both-frame behavior remain controlling.

The rule's design obligation is to determine how every actual entry in
`Γ_q` behaves when the Application occurs under each of the two independent
description frames and their aliases. In particular, a challenge or event
entry already in `Γ_q` can affect the proposed output strategy; a provider or
future introduced later cannot. The candidate does not assert that those
additional dependencies are harmless, principal, or equivalent to the old
source. The exact Generalize actions and copy maps must be constructed from
their owning rules before the candidate can become Authoritative.

## 5. Proof and implementation boundary

R43 establishes that the approved bounded `Application_N` definition and
`Original-ResultLiteral` case do not instantiate q. The original Code-Call
input consumes `Comp(E_q,A_q),o_q`; it does not introduce an authentic q output
declaration. Typed-core synthesis constructs the symbolic Application
computation but does not give the missing old Name/Name output owner. The
candidate therefore adds a semantic source rule; it is not a derivation from
those premises.

R42 proves that moving an output choice across an inherited challenge or
later provider can change the legal strategy set even when pointwise endpoint
tuples coincide. The actual q fibers and source behaviors have not been
compared. No conservation, equivalence, soundness, principality, termination,
F1/FK1, CopyScope, N-Transport, source/native commutation or production result
is claimed. The original parent remains **OPEN, 0 → 0**.

Implementation stays **NO_SAFE_CODE_SLICE** while Rust paths have unknown
owners and the rule is not Authoritative. The R41 native map and R42
implementation gate are planning evidence only. After the candidate is
reviewed and adjudicated, any implementation must retain one typed
output-owner certificate through source emission, native demand, typed Result,
actual copies and Generalize. The implementation must fail closed on a wrong
occurrence, class, scope, dependency, effect or provider.

## 6. Rejection conditions and review request

Reject or revise this recommendation if: any required output/header type uses
a later binder; the Application effect is circular or cannot form at the
chosen scope; a full original Call arm cannot be expressed; an existing
authoritative Application case conflicts; the full-context dependency changes
ordinary Generalize eligibility or natural inference without a principled
account; or a native consumer requires reconstructing provenance.

The independent compiler review must produce either a concrete q-indexed
formation certificate and ordered Generalize/copy map, or the exact failed
premise and a coherent revision. The spec review must verify the candidate's
scope, the user's delegation, and the preserved parent and source domains.
Only Luna adjudicates after both frozen reviews. Even a clean result approves
this proposed rule's design scope only; the original theorem and every
proof/implementation gate listed above stay open.
