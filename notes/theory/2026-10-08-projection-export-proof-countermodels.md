# Two concrete failures in the first projection-export proof

Date: 2026-10-08
Baseline: `30842d31f1b40e39b8a5b9fb271adcf99934a048`
Status: independently reviewed finite semantic countermodels
Scope: native ordinary VP production and source evidence preservation
Production change: none

## 1. Result and exact target

Independent mathematical and specification pre-reviews of the first export
draft found two invalid steps. This note gives their small semantic witnesses
and the exact corrections. They falsify those steps, not the possibility of
a finite transformed public export. In particular they do not show that
`my id x=x` has a bad execution or should be rejected.

The governing meanings are the selected
[source checking and Generalize](2026-10-08-source-generalize-definition-and-proof.md)
§§3.2–3.4 and GC, the
[complete Function law](../design/2026-10-08-contextual-function-membership-definition.md),
and the independently reviewed
[ordinary VP constructor](2026-10-08-id-public-phase-constructor.md) §§3–4.
VP production includes independent carrier observations without requiring an
execution witness for every production member. Source evidence strategies
retain their original scopes and are not identified by proof irrelevance.

## 2. A changed input contract cannot be checked from actual payload typing

### 2.1 The finite witness

Use one ground immutable carrier t, one world and the same static port,
receipt, formal and result incidences throughout. Its actual designated
execution returns `0:Int`. There are no operations, requests, raw handles,
captures, State transitions or latent providers in this witness.

Define two independent whole-carrier contracts with identical inert-formation,
world and current-authority clauses. Include all restrictions and zero-step
and administrative prefixes of the following Returns:

| Contract | Payload type | Complete Return alternatives at t |
| --- | --- | --- |
| I_n | Int | `Return(0)` |
| I_w | Any | `Return(0)` and `Return(true:Bool)` |

Both contracts have empty operation effect. Their completed Returns retain
the same world and original result/provider incidence, and have the displayed
ground hereditary certificates. The Bool alternative is a complete independent
abstraction license. It is well typed at Any and has no source-execution
witness requirement.

The carrier has both `Car(I_n,t)` and `Car(I_w,t)`: its actual Force prefixes
and Return belong to both complete contracts. More generally, with the same
inert guards, a certificate at I_n embeds in I_w by injecting each universal
execution observation into the larger complete relation. This proves the
needed admission map; it is not an appeal to successful Direct.

Compare these actual ordinary roots:

```text
u = VP-Echo(I_w, Any, IF)
V = VP-Echo(I_n, Int, IF)
```

The same independently admitted V challenge can be used at u through that
carrier-certificate injection. A domain restriction H, if present, can be
the true ground predicate at this same input. Thus the domain inclusion
premise is satisfied in this example.

### 2.2 The failing complete observation

On that checked challenge the source root u has the following valid
production derivation:

```text
VP-Start; VP-Receipt
VP-Force using I_w's licensed Return(true)
VP-Entry binding true with its hereditary Any certificate
VP-BodyReturn returning that same true
VP-InvocationReturn
```

Every Echo equality holds. All IF guards and current-world incidences hold.
Nevertheless V rejects the same entry/result tuple: `true` is not an Int
and I_n has no such complete Return alternative. Therefore

```text
D_V ⊆ D_u
but Complete_u restricted to D_V ⊄ Complete_V.
```

The draft checker incorrectly used the target argument type as the source
result-proof input whenever the source carried Echo:

```text
source is Echo  =>  result_input := target.argument
```

Its accepted example then used `Int <= Any` for admission and `Int <= Int`
for result checking. The actual carrier indeed returns an Int. The extra
production observation above does not. Echo identifies the result with the
entry payload of **that production observation**, not with a separately
selected actual execution's payload.

### 2.3 Exact correction and a still-valid nonidentity use

A proof that changes I must separately establish inclusion of the complete
source entry-observation relation on the checked domain. Scalar argument
inclusion and uniform actual carrier acceptance do not supply this proof.

There is a direct safe fragment with the **same whole I and IF**: restrict
admission by an independently typed H while leaving the complete observation
contract unchanged. Its domain proof is conjunction elimination and its
observation proof is identity under H.

There is also a direct nonidentity result use at the same I_n:

```text
VP-Echo(I_n,Int,IF) <= VP(I_n,Int,Any,IF).
```

On every source production member, I_n's complete entry Return certificate
types the entry payload at Int. Echo types the same outward value at Int;
the ordinary hereditary Top rule transports that value to Any. Before Return
the matching phase and pending rules are identical. No extra source entry
alternative was removed. This proof uses the production certificate in the
tuple being checked, rather than the outcome of another execution.

## 3. One total proof constructor does not eliminate a proof-choice fiber

The first draft wrote, for example,

```text
name_evidence := Restrict(formal_evidence)
```

and treated this construction as a defining equation for every lawful
source evidence assignment. Constructor soundness supplies a valid output.
It does not by itself supply uniqueness of the source witness relation.

The smallest discriminator has one fixed input evidence c and two possible
source evidence witnesses n0 and n1 at the same original EventProof scope:

```text
NameEvidence(c,n0)
NameEvidence(c,n1)
n0 != n1
```

They certify exactly the same value/provider, world and hereditary membership.
Take a total sound restriction constructor choosing n0, and the original
well-scoped client predicate `W := (name_evidence = n1)`. The source fiber is
nonempty using n1. Replacing the binder by that constructor changes W to
`n0 = n1`, so its public fiber is empty. No type variable, operational event
or authority field has changed.

This is a concrete two-element evidence model of the draft's stated
constructor premises. It disproves the implication from those premises to
exact evidence elimination. It does not assert that a particular already
fixed Name clause has a two-element fiber. Its actual clause must be inspected;
some literal projection outputs may indeed be definitional aliases.

The source grammar also explicitly permits different finite logical proofs
with the same endpoints: identity and composition of identities are permitted
by source checking §3.2(1). Such independent Check/ViewLogic/EventProof choices
cannot be deleted merely because both prove the same membership. No quotient
identifying all such proofs was selected by SRC-J or GC.

### 3.1 Exact correction

For each removed coordinate, exhibit the actual source clause forcing its
value and substitute into every dependent consumer at the original telescope.
Same-value/provider aliases from Name and Return are examples of this case.

For any source-owned or client-owned independent logical witness, keep its
binder, all alternatives, dependencies and original local relation. The
public constructor may normalize that relation into independent ordinary
certificate rules, but cannot replace it by one chosen successful proof.
A source relation hidden in an opaque residual is not such a normalization.

This correction is stronger than saying that G can manufacture a source
introduction proof. Exact source-lawful completeness with arbitrary W needs
the original witness choices, not only existence of one valid introduction.

## 4. What these countermodels close

The first countermodel closes the question whether target actual payload
typing alone justifies the changed-I Echo comparison: it does not, even for
one pure ground carrier. The second closes the question whether a total
canonical constructor alone justifies erasing an unconstrained proof-choice
coordinate: it does not, even for a two-element fiber.

Neither result is an OPEN-obligation inventory or a renamed export-adequacy
premise. Each identifies a failing inference and a finite tuple rejected by
its claimed conclusion. The safe unchanged-I result weakening and admission
restriction have direct case proofs above. Uniform source inlet construction,
the exact evidence normalization and complete public export remain separate
proofs; these countermodels are constraints on those constructions.

## 5. Review packet

Producer: primary integrator, using separately submitted mathematical and
specification pre-review findings. The mathematical pre-review supplied the
complete-contract witness; both reviews independently identified the proof
fiber error. A fresh independent specification review of this exact integrated
note also checked both mathematical countermodels and the safe fragments.
It passed with no blocking, major or minor finding. The primary accepted the
verdict at exactly the stated scope. The
[integration record](../progress/2026-10-08-projection-public-export-review.md)
retains the review boundaries.

No production solver, source rejection policy, Authority aggregate or
approved-answer file is changed. The provisional checker and export draft
must not be cited as proving the rejected steps.
