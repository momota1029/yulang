# Literal L1 source rule adoption

Status: Authoritative  
Scope: Original Yulang literal introduction for all raw source payload constructors, including its intrinsic value/type, pure Return, and contextual-effect boundary. This does not define Simple-sub generation, satisfaction, solver readout, or Rust behavior.  
Approved-by: user  
Approved-at: 2026-11-02  
Drafted-by: Luna primary  
Reviewed-by: `/root/literal_l1_adoption_review` (`spec_auditor`), exact-text PASS  
Supersedes: the unadopted disposition of the R206 literal-introduction candidate, only for the source-rule decisions stated here; R207's original-coordinate correction remains in force.

## Adopted introduction

For every original raw literal `l`, let `p(l)` preserve its complete payload,
`τ(l) := PaperTypes.literalType(p(l))`, and
`v(l) := PaperTypes.Value.literal(p(l))`. The constructor map is:

| Raw constructor | Base type |
| --- | --- |
| unit | Unit |
| bool | Bool |
| int | Int |
| floatBits | Float |
| string | String |
| bytes | Bytes |
| path | Path |
| character | Char |

The literal introduction has descriptor `Value(τ(l))` and value `v(l)`.
At the original occurrence `q`, root coordinate `r`, ambient event `e₀`,
scope `ξ`, and shared witness `ω`, its local row and Return are:

```text
LitRow(q,l,r,e₀) =
  ⟨ descriptor = Value(τ(l)), value = v(l), root = r, event = e₀ ⟩

Return(LitRow(q,l,r,e₀)) =
  ⟨ Comp(empty, τ(l)), v(l), r, e₀ ⟩
```

The intrinsic performed-effect row is empty. The rule does not create a new
root, event, scope, occurrence, or witness. Contextual permission, actual
inflow, residual effects, Call effects, guards, and future obligations remain
in the enclosing source judgment.

This is a sufficient base introduction, not an exhaustive characterization of
literal checking. Preserve every independently admitted structural,
annotation, method, and adapter alternative with its original premises, guard,
effects, and boundaries. A selected conversion retains distinct source and
target rows and its own event/effect transition, linked to the same literal
occurrence and outer shared witness. This adoption does not assert that an
unregistered overload exists or does not exist, and it does not add a policy
that excludes one.

## Proof and implementation boundary

The approval fixes the original L1 source introduction and pure Return law.
It does not supply a Simple-sub atom or actual generator clause, define
independent satisfaction, prove a solution readout, establish `sameScoped`,
instantiate the full source model, or close any parent theorem. Those remain
separate proof obligations. Any such construction must use the same original
payload, `(q,r,e₀,ξ,ω)`, and preserve the complete enclosing effect and checking
obligations. No Rust implementation or production promotion follows from this
document alone.

## Provenance

User approval was given in the 2026-11-02 conversation in response to the
R206 proposal. R206's independent review was PASS for its concrete payload,
value/type, and effect candidate. This addendum incorporates R207's later
correction to use the original `r` coordinate and preserves all original
checking alternatives. The independent review returned PASS on SHA-256
`05f1d1fb8ea9c54b523ab7909005f909d8cb6ddbf73a3f42a6d501a1c238de35` before
this review-receipt line was recorded. The reviewed text is ready to use as a
proof-construction input; the receipt does not reopen the user's decision.
