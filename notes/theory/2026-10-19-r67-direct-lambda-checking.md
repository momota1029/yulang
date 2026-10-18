# R67: direct Lambda checking at the original whole annotation

Status: candidate partial source-rule derivation and exact first unsupported
premise. Sole author `/root/r67_direct_lambda_proof`, no descendants. This is
neither a complete operand derivation, a reviewed theorem, source/native
correspondence, a semantic amendment, nor production authority.
Sprint `direct-lambda-checking-20261019-r67`, revision 1, contract SHA-256
`6e5a248634eab018f4020a416ca5fac1124452ecc7cb3ad789ffa6c440be349c`.
Luna-supplied baseline `3b974b9337d8490e1af2ebaa5f1b54ece2e62cd5`
and activation `2a02086f5db35c1903762327e75e85b2d59de30c`.

## Original claim and this route

The parent is computation-forwarding preservation §§1,6–7 on its unchanged
source domain: one shared `xi=(nu,K,D)`, open incoming computation effect,
every finite prefix, arbitrarily repeated and simultaneously live receiving
entries, and separate receiver and foreign-continuation obligations. Its
native §6 original-template implication remains conditional on authentic
per-instance mapped-bound admission; it does not imply a source operand.
F1/FK1 and other independent quantifiers are not discharged here. Simple-sub
A/B remain OPEN 0→0 and R50 is NOT ADOPTED.

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Fix original resolved family `I`, definition `d`, retained Lambda `L`, formal
`t`, body Name `n`, formal annotation `a_t` and whole-binding annotation `a`.
Their row occurrences are respectively `p_t` and distinct `p_A,p_R`; `E_t`
is the open incoming computation effect. Keep one original component context
`C` with provider, original captures, source choices, ordinary constraints,
body/result evidence, scopes, and a single shared `xi` strategy. The symbolic
source interface and prior evidence must be constructed in `C` before
whole-annotation Function checking uses them; completed does not mean solved.

This packet tries the direct source Lambda/Parameter/Name/Result/checking route.
It does not use the Result-A equation for an unannotated Lambda result and
does not assume R66's already-complete `D_L` premise.

## Constructible prefix and conditional body lemma

1. HIR `local_source.rs:598–630,714–720,1016–1037` retains `L`, its original
   parameter binding and direct `Resolve(n)=Parameter(t)`, while storing `a`
   separately. `source_annotation.rs:450–500` retains separate written Function
   argument/result syntax. These are occurrence/owner facts, not typed
   Function formation. Reuse reviewed R64 D0–D2 at exactly that scope.
2. The selected Parameter rule and reviewed formal construction give the
   Computation role and `Gamma(t)=Computation(E_t,Int)`. RootPermit at
   `a_t/p_t` supplies local permission for `I`, without `E_t <= {I}`, Force,
   inflow, handling, or a grant at `a/p_A`. NamePermit follows the actual
   `n -> t` binding and preserves the same computation carrier/provider and
   that formal-local permission.
3. The selected source-result Name rule therefore yields
   `Synth(n)=Computation(E_t,Int)` with no extra pure result layer. This is a
   source description of the body Name, not a completed Lambda interface.
   No witness or endpoint is selected after solving.

There is a useful *conditional* body step. At a genuine body checking
occurrence, if its owner supplies (i) a same-computation target equal to this
complete Name interface at the original body scope and (ii) the actual
designated consumer for this computation, source Generalize §3.2(3)'s
same-computation rule can check the same value/provider, and §3.1's Result
rule can consume it through that consumer. The whole joint tuple and ordinary
constraints remain attached. This does not choose that target or consumer.
In particular `p_R` cannot be inserted as the body's prior target merely
because its written syntax matches an effect family.

Applying the conditional step to the parent identifies the exact owner that
must turn `Name(t)` into the Lambda body's checked observation. It does not
establish a fixed-source legal Lambda, F1/FK1, a foreign continuation or a
native mapped-bound route.

## First unsupported direct rule premise

Source Generalize §3.1 requires, for Lambda, the actual role and entry,
captures, **body checking under the actual formal**, body consumer and
complete invocation. It explicitly requires the body proof for an
*independently admitted challenge*; the challenge cannot be formed by
assuming body safety or callee acceptance. Section 3.2(4) checks an already
formed callable using proved domain and observation inclusions; §3.2(6)
checks an already completed operand against the annotation target. Neither
is an introduction rule for this missing operand. Section 3.3 permits a body
inference declaration inside the invocation telescope only when its owning
rule actually introduces it. The pinned rules do not exhibit that
introduction for `(d,L,a)`.

Attempting the direct Lambda rule after the prefix first needs the following
source-owned local derivation, **R67-DIRECT-BODY-CHECK-1**:

```text
In C, before whole-annotation checking at (d,a):
  form L's independently admitted challenge/domain from the actual retained
  Computation formal entry and original captures;
  for each such challenge h, introduce the body's complete checking target
  B_L(h) at its authentic scope and derive n <= B_L(h) with the original
  body checking alternatives and the designated computation consumer;
  retain the body's result, Return/rebind, complete invocation return and
  their dependent provider/evidence fields in one joint rule instance.
```

The first unsupplied part is the source-owned **body checking target and
applicable checking/consumer proof at the independently admitted Lambda
challenge**. `Gamma(t)` and `Synth(n)` give the operand of a possible check,
but do not choose `B_L(h)`, establish that check, or designate its consumer.
The generic Lambda schema lists these as premises; `Build` (§4) conjoins
their actual rule programs and SRC (§6) reconstructs already applicable rule
instances, so neither supplies the missing premise by itself. The distinct
Function checker needs the resulting source domain and observations as its
inputs, not as outputs of a successful native comparison. Using the whole
annotation's `p_R` or Function target to create `B_L(h)` would require a
specific target-directed source rule and a same-context factorization proving
the purported prior operand/evidence; none is pinned. This is a bounded
derivation failure among the selected clauses, not impossibility, an ambiguity
counterexample, or a license to restrict ordinary inference.

If an authentic owner supplies R67-DIRECT-BODY-CHECK-1, continue *within the
same joint C*: construct the Function interface from its independently
admitted challenges and full body/invocation observations, then apply
§3.2(4) to the whole annotation with proved checked-domain inclusion and
observation inclusion for each checked challenge. Retain all permitted
nonidentity proof/conversion alternatives and the final target/root of
§3.2(6). This is a dependency order, not an assumed derivation.

## Source/native boundary and parent application

The fixed HIR owners retain `L/t/n` and separate `a,p_A,p_R`. In current native
construction, `candidate_source.rs:869–929,991–1034` records formal role,
registration, annotation action and Name registration; `:1409–1425` retains
the Lambda recipe and body endpoints; `:1450–1468` schedules the whole
annotation on the body endpoint. `candidate_effect.rs:1605–1703` constructs
negative checking and positive exposure signatures. These records/constraints
are potential consumers of a source derivation, not proof that the source
body-checking rule supplies `B_L(h)` or a designated consumer. The current
negative-concrete `p_A` preflight and signature-effect guards remain in force.
No fixed-source native pair, `Sol_src`, `Corr`, actual `Q`, `Sol_nat`, solution
direction or whole-judgment typed substitution is established.

The parent therefore remains OPEN. The R65 completed current operand is still
missing, now localized to the direct body's checking target/consumer at the
Lambda rule. R66's Result-A applicability question is not answered by this
route. Downstream R64 `p_A` typed interpretation and own permission, R61
whole-ascription formation, correlated `p_R`, actual Q and source/native
correspondence remain OPEN. Do not merge residual, provider or witness
lineages or transfer `p_t` permission to `p_A`. The source has no Catch, so
permission does not subtract any incoming effect.

The next in-envelope source step for Luna is to inspect the actual original
Lambda/body-result owner rule for the body checking target, designated
consumer and invocation telescope in this whole-annotated binding. A complete
rule instance with these premises and source-owned Function output falsifies
this bounded obstruction. A target-directed rule that supplies them only
through the written annotation instead falsifies an independently prior
operand and requires a proved joint factorization. If code evidence is
needed later, the minimal provisional TODO is to trace the existing
`candidate_source::Action::Lambda` recipe/body endpoint into its action
consumer and compare it with `Action::Annotation`; exact falsifier: the
alleged prior typed operand depends on the annotation target or negative
`p_A` evidence that it is supposed to precede. No code edit is proposed here.

Reused within their premises: R64 D0–D2, reviewed R65 bridge mismatch,
reviewed R66 conditional cut, reviewed formal RootPermit/NamePermit, selected
Name synthesis, and source Generalize's actual Lambda/checking rule schemas.
Rejected: restoring a withdrawn bypass, Result-A Lambda synthesis at this
annotated occurrence, a separate Lambda solve, an assumed completed `xi`,
post-solve witness selection, inferred body target, guessed consumer,
Function inclusion as an oracle, and native inequalities as source premises.
Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion and generalization remain unchanged.

Checks/resources: static inspection and SHA-256 verification only. The R67
contract and 34/34 frozen semantic dependencies matched before authoring;
their paths, hashes and original authors/provenance are the exact contract
manifest and pinned file headers. No tests, builds, execution, probes,
instrumentation, measurements, Git, compiler/semantic/test edits, external
contact, new dependencies or scratch files. Requested `gpt-6-sol/high`;
observed model/effort UNKNOWN/UNKNOWN. The 900-second grant is charged in
full; actual elapsed/CPU/RSS UNKNOWN, no carryover. Only this note and its
exact inbox handoff are authored. Independent review/intake belongs to Luna.
