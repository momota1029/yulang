# Operation licensed-field rule: reversible research semantics v1

Status: **ADOPTED FOR RESEARCH SEMANTICS v1**, not enabled in production. The
user explicitly authorized proof-motivated, reversible semantic interpretations.
This choice is the first new rule in the Operation field-lineage path. It is
not an old-rule derivation, conservative extension, or proof of the original
parent theorem. Independent review and a source-producer derivation are in
progress under r16. If those fail, withdraw v1 or revise it under a new
contract; do not rewrite the old rule history.

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN / closure
0. Fixed-c scope, source domain and quantifiers remain the comparison target.
All preexisting judgments continue to be admitted. The v1 rule is additive:
it records a source-licensed field when the actual source and complete typing
proof supply it. It never rejects a source occurrence for lacking the new
evidence. The full parent still requires correspondence for every originally
quantified case, including cases where this additive rule yields no field.

## Semantic choice

At the original Operation source formation, before any response, output,
solver observation, handler match or consumer selection, fix the Operation
contribution `c` together with its source declaration/reference, joint
instantiation `theta`, complete `Sigma_theta=(A_theta,B_theta,Lambda_theta)`,
scope and source formation derivation. This formation-time `c` is the one
contribution named throughout v1. The rule does not select a replacement
`c*`, choose `c` after observing an output, or filter the parent quantifier to
forms where an old selector was already available. It introduces source
lineage for this same fixed `c`; its relation to an old-semantics contribution
remains an explicit compatibility obligation.

The source-owned field license identifies one positive Written operand at
`s1 = Operation.Function.ResultValue.Function.ResultEffect`, position `j`,
under its original output binder. It retains the declaration, reference,
joint instantiation, exact source occurrence, field position, license and
future/provider dependencies. Root intrinsic Self at
`s0 = Operation.Function.ResultEffect` is a different field and cannot
discharge this rule.

## New judgments and exact constructors

The v1 layer has three proof objects. The following notation is part of this
candidate semantics, not a claim that the old rules already contained these
objects.

```text
PositiveWrittenField_v1(p,v,theta,b_out,s1,j,a; d_sig)
OpFieldLicense_v1(p,v,theta,b_out,s1,j,a; d_sig, d_pos, ell_field)
SourceOperationField_v1(c,p,v,theta,b_out,s1,j,a;
                        d_form,d_sig,d_pos,license)
OpFieldAtOutput_v1(c,p,v,theta,b_out,s1,j,a,d_dev,sigma_out;
                    phi_out,ell_out)
```

`d_sig` is the complete typed `Sigma_theta` derivation at the original output
binder. `d_pos` is its projection at exactly
`s1 = Operation.Function.ResultValue.Function.ResultEffect`, operand `j`, and
has conclusion `Positive Written(s1,j,a)` in `B_theta`. It is not a family-set
membership fact. Its only v1 constructor reads the exact typed signature node:

```text
d_sig : CompleteTypedSigma_v1(p,v,theta,b_out,Sigma_theta)
d_sig[s1,j] = Written(a) with positive polarity
------------------------------------------------ OP-Positive-Written-Field-v1
d_pos : PositiveWrittenField_v1(p,v,theta,b_out,s1,j,a; d_sig)
```

Its eliminator returns the identical `d_sig`, path `s1`, ordinal `j`, operand
`a`, and positivity equation; it has no family-membership or ordinal-search
case. The new license constructor is:

```text
d_sig : CompleteTypedSigma_v1(p,v,theta,b_out,Sigma_theta)
d_pos : PositiveWrittenField_v1(p,v,theta,b_out,s1,j,a; d_sig)
------------------------------------------------ OP-Written-License-v1
ell_field : OpFieldLicense_v1(p,v,theta,b_out,s1,j,a;
                              d_sig,d_pos, LicenseAt(p,v,theta,s1,j))
```

`LicenseAt` is the chosen v1 declaration-field license: it says that this
resolved source occurrence `v` owns this exact positive written operand under
the full `theta` and output binder. This is a newly introduced judgment, not an
old permission, solver result, output-provider identity, dynamic event,
subtraction fact or successful comparison. Distinct positions have distinct
license objects, even when their operands are equal.

The source-field proof object is the following ordered dependent record:

```text
q = SourceOperationField_v1 {
  c, p, v, theta, b_out, s1, j, a;
  d_form : OperationForm_v1(p,v,theta,c,Sigma_theta);
  d_sig  : CompleteTypedSigma_v1(p,v,theta,b_out,Sigma_theta);
  d_pos  : PositiveWrittenField_v1(...; d_sig);
  license: OpFieldLicense_v1(...; d_sig,d_pos,ell_field)
}
```

The formation rule is explicitly:

```text
d_form : OperationForm_v1(p,v,theta,c,Sigma_theta)
d_sig  : CompleteTypedSigma_v1(p,v,theta,b_out,Sigma_theta)
d_pos  : PositiveWrittenField_v1(p,v,theta,b_out,s1,j,a; d_sig)
license: OpFieldLicense_v1(p,v,theta,b_out,s1,j,a; d_sig,d_pos,ell_field)
------------------------------------------------ OP-Written-Form-v1
q : SourceOperationField_v1(c,p,v,theta,b_out,s1,j,a;
                             d_form,d_sig,d_pos,license)
```

`OP-Written-Form-v1` constructs this record once at the actual source
declaration. Its eliminator `unpackField(q)` returns exactly the stored tuple
`(c,p,v,theta,b_out,s1,j,a,d_form,d_sig,d_pos,license)`; each projection has
that field's displayed dependent type, and re-packing the projections is
definitionally `q`. No projection reconstructs `c`, `v`, `j` or a license from
family equality. The constructor is fixed before observations; it supplements
the v1 formation record without changing the contribution's identity.

## Complete-development indexed output action

An output certificate must be tied to one admitted complete Operation
development, not to separately selected output, typing and substitution
objects. Introduce the following indexed package as a **required projection of
an authentic complete development**. It is a dependent bundle of evidence, not
a new way to create an execution:

```text
d_orig : one actual complete Operation development under the original rules,
         admitted at the original p,v,theta and fixed c
d_dev  : CompleteAdmittedOperationDevelopment_v1(c,p,v,theta,d_form; d_orig)
```

The only constructor for the wrapper is `OP-Complete-Dev-Wrap-v1(d_orig)`;
it accepts no separately supplied output, typing or map fields. This name is
an index-preserving wrapper for the original parent evidence, not a newly
assumed operational rule. The cited source artifacts do not provide `d_orig`
for every original case; absence of that actual original derivation is an open
premise, not evidence that the wrapper has a fabricated inhabitant.

Its projections are fixed by the one underlying development:

```text
adm_dev    : original complete admission evidence in d_dev
d_A        : actual ordered suffix k0 >>= A_decl of d_dev
(r_resp,C_now) : response and resumed live state in d_dev
(r_out,C_out)  : final result and whole state after d_A in d_dev
beta_out   : complete output typing derivation in d_dev
sigma_out  : original whole dependent output/world/future substitution in d_dev
M_dev      : actual whole typed/admission/provider/future map in d_dev
```

The projection equations are definitional: `d_A`, response, final output,
`beta_out`, `sigma_out`, and `M_dev` are all projections of this same
`d_dev`, whose indices are the formation-time `c,p,v,theta,d_form`. Supplying
unrelated derivations with equal endpoint types does not construct `d_dev`.
The candidate currently has no producer for this package in every original
case; until an authentic owner supplies it, the output rule is inapplicable and
the parent remains open.

The new whole-field action is also explicit. `M_dev` must project an exact
field action `m_j` whose source is `q`'s `d_pos` and whose target is operand
`j` at `s1` in `beta_out` after the actual `sigma_out`. Its constructor
requires the same complete output map and exact path/ordinal equations:

```text
q                  : SourceOperationField_v1(c,p,v,theta,b_out,s1,j,a; ...)
d_dev              : CompleteAdmittedOperationDevelopment_v1(c,p,v,theta,d_form)
M_dev              : WholeOutputMapOf(d_dev)
field_equations    : source(m_j)=d_pos(q) and target(m_j)=field(beta_out,sigma_out,s1,j)
license_equations  : scope/provider/world/future/admission indices of license
                     map along M_dev without changing c,p,v,j
------------------------------------------------ OP-Whole-Field-Transport-v1
tau_v1 : LicensedWholeFieldAction_v1(q,d_dev,m_j,field_equations,
                                      license_equations)
```

`LicensedWholeFieldAction_v1` has one eliminator, `unpackAction(tau_v1)`,
which returns the identical `q`, `d_dev`, `m_j`, path equations and license
equations. It has no weakening-by-family, coordinate-equality, responder, or
fresh-contribution eliminator. The formation and transport constructors are
new v1 semantics; they do not follow from old `DeclContribution` evidence.
The transport constructor is conditional on an actual `M_dev` and its exact
field equations. The design does not yet prove that all admitted developments
have these equations.

Only then can output incidence be introduced:

```text
tau_v1 : LicensedWholeFieldAction_v1(q,d_dev,m_j,...)
phi_out : projection(m_j, beta_out, sigma_out, s1, j)
ell_out : license_projection(tau_v1, M_dev)
------------------------------------------------ OP-Written-Out-v1
eta_v1 : OpFieldAtOutput_v1(c,p,v,theta,b_out,s1,j,a,d_dev,sigma_out;
                            phi_out,ell_out)
```

`eta_v1` has one eliminator `unpackEta(eta_v1)`, returning the same `q`,
`d_dev`, actual `m_j`, output path/ordinal, `phi_out` and `ell_out` with their
indexed equations; re-introduction is definitionally the original `eta_v1`.
There is intentionally no eliminator from this v1 object to old
`contributes-to`, Contrib, Inc, Cover, Permission or subtraction judgments.
NPAIR L2 and other real consumers therefore remain open until their own
versioned introduction is defined and supplied with the same indices.

Here `d_A`, response and final output are eliminated only from `d_dev`; they
cannot be supplied independently. `OP-Written-Out-v1` is deliberately tagged
v1. If `d_dev` or the exact whole-field action is absent, this rule yields no
`eta_v1` but does not reject the original source or erase its development.
The fixed `c` remains the `c` stored in `q` and indexed by `d_dev`.

## Cases and boundaries

- **Pending/requesting R:** keep the live state, event, history and raw
  ordered `k >>= A_decl`; no complete-output field evidence is produced yet.
- **Divergent R:** retain every original finite prefix; do not add an eventual
  return premise.
- **Returning R:** apply `OP-Written-Out-v1` only to its actual complete
  `A_decl` result and complete typing.
- **W:** preserve the actual predecessor and whole W map. A field license
  transfers only along a genuine whole typed map that retains the same `c`,
  occurrence and independent future/admission evidence. Coordinate equality
  does not create a map.
- **Z, including unanchored Z:** retain its independent declaration, whole
  tuple, license, future and domain evidence. It has no predecessor induction
  hypothesis. This rule does not attach an unrelated Z output to `c`; a
  v1-Z field action requires its own real source evidence and remains OPEN
  unless such a source case is supplied.
- **Operand/Alt/Pair/Op/Ref/Scope/Rename:** retain antecedent, branch tag,
  shared tuple, exact local origin, reference and binder actions. A composite
  constructor cannot turn a reused responder/provider field into a local
  Operation field.
- **Consumers:** `eta_v1` may make a v1-incidence-sensitive consumer
  applicable. Permission, N-Ingress, selection/removal, residual, pending or
  invalid state are governed by their explicitly versioned v1 contracts; this
  rule does not manufacture a handler selection or subtraction witness.

The v1 rule does not state or prove old `eta_c`, old Contrib/Inc/Cover
reflection, consumer equivalence, N-Transport, F1/FK1, soundness, principality,
termination, or production readiness. No old parent condition closes merely
because this judgment has been introduced.

## Observable effect, compatibility and falsifiers

When a source-produced `eta_v1` is consumed, a positive Written result-effect
field may now contribute to v1 incidence and type inference where the old
source rules supplied no such judgment. That can change effect applicability,
subtraction opportunities, inferred constraints, diagnostics or program
acceptance. The change is intentional and versioned; old/new equivalence is
not claimed. The implementation must be feature-gated until the v1 producer
and consumer are independently reviewed and a focused source execution shows
which behavior changed.

| Case | Prior semantics | v1 rule | Determining evidence and current status |
| --- | --- | --- | --- |
| Positive Written field with no v1 license proof | Existing judgments remain admitted; no `OpFieldLicense_v1` judgment exists. | No source-field proof is constructed. | Exact `d_sig` and positive field projection absent; no rejection of the old source. |
| Licensed source field, but no authentic complete development/map | No old same-c output incidence follows from field syntax alone. | `q` may be formed; no `tau_v1` or `eta_v1` follows. | `d_dev` / `M_dev` absent; this is the current source/native gap. |
| Complete admitted output and exact same-c whole-field map | No old/new equivalence is asserted by this note. | `tau_v1` and then `eta_v1` are constructible for that exact output field. | Requires one `d_dev`, its actual `A_decl` suffix, `beta_out`, `sigma_out`, admission and path/license equations. No fixture currently establishes it. |
| Output field differs, or only response/predecessor coordinates match | Old rule history remains unchanged. | No `tau_v1` for that field; the original execution remains admitted. | Exact path and ordinal equations fail; no fallback by family equality. |
| Pending or divergent R | Existing request/history and finite prefixes remain. | No complete-output `eta_v1` is produced; no eventual-return premise is added. | Actual pending prefix or divergent finite development; complete output is absent. |
| W/Z, composite, reference, scope or renamed field | Existing constructor and whole action remain in force. | No v1 output action unless its own complete indexed map supplies the same field/license equations. | Full case actions, especially independent Z/domain evidence, are OPEN. |
| NPAIR/Permission/subtraction/consumer decision | Prior consumers retain their existing contract. | This rule alone does not change a consumer or select/remove an effect. | A versioned consumer constructor and old/new execution are not yet specified; observable acceptance/diagnostics remain OPEN. |

Keep separate gates:

1. rule definition and well-typed proof objects under v1;
2. source producer and actual v1 consumer correspondence;
3. full unchanged-scope parent theorem under v1, including every original
   R/W/Z, future, history, admission and F1/FK1 case;
4. old-semantics compatibility, inference soundness/principality, termination
   and production enablement.

Decisive falsifiers are: choosing `c` after an output; different contribution
identity at a copied field; using `s0` instead of `s1`; treating response as
complete output; circularly assuming `eta_v1`; merging source occurrences by
family/member ordinal; a returned field lacking the source license/whole map;
an original W/Z admitted case without the required same-c action; or an
implementation that emits evidence without a source producer or consumes it
at a different owner. Any such finding rolls back this v1 choice or leaves its
parent and production gates open; it never narrows the original source domain.
