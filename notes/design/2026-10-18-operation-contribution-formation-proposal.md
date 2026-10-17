# Operation contribution formation and complete-output action

Status: Draft interpretation proposal, revision 1; NOT adopted and NOT independently certified.
Assignment: NPAIR-OPERATION-CONTRIBUTION-CONTRACT-20261018.
Author: `/root/npair_operation_source_contract`, sole author; descendants 0.
Requested Sol/prover/high; observed model/effort UNKNOWN/UNKNOWN.
Sprint: `npair-operation-source-contract-and-replay-reachability-20261018`, revision 3,
SHA-256 `1fa25ac715f9bd583c7dc56e11b1fe027f71e953faac0fc6130b2e2b009ed94d`.
Source baseline supplied by Luna: `759f9d0b784c71f19dc489199edf2d268174cbbc`.
Activation/dispatch commit supplied by Luna: `2ee514483a68aaf3b36a4726d9f0a0b9a2cf6e59`.
Neither commit was authenticated with Git under this leaf packet.

## 1. Original inputs and proposed completion

Fix the original declaration p, actual clause `Prim(alpha,m_q)`, actual typed
reference `Ref(t,m_v)` at v, one lawful joint theta, complete
`Sigma_theta=(A_theta,B_theta,Lambda_theta)` and original `xi=(nu,K,D_original)`.
Retain the entire original parameter/binder telescope and witness
`w : Prim_alpha(h,y;xi)`. Complete Lambda includes primitive/phase, response,
raw-continuation, provider/future, world, guard, admission and licensing fields;
the printed arrow is insufficient. Family projection cannot recover theta.

The target is the original fixed contribution c, chosen before observation.
The distinct paths are

```text
s0 = Operation.Function.ResultEffect
s1 = Operation.Function.ResultValue.Function.ResultEffect.
```

The parent requires that same c at the actual complete output's Written s1.
It does not permit choosing a contribution after seeing y or replacing c with
a complete-Call contribution, an Apply variable, a family, or an arbitrary atom.

The revision-2 reviewed Operation source-construction input §§2-4 supplies
the concrete source-defined request carrier and designated consumer below;
there is no missing arbitrary native implementation body at that source case.
Its complete production Z/W clauses and this c-field interpretation remain
separate independent obligations.

**Given:** IF-Insert/Use retain the complete original telescope and actual
reference placement. Operation has inert carrier/native return, followed by
the declaration-derived one-layer consumer. The source tail is

```text
k0(r_resp,Cnow) = Return(r_resp,Cnow)
D_tail_src(r_resp,Cnow) = Return(r_resp,Cnow) >>= A_decl.
```

**Derived from these inputs:** the complete result is the actual result of
`A_decl(r_resp,Cnow)`, if it returns. It need not be identified with r_resp.
Full Sigma typing, when independently established, supplies the complete
B_theta result certificate at that actual result. Authentic CallMem stores
and eliminates to this same whole proof. None of these facts selects c.

**Proposed completion:** add the source-owned contribution formation and
field eliminators below at the Operation primitive owner. They add an
explicit contribution interpretation to the existing typed signature field.
They are not recovered historical rules. Attributing a written guarantee to
this contribution can affect active incidence/removal consumers, so this
addition cannot be declared conservative from its syntax or erasure alone.
Luna must adjudicate compatibility or semantic change before adoption.

## 2. Formation at the actual owner, before observations

At actual declaration/reference formation retain an ordered formation record q:

```text
q = (p, alpha, actual registration and reference v, joint theta,
     complete Sigma_theta and its original scope tree,
     b_out, s, j, a, original field-license reference).
```

Here b_out is the existing binder of the complete declaration result after
its consumer/completion. `s,j,a` are the actual positive Written field path,
source operand position and operand, checked by walking B_theta under that
binder. A declaration with two equal operands has two positions; a graph edge
is retained with its actual occurrence rather than unfolded into a new one.
The field-license reference must independently license that original field
at this declaration, scope and substitution. No license is obtained from a
row name, future successful comparison, NPAIR Permission or a new constructor.

Proposed introduction:

```text
q : the actual typed formation above, with its independent license
s,j,a : the corresponding positive Written occurrence in complete B_theta
---------------------------------------------------------------- OC-Written-Form
c = OperationWritten(q) : OperationContribution(p,v,theta,Sigma_theta;b_out,s,j,a)
```

This c is a suspended field contract fixed once at formation. Its dependent
provider variable is b_out, not an observed provider chosen in the constructor.
The rule consumes no challenge, response, observation, eta, At, desired formal,
subtraction proof, or solver query. Source/operand positions are typed data,
not evidence that every existing contribution has this constructor.

Proposed elimination, solely for this constructor:

```text
elim_form(OperationWritten(q)) = q
```

Elimination returns the complete original declaration/reference/substitution,
complete Sigma, binder, path, position, operand and license reference. It never
inverts a family, native row ID or printed type. Original contribution cases
remain available, with identity-preserving inclusion of their entire original
witnesses. They do not gain this eliminator. Other proposed cases (Self at s0,
consumer-direct, tails, inherited contributions) remain distinct and are not
reclassified as Written. This is an additional constructor case, not exhaustive
inversion of the original contribution judgment.

Application to the parent's already-fixed c requires its actual original
formation to be precisely this case, with these indices, or genuine original
identity-preserving introduction/elimination maps. No such fact is proved by
writing `c = OperationWritten(q)` in this proposed rule. The rule is a concrete
source-owned interpretation to test, not a replacement for the parent's c.

## 3. Complete-output Written action through A_decl

Let d_resp be the actual admitted response/current-state evidence; let d_A be
the actual complete `A_decl(r_resp,Cnow)` development in that same joint tuple.
At a genuine Return, eliminate d_A and full Sigma at their original binders:

```text
out(d_A) = (r_out,Cout)
beta_out : r_out has the complete original B_theta interface at Cout
phi = field_projection(beta_out,s,j)
```

Here s is the global occurrence path anchored at b_out. The projection walks
only its suffix relative to B_theta: for s1 this is the returned Function
ResultEffect, not another descent through an Operation root. Let sigma_out
be the existing dependent substitution of b_out and its live world/response
fields obtained from d_A. The stored operand a remains a suspended expression;
its output instance is a[sigma_out]. It is not copied from a pre-completion
provider or assumed world-independent.

`field_projection` walks the complete original result-type certificate to the
positive Written occurrence. It returns its guarantee operand and dependent
future/provider/constraint/license judgments, not an executed request. If the
original type certificate does not expose that projection, that is an explicit
missing primitive typing lemma; no synthetic beta_out is introduced. A field
with a tail retains its complete open tail and later-lower checks.

Proposed action and its computational eliminator:

```text
c = OperationWritten(q) formed once as in OC-Written-Form
(d_resp,d_A,beta_out) : authentic complete source/typing evidence above
G(d_complete), all original guards/licenses/admission obligations hold
---------------------------------------------------------------- OC-Written-Out
WrittenOutput(c,d_complete,b_out,r_out,Cout,s,j,a[sigma_out],phi)

elim_out(WrittenOutput(...)) =
  (c,q,d_complete,d_resp,d_A,b_out,r_out,Cout,s,j,a,sigma_out,phi,
   original guards/licenses and complete witness lineage)
```

This explicitly **proposes** the incidence of the formation-fixed c at the
complete output. Original full typing gives phi; the new attribution to c is
the content added by OC-Written-Out. It is not a previously proved original
DescMem/At theorem, and is not a free predicate assigned the target truth.
The actual source action computes by structural projections and one
constructor application. The additional relation has fixed introductions and
computational eliminators instead of an uninterpreted bridge hypothesis.

The A_decl action is concretely

```text
act_A(c,d_resp,d_A,beta_out) =
  WrittenOutput(c, complete_bind(d_resp,d_A), b_out,
                fst(out(d_A)), snd(out(d_A)), s,j,a[sigma_out],
                field_projection(beta_out,s,j)).
```

The action is a section over each actual complete result fiber, not a total
function from a response provider to some invented returning output. For one
fixed q the same c and formula handle every actual complete output d_A with
its own sigma_out and beta_out. This gives the proposed constructor order
`form c before forall actual d_A`; it does not establish that the parent’s
already-fixed c has this formation.

The c on both sides is identical; its provider-dependent occurrence is
instantiated at b_out's actual output. There is no intermediate assertion at
r_resp. Even if A_decl returns a different provider, this formula uses its
actual output and that output's complete type proof. A same-provider special
case needs the original equality proof and reduces the same formula. It does
not assert that effects of the response provider or consumer move into s1.
The rule concerns a static positive guarantee at that field. It emits no
request at Operation construction, no request at returning a Function, and no
request merely because a written operand exists.

For a pending Request, retain the original raw suffix `k >>= A_decl`; at each
actual admitted resumed state apply the formula only if the full suffix
returns. For divergence or a finite pending prefix there is no out(d_A), and
no OC-Written-Out return instance. The suspended c and complete continuation
remain. This is pointwise over every independently admitted finite history;
there is no bounded test-history or termination premise.

## 4. All original alternatives, guards and domains

Keep the original grammar verbatim at each original fiber:

```text
H_G(R) = least X. G(y) and
  (R(y) or Z(y) or exists x,z. X(x) and W(x,y,z)).
```

No W/Z interpretation is selected here. The proposed output eliminator for a
complete alternative is determined by its genuine whole-tuple result/type
certificate, never by a source execution anchor. This is a universal rule
schema with independently required concrete cases, not evidence those cases
have already been supplied.

| Actual last case | Proposed action and independent obligations |
| --- | --- |
| Returning R | Use the response and actual A_decl complete output above, with original source typing and final G. |
| Pending/nonreturning R | Retain the original suffix and current-state response contract; instantiate only at a genuine later Return. No fabricated output. |
| W fixes result coordinates | Retain predecessor and W witness, final G and the original output certificate. Same coordinates alone do not prove its license/action. |
| W changes provider/world/scope/field | Eliminate its actual final whole result/type proof at its output binder; instantiate c there only under the same actual declaration interface. Retain the changed-field law, all licenses and the independent admission/domain action for live changed coordinates. |
| W changes the declaration/interface itself | No cast into q's old field. Require the original whole-map law connecting the interfaces, including c identity and license; otherwise the original quantified case is unresolved. |
| Z | Use its independently licensed complete whole tuple, own output-dependent provider/future interface and final G. Its genuine declaration insertion and actual use supply placement; no execution anchor is imposed. |
| Union | Retain the actual tag and branch-to-result map. |
| Conjunction | Use both proofs at the same original tuple. No recombined marginal witnesses. |
| Bind/Call/consumer | Use actual ordered rebind/result and full invocation evidence. Authentic CallMem preserves d; it supplies no missing field introduction. |
| Return/Delay/capture | Keep latent interfaces latent. Returning a provider does not force it. |
| Scope/Rename/Ref/recursion | Keep original binder positions, lawful whole substitution, actual reference and finite original derivations. Recursive references remain graph edges. |

G checks ordinary descriptor membership, genuine guarantee bounds, all original
K/D, authority, scope, provider/admission and dependencies at the final tuple.
An original permitted tuple must never be discarded because the proposed
field projection is unavailable. Failure to lift is a failed compatibility
obligation; it is not a source-refusal rule. No new admission premise is added
by OC-Written-Out. Positivity of membership proves no domain law.

Whole legal injective renaming transports q, complete proofs, c and every
incident field together; structural projection then commutes by its original
typing law. This proves only the constructor's schematic renaming calculation
when that law is given. Extrusion, identification during qualifying intrusion,
joint hiding and generalization need their own actual whole actions; they are
not consequences of injective renaming. Original Value-SCC qualification,
ordinary constraint generation/accumulation/propagation and live checks remain.

## 5. Compatibility, reflection and discriminators

This package fixes a constructor and its complete-output action. It does not
prove that all original contribution formations are its image. To be a
conservative completion at the original primitive owner, the following must
be established with the actual original cases:

1. Every original permitted whole witness, including every R/W/Z derivation,
   has a lift with the same h,y,xi,theta, provider/future, G and original c.
   Forgetting returns the entire same original evidence, not just Pi(y).
2. Every added constructor incidence is a valid original incidence for that c,
   and every original incidence remains available. No Written duplicates,
   tails, imported license or other original contribution is identified.
3. Original active consumers have identical behavior on corresponding full
   inputs in both directions: applicability, selected residual lineage,
   retained lowers/checks and suspended/invalid states. Storage erasure alone
   proves none of this. A consumer that distinguishes the proposed incidence
   from the original one is a semantic-change witness.
4. All original world/admission/future actions and whole substitution laws
   commute at their original binder positions, including changed W/Z domains.

These are proof obligations, not proposed definitions of original semantics.
The first presently absent case is the original fixed c's actual formation
and its elimination into the complete-output field. Complete Sigma/Lambda
and concrete W/Z laws also remain independent inputs. No two complete
compatible denotations, admitted counterexample, or semantic equivalence is
established here.

Discriminators for review: two equal-family Written positions retain two
identities; root Self at s0 cannot eliminate as Written s1; A_decl may be
used only through its actual output proof; an unanchored Z must not disappear;
a changed provider requires its own full future/domain evidence; the same
formation-fixed c must work for every observation rather than choosing one
per output; an original c of another constructor is not silently renamed.
A complete original witness failing any required lift/reflection refutes the
proposed conservative completion. Missing bytes alone do not refute it.

## 6. Source/native target and authority boundary

Stable pinned source inspection and the frozen reviewed original-c audit
give the following forward target. The FreshUse fact is reused from that
audit, independent of concurrent implementation changes. `candidate_operation`
builds the complete signature and value link42. `candidate_signature_value`
passes the intrinsic family only at the pointer-identical root Function;
the nested returned Function has no intrinsic Self insertion. At its actual
Written positive field, `candidate_signature_effect` emits Support(view)
with the original concrete operands/tail. `candidate_check_effect_operand`
expands it to position-indexed AnnotationMember(view,j). FreshUse's separate
AnnotationMember arm remaps the view while retaining j. Its Contribution arm
is a distinct native constructor and cannot identify original semantic c.

A source/native relation must retain this semantic formation and full output
proof alongside the authentic source-position/view/cache invariant. Multiple
semantic witnesses at one native member must retain their distinct evidence;
no inverse from member/family/row is promised. This proposal supplies neither
that source emission nor semantic ingress, At, residual subtraction, or the
R1/Install(g)/Capture/whole FreshUse/J2 chain. No production code change is
authorized. The paired application note records exact parent consequences,
TODOs, dependency hashes and stop receipt.
