# Open typed carrier declaration interface

Date: 2026-10-13
Status: Draft; original declaration instance unprovided; not ready for adoption
Scope: proposed parametric interface for the carrier-contract domain before an invoke argument challenge
Baseline: `research/simple-sub-intrusion@921cbbb778e413a25ac02872939eeb9d6ff62d64`
Prepared-by: primary from architect `construct_typed_carrier_interface_proposal`, including its formation repairs
Reviewed-by: spec_auditor; compiler_referee, context finding repaired and fresh delta passed
Approved-by: none
Implementation / original source application / F5 authority: none
Supersedes: none

## 1. Proposed interface and original parent

Represent contract presentations by an open dependent package indexed by
independently typed original declarations. Each declaration supplies its own
complete ordered argument telescope, schema, primitive meanings, alternatives,
constructor operations and scope actions. A presentation retains those inputs;
it chooses no replacement interpretation.

The owner is original local declaration formation before formal registration
and typed registry decoding. Parameter/Lambda supplies an actual source-scoped
application. The typed argument supplies its particular `J` and formation
evidence at the original later challenge scope.

The original parent remains:

```text
Gamma_form^src(p) |- mu : Delta_in^orig
intro_orig[mu]
```

This proposal supplies interface equations for review. It supplies neither an
actual original declaration nor its source application. Complete Call,
soundness, natural inference, correspondence and F5 remain OPEN.

## 2. Contexts and universes

Use a cumulative hierarchy `U_0 : U_1 : U_2 : ...`. Choose a level `i`
containing the operand types of the declaration instance. Contexts and
well-formed judgments are explicit; no universe contains itself.

```text
Tel_i(Gamma) : U_(i+1)
epsilon : Tel_i(Gamma)

Theta : Tel_i(Gamma)      Gamma.Theta |- A : U_i
------------------------------------------------
(Theta; x:A) : Tel_i(Gamma)

|epsilon| = 1
|Theta; x:A| = Sigma theta:|Theta|. A[theta]
```

The sums interpret an ordered argument telescope. They do not replace the
original semantic quantifier tree with existential binders. Original universal
response/future nodes retain their universal meaning, position and incidence.
Schema codes are distinct from witnesses inhabiting their interpreted types.

## 3. Independently supplied declaration interface

At the actual predecessor context `Gamma_decl`, the proposed interface `D`
has the following external inputs:

```text
declarations : U_i
Args_d       : Tel_i(Gamma_decl,d:declarations)
B_d          : original typed binder/quantifier tree at (d,Args_d)
scope_d      : original scope map to the source binder tree

Gamma_decl,d:declarations,alpha:|Args_d| |- Schema_d(alpha) : U_(i+1)
Gamma_decl,d:declarations |- schema_d : Pi alpha:|Args_d|. Schema_d(alpha)
```

Here `|Args_d|` is interpreted in `Gamma_decl,d:declarations`; each
argument field may depend on `d` and its preceding argument fields. The level
`i` is chosen for the supplied signature, as in §2.

`declarations` is a supplied index type, not a fixed global primitive census.
The finite declaration-token closure used by one raw registry recipe remains
the adopted local dependency closure. A token alone supplies no `Args_d`,
actual argument `alpha`, schema or local law.

The actual original schema at `(d,alpha)` must expose each field with its full
type at the field's original predecessors. Let `Gamma_(d,alpha,b)` be the
context at node `b` of `B_d`. A schema field there has type
`Tel_i(Gamma_(d,alpha,b))`; its event witness, when required by the original
rule, has that telescope's interpreted type in that same context.

The required manifest is:

| Original fields | Required placement and retained data |
| --- | --- |
| Descriptor, root, owner, provider, designated port | Actual sorts, identities, complete arguments and original incidence |
| Inert license and static formation | Original operand telescopes and local introduction signatures; no event witness moved into static formation |
| Event, challenge, receipt, Force and same-result rebind | Original ordered nodes, receiver/result incidence and complete types |
| Return and complete/pending observations | Original result, provider and current-world indices and all conjuncts |
| Request, operation instance and response | Actual Request node and original dependent response domain |
| Raw resumption and resumed world | Original handle, response and current resumption-event dependencies |
| Unfinished suffix, latent use and compatible futures | Original ordered continuations, shared witnesses, live worlds and quantifiers |
| Profile, guarantee, lifetime and authority | Complete original dependent predicates, domains and applicable evidence |
| Every additional original field and alternative | Exact original operand position, type, scope and application |

For an original telescope `(x_1:U_1; ...; x_n:U_n)`, require each genuine
formation judgment at `Gamma_decl`, actual preceding declaration arguments,
original ancestor nodes and `x_<j`. This table is an import-interface
requirement, not an instantiated complete manifest.

The primitive families are independent typed inputs: license, formation,
descriptor membership, admission, production, profile, guarantee, world,
lifetime and future predicates, each with its **actual** complete operand
telescope. The original declaration also supplies each genuine local operation:

```text
op_(d,r) : Pi theta:|Operands_(d,r)|.
             |Premises_(d,r)(theta)| -> Conclusion_(d,r)(theta)
```

An actual imported signature must display `Operands`, `Premises` and
`Conclusion` at their original scopes. These operations are not a new
certificate asserting complete correctness. Their existence, validity and
application are genuine remaining owner obligations.

## 4. Original alternatives and W/Z

Retain each declaration's actual alternative index, complete alternative
arguments and whole-tuple relation at their original binders. Where the
declaration uses W/Z, their full provider, guard, domain, operation, future and
scope arguments remain part of that signature:

```text
W_d : Pi original invariant operands.
        Pi x:WholeTuple_d. Pi y:WholeTuple_d.
        Pi z:RewriteWitness_d(x,y). Prop

Z_d : Pi original invariant operands. Pi y:WholeTuple_d. Prop
```

No W/Z meaning is selected by these equations. Source-contracts §3.7's
positive abstraction grammar is a conditional sufficient characterization.
Its equation is retained when genuinely supplied by the original declaration;
this interface imposes no such equation on every declaration.

The package preserves every original licensed alternative, including a Bool
Return in a broad `J/Any` contract when the actual carrier returns Int. Actual
Force traces do not define the package's complete licensed domain.

## 5. Presentation, formation evidence and elimination

Define the proposed presentation type:

```text
Gamma_decl |- CarrierDecl(D) := Sigma d:declarations. |Args_d| : U_i
Gamma_decl |- C_J(D)        := CarrierDecl(D) : U_i

Gamma_decl,J:C_J(D) |- d_J := fst J : declarations
Gamma_decl,J:C_J(D) |- alpha_J := snd J : |Args_d|[d_J/d]
Gamma_decl,J:C_J(D) |- schema(J) :=
  schema_d(alpha)[d_J/d,alpha_J/alpha]
  : Schema_d(alpha)[d_J/d,alpha_J/alpha]
```

The symbolic binder `J` introduces no actual inhabitant at formal formation.
Subsequent schematic uses of `d` and `alpha` at a J-indexed field denote these
components and use the displayed declaration/component substitutions.

The schema is fixed by the supplied declaration and its arguments. A `J`
presentation neither selects a substitute schema nor asserts formation,
license, carrier validity or admission. Its original formation/provenance
presentation has an independently supplied type at its actual predecessors:

```text
Gamma_decl,d:declarations,alpha:|Args_d|
  |- FormationPresentation_d(alpha,schema_d(alpha)) : U_i
Gamma_decl,J:C_J(D) |- FormationPresentation(J) :=
  FormationPresentation_d(alpha,schema_d(alpha))[d_J/d,alpha_J/alpha]
  : U_i

Gamma_challenge |- J : C_J(D_challenge)
Gamma_challenge |- kappa_J : FormationPresentation(J)
```

The last two judgments are argument-supplied premises at the actual challenge
context, after its lawful application/transport of the interface. The field
type `kappa_J:FormationPresentation(J)` occurs after the symbolic J binder in
the checked inlet telescope; declaring that type asserts no inhabitance.

`kappa_J` occurs once as the later checked-inlet formation field. Proof
arguments already present in an original `Args_d` remain there; no proof
irrelevance or extra duplicate formation requirement is introduced.

```text
Gamma_decl |- declarations : U_i
Gamma_decl,d:declarations |- Args_d : Tel_i(Gamma_decl,d:declarations)
-------------------------------------------------------------------
Gamma_decl |- C_J(D) : U_i

Gamma_decl |- d_0:declarations
Gamma_decl |- alpha:|Args_d|[d_0/d]
----------------------------------
Gamma_decl |- (d_0,alpha):C_J(D)

unpack(d,alpha) = (d,alpha)
elim_Q((d,alpha),f) = f(d,alpha)
```

These are proposed dependent-package equations. They are not an identification
with an independently fixed original declaration sort. Domain formation needs
the original typed interface, and supplies no `J`, `kappa_J`, carrier, current
guard or future witness at static formal formation.

## 6. Whole scope action

For each genuinely supplied lawful scope action `rho`, require its original
actions on declarations, ordered arguments, schemas, primitive operations and
formation presentations. Package action is derived pointwise:

```text
rho : Gamma_decl -> Gamma_decl'
Gamma_decl,d:declarations |- Args_d : Tel_i(Gamma_decl,d:declarations)
Gamma_decl',d':rho declarations
  |- (rho Args)_(d') : Tel_i(Gamma_decl',d':rho declarations)

rho(d,alpha) = (rho d,rho alpha)
rho(schema_d(alpha)) = schema_(rho d)(rho alpha)
rho kappa_J : FormationPresentation_(rho d)
               (rho alpha,schema_(rho d)(rho alpha))

action_id = id
action_(tau o rho) = action_tau o action_rho
scope_(rho schema) o rho_B = rho_source o scope_schema
```

The last package/schema/witness equations are conditional on the actual
typed package and, where used, its separately supplied `kappa_J` at their
original source/challenge scopes. Transported arguments inhabit
`|(rho Args)_(rho d)|` at the lawful target context. They supply no static
package or formation witness from type formation.

Retain each original proof choice and shared witness. No action manufactures
formation evidence from `J`. The whole tuple transports provider, owner,
operation, current/resumed world, raw continuation, pending suffix, profile,
guarantee and future fields together. Endpoint substitution does not merge
independently owned source keys or proof alternatives.

Applicable primitive action laws remain inputs. An injective embedding is
not automatically a semantic equivalence; every direction used by an original
consumer needs its genuine law.

## 7. Formal, argument and consumer bridge

Formal formation applies `D` to actual preceding raw `p`, source context,
header, Desc and scope inputs. Each `Declare-Owned-Port` must then receive its
actual complete local declaration application and scope map. The candidate
owner declaration permission supplies no original contribution license or C0.

At the original challenge binders, the argument supplies:

```text
J=(d,alpha):C_J(D)
kappa_J:FormationPresentation_d(alpha,schema_d(alpha))
t:the original carrier domain at schema(J)'s actual indices
carrier_J:the complete original Car_J(t) certificate
```

Original result checking, whole designated-port incidence, static constraints,
whole observation checking and current independent guards follow at their
original scopes. Whole checking retains every licensed alternative and all
response/raw-resumption/future developments; no later filtering removes a
licensed observation.

The required bridge is original declaration application -> ParameterOrigin
and owned port schemas -> Entry-Value/ValueBind -> Register-Parameter -> the
same formal Name -> complete Apply/Call. Every original-to-candidate map
remains a separate obligation. The id/pick-only inlet adoption is not extended
to invoke by this Draft, and no universal Gen-Call-0 prerequisite is added.

## 8. Authority and adoption readiness

Existing bounded registry authority supplies the nominal keys, raw Seal,
complete ordered applications, owner permissions and whole action boundaries.
Original source contracts supply Desc before challenge, argument-supplied `J`
and the retained complete observation semantics. Registry construction §4.1
permits independent original W/Z and opaque families at their predecessors.

New Draft equations are `CarrierDecl(D)`, `C_J(D)`, the explicit schema
projection interface and their package introduction/elimination/actions.
No actual complete original declaration manifest was instantiated in this
pass. **This proposal is not ready for user adoption as the original domain.**

The next gate is an actual declaration instance: display every argument and
field type at its predecessors, supply the original schema and formation
constructor signatures, and check the complete actions and consumer
applications. Original-domain coverage, authentic substitution,
`intro_orig[mu]`, source/native correspondence, complete Call and F5 remain
OPEN. Mathematical packaging proves neither effective checking nor a compiler
supplier for this interface.

Falsifiers include an unavailable later decoder argument, an unprovided
original license, moved event/world/quantifier, replaced provider or proof
choice, omitted licensed alternative, or a scope action lacking its required
primitive law. Reconsider the affected Draft hookup if any occurs.

Mode: M3; compiler_referee for formation/preservation and spec_auditor for
scope/authority. Static checks only, zero tests/builds/probes/measurements.

## Sources

- [Registry adoption](2026-10-10-original-registry-constructor-adoption-proposal.md) §§1–3.
- [Registry construction](../theory/2026-10-10-source-owned-original-registry-construction.md) §§2, 3.1, 4.1–4.2.
- [Uniform Value entry](../theory/2026-10-08-uniform-value-entry-constructor.md) §4.
- [Source contracts](2026-10-05-source-contracts-and-common-allowance.md) §§2, 3.7.
- [Formal-entry Draft](2026-10-13-original-formal-entry-constructor-draft.md) §§1–7.
- [Domain cut](../progress/2026-10-13-invoke-carrier-contract-domain-cut.md) §§1–5.
- [Inference principles](2026-10-11-yulang-inference-top-level-principles.md).

## Primary review and proof handoff

`spec_auditor` passed the original frozen Draft's authority and scope review
with no findings. `compiler_referee` found a major predecessor-context error:
the declaration-dependent argument family had been formed in `Gamma_decl`
rather than `Gamma_decl,d:declarations`. An `implementer` repaired the family,
dependent package formation/introduction/projection and scope-action contexts.
A fresh independent `compiler_referee` delta review passed at SHA-256
`6997ff026b120437d6aaaf9ec3b1cb89f5824491dff80b705e0d7caafc81a78d`.
The declaration-dependent Bool/Int discriminator now forms at its actual
predecessors. No required finding remains in the reviewed interface scope.

A focused follow-up review classified the schematic J/kappa judgments as a
minor scope ambiguity. The primary made projection/type formation explicitly
use the symbolic J binder and restricted actual J/kappa input judgments to
the challenge context. Whole witness action is expressly conditional on
those actual supplied inputs. This clarification creates no static inhabitant;
the primary checked the permitted minor-only delta.

The independently reviewed [open-package formation lemma](../theory/2026-10-13-open-declaration-package-formation.md)
supports the dependent formation step once the genuine indexed declaration
interface is supplied. It establishes identity retention only for an actual
original supplied record or its established original maps. It does not prove
that this new presentation is an unknown original J domain, or that
`(d,alpha)` captures every original proof choice. Those exact correspondence
and coverage premises remain at the original declaration owner.

No original manifest, authentic source application, complete Call theorem,
implementation or user approval was supplied by review. Adoption as the
original domain remains not ready. Static local links, fences and whitespace
checks pass; direct governing inputs stayed byte-identical. No tests, builds,
probes or measurements ran.
