# Open original declaration packages: dependent domain formation

Date: 2026-10-13
Status: independently reviewed conditional mathematical lemma; research only
Baseline: `921cbbb778e413a25ac02872939eeb9d6ff62d64`
Branch: `research/simple-sub-intrusion`
Producer: `/root/prove_open_declaration_package_formation`, prover leaf
Exclusive lease: this new file only
Authority, compiler implementation, original signature existence, parent closure: none
Budget: one leaf, at most 25 minutes; static reads/derivation only

## 1. Result and frozen objective

**Conditional result.** An independently formed original dependent contract
declaration can be retained as an open dependent package at its original
predecessor context. Formation of the package domain needs formation of its
field types under symbolic original binders. It needs no inhabitant of the
future contract domain. Retention uses the original fields, alternatives,
functions and witnesses, so it preserves every inhabitant and licensed
observation of that supplied declaration. No closed enumeration of W/Z
alternatives is needed for this mathematical operation.

This is a parametric lemma about a genuinely supplied complete declaration,
not a declaration supplier. It neither exhibits the original invoke signature
nor gives the compiler its formation, elimination, action or operational
interpretation. A common interface that ranges over multiple independently
typed declarations additionally needs their original typed indexing interface;
that interface is an input, not a consequence of the per-declaration lemma.

The stable parent remains:

```text
authentic formal-entry declaration/application preserving every independently
typed argument's complete contract and all original licensed observations;
Gamma_form^src(P) |- mu : Delta_in^orig, then intro_orig[mu].
```

Its original quantifiers, supported source domain and complete Call meaning
remain unchanged and OPEN. This note proves a feasibility lemma under explicit
mathematical hypotheses. It does not replace the missing source judgment with
an opaque `CompleteContract`, finite execution trace, new license, native
four-port demand or pre-event witness.

## 2. Governing dependencies and authority

| Exact source | Use and boundary |
| --- | --- |
| [Inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md) §§1–5, Evaluation, Authority and integration | Native Simple-sub; prove decisive invariants before dependent implementation; preserve natural inference and necessary safety. |
| [Uniform Value inlet](2026-10-08-uniform-value-entry-constructor.md) §§4.1–4.3 | Pre-challenge Desc; J comes from the typed argument; complete checked record and all observation-indexed Delta obligations; broad J/Any retains a licensed Bool Return beyond an actual Int trace. This does not adopt the id/pick constructor for invoke. |
| [Registry construction](2026-10-10-source-owned-original-registry-construction.md) §2, §§4.1–4.2 | Genuine complete local declarations remain inputs. Every field type is formed at its original predecessors. Independent W/Z and opaque parameter families are allowed at those binders; an unavailable decoder argument remains forbidden. |
| [Registry adoption](../design/2026-10-10-original-registry-constructor-adoption-proposal.md) §§1–3 | Six bounded pre-Call representation/API choices are Authoritative. Complete original local applications and `intro_orig[mu]` are explicitly unprovided. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.1–2.2, 3.2, 3.7 | Independent whole-tuple meanings, active ordinary descriptor conjunct and admission; original ordered Bind; W/Z grammar is an unselected sufficient production characterization. |
| [Carrier-domain cut](../progress/2026-10-13-invoke-carrier-contract-domain-cut.md) §§1–4 | Minimum is pre-J domain formation, not a pre-J inhabitant; no original constructor or architecture alternative is selected. |
| [Formal-entry draft](../design/2026-10-13-original-formal-entry-constructor-draft.md) §§4–6; [application cut](2026-10-13-apply-formal-entry-declaration-proof.md) §§1,3–5 | Original ordered signature, introduction, elimination/action and candidate map remain source-owned inputs. Draft is not authority. |
| [Call-input construction](2026-10-07-call-input-construction-proof.md) §3.2 | Entry-Value consumes authentic origins and port declarations before forming its ValueBind. It supplies no earlier contract-domain declaration. |

Workflow sources read: `rules/agent-orchestration.md`, especially **Model
routing and Astra escalation** and **Proof delegation and decomposition**;
`rules/research-lab.md`; `rules/design-authority.md`; `rules/compiler-engineering.md`;
`rules/git-concurrency.md`; `rules/orchestration-budget.md`; and the
`yulang-proofs` skill. Task/index records are locators, not semantics.

## 3. Mathematical setting and exact premises

### 3.1 Sorts, scopes and quantifiers

Work in a dependent metatheory with cumulative predicative universes
`U_0 : U_1 : ...`, dependent sums and products, and substitution. Evidence is
retained as typed data; no proof irrelevance, choice, proof erasure or
function-extensionality axiom is used. For `A : U_i` and
`x:A |- B(x) : U_j`, both `Sigma x:A. B(x)` and `Pi x:A. B(x)` are in
`U_max(i,j)`. In particular a type-valued slot `T : U_i` has domain
`U_i : U_(i+1)`; this level increase must be counted.

These are explicit mathematical hypotheses, not claims about executable
Yulang typechecking. No universe-size restriction on source programs is
adopted here. The lemma is level-polymorphic: each supplied declaration uses
its actual levels. It does not place contracts at every universe level into
one fixed small universe.

Quantify metatheoretically over every well-formed original predecessor
context `Gamma`, every independently supplied complete original declaration
`D` at that context, and every inhabitant of its original contract domain.
For the source application of interest, `Gamma` is the actual predecessor
context of J within `Gamma_form^src(P)`, with raw P and genuinely preceding
source/header/port parameters. It does not include J, a later typed decoder,
registration, Call result or future event witness unless its original binder
has already occurred. Fixed external inputs stay in Gamma.

`D` denotes the supplied original declaration itself, with its literal
ordered types, scopes, binders and original constructor/eliminator equations.
It is not a newly postulated object of type `CompleteContract`. A use of this
lemma must exhibit those types and their formation derivations. In this
parametric proof their names are metavariables for arbitrary supplied types.
No missing original invoke field is filled by declaring a metavariable.

### 3.2 Complete declaration premise, field by field

For a flat original record telescope, the premise is the family of judgments

```text
Delta_D = (z_1:T_1; ...; z_n:T_n)
for every i=1..n:
  Gamma,z_1:T_1,...,z_(i-1):T_(i-1) |- T_i : U_(ell_i).
```

`n` is arbitrary; no global bound is assumed. Each `T_i` is the entire
original type, including all implicit/opaque applications and their actual
arguments. Original sums retain their original label type and every arm.
Type-valued declarations, primitive contracts, provider/world families and
local law fields retain their complete types. Existing independently fixed
contracts are genuine inputs, rather than laws generated by packaging.

For a declaration with branching scope, use its actual original binder tree
`B_D`. For every binder node b, the premise is

```text
Gamma, Pred_D(b) |- T_b : U_(ell_b).
```

`Pred_D(b)` is exactly that node's ordered ancestral binder context. Its
quantifier/record constructor is the original one. A universal branch is a
dependent product at that position; a witness/record field is a dependent
sum at its position; an alternative is its original sum/indexed family.
An independently supplied primitive type already formed at a node may be
kept whole without unfolding it. This is ordinary use of an existing typed
family, not a assertion that an unspecified source primitive has that type.

There is finite declaration syntax in this setting, with arbitrarily large
or infinite domains inside products, sums or supplied primitive families.
If a declaration uses recursive types/relations, their original formation
and unfolding rules must already be independently justified; packaging does
not derive them or alter least/greatest interpretation. A merely circular
claim of formation is not this premise.

All originally shared operands occur once in their owning binder context
and are referred to from later fields. If a field originally contains
`Sigma w:W. Pi e:E(w). Q(w,e)`, that entire order is retained. It is never
replaced by `Pi e:E. Sigma w:W. Q(w,e)`. If a witness is originally chosen
inside a response/event/future branch, it remains there.

### 3.3 Substitution and action premises

For ordinary capture-avoiding substitution, supply an actual typed context
substitution `sigma : Gamma' -> Gamma`: if Gamma has fields
`x_i:A_i(x_<i)`, each component has type

```text
Gamma' |- sigma_i : A_i[sigma_<i/x_<i].
```

All shared occurrences use that one substitution; its lift beneath a binder
retains the binder and substitutes only its predecessors. No marginal
fieldwise witness selection is allowed.

For an original semantic action, the additional premise is the actual
whole-package action on the already supplied original domains:

```text
S_alpha : O_D -> O_D'
S_id(j) = j
S_beta(S_alpha(j)) = S_(beta o alpha)(j).
```

Here `O_D` is the original domain obtained from D's explicit telescope;
`O_D'` is the actual target declaration at its lawful target context. These
equations are pointwise equations of retained original records/functions
(or their given original observational equations), not an assumption that
arbitrary coordinate changes preserve contract validity. If an action changes
provider/admission coordinates, its original domain certificate and all
required hypotheses remain necessary. The lemma derives no such certificate.
Identity formation needs no nonidentity semantic action premise.

### 3.4 Semantic consumer premises

For each actual original licensed observation/admission/receipt/Force/rebind
consumer c, at its original event context, its supplied complete type is
written parametrically as

```text
E_c : Pi j:O_D. U_(e_c)
R_c : Pi j:O_D. Pi eta:E_c(j). U_(r_c)
use_c : Pi j:O_D. Pi eta:E_c(j). R_c(j,eta).
```

`E_c(j)` is c's entire original event/operand telescope and `R_c(j,eta)`
its actual result type. Original licensed observation relations can instead
be type families at those same arguments; this does not assert they are
inhabited. These are notation for real supplied consumers, not universal
invocation soundness hypotheses or additional compiler laws. Preservation
below is identity preservation for each supplied consumer. Existence and
completeness of the source consumer inventory remain separate evidence.

## 4. Formation and identity preservation lemma

**Statement.** For every Gamma and D satisfying §3.1–§3.2, form the package
domain `C_D` at Gamma by retaining D's original dependent record expression.
There are maps `enc_D : O_D -> C_D` and `dec_D : C_D -> O_D` retaining every
original field, branch and function, with pointwise two-sided identity and
with every supplied consumer of §3.4 unchanged. Domain formation needs no
`j:O_D` or `p:C_D`. Under §3.3, syntactic substitution commutes with
formation and identity packaging; each original lawful semantic action
transfers with the same domain conditions and composition equations.

**Formation proof.** For the flat telescope take

```text
C_D = Sigma z_1:T_1. ... Sigma z_n:T_n. 1
```

where `1:U_0` closes the record and is not an original semantic witness.
From the last formation judgment form `Sigma z_n:T_n.1` in its predecessor
context. Repeat backwards until the outer sum is formed at Gamma. The level
is `m=max(0,ell_1,...,ell_n)`. Each rule uses the symbolic binder z_i; none
requires a term of `T_i`. Empty field domains are allowed. Hence a domain
with no inhabitants can be formed at precisely the same scope.

For branching declarations apply the same construction structurally at the
original nodes, using products for universal branches and the original sum
constructors for alternatives. The already supplied formation judgment of
each domain is used only under its actual predecessor context. Primitive
formed families are retained directly. The universe level is the maximum
required by the original finite expression, including `ell+1` for any slot
whose domain is `U_ell`. This derives domain formation from the displayed
field formations. It does not assume the conclusion `Gamma |- C_D type`.

**Identity proof.** Choose the same original dependent record presentation
for `C_D` and `O_D`; encoding and decoding are definitionally the identity
on that record. In particular a function field f is retained as f, without
eta expansion or replacement by a pointwise-equivalent function. An original
branch tag and its full dependent arm are kept together. No equality of witness
proofs is decided and no new witness is selected. This proves preservation
even for a dependent consumer whose domain mentions the original function
field itself, not only its pointwise outputs.

If an implementation instead introduces a separate named wrapper, its exact
introduction/projection beta and record eta laws must establish the same
two-sided identity (with dependent transport where necessary). Those wrapper
laws are not derived from similarity of field names. They are not needed by
the mathematical identity presentation here. No equality with a separately
fixed opaque nominal domain is inferred without its actual original map.

For any `j:O_D`, set `p=enc_D(j)`. In §3.4's consumer notation define

```text
E_c^pkg(p)     = E_c(dec_D(p))
R_c^pkg(p,eta) = R_c(dec_D(p),eta)
use_c^pkg(p,eta) = use_c(dec_D(p),eta).
```

At `p=enc_D(j)` these have the original domains, result types and output
fields at the same eta. This applies to every original consumer and every
original licensed alternative, including an observation without an actual
execution witness. It proves neither that j exists nor that a particular j
meets a separate Delta admission/checking obligation. QED for formation and
identity preservation.

**Substitution proof.** Dependent sum/product and original family application
formation commute with the one capture-avoiding substitution. Induct on the
same original expression to obtain `C_D[sigma] = C_(D[sigma])` with original
binder lifts. Enc/dec are the same retained identity terms after substitution.
For type-valued fields, substitution acts on that same field and all its
dependent uses. It does not substitute separate endpoints independently.

**Semantic action proof.** Transfer the given original action by

```text
A_alpha(p) = enc_D'( S_alpha(dec_D(p)) ).
```

Its complete domain is the supplied original action domain. Two-sided
identity cancels the intermediate `dec_D'(enc_D'(...))`. Therefore
`A_id(p)=p` and `A_beta(A_alpha(p))=A_(beta o alpha)(p)` follow from the
original pointwise equations. Any changed world/provider/witness is exactly
the one the original action produces. Original domain/admission certificates
are retained, not derived from packaging. QED.

## 5. What open means; no closed alternative census

For an original alternative family whose complete declared type is

```text
Gamma |- L : U_l
Gamma,a:L |- Arm(a) : U_a
Gamma |- Sigma a:L. Arm(a) : U_max(l,a),
```

L may be infinite, externally supplied, or abstract with no visible
enumeration. Retaining this family forms the domain without listing L's
inhabitants. For every tag a and original `w:Arm(a)`, identity encoding keeps
that same a,w and every dependent field. An unknown W/Z family is retained
with its full original declared type; it is never interpreted as having no
alternatives. Unknown field formation, however, is still missing evidence.

For a genuinely supplied original family of declarations, let its original
index/interface type and domain family be

```text
Gamma |- I : U_i
Gamma,k:I |- O_k : U_m
```

with complete declaration and consumer fields retained at k's predecessors.
Then its original open dependent package is `Sigma k:I. O_k : U_max(i,m)`.
The previous proof applies at every k and preserves `(k,j)` by identity.
No finite or closed census of I is required. Universally quantified k is
instead retained as a product when the original declaration uses that order;
this lemma does not convert it to a sum.

If an original interface permits a type-valued domain parameter
`T:U_m`, a package `Sigma T:U_m. ...` lives at least in `U_(m+1)`.
Thus accepting an open typed family is mathematically different from assuming
`U_m:U_m`. Keeping a universe-polymorphic family avoids that false equation;
an interface spanning an unbounded hierarchy cannot be represented by one
small package without an additional independently justified universe theory.
No such theory or restriction is selected for Yulang here.

The conclusion quantifies over **all inhabitants of each original supplied
declaration**, and over every index of a supplied original declaration family.
It does not manufacture a common typed index I or prove that a proposed I
covers every original argument contract. Such coverage, if required by the
actual `C_J`, is a separate source-interface premise. Introducing a new I
whose inhabitants are only an easy subset would fail the original parent.

Source-contracts §3.7's particular `H_G(R)` grammar is unnecessary for this
retention lemma. If an original declaration uses it, retain R,G,W,Z and all
its arms. If a different independently typed original contract is supplied,
retain that contract. The note does not prove grammar equivalence, conservative
abstraction correctness or exhaustion of an unspecified source kernel.

## 6. Complete event scopes and shared witness preservation

The structural proof retains the original tree rather than flattening it.
For a local original universal response block, at an already formed original
prefix eta, one possible *given* original order is

```text
Resp(eta)                         : U_r
r:Resp(eta) |- RawResume(eta,r)    : U_k
r,k        |- CurrentWorld(eta,r,k) : U_w
r,k,w'     |- Future(eta,r,k,w')   : U_f
r,k,w',f   |- Evidence(eta,r,k,w',f) : U_e

Pi r:Resp(eta).
Pi k:RawResume(eta,r).
Pi w':CurrentWorld(eta,r,k).
Pi f:Future(eta,r,k,w'). Evidence(eta,r,k,w',f).
```

Each abbreviation denotes its supplied original complete type, at the shown
predecessors. This example illustrates product formation; it asserts no
concrete signature or binder order for invoke. If the original rule restricts
worlds/futures by a dependent compatible-world/evidence domain, that entire
domain is retained. If its order is different, the actual tree is used.
Universal responses remain universal, not a finite response sample or a
preselected response. Witnesses chosen beneath r,k,w',f stay beneath them.

Operation/declaration instances, output providers, raw handles, pending
suffixes and original licenses occurring in eta are that same original eta
in every branch. If a pending suffix instead has its own later binder, it
stays there. At a Request, neither encoding nor decoding runs the raw handle,
chooses a response, repeats receipt, replaces the unfinished suffix or fixes
a future world. At Return it retains the same decorated value and its
current-world/provider/certificate fields. It does not replace J's original
payload inclusion by a new independently chosen inclusion.

In particular the original Bind meaning from source-contracts §3.2 remains

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S).
```

The package changes none of these operands. A shared outer witness serving
both observation and descriptor membership is retained once; admission,
membership and ordinary `DescMem` are not proved by choosing compatible
projections separately. Every dependent guard of `delta_check` stays under
its original observation/response/resumption/future binder. Identity
preservation supplies no guard proof missing from the typed argument.

The broad J/Any discriminator is preserved immediately: a J licensing a Bool
Return retains it even if the carrier's actual Force returns Int. Encoding
uses J's original complete relation, not that carrier's actual trace set.
No observation is removed to make the formal body safe.

## 7. Source and operational bridge ledger

| Owner/consumer at pinned baseline | Evidence and exact remaining premise |
| --- | --- |
| Original contract declaration owner; registry construction §2 and §4.1 | The lemma accepts the owner's actual complete typed declaration, each predecessor formation, primitive/action law and original consumer. No such full invoke input is constructed here. |
| Original formal-origin/carrier/entry-port owner; adoption §2; formal-entry draft §4 | Must supply the genuine pre-J interface/domain, full original telescope, introduction/eliminators, laws and lawful target domains. Then every actual static substitution term must be checked. The lemma supplies no term of an unknown telescope. |
| Header-Parameter → Declare-Owned-Port → FormalOwner-Ports → Assemble-Value-Entry → Register-Parameter; registry §§4.1–4.2 | Adopted API retains full declarations at original binders. Identity packaging can retain a declaration already supplied here. API presence and package feasibility do not establish its actual application or equality with an original judgment. |
| Entry-Value; Call-input §3.2 | Consumes authentic ParameterOrigin and carrier/receipt/Force/rebind declarations; forms Receive → Receipt → designated Force → typed rebind/ValueBind. No original domain is introduced by this consumer. |
| Uniform inlet §§4.2–4.3 | Typed argument supplies J, provenance/Car, same-result inclusion, whole port map, static and universally event-indexed checks, and current guards. Packaging retains those fields if supplied; no pre-J inhabitant is required and no check is synthesized. |
| `crates/yu-hir/src/module/local_source.rs:154`, `:257`, `:636` | `LocalSourceParameter` and `form` retain actual identity/scope/annotation; parameter is bound before body; Name follows that lexical edge; Integer retains token. Syntax/scope evidence supplies no semantic contract-domain type. |
| `crates/yu-solver/src/candidate_source.rs:187`, `:394`, `:532`, `:660` | Formal/Name share recipe registration; Apply retains authentic source children/positions/checking; parameter native root is initialized; scheduled `Action::Candidate` calls `admit_candidate_fact`. Real activation is present, beyond stored metadata. No original dependent contract package is introduced on these inspected paths. |
| `crates/yu-solver/src/shadow_apply.rs:1312` | Validates ApplySourceInput correspondence, forms the negative Function demand, records provenance and calls `constrain_live_value`; submits callee/invocation effects to application effect. This is native generation/accumulation, not original domain introduction or complete replay/soundness evidence. |
| `crates/yu-solver/src/candidate_call.rs:16`, `:206` | Source/native record types and `pending_construction` expose missing suppliers. Their inventories do not construct a domain, decode an original contract or prove all relevant original supplier paths absent. |

**Established static bridge:** actual source occurrence/scope → native
registration/Apply recipe → scheduled native demand/effect submission at the
inspected owners. **Conditional bridge:** supplied complete original
declaration → its unchanged dependent package and typed eliminations.
**Missing bridge:** original source owner → actual pre-J domain/declaration
and complete substitution → authentic entry introduction → complete Call
and semantic native consumer correspondence. Complete activation/replay,
levels/extrusion/intrusion/generalization and public publication are not
proved by either bridge in this note.

## 8. Falsifiers, economy audit and next action

A falsifier of the mathematical claim must provide a genuinely well-formed
original declaration in the stated metatheory whose unchanged dependent
record cannot be formed at its predecessors, or an original inhabitant or
licensed observation lost by identity encoding/decoding. A future/self
argument in a field's domain violates the explicit premise; merely missing
formation evidence is not such a counterexample. Requiring a fixed small
universe to contain itself or all higher universes would exceed the stated
sort rules. Promoting that requirement to a source rule would need authority.

Discriminators for a proposed application: check that no universal response
has become an existential choice, no shared witness moved beneath/before its
original binder, no domain changed after observing J, no proof alternative
was quotiented, and every original broad licensed observation survives. For
nonidentity action, check its real target domain and certificate rather than
assuming unchanged admission from type or membership containment.

Prior original-kernel/application and source-owned grammar attempts left the
same authentic declaration supplier untouched. Under the existing economy
audit, the actual well-scoped entry/complete Call is A correctness and B
natural inference for the original parent. A closed W/Z enumeration is not
established as a necessary premise of dependent retention; §3.7 is a sufficient
conditional characterization. Recovering full contracts from native endpoint
IDs or actual traces would create D reconstruction debt. The present lemma
does not alter any obligation class or close a gate. It answers the distinct
mathematical feasibility question instead of repeating source reconstruction.

**One next action:** the primary should obtain the original typed argument
contract interface at the formal predecessor scope, including its complete
declaration/index domain (if family-indexed), original eliminators, observation/
admission/action laws and actual typed source arguments. Apply this lemma to
that supplied interface and check its complete substitution. If none is
selected, a fully specified interface proposal still needs the existing
independent review/authority path; this lemma alone authorizes no implementation.

## 9. Checks, dependencies, resources and unverified scope

Checks performed: initial absence of leased path; read-only HEAD/branch/status;
bounded exact-source reads; manual dependent sum/product formation,
substitution and pointwise identity derivation; exact Rust producer/activation/
consumer inspection; SHA-256 dependency capture and pinned byte comparison
of 21 direct repository inputs (all equal to the pinned bytes).
No tests, builds, probes, executable proof assistant or decidability check ran.
Some initial batched captures truncated; decisive policies and constructor
sections were reread with bounded output. No absence claim relies on a
truncated search. No original signature is invented from these reads.

Direct proof and bridge hashes at baseline:

```text
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb  notes/theory/2026-10-10-source-owned-original-registry-construction.md
2d6439507f01f38234909f98d86b1d2fbe31d3c7dd60d453cf1c199604020451  notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
d56ea1b5d508899ddf087d34ceba03a0ffe1b306ef12b991f29008b27c258e1c  notes/progress/2026-10-13-invoke-carrier-contract-domain-cut.md
4d70159a94ef1ac0d6f62b1bcc7990a5b783367a1915914bdba2334c0f532f5f  notes/design/2026-10-13-original-formal-entry-constructor-draft.md
4da9916f6fe1b9070cd2d53c2f9afed331d8fc25e5598cf4389de7f8d88ec153  notes/theory/2026-10-13-apply-formal-entry-declaration-proof.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35  crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411  crates/yu-solver/src/shadow_apply.rs
```

One leaf, no descendants and no specialist contact. Zero Cargo/heavy processes,
test cases, semantic probe cases or measurement samples. Short static reader
calls only; CPU/RSS uninstrumented; wall time below the assigned 25-minute
bound. No other output path or shared record edited; no Git mutations.
Writes stop on submission and independent review belongs to the primary.

Requested route: prover / normal `gpt-6.1-sol` / high. Configuration registers
prover and supplies Sol/high defaults; prover.toml leaves model/effort unpinned.
The callable schema exposes prover and this leaf received the proof contract.
Observed effective model/effort metadata: unknown. No override, Astra or hot
reload is claimed.

Unverified: the actual original invoke declaration/index domain and introduction;
full source application, typed semantic decoder/action supplier and consumer
inventory; actual argument checks and independent admission; complete Call,
effect hygiene, soundness, required principality, termination, executable
typechecking/decidability, lifecycle replay, levels/extrusion/intrusion/
generalization, source acceptance, public extraction and F5 production cutover.
The conditional lemma received fresh independent mathematical review below.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-13-open-declaration-package-formation.md`.
- Baseline SHA: `921cbbb778e413a25ac02872939eeb9d6ff62d64`.
- Changed dependency hashes: none in the compared frozen direct inputs; recheck at integration if HEAD moves.
- Claim/review status: independently reviewed conditional mathematical lemma and bounded source bridge; parent remains OPEN; no producer certification.
- Checks already run: static rules/source inspection, manual formation/identity/substitution/action derivations, read-only HEAD/status, dependency SHA-256 and pinned byte comparison; no tests/builds/probes.
- Proposed checkpoint message: `research: derive conditional open declaration package formation`.
- Shared-record deltas left to primary/curator: record this feasibility lemma with its precise supplied-declaration and family-index premises; closed W/Z enumeration is unnecessary for this lemma; retain the original pre-J supplier, authentic application/decoder/action and complete Call parent as OPEN. No shared record was changed.

## Primary independent review and application

Fresh `compiler_referee` `review_open_declaration_package_proof` reviewed the
frozen producer artifact at SHA-256
`80fcb05827dd7d6b1b6e16957c1af4043fb4f2a6b833de514dc72c369500abdb`
and reported no blocking, major or minor finding. Review covered the exact
conditional theorem, predicative universe bounds, identity presentation,
dependent consumers, one joint substitution, supplied whole actions and
original alternatives/event scopes. It also independently inspected the
bounded source bridge's cited producer and native demand/effect consumers.
Full lifecycle/replay, source admission and production inference remain
outside that review.

The primary applies the lemma to the open-interface proposal only at its
mathematical formation step: a genuinely supplied declaration-index type and
predecessor-typed argument family permit the proposed dependent package type.
The lemma does not identify an unknown original contract domain with that
package. Coverage, original presentation identity/proof choices, actual schema
and action suppliers, complete substitution and `intro_orig[mu]` remain at
their original owners. The parent gate remains OPEN; no implementation follows
from this application. Task and laboratory records are synchronized by the
primary checkpoint.
