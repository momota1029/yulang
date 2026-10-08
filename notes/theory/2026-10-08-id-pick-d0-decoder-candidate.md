# D0 for `id` / captured `pick`: missing public descriptor clauses

Date: 2026-10-08
Status: Unreviewed research candidate and bounded supplier audit
Baseline: `d67fab6fbd81837a0be15b1cf35b06a6e1046f16`
Branch at assignment: `research/simple-sub-intrusion`
Exclusive lease: this file only; writing stops on submission
Authority, semantic adoption, compiler implementation and gate closure: none

## 1. Objective and result

Determine whether the committed authorities supply a source-free ordinary
descriptor for `Sigma_id = forall a. a -> a` with typed result selection,
and `Sigma_pick = forall a. a -> B_z` with fixed public capture incidence.
Method: invert the named descriptor suppliers and separate their construction
premises from their established outer membership rule; then specify a D0
candidate family at the missing interface. Analytic witnesses discriminate
unselected clauses. No executable transition model is added.

**Bounded finding:** the inspected rules supply neither a complete public
descriptor formation rule from these inputs nor its independent admission
and observation clauses. This is not a repository-wide absence theorem.
There is an established same-provider Function membership meaning; D0 must
fill its independent descriptor inputs, rather than replace that meaning.
The candidate below is a clause-level proposal with explicit primitive and
formation premises, not a public-sufficiency theorem. Several choices remain
unselected. No alternative is selected here.

## 2. Authority and already selected meaning

The integrated [root-policy q1/a1](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md)
decision items 1–5 and its [receipt](../../questions/2026-10-08-successor-generalize-root-policy/receipt.md)
choose a transformed/displayable actual public scheme with necessary extra
use information. Sufficiency is a goal; concrete semantics, representation,
algorithms and implementation remain subject to separate approval. An import
whose meaning is the full source relation under another name fails this goal.

The following exact source sections govern this bounded audit:

| Source | Established content and limit used here |
| --- | --- |
| [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5 | Distinct written/internal/public layers; source-formed slots, paths and shared `xi=(nu,K,D)`; actual roles; independent admission. Detailed formation and exhaustive production semantics remain open. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.1–2.2, 3.1–3.7, 5.3 | Generic independently interpreted clauses; active constrained-root hypothesis; independent `DescMem`; source/admission inventory; possible exhaustive positive Option 2 grammar; additional actual-root resolver hypothesis. These concrete clauses remain unselected. |
| [Source result synthesis](../design/2026-10-02-source-result-synthesis-choice.md) §§1–3 | Value entry forces/rebinds once, including an unused argument; Value result is pure introduction; known Computation interface is forwarded; latent results are not recursively forced. These source choices are selected. |
| [Contextual membership definition](../design/2026-10-08-contextual-function-membership-definition.md) §§1–4, selecting [input realization](2026-10-08-call-semantic-input-realization.md) §3.1 | Selected outer Function value membership on the same actual provider, with universal independent complete challenges and actual observations. Complete descriptor/admission/observation relations remain independent inputs. |
| [Native source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–4 | Source-owned templates, fixed external anchors and exact lawful source uses are selected before public projection. Public projection and production Direct are expressly separate. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6–9 | Conditional typed primitive and complete-invocation presentation; body/result differs from full invocation. Draft outside selected source premises. |
| [Coupled core](../design/2026-10-01-coupled-effect-interface-core-draft.md), “Candidate Function contract over the same relation” | Independent punctured-context formulation and all finite prefixes; explicitly a candidate, not the missing public decoder rule. |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) Gates D–E, §§18, 21, 24 | Representation follows coherent semantics; separate approval before implementation; actual role, ordinary Value entry and latent forwarding preserved. |
| [F5 foundation](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md) §§1–2 | Closed pure scheme machinery excludes effectful admission, roles and dynamic dependencies. Printing its arrow is not D0 for the approved successor envelope. |
| [Reviewed transformed-export candidate](2026-10-08-id-pick-transformed-public-export-candidate.md) §§3–5; [earlier bridge](2026-10-08-id-descriptor-source-bridge.md) §§4–6 | Source-base selection rewrite and finite public interface candidate; S1/S2 descriptor formation/activation remains a premise. This note does not claim another proof of that rewrite. |

The committed design index was a locator only. Dirty shared coordination and
the pending `readinvoke-source-presentation` question were excluded. The
production Option A and Option 2 [receipts](../../questions/2026-10-05-production-function-denotation/receipt.md)
and [membership receipt](../../questions/2026-10-05-production-function-bound-membership/receipt.md)
retain independent whole-tuple interpretation and allow licensed extras; they
do not choose a complete extra grammar or admission rule.

In particular, preserve the selected contextual definition's membership
meaning verbatim:

> A callable value meets a complete Function descriptor when that same actual
> callable realizes its independent contract. Retain its actual decomposition
> `Act(v,U,r)`; do not recover U from the checked type's printed shape.
> For every independently admitted complete challenge of that value, membership
> requires:
>
> 1. acceptance by U of that challenge's same whole carrier, with its original
>    typed receipt/context preconditions at the challenge's live event;
> 2. every complete or pending observation and admitted continuation/future
>    development of U's actual complete invocation to satisfy the descriptor's
>    full observation contract and joint hard envelope.
>
> These obligations range over each genuine actual decomposition retained by
> the value, rather than choosing a convenient provider after a callee returns.

The selected input-realization §3.1 additionally covers administrative and
zero-step observations, compatible future-event restriction, and every
retained actual decomposition. Candidate `D_r,P_r,DescMem_r` below are inputs
to this meaning; membership is not redefined to make the public ports fit.

## 3. Proposed D0 formation interface and explicit premises

Envelope: the reviewed candidate's finite, immutable, nonrecursive ordinary
Value-parameter Lambda, with one resolved terminal Name, outside callback
literal position. `pick` uses the same existing captured value at its original
monomorphic contract. The construction certificate may inspect source once;
use may not traverse source. No raw-source compiler acceptance is claimed.

The following is **candidate rule syntax**, not an existing constructor:

```text
ProjectionExportCert(Sigma,sel,imports; original scopes)
IndependentKernel(L)        LegalExistingFunctionPresentation(L; ports,clauses)
FixedImportCert(imports)    WholeInstantiationCert(rho; scopes,xi,incidence)
-------------------------------------------------------------------- D0?
Decode(rho(Sigma,sel), imports, L) = r_u : OrdinaryFunctionDescriptor
Expose(r_u) = (ports_u, D_u, Base_u, Extras_u, Guard_u, DescMem_u)
```

`ProjectionExportCert` is publication-time proof of the selected source
envelope, actual Pure role, Value entry, Value result consumer, endpoint
sharing and resolved result selection. It is not a retained source relation.
`sel=FormalResult` or `sel=FixedCapture(j)` is a finite typed schema index;
`j` references an actual public contract, never a source-definition handle.
Whether a uniform decoder can omit some schema fields is unproved.

`ports_u` exposes the whole-carrier/actual receipt and receiver, rebound value
`A=rho(a)`, body result `Comp(empty,B)`, complete invocation, typed responses,
raw resumptions and returned-provider future-demand ports. `B=A` for `id`;
`B=B_z` for `pick`. The latter endpoint, provider and its transitive contract
dependencies stay fixed. The body `empty` guarantee is not a complete-call
empty-effect bound. Pure role is supplied by construction evidence for this
envelope; Value entry alone never establishes Pure for arbitrary callables.

`L` is the independently interpreted typed observation/primitive kernel,
including contracts and licenses, not an arbitrary per-export predicate
program. The candidate is finite in schema size plus its explicit imports;
no finite bound or sufficient canonical representation for import contracts
has been established. `LegalExistingFunctionPresentation` is a missing
formation supplier: the existing fields must legally expose these predicates
at `r_u`. Naming it does not prove it or authorize a new descriptor kind.

`WholeInstantiationCert` freshens local `a` and all eligible incident operands
once, retaining original binder order and one shared `xi`. Imported fields,
provider identities, challenge domains, capture permissions, operation
witnesses and scopes do not freshen. Any binding connecting `a` to a fixed
outer coordinate remains active. No independent port-wise existential hiding
or runtime-per-challenge choice is supplied by D0.

## 4. Candidate admission and independent ordinary descriptor clauses

The entries in this section are **proposed fillings of independent inputs**,
not newly established semantic rules. They explicitly expose where a kernel
supplier is still needed. For a fixed instantiation frame, `h` is the entire
original joint challenge/history tuple, not a list of its endpoint types.

Candidate admission is generated by these four constructors:

| Constructor | Required premises and output |
| --- | --- |
| Initial | Independently valid compatible punctured context, valid other-value environment, actual registered callable/carrier holes and original incidence, and `CarrierOK(A,t,e)` at the live event. Assemble the same complete challenge with the actual receipt preconditions; include fixed-import validity for `pick`. No actual-U acceptance, successful execution, output safety or `Direct` premise. |
| Response | An already exposed original operation witness and independently typed response, with the original response endpoint, context and actual current configuration. Extend that same history. |
| Raw Resume | The same exposed raw handle, its independently admitted response/resumption contract and live configuration. Extend its history without replaying receipt or choosing a new continuation. |
| FutureUse | An actually returned provider at its designated typed port and an independently admitted compatible demand, retaining its identity, original contracts and joint dependencies. Use the demand's current configuration. |

`CarrierOK(A,t,e)` requires the carrier's own independent finite-interaction
contract: all its completed payloads meet `A`; all its pending prefixes,
requests, response and raw-handle interfaces, typed paths and joint hard
conditions are valid. It has no required Return or inhabited-result premise.
The original carrier may diverge. This is an exact supplier obligation, not
an assumed decidable predicate. Hereditary/recursive provider contracts must
use their existing selected interpretation or an independently supplied law;
positivity or this four-case list alone does not establish it.

At the same ordinary root the candidate is

```text
D_u(h;xi) = Admit_u(h;xi)

DescMem_u(O,w;xi) =
  TypedEndpoints_u(O,w;xi)
  and ActualInterface_u(O,w;xi)
  and TypedEventGuards_u(O,w;xi)
  and PhaseGuarantees_u(O,w;xi)
  and OriginalScopeAuthorityDependencies_u(O,w;xi)

P_u(h;xi) = { Pi_xi(O) |
  CompleteRules_u(h,O,w;xi) and DescMem_u(O,w;xi)
  at the original witness scopes }.
```

These are candidate ordinary descriptor leaves with the following exact
intended independent meanings:

| Leaf | Required interpretation, separate from source-base generation |
| --- | --- |
| TypedEndpoints | Completed rebound payloads satisfy `A`; body/invocation result values satisfy `B`; every latent returned provider satisfies its original complete typed contract on all independently admitted compatible future demands. Prefixes impose their pending-port obligations without requiring a Return. |
| ActualInterface | Retain the actual registered callable/receiver, Pure role and Value entry of this publication, the actual receipt and designated Value-result/invocation consumer. A typed invocation Return requires the independent entry-completion/rebind event witness at that same activation. |
| TypedEventGuards | Each emitted request carries its independently licensed original instance, typed arguments/responses, raw continuation and current configuration; resumption retains its original handle and pending interfaces. Every phase/receipt/rebind event is checked by its local typed rule. Matching endpoint IDs cannot supply the witness. |
| PhaseGuarantees | The projection body has the selected pure Value-result guarantee. Full invocation includes entry demands licensed by the whole argument's contract and its actual source/receiver incidence. Future latent demands are checked at their own provider ports. No body guarantee is applied indiscriminately to entry or future events. |
| OriginalScopeAuthorityDependencies | All symbolic `nu,K,D`, shared endpoints/providers, capture/import incidence, typed visibility and original scope/lifetime predicates hold jointly. A request family name or stored lineage supplies no active capture grant. |

These clauses do not mention `Base_u`, source execution, or the wire's image.
For example, type/operation/authority judgments must already have independent
meanings before interpreting this descriptor. Their local constructor laws
must prove each source-base observation satisfies the conjunction. If such a
law is absent, the candidate remains conditional; it cannot define a leaf as
“whatever the projection schema emits” to complete the proof.

`ActualInterface` and `PhaseGuarantees` require concrete declarative local
rules for entry-completion and phase incidence. The existing source rules
determine actual execution in this envelope; the independently interpreted
descriptor counterparts are still a D0 supplier. A phase tag is not that
supplier. Likewise endpoint shape does not establish result-provider identity.

The universal actual-provider obligations quoted in §2 remain the selected
outer membership rule. The new admission constructors, endpoint/event leaves
and their activation in an ordinary descriptor remain candidates. Testing a
checker that assumes these leaves would establish only consistency with L.

## 5. Separate source base, production extras and unselected alternatives

`Base_u` can use two fixed uniform typed schema programs, justified at
publication by the reviewed source rewrite:

```text
Receipt(p,t,e);
Force(t) >>= (v,C_current).
  Rebind(v,C_current);
  ValueResult(select(sel,v,captured_j),C_current);
  InvocationReturn
```

They are shared constructor schemas, not copied source definitions. Their
typed primitive contracts and current-state Bind law remain genuine premises.
The selector returns `v` for `id`, the actual fixed `captured_j` for `pick`;
it executes neither returned latent provider. Source-base membership entails
exact selection; it does not define ordinary `DescMem_u`.

Production `CompleteRules_u` must additionally account for every independently
licensed Option 2 alternative. Two **candidate construction approaches** are
left open:

1. A declared finite independent production-rule inventory at this root,
   including primitive extras and their typed interfaces, with complete guard
   checks on every conclusion and separate admission certificates.
2. Source-contracts §3.7's proposed positive `H_G(Base_u)` construction with
   independently interpreted `W,Z` and complete `G`. The `Z` arm permits
   unanchored extras. A `W` witness includes all changed and fixed operands,
   original scopes, introduced providers and future-domain certificates.

Neither grammar is selected. The second retains fixed universal provider
contracts outside its recursive operator; no universal quantification over
the growing membership relation is smuggled into a finitary rule. Concrete
`W,Z`, licenses, complete bounds and exhaustive inventory are absent from this
assignment. Setting them empty does not verify an unspecified production root.

An orthogonal unresolved choice is how result selection constrains extras:

| Candidate | Constraint on production-only result providers |
| --- | --- |
| S: selection in hard descriptor guard | Every completed result has the selected rebound/captured provider; extra traces still need independent licenses and may lack source derivations. |
| T: selection in source base only | An extra may return another independently typed provider satisfying the full fixed output/capture contract and all guards, when an independent extra rule explicitly licenses it. Type `B` alone is insufficient. |

Both preserve exact selected source behavior. Option 2 permits extras; it
does not settle S versus T for these projected exports. T cannot freshen or
replace `pick`'s original imported contract; any different provider must be
licensed against that same contract with its complete authority and future
domains. If that fixed contract already requires provider equality, T allows
no replacement. S must not covertly demand a source witness for all extras.

No lower bound on alpha follows from these alternatives. A less precise
uniform contractual arrow could discard selector information if approved
natural inference, safety and principality allow it; that route needs its
own abstraction proof. Choosing S or T and their effect on ordinary queries
requires a concrete independently reviewed design and user approval before
adoption. Existing source entry/result meaning is already selected.

## 6. Named witnesses and conditional deductions

The witnesses below are analytic decorated-kernel discriminators, not compiler
runs or newly discovered raw-source acceptance failures. They use only the
specified source laws and explicit independent-contract hypotheses. No seed
or enumeration range exists. They falsify named shortcuts, not all D0 variants.

**W-entry-prefix (one request, no Return).** Assume a lawful carrier `t` whose
first designated Force produces `Request(q,C,k)` and whose continuation never
returns. Assume no eligible ambient handler for q. `pick` must enter/force the
unused argument, so its complete invocation has a finite q prefix despite its
pure constant body. A candidate `PhaseGuarantees` applying body `empty` to
the complete invocation rejects that source-base prefix. A candidate Initial
rule requiring a returning payload rejects the independently admitted carrier.
One request is minimal for separating a complete-call effect guarantee from
a pure-body guarantee. This does not choose a new request license: the lawful
carrier and original operation contract are premises.

**W-extra-selector (two providers, one Return).** Fix two independently valid
immutable latent providers `p0,p1` at the same B and shared non-coverage
contract. Give the single independent extra rule a license to return p1 after
lawful entry; the source-base selector returns p0. Suppose the fixed public
contract permits both and every other guard holds. T admits this licensed
extra; S rejects it on provider identity. Two distinct providers and one
Return are minimal to distinguish S/T; no execution of the extra as source
is assumed. If the imported contract demands equality, the witness's explicit
premise fails, and no distinction follows. The witness demonstrates the
unresolved design choice, not that S or T is inconsistent with Option 2.

**W-shared-import (two uses, one fixed contract).** Let the fixed captured
contract require an output provider with latent guarantee `Read` at its
original instance and shared dependency. A proposed use freshens that import
and gives the second instance guarantee `Write`, allowing a Write future
request forbidden by the original fixed contract. The new provider may still
have matching erased B. This falsifies the candidate mutation “freshen every
printed/incident field,” under the independent distinct Read/Write licenses.
It supplies no proof that finite public import summaries are sufficient.

**W-query-owner (two roots, one missing evidence rule).** Let `r_hidden` and
`r_u` have extensionally identical independent `D,P`, and let a sound resolver
have a certificate rule at `r_hidden` but none at `r_u`. No inspected supplier
mandates the missing rule. A successful hidden-root comparison then coexists
with failure at the actual export. This is a minimized resolver countermodel
to “semantic equality supplies actual-root Direct”; it is not a Yulang
program or an authorized ordinary-behavior restriction.

Conditional deduction for the proposed guard: if every typed primitive image
in `Base_u` satisfies all five independent leaves in §4, and local Bind/receipt
transport preserves them with the original scopes and current configurations,
then every finite source-base derivation satisfies `DescMem_u`. Induct on the
finite derivation; use the local image law at each leaf and the transport law
at composition. This is precisely the local typing premise needed by
source-contracts §2.2. It is not established here: the D0 local descriptor
image laws remain unsupplied. Extending the conclusion to `CompleteRules_u`
also needs a guard-preservation proof for every declared production arm.

The quoted contextual membership rule supplies universal actual-provider
checking once independent `D_u,P_u` exist. It neither supplies these missing
image laws nor proves the decoded root is legal, admits the complete original
context domain, satisfies production containment, or factors all valid views.

## 7. Actual use ports, owner handoff and stopping condition

Every descriptor, admission, source-base, production, guard and import leaf
must be active at **the same actual decoded `r_u`**. Use freshens eligible
local coordinates jointly, conjoins the caller's original constraints, and
submits `Direct(r_u,F_use)` before one whole `Pi_xi`. For source-contracts §5.3's
candidate sufficient query rule, the resolver needs finite `Eq` evidence for
complete admission, `Le` evidence for complete membership including actual
`DescMem`, imports and all production alternatives, and one scope/incidence
map with matched actual role/entry/consumer. This remains an independent
resolution-conformance premise, not part of a source rewrite theorem.

Precise owners/options handoff:

| Missing supplier | Owning responsibility / required next evidence |
| --- | --- |
| Ordinary descriptor formation | Public-projection design owner: decide legal exposure of §4's independent leaves in the existing Function presentation, or supply a different source-free rule. No source pointer at use. |
| Complete admission | Independent context/carrier/contract owner: supply Initial/Response/Resume/FutureUse assembly and hereditary contract laws for every compatible original context; no filtering by actual success. |
| Descriptor leaf laws | Typed primitive/descriptor owner: define event/phase/endpoint rules independently and prove every projection image meets them, without defining membership as that image. |
| Complete production alternatives | Production semantic owner: choose an exhaustive grammar and independently license every extra, with fixed parameters, full guards and domains. Resolve S/T only against actual public-contract behavior requirements. |
| Finite public capture contract | Public contract/generalization owner: furnish independently sufficient summary for the actual captured value and transitive fixed dependencies; do not rename its source relation. |
| Actual ordinary query | Resolver owner: expose and recognize finite evidence at `r_u` under the actual chosen clauses. |

The previous bridge and reviewed transformed-export note leave the same D0
premise open. This method exposes its source-independent descriptor leaves
and concrete S/T discriminator rather than proving a third assumed-decoder
variant. Production adoption needs independent review and explicit approval
of missing concrete semantics/representation. The selected same-provider
membership, Value-entry and result-synthesis rules are not reopened.

**Recommended next action:** the primary obtains one narrowly scoped design
artifact from the public-projection/descriptor owner, resolving legal ordinary
descriptor formation and exact independent leaf suppliers before another
sufficiency proof assumes D0. Present genuinely unresolved alternatives after
independent review; leave production, import-summary and query seams explicit.

## 8. Coverage, checks, resources and dependency fingerprints

Coverage is two decorated projection schemas and four analytic witnesses.
No new executable oracle, random seeds, domain sweep, mutation execution,
tests, builds, source acceptance run, formatting, children, Git mutation,
question write or shared-record edit occurred. There is no incomplete search
whose unvisited range is claimed covered. An exploratory file-path lookup
for older type-spec/reference paths failed; they supplied no premise. The
committed index and extant source documents supplied the actual authorities.

Oracle independence: source-entry deductions use selected source laws; D0
endpoint/phase/event leaves, carrier admission, import-summary sufficiency and
production grammar are still candidate inputs. Source base and descriptor
would share typed primitive licenses and transport laws. A checker assuming
those same laws could not independently establish their source meaning or
conservativity. No independent review of this artifact is claimed.

Commands/checks: bounded `git show`, `sed`, `rg`, read-only `git status` and
`git rev-parse`; one Python pinned-byte SHA-256 comparison; final static lease,
local-link, heading and whitespace check. These are document integrity checks,
not semantic validation. No numeric process/CPU/RAM/wall-time budget was given;
only short read processes and static checking used, zero heavy processes.
CPU time, peak RAM and total research wall time were not instrumented.

Unverified scope: existing-descriptor legality, independent primitive image
laws, exhaustive admission, all production extras, public import sufficiency,
effective actual-root Direct, principality/minimal alpha, recursive SCCs,
annotations/adapters/mutable captures, source acceptance and production cutover.

Pinned direct dependencies below have unchanged live bytes at initial check
except `notes/design/INDEX.md`, whose dirty bytes were excluded. The source
Generalize and contextual definitions are committed authoritative dependencies,
not remote-only claims. Final revalidation is reported in the return packet.

| Path | Pinned SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/INDEX.md` (locator, committed bytes only) | `eb6299147fccf0352b3aceea589208eeb3f4368a7c11f8fa714da1cce1f4b609` |
| `questions/2026-10-08-successor-generalize-root-policy/question.md` | `69f43d833a0237523c88a26125f3cf4878e599e38903f84b458d437da662072b` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |
| `notes/theory/2026-10-08-id-pick-transformed-public-export-candidate.md` | `f940ae9bf9b01af471075477513e040821d8619cd12b9023d83e9302b467f5c3` |
| `notes/theory/2026-10-08-id-descriptor-source-bridge.md` | `dcc91b8cb958f68208b61f490b68cbc3d42318b65f14604b0ad80742b1798a10` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` | `9eca7e45d1f0927397763481b0280bf54182408bd3c562aa2f6e80454f57ba3d` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |

## 9. Commit packet

- Exact leased paths: `notes/theory/2026-10-08-id-pick-d0-decoder-candidate.md`.
- Baseline SHA: `d67fab6fbd81837a0be15b1cf35b06a6e1046f16`.
- Dependency changes: none among semantic inputs at initial comparison;
  dirty index excluded and pinned locator used. Final recheck in return packet.
- Claim/review status: unreviewed bounded supplier audit and conditional D0
  rule alternatives; analytic discriminators; no sufficiency or closure claim.
- Checks already run: source/receipt reads, committed-index routing, pinned
  byte/hash comparison and read-only status; final document results in packet.
  No tests/builds or semantic executions.
- Proposed one-line research-checkpoint commit message:
  `research: expose independent id and pick public descriptor premises`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  this D0 candidate; distinguish already selected same-provider membership from
  missing public descriptor inputs; record S/T and complete production grammar
  as unselected alternatives; keep public sufficiency, import summary, actual
  Direct and principality open. No shared record or question bundle is written.

Frozen on submission; independent review and any adoption belong to the primary.
