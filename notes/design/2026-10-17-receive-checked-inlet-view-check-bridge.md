# Original receive F2: proposed checked-inlet VIEW and CHECK rules

Date: 2026-10-17  
Status: **Draft / unselected source-rule candidate; no independent review yet**  
Author: `/root/receive_checked_inlet_bridge`; sole writer; no descendants  
Assignment / revision: `F2-CHECKED-INLET-BRIDGE-20261017` / 1  
Sprint: `receive-checked-inlet-bridge-and-entry-control-20261017`  
Initial contract: revision 1, SHA-256 `df6aff1e5acec431ad471ed9f5a2ed293233ddc322b36efefbe559baae289708`  
Current contract: revision 2, SHA-256 `aaa610f373dea738ffeb9a34edbe4d1ae85bbd11b6f48a1e449b28d733889ee6`  
Baseline supplied by Luna: `3ba3e0f38`; no Git inspection.  
Revision-2 checkpoint supplied by Luna: `ef1336408`; no Git inspection.  
Supersedes: none. No admission definition or compiler behavior is selected.

## 1. Parent result and boundary

This candidate states two separate source rules at the **original F2**: VIEW
eliminates checked inlet admission into the incoming computation view; CHECK
introduces that admission from the incoming view and the original contextual
clauses. Neither follows merely from the selected carrier interpretation.
The actual F2 source-generation rule and its original clause occurrences are
still missing. Both SAT2 inclusions therefore remain OPEN.

The useful reduction is precise. Selected carrier validity already contains
universal designated-execution typing, including retained carriers that are
never forced by their recipient. The remaining choice is the view/domain
relation and contextual clause coverage at original F2, rather than whether
retention deletes execution obligations. The proposed rules expose that choice
without defining `I2=SAT`, replacing `B_in` with `J_U`, or selecting a provider.
Their local application below identifies the exact first missing constructor
for each direction; no repeated generic preservation theorem is offered.

The added guard-source audit resolves a possible misapplication: source-contracts
§3.7's `G` is the **final observation envelope** of its Draft abstraction grammar,
not the independently formed contextual admission guard `G_c2`. It expressly
retains separate admission/domain obligations. Therefore that generic inventory
cannot fill F2's missing CHECK premise by renaming G, and its observation/output
clauses cannot be moved before admission. Section 4.4 separates these uses.

The parent is the original FORWARD-FIRST-CALL §§1–2 in
`notes/theory/2026-10-16-first-call-joint-forward-preservation.md`.
Its reviewed local forward theorem under one anchored MODEL and lawful maps
remains valid. This work addresses formation/checking of its independently
typed punctured suffix `g:Value(A1); g(Unit)`. The theorem does not manufacture
that suffix's `VIncl(A1,F2)`, an exhaustive F2 interpretation, or MODEL existence.

## 2. Original telescope and domain inventory

Keep the original source and coordinates:

```text
my receive (f: () -> 'a) = { my g = f(); g() }
c1 = f(Unit); c2 = g(Unit)
g = original result binder r_b_g, with original A1
F2 @ (sigma2, Delta2); c2 output = Comp(E2,A2)
B_in(theta) = Comp(E_in(theta), A_in(theta)) @ F2's incoming ports
xi = (nu,K,D)
```

The following is the preserved binder order from the pinned parent and prior
comparison. It is not a new existential presentation of the descriptor:

1. Universally retain the original source/binder/scope tree, original alpha,
   original A1/E1 and F2/sigma2/Delta2 positions, joint xi, and independently
   licensed static assignment theta/eta0 and description witnesses. Original
   dependencies determine the order within this static telescope. These are
   fixed before choosing a hypothetical g, provider, challenge or observation.
2. For **every** full original decorated `v in Value(A1)`, retain **every**
   genuine `Act(v,U,p)` and its immutable captures. No actual c1 return image
   replaces this domain. Metadata `role(U), entry(U)` stays under this binder;
   there is no universally preselected role or fabricated callee formal.
3. For every independently compatible original punctured context, history and
   complete hole filling `(h,k)`, retain its current event `e=(eta0,h)`, live
   `C_e,w_e`, registered hole values and one joint incidence tuple. Callable
   hole typing is hypothetical at F2; it does not assume tested v membership.
   Whole-carrier checking is at the independently fixed I2. Description
   witnesses stay above this binder; live event evidence stays below its event.
4. For every independent designated demand `delta in Dem(k,h)` and every
   original `O in Obs(k,delta)`, retain the original full dependent tuple.
   Every admitted Response/raw Resume/FutureUse development has its own live
   event and original raw handle/response binder/unfinished suffix. Quantifiers
   over future developments are dependent families, never choices of a good run.
5. Only below an actual Return is its result value/root/provider/current-world
   tuple bound. A Value-entry formal rebind uses that tuple. Retained entry
   binds the same k without a Force-result binder. EventProof witnesses remain
   below their own events, with one shared event tuple across all conjuncts.

This retains all scopes, roots, source occurrences, profiles, typed paths,
registrations, licenses, context/continuation fields and correlated K/D. No
provider, residual or witness lineage is identified with another.

| Original class | Required coverage in both proposed rules |
| --- | --- |
| Initial/current and counterfactual compatible contexts | Every independently typed compatible punctured context, with original valid other bindings and actual registered holes; no Q or tested-membership filter |
| Inert carriers | Source Delay and every independently licensed formation, including non-source/Option 2 carriers; original reify/scope/capture validity |
| Designated demands | Every original compatible demand, with its live world and original consumer/interface; no demand added or removed because T succeeds |
| Zero-step/administrative/entry prefixes | Their current fields and suspended dependent obligations; no premature receipt, Force result, rebind or body result |
| Complete Return | Same returned decorated value/provider, hereditary result/future certificate, current world and typed result incidence |
| Pending Request | Original request/payload/response interface and raw continuation, current world, pending ordered suffix; no Return asserted |
| Response and raw Resume | Every independently admitted response and resumed state; same raw handle and unfinished suffix, including a further Request |
| Divergence | Every finite prefix; neither admission nor typing requires termination |
| FutureUse | All independent compatible later events, including latent values/providers; current authority is checked there, never revived from origin |
| Independent W/Z/opaque alternatives | Full original declarations, guards and output-dependent provider/future interfaces, including alternatives lacking source execution |
| State and foreign continuations | Original independently supplied transition/domain laws; no action obtained from immutable identity or a local subtree restriction |

`I2` (checked inlet), `J_k` (a supplied carrier's certified view), `B_in`
(incoming-port expression) and `J_U=CarrierContract(U)` (actual provider inlet)
remain four separate objects. None is identified by native Function shape.

## 3. Authoritative facts available before either candidate rule

The selected contextual Function definition §2 and semantic-input §2 assemble
a checked challenge from the compatible punctured context, valid other values,
actual registered holes/incidences and independently checked whole-carrier
admission. The constructor consumes this last premise; it does not derive it.
Only subsequent elimination of full same-provider membership gives ActualAdm
at `J_U`. Using that projection to manufacture I2 admission would be circular.

Semantic-input §4.3 provides the carrier criterion at a **supplied original
view J**: inert formation and all designated execution observations. Its
unfolding exposes both fields at J. Lemma W's RetainBind preserves the same
hereditary carrier certificate; it does not turn mere inert storage into one.
Theorem R explicitly places independent whole-argument checking between Name
Delay validity at `Comp(empty,A_x)` and admission at its checked Function.

The selected Strict constructor consumes the actual `I,R,IF` and full
background. It preserves receipt/Force/Return/rebind/body order, pending raw
handles and dependent suffixes. For the constructed step only, closure
inversion identifies its actual inlet with its supplied I_x. It supplies no
identification of arbitrary F2 with that step or its inlet.

IF-Insert/IF-Use in the selected source-interface definition §§2–3 retain an
actual primitive clause occurrence and its complete contextual use under the
original scoped substitution. They require the whole original contract. A
finite registered graph can retain infinite parameter families without
enumeration. Neither constructor creates a missing guard or proves an
admission-domain action from positive membership.

## 4. Proposed VIEW elimination and CHECK introduction

Use `Checked_I2(theta;h,k)` only as a name for the **original** whole-carrier
checking judgment. Let `A2(h,k)` be the original complete contextual admission
of the prior comparison. Neither name is assigned a new truth condition here.
Write the existing candidate expression, with its independent domains,

```text
HC_B_in(h,k) = Form(k;e_h)
  and forall delta in Dem(k,h). forall O in Obs(k,delta).
      T_B_in(theta;h,k,delta,O).
```

Full T retains all value/provider/world/request/response/path/latent and hard
joint fields; outward support or four port checks cannot replace it.

### 4.1 VIEW? — owned by original Function source generation/descriptor

The proposed elimination rule, at the whole original telescope, is:

```text
original checked tuple d : A2(h,k), retaining Checked_I2(theta;h,k)
---------------------------------------------------------------- VIEW?
Form(k;e_h)
forall delta in Dem(k,h). forall O in Obs(k,delta).
  T_B_in(theta;h,k,delta,O)
each original contextual guard at its actual clause occurrence and event
```

This is an unselected law to prove from the actual F2 constructor, not an
additional premise hidden in a new definition of A2. Its guard conclusion must
be the occurrence-indexed inventory discussed below, with exact argument
incidences. Projecting some similarly named contextual facts is insufficient.

There are two legitimate implementation-free proof routes. If the owning
checked contract already exposes exactly the same carrier view and independent
demand/observation fibers, unfold that certificate and use identity incidence.
Otherwise supply a complete typed view action: for **each target** `(delta,O)`
in the original B_in fiber, provide its lawful coverage by checked evidence,
or an independently established original constructor proof of that target
case. Coverage must preserve the same registered k/h and correlated indices;
its action must transport full T, formation and the actual guard witnesses.
An old-to-new forward map alone does not cover new target observations.

This action is not necessarily equality of views, a bijection of domains, or
equality of all proof objects. Requiring any of those without its source law
would strengthen the task. Conversely, projecting only result/effect marginals
cannot supply the complete action.

### 4.2 CHECK? — owned by original whole-argument checking/descriptor

The separate proposed introduction is:

```text
HC_B_in(theta;h,k)
original independently compatible context and valid other bindings
actual registered callable/carrier holes and their original incidences
each original contextual guard at its actual clause occurrence and event
---------------------------------------------------------------- CHECK?
Checked_I2(theta;h,k), on this same complete tuple
```

Then selected checked-challenge assembly constructs `d : A2(h,k)`. These two
steps are distinct: assembly is selected; CHECK? remains unselected. There
is no premise `ValueMem_F2(v)`, `Acc(J_U,k)`, complete invocation safety, desired
output membership, Q or a successful native comparison.

CHECK? must inspect the original inlet introduction clauses. If they contain
a relational clause absent from full B_in and the enumerated guard fields,
that clause is a missing premise with a source owner, not a consequence of
record assembly. Every correlated field uses the same original witness; an
existential witness chosen separately for each field is invalid. This is not
the converse of VIEW? by Function variance or Theorem F: Theorem F already
requires whole challenge/observation inclusions and actual source membership.

### 4.3 Occurrence inventory boundary

The selected inputs identify guard families and their owners, but they do not
enumerate the complete original F2 clauses. The source-direction definition
§5.1 leaves the complete source constraint-generation judgment open. Contextual
membership §2 leaves descriptor admission/observation relations independent.
Thus writing `all guards hold` would hide precisely the missing rule.

For each proposed guard occurrence, the required record is:

```text
(actual original declaration/root occurrence,
 actual IF-Insert and IF-Use occurrence and scoped substitution,
 complete dependent parameter/evidence telescope,
 original clause, original argument incidences,
 role: admission prerequisite | carrier observation | invocation observation,
 event position, actual lawful world/domain/typed-view action).
```

This is a proposed finite record format, not a newly emitted compiler record or
an assertion that F2 already has it. An infinite family remains one original
dependent clause; no finite list of example observations replaces its quantifier.
In particular invocation-output guards cannot be promoted to pre-admission
requirements merely because they appear in a complete Function contract.

### 4.4 Finite candidate guard ledger, with explicit missing occurrences

Luna authorized the added source-contracts §3.7 dependency in contract revision
2. It has status **concrete clauses remain Draft**. The following ledger uses
its complete-envelope families as an unselected checklist, together with the
already selected contextual constructor fields. It does not adopt its H/W/Z
grammar, assign that grammar to F2, or supply F2's actual guard inventory.

`A` below means an independently justified admission/context prerequisite;
`C` means a field of the carrier's full observation certificate; `P` means a
field of the provider's complete invocation certificate. A family can have
distinct A/C/P occurrences; an occurrence at P cannot be copied into A.

| ID / candidate family | Full operands and position to retain | Owning clause / candidate rule use / unresolved F2 evidence |
| --- | --- | --- |
| G01 context and environment | Independent punctured context, valid other values, original continuation under hypothetical callable hole, current C_e/w_e | Selected semantic-input §2 context constructor; A in CHECK and projection in VIEW. Original F2 context-reference occurrences still required. |
| G02 registered holes and incidence | Same v/U/p and whole k, roots, hole registrations, typed callable/argument/receipt/receiver paths and source-use maps | Selected checked-challenge assembly and IF-Use; A. Registration is not membership, actual receipt or authority. Missing exact F2 substitutions cannot be inferred from port IDs. |
| G03 scope, license, captures and profile | Original binder/scope tree, primitive/reify license, dependency-closed captures, slots/profile and reference validity | Selected carrier formation and independent primitive contract; A and Form, with C/P occurrences below their events. No new capture grant from matching shape. F2 occurrence/eligibility records OPEN. |
| G04 ordinary descriptor membership | Entire decorated value/computation/carrier/provider tuple, its original typed paths and latent/future fields | Draft §3.7 full envelope and selected carrier criterion; C inside full T_B_in, P inside full P_F2. Tested Function membership is excluded from A. No factorization into marginal endpoints. |
| G05 genuine guarantee bounds | Original guarantee operands, equations/inequalities and joint assignment; same observation's outward support at the designated port | Draft §3.7 retains genuine bounds in the final envelope; C/P at their original positions. An original independently declared A occurrence would need its own source proof. No new empty-effect assumption or removal of retained equations. |
| G06 admission-dependent typing/provider conditions | Same actual provider decomposition, interface parameters, role/entry, whole carrier, typed receipt prerequisites and full shared context | Selected independent I/IF and Draft §3.7; actual A occurrences before entry, C/P occurrences at their events. `Acc(J_U,k)` is supplied later by membership, never an A premise. RG2 and exact F2 incidences remain OPEN. |
| G07 original K constraints | Every original K predicate with the same operand occurrence, joint witness and dependent scope | Draft §3.7 explicitly retains original K; selected rules retain joint evidence. Apply an actual A/C/P occurrence only at its owning position. The complete F2 K-atom list and actions are absent; `K is valid` is not a new closed premise. |
| G08 original D constraints | Every original D incidence/relation with original endpoints, source positions and correlated witness | Same source envelope and IF-Insert/IF-Use owners; preserve original identity and scope. Complete F2 D-atom list and actions are absent; no independent per-port witnesses. |
| G09 authority and entry phase | Actual event's eligibility/receipt preconditions versus established receipt and later live Observe/Receive authority | Selected membership §2 and semantic-input §§2,4.1; A only for original prerequisites, C/P for later transitions. No origin/lineage-to-live-grant inference. Exact F2 prerequisite clauses OPEN. |
| G10 response, raw continuation, world and future compatibility | Original typed request/response interface, raw handle, resumed C'/w', ordered unfinished suffix, dependent future provider and every admitted history extension | Selected carrier/Strict and source-interface clauses; C/P universal dependent branches, original A contextual prerequisites where declared. A later result/continuation safety proof cannot be demanded to form the initial challenge. Foreign/State domain actions remain independent. |
| G11 independent alternative declarations | Every actual W/Z/opaque arm's whole tuple, fixed/changed coordinates, operands, original scopes, final hard predicates, own output-provider/future contract | Selected IF placement and candidate §3.7 envelope; C/P coverage, including unanchored extras. No actual F2 W/Z grammar is supplied or adopted. An arm lacking source execution stays in its original domain. |
| G12 invariant parameters and changed-domain actions | Entire original parameter tuple, lawful typed correspondence, legal event/scoped substitution and any admission-live history/provider change | Draft §3.7 explicitly requires independent domain certificates; selected IF preserves original actions. This is a proof obligation on transport, not a success-filter for A. No positivity or forward-only map proves it. |

This table is finite in **families**, not an exhaustive list of instantiated
F2 predicates. It identifies what a source-owner completion must furnish for
VIEW and CHECK and where each proof is consumed. G01–G03/G09 already have
selected constructor-level meanings; their F2 incidences remain to be supplied.
G04–G12 explicitly retain every original clause if present, with its proper
event and sort. There is no proof that the original F2 envelope has no other
clause. Consequently the requested full original inventory cannot be claimed
from this packet's inputs. The first unavailable evidence is the actual F2
source-definition/occurrence record, not a missing finite list of executions.

The source-contracts example of a Write extra under a fixed Read guarantee
illustrates why G05 cannot be dropped; it is not a c2 counterexample. Its
positive-grammar theorem cannot prove CHECK: §3.7 explicitly keeps admission
independent and requires a separate domain certificate when it changes.

### 4.5 Unselected choices exposed by the ledger

1. **Original complete incoming view, no extra admission clause.** If the
   actual F2 owner identifies its carrier certificate's complete view/domain
   action with B_in and exhibits precisely the original A occurrences above,
   VIEW and CHECK can be source elimination/introduction rules. The owner must
   prove both, including coverage of all original alternatives. This is the
   intended candidate, not a selection that I2 equals SAT.
2. **Additional original admission relation.** If a real F2 clause relates,
   for example, an existing carrier-provider coordinate to a context-owned
   coordinate beyond HC_B_in and the prior G_c2 expression, CHECK lacks that
   particular clause. The owner must display its original predicate and
   scoped operands. Adding an unnamed Psi would merely rename the obstruction.
   Adding a new such predicate would change admission and requires authority.
3. **Original checked view does not imply full B_in.** If actual original
   admission permits a tuple for which a B_in target case fails, VIEW fails.
   Adopting the candidate would then exclude that original challenge and
   change the accepted meaning. A source-qualified witness needs original
   A2 evidence, an independently admitted failed target case and the original
   source/component correspondence; none is produced here.

These alternatives distinguish specific consequences without inventing a
concrete missing clause or moving a proof obligation into a changed domain.

## 5. Separate local attempts at original F2/xi

**L: A2 implies the prior SAT2 predicate.** Fix one arbitrary original tuple
at the telescope in §2. Selected checked-context elimination retains h/k,
their original incidences and Checked_I2. Where the original checked carrier
certificate is supplied, §3 exposes its formation/execution fields at its own
view. The next step is VIEW?'s target-fiber coverage/full-view action and
original guard projection. Those are not supplied by F2's four ports or the
selected source direction. L stops here. Conditional on the proposed rule and
an exact inventory match with the prior G_c2, conjoining its outputs gives SAT2
on this same tuple. This elementary consequence adds no established F2 law.

**R: the prior SAT2 predicate implies A2.** Its Form and universal T_B_in fields
supply HC_B_in at those same fixed domains. The pinned G_c2 is itself an
uncompleted inventory expression; it does not certify that every original
CHECK prerequisite is present. Even if that inventory match were supplied,
the first missing inlet constructor is CHECK?. After CHECK? the selected
challenge assembly is valid and needs no provider-success premise. R stops
before that assembly, without assuming an inverse to VIEW?.

In particular the added §3.7 input does not close the gap between SAT's G_c2
and CHECK's prerequisites. Its final G checks each observation, while admission
is an independent domain. Its guarantee/provider/future fields can guide full
T_B_in/P_F2 coverage; they cannot be used as an exhaustive initial guard list.
This locates the precise failed join and avoids deriving admission from the
post-admission observation contract.

The distinction is substantive. As logical discriminants only, a checked view
can cover a smaller independent observation fiber than B_in, in which case
VIEW requires new-case evidence; or original admission can additionally
require a context/provider correlation not entailed by full B_in, in which
case CHECK requires that actual clause. These configurations are **not**
source-qualified c2 counterexamples. Neither is made into an admission rule.

The old ignored-retained-body example cannot choose between these possibilities:
retained typed binding already carries full execution validity at its declared
view. Changing J_k while asserting original admission simply reintroduces the
missing checked-view rule. Divergence is not a typing failure. After these two
directional attempts, the useful next method is original source-owner clause
formation/selection, not a third generic Generalize or retained-body argument.

Application to the parent is exact: a lawful bridge would settle only original
inlet correspondence after all its premises were established. It would still
not prove all-A1 VIncl, RG2, complete R/IF, joint WF_Dec, invocation-image CIncl,
Bind/residual/world joins, MODEL or source T. First-call `S_alpha subset S_A1`
supplies neither `S_A1 subset S_F2` nor a restriction to actual returns.
F1/FK1 and arbitrary foreign continuations remain independent. One local
future-subtree action cannot settle those quantifiers.

## 6. Source/native boundary and implementation TODO

Direct reads of pinned code confirm these bounded facts:

| Source owner | Evidence | Limit |
| --- | --- | --- |
| `RuntimeProgram::from_hir`, program.rs:382–402 | Lambda retains its actual parameter; that formal's outer effect annotation determines Value/Computation entry | No Pure/Handler inference, original I2 interpretation or B_in identification |
| Closure dispatch, machine.rs:693–747 | Value pushes ValueEntry before executing the delay; Computation binds the same delay and enters the body | No checked whole-inlet construction or typing of every demand |
| `Frame::ValueEntry`, machine.rs:819–836 | Binds the received result at that actual Return before evaluating the body | No result before Return; no full source T certificate |
| Playground `execute`, lib.rs:143–153 | `_candidate` is discarded; RuntimeProgram imports HIR plus default evidence | No inference-to-runtime complete admission/plan import |

Inherited native owner locators in the pinned candidate name
`emit_candidate_source`, `candidate_call::observe`,
`CandidateSourceCall::pending_construction` and `OriginalGenCall0Input`.
Their prior audit supplies incidence/port records and pending construction
fields; it explicitly supplies no complete SAT2 constructor. This packet did
not independently reread unpinned compiler files. In particular Local(g) does
not become a formal by introducing CHECK notation.

**NO_SAFE_CODE_SLICE for this bridge.** The directly inspected runtime
construction and closure-dispatch owners cannot decide the absent source law.
The minimum future implementation TODO is conditional: after Luna selects or
proves the actual rule, have the original source-generation/checking owner
retain its exact clause/view/domain incidence evidence through the existing
producer and whole-argument consumer. Falsifier: an original legal challenge
or observation has no evidence path, or the retained record certifies only
port identity. No provisional code is needed to decide a currently unspecified
semantic clause, and no code edit is authorized here.

All ordinary Simple-sub generation, accumulation, propagation, levels,
extrusion, qualifying intrusion and generalization remain required. The
candidate suggests no early checking, native bypass, source restriction,
restored withdrawn shortcut, or Generalize-based reconstruction of a missing
source contract.

## 7. Mutual TODOs, checks and provenance

- **F2-CHECKED-INLET-BRIDGE-20261017/VIEW:** original Function source-generation
  and descriptor owner. Input: unchanged original c2 graph, A1/F2/sigma2/Delta2,
  theta/xi and independent inlet contract. Output: actual checked-certificate
  elimination with every target demand/observation covered and each original
  guard projected at its exact occurrence. Falsifier: uncovered target case,
  changed binder/domain, or dependence on actual provider success.
- **F2-CHECKED-INLET-BRIDGE-20261017/CHECK:** original whole-argument-checking
  owner. Output: source-owned introduction at I2 from full B_in and expanded
  original guard records, or the exact missing original clause. Falsifier:
  a SAT tuple violates an original admission clause; a guard is manufactured
  from Q/membership/output; correlated witnesses are chosen independently.
- **F2-CHECKED-INLET-BRIDGE-20261017/CLAUSES:** original primitive/descriptor
  owners and Luna authority routing. Supply actual occurrence records of §4.3;
  distinguish admission clauses from observation obligations. Falsifier:
  a generic family name substitutes for an actual original F2 clause, or a new
  restriction is adopted by calling it an old guard.
- **F2-ENTRY-CONTROL-20261017:** Luna's separately leased source lane starts
  after this writer stops. Use selected Strict phases to trace the returned
  step's Delay/Force/Request/raw-resumption/Return/rebind/body order. Return
  exact first broken join if any. This evidence must not be imported as
  arbitrary c2 admission, Pure/Handler classification or a full source T plan.

Reused within their actual premises: prior comparison's retained-carrier
readout and two missing directions; selected checked-context assembly and
carrier/RetainBind laws; selected Strict and source-interface incidence;
reviewed local first-call theorem under MODEL; prior HIR identity trace.
Rejected as closure: provider-success admission, source-image domains,
Unit-derived roles, foreign Strict identification, port-only view equality,
ignored-body/divergence separators, forward-map-only coverage, and new guards
smuggled into G. Historical authors are the named producers in the pinned
files; original source-code authors are UNKNOWN in this read-only audit.

Five substantive stages: pin/binder audit; selected-law extraction; separate
VIEW/CHECK drafting; domain/guard and parent application; source-owner handoff.
Checks are byte hashes, source reads and author argument inspection only.
No tests, builds, executable probes, compiler/runtime execution, Git, external
contact, descendants or independent certification. Requested model/effort:
gpt-6-astra/medium. Observed effective model/effort: UNKNOWN. Canonical worker
is the author; opaque runtime/session identity and actual launch timestamp:
UNKNOWN. First observable active-work receipt: 2026-10-17 02:57:57 UTC.
The 720-second cap includes these reads and is not reset by a contract update.
Final pins, charge and writer STOP appear in the exact assignment handoff.
Only this artifact and its assigned inbox are new paths; scratch paths: none.

## 8. Dependency and author freeze

The contract's revision-2 **20-input manifest**, at SHA-256
`aaa610f373dea738ffeb9a34edbe4d1ae85bbd11b6f48a1e449b28d733889ee6`,
is incorporated as this artifact's exact direct dependency manifest. All
19 revision-1 inputs and its contract matched before initial reliance. Luna
then authorized revision 2; all 20 inputs and its contract matched at
2026-10-17 03:01:23 UTC before inspecting the added §3.7. No mismatched bytes
were used. The added input SHA-256 is
`1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
Its authorized use remains candidate inventory only. Workflow authority reads
are not new semantic premises. No other semantic dependency was added.

Prior artifact authors reused: `/root/receive_role_indexed_inlet_introduction`
(SAT/RG syntax), `/root/receive_sat_admission_comparison` (admission audit),
and Luna `/root` (selected HIR source trace and primary adoption/review records).
Other historical proof authors retain their pinned records; their effective
models and opaque identities are not inferred. No prior review certifies this
new draft. Sole current author and final writer: the header identity.
