# Successor global synthesis: one joint source relation and the remaining gates

Date: 2026-10-07
Status: producer-authored research audit and proof reduction; independent review pending
Implementation authority: none; no production inference cutover
Baseline: `ac2864a48868b017a8b6fedc6a665f24d0c2daff`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this note and `tools/research_successor_global_synthesis.py`
Scope: full-successor residual, source/world, principality, production,
selection/resolution, resource and lifecycle dependencies. Recursive and
source-association constructions belong to the separately assigned producers.

## 1. Result and authority

The existing whole-relation results support an important reduction: **a
completed original profile is not a separately supplied input at every
fragment, receipt, capture, recursive-use and principal-use seam. It is one
jointly constrained original source coordinate, quantified at its original
scope.** Source generation can expose its unknown inventory and obligations
before solving them. The unrestricted theorem must prove that the original
source relation supplies that coordinate; repeating completed-profile
hypotheses throughout the DAG does not create additional independent gates.

This reduction removes duplicate *premises* from the inventory. It does not
prove a compatible complete profile exists for every source, select exhaustive
profile licensing, or prove unrestricted source adequacy. The exact semantic
cuts are displayed below rather than hidden inside a supplied `TypedContext`,
`JointWF`, completed `P`, or successful comparison.

The strongest whole-relation route still reaches two different predicates:
the independent source/production relation and the actual exported direct
query. Exact relation rewriting preserves a direct query already present; it
cannot derive its existence. Legal common-descriptor formation, original
joint nonemptiness, and all-valid-view lifting therefore remain different
obligations. Likewise, Option 2 prevents retiring the production-extra
containment obligation after the source-reference theorem succeeds.

No source counterexample or user-decision blocker is established. Missing
rules below are semantic/proof work, not evidence of two complete competing
Authority-consistent semantics on the same admitted source. In particular,
none is labeled `BLOCKED-BY-USER-DECISION`.

Authority for this audit is current user instruction first, then approved
in-scope decisions, reviewed theorems in their exact scopes, confirmed
implementation facts, frozen Oracle history, and general PL reasoning. The
[current directional correction](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
requires a protected inferred variable's source Function **upper output** to
receive protection and forbids that seed from back-protecting an existing
lower/provider. Independently present provider protection survives. Actual
callable role and Value/Computation entry remain separate from internal
inference views. E/R and a blanket result-default policy are not selected.

The [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§2–4,
8–12 requires soundness, principality relative to the chosen conservative
abstraction, source adequacy and final well-typed-program capability. Its
later method/role/implementation-resolution gate remains mandatory. The
[Option A approval](../../questions/2026-10-05-production-function-denotation/approved-answer.md)
and [Option 2 approval](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
select independent production semantics over the original `Rel_C`/`xi`,
including licensed extra observations. They do not supply concrete exhaustive
membership/admission clauses or implementation approval. The
[rebuild addendum](../design/2026-10-04-scc-intrusion-cross-edit-rebuild-addendum.md)
is Authoritative for rebuild and the complete boundary direction, but leaves
interface fields and effective equality open.

## 2. The positive reduction: quantify completion once

### 2.1 Independent source atoms, not solver-produced truth

Fix source `S`, its resolved occurrence graph, original binder tree, imports
and source scopes. Retain one original joint assignment `xi=(nu,K,D)`.
Let `x` contain its original value/effect endpoints and shared roots, `p`
contain its original signature/profile/slot coordinates, and `w` contain
world, source, receipt and history witnesses. Write

```text
J_S(x,p,w;xi) = SourceAtoms_S(x,p,w;xi).
```

`SourceAtoms_S` names independently interpreted source judgments. It does not
mean the comparison solver accepted the program. Its profile clauses are
obligations such as complete signature licensing, original applicability,
typed slot formation and source contribution membership. The word “atoms”
does not make these predicates decidable or supply their missing meanings.
Original universal world/challenge/response/future-history quantifiers remain
inside their independently interpreted admission and validity judgments.
Existential `w` is a joint witness/certificate at its licensed source scope;
it is never one selected execution or one selected world used to replace an
all-world admission requirement. Non-existential source binders remain in
their original binder tree as explained below.

The reviewed [unsolved profile/admission construction](2026-10-06-source-profile-admission-construction.md)
§1 already emits an original unknown inventory/profile and an upper Function
demand jointly for its exact source. The
[typed-core construction](../design/2026-10-02-typed-computation-core-elaboration.md)
§6 constructs finite role/result skeletons from ordinary constructors while
keeping endpoint obligations symbolic. The local directional producer and
selected SV transition then use their independently justified source
subrelations. They do not wait for arbitrary solved-profile traversal.

### 2.2 Whole-source completion and a public use

For eligible existential coordinates, keeping each binder at its original
scope, the original complete relation is

```text
Old_S(x;xi) = exists original-scope p,w. J_S(x,p,w;xi).
```

For a public view assignment `v`, an ordinary use through an actual common
export has the one joint relation

```text
Use_S,V(v;xi) = exists original-scope x,p,w,a.
    J_S(x,p,w;xi)
    and K_G(x,p,w,v;xi)
    and Q_common(x,p,w,a;xi)
    and Direct(B_common(x,p,w,a), R_V(v);xi).
```

`K_G` retains the legal source/scope graft. `Q_common` retains every direct
common-formation check. `Direct` is the actual common export query, including
its resolver/adaptation/evidence alternatives. Its root cannot be replaced
by an unexported retained source root. Original rigid binders are not moved
through existential projection. This displayed notation abbreviates the
original binder tree; it is not a prenexing rule.

The [certified-use theorem](../design/2026-10-04-certified-callback-and-constrained-use.md)
§§5–6 supplies the finite fresh-copy/graft/query graph. The exact remaining
all-view sequent is therefore

```text
IndependentValid_V(v;xi) implies Use_S,V(v;xi)
```

for **every independently valid public view in the claimed source envelope**.
No completed-profile premise appears outside this relation. Completion is
chosen jointly with its source, world, comparison and query evidence.

### 2.3 Why this eliminates duplicate gates

Suppose a fragment transport lemma is uniform over every original compatible
completion. To use it in the complete relation, take the `p,w` already
witnessing `J_S`; the lemma supplies the transported fragment on that same
witness. All following fragments use those identical coordinates. Conversely,
forgetting only fresh total derived coordinates retains the same original
`J_S` witness at its original scope. Thus the local lemmas require no separate
completion oracle and no independently selected completion for each use.

The reduction is an existential-introduction/elimination proof on the original
scoped relation. It uses neither concrete-success transitivity nor recovery
of source licensing from a normalized type. The existing
[DFRAG completion factorization](2026-10-06-directional-profile-completion-factorization.md)
and selected [receipt construction](2026-10-06-directional-source-view-instantiation-construction.md)
are reused in their exact scopes; they are not reproved here.

There is one independent remaining nonemptiness theorem:

```text
IndependentAdmittedSource(S,xi) implies exists original-scope x,p,w. J_S(x,p,w;xi).
```

It requires the SIG/INIT/RAW/REC/GEN leaves in §4. An event-free identity
execution, finite returning prefix, or empty outward support does not derive
it. The source is an admitted source independently of pending `Q`; the
antecedent cannot be defined as “there is a solution of `J_S`.”

This is a proof-architecture reduction, not new unrestricted theorem closure.
It retires repeated opaque completion inputs and makes the one remaining
existence obligation explicit. A new conditional transport theorem over
supplied completed profiles would leave this cut untouched and is unnecessary.

### 2.4 Minimal obstruction to separate completions

Let a single original profile coordinate range over `{0,1}`. Two independently
nonempty fragments can require `p=0` and `p=1`. Each has a completion and
their joint source relation has none. This is the minimum one-coordinate,
two-alternative witness to the invalid inference

```text
for every fragment j, exists p_j. Fragment_j(p_j)
therefore exists p. for every fragment j, Fragment_j(p).
```

It is a mathematical inference counterexample, not a Yulang profile instance.
The repaired positive construction is to retain `J_S` and choose its one
profile coordinate only after all original clauses are joined. No product of
marginals or per-use completions enters the target theorem.

## 3. What whole-relation unification can and cannot retire

The full-source/production proof can share `SIG`, `INIT`, `HIST`, `RAW`,
`PHI` and the original witnesses. Source-call receipt, event membership,
origin/capture, generalized use and punctured-context admission should all
refer to these common judgments rather than each importing a new completed
world or profile certificate. This unifies their semantic input without
defining production membership as source-reference membership.

Two sufficient proof squares remain:

```text
source transition + independently formed source row
    -> original source observation in J_S
    -> production actual observation in Sat_A

independently typed punctured source context
    -> challenge in checked D_C
    -> challenge in independently generated actual D_A.
```

The first square yields source-to-production coverage when its atomic
constructors commute. The second yields the domain half when all context
and response/history clauses commute. The opposite observation inclusion
`P_A subset P_C` additionally quantifies over **all** production members,
including members with no source-reference constructor proof. Sharing source
initialization cannot remove that quantifier.

The following apparent gates are redundant and should not remain independent
unproved leaves:

- a separately completed `P` at every fragment/capture/use: replace it by the
  same original `p` inside `J_S`, preserving the existing local scopes;
- a fresh event-origin certificate per transport: source-generated origin
  and capture facts belong to the same `w` and identity map;
- explicit new `m_V` calculus: ordinary copy/graft/query construction already
  exists; retain its all-view lifting sequent;
- reversing solver/intrusion state across edits: the Authoritative addendum
  permits rebuild; complete interface/equality and reuse validity remain;
- production source-constructor coverage as a membership *restriction*:
  Option 2 allows other independently licensed members; reference coverage is
  a sufficient subcase;
- pure structural arbitrary-to-regular existence: FMP closes that exact
  package; do not reopen it under the residual heading.

These retirements do not silently retire `SIG`, `INIT`, actual export
`Direct`, legal descriptor formation, full production containment, or joint
effectivity. The active theory map's exact-rewrite and factor-cover results
are already adequate preservation machinery and need no duplicate proof.

## 4. Deduplicated independent leaf inventory

Status meanings: `CLOSED` refers only to the stated reviewed scope;
`CONDITIONAL-CLOSED` retains the displayed hypotheses; `IMPLEMENTATION-ONLY`
is work following a settled contract and its approval, not present permission;
`OPEN-PROOF` is a missing derivation/algorithm; `OPEN-SEMANTIC` is a missing
exhaustive independent judgment or contract. An absent rule does not establish
a user decision. The inventory is exhaustive for the **currently recorded
successor objective and supplied dependency documents**, not every imaginable
future language extension.

| ID | Status | Minimal remaining judgment/obligation | Governing evidence |
| --- | --- | --- | --- |
| SIG | OPEN-SEMANTIC | `SignatureLicense_S(beta,Slots(beta),p,owner,scope;xi)` at original introduction; exhaustive applicable positions and own/inherited sources independently of Q | Unsolved profile/admission construction §§1–2; current call-view authority; directional correction §§2–4 |
| INIT | OPEN-SEMANTIC | Initial open world/environment/import/hole relation at one fixed `xi`, including source-licensed alias identities and hole-dependent values without checked-membership circularity | Concrete compatibility §8, rigid-hole/open-graph clauses; original source admission construction |
| HIST | OPEN-PROOF | For every source-admissible response/future input/resumption and independently valid original world, `WorldStep(C,C')` preserves original validity and all admission-live dependencies | Source-interface adequacy §4; independent all-world admission gates; complete finite histories are not one tested filling |
| RAW | OPEN-PROOF | Every included raw constructor emits its exact whole-carrier/path/source atoms and every independently typed constructor derivation lifts back, with complete alternatives | Typed-core §6: Name/Lambda/Apply/Bind/Handle table; annotation/pattern/conversion/global-interface coverage remains outside its supplied-input result |
| REC | OPEN-PROOF | Actual simultaneous body/member assumptions validate/discharge on the same provider graph, comparison premises and scopes | Recursive producer lane; K/KP/KV removed runtime graph construction as a premise, not guarded discharge |
| GEN | OPEN-PROOF | Actual generalized-view eligible-binder placement, fixed imports/non-generic/world roots, complete per-use freshening and recursive/environment admissibility | Recursive/generalization lane; lexical ancestry and candidate projection endpoints do not select semantic eligibility |
| BOUND_ADAPT | OPEN-PROOF | Source emits/realizes each typed boundary and original Path/Incidence map; adapters preserve actual callable role/entry, argument/result consumer placement, provenance and complete observation semantics, with complete resolution alternatives | Typed-boundary §§3–6 and typed-core §§7–9 prove supplied-shape/certificate results; unrestricted unknown-shape/raw-source conversion and boundary realization remain open |
| EBRIDGE | OPEN-SEMANTIC | Comparison-independent mixed abstract/concrete component membership and annotation-to-polarized-port/event-occurrence relation on one original nonempty fiber | Concrete compatibility mixed component sections; scoped EROW selected examples do not define exhaustive mixed membership |
| SUBIMAGE | OPEN-PROOF | Complete shallow/deep handler image justifies exactly attached targeted event removal while retaining independent same-family events, continuations and symbolic invariant K,D | EROW scoped deep contract; ordinary semantics §5; support-only global cancellation is refuted by reviewed raw-resumption characterizations |
| RELEASE | OPEN-PROOF | Independent `'e` attribution and emission produce actual outward crossing after intervening computation/handler processing; release persists only at the selected same target view while the original receiver lives, with ordinary later eligibility | Approved protection-release crossing handoff; public provenance notation; graph/query/filter exactness over supplied Path/Incidence proves neither these source facts nor lifetime |
| ORDINARY | OPEN-PROOF | Complete source ordered search, active-boundary eligibility, generic arm/request instance OpCompat, rigid-hole scope, raw resumption and outside-arm/deep-expansion theorem | Ordinary computation §§4–6; charter §§13–22; selected local rules/candidate exact embedding do not prove the full finite source inference gate |
| CTX | OPEN-PROOF | Each source derived comparison has `j_child=Ctx_r(j,u,v,witnesses)`; a finite canonicalizer preserves every rule/guard distinction, alias invalidation and sibling opening identity | Source-context finite closure §§2–3 assumes finite `J_T`/`A_T`, does not construct them from source |
| PHI | OPEN-SEMANTIC | Exhaustive primitive `Guard/Phi/K,D` interpretation with complete original operand tuples, especially when projection/grafting changes a structural endpoint | Residual source-premise audit; open residual §7; retaining old operands is different from transporting a varying endpoint |
| JDEC | OPEN-PROOF | Complete effective **joint** solving or exact effective residual representation, including source predicates and declared source acceptance; one simultaneous witness | Pure effective-search boundary explicitly excludes Guard/Phi/effects/admission; see §6 below |
| JPROJ | OPEN-PROOF | Effective principal public projection with original binder alternation, invariant coordinates, evidence alternatives and structural/effect correlation | Open residual §§4–5; equality/residual factorization does not compute a public principal interface |
| DESC | OPEN-PROOF | One admissible common descriptor at all original typed Function paths, preserving required source challenges and path-specific carriers on one descriptor | Common-preimage §6.1; common allowance §§5–7; A-extension proves only its guarantee-only envelope |
| DIRECT | OPEN-PROOF | `IndependentValid_V(v) => Use_S,V(v)` through the actual common export, including resolver/evidence completeness for every valid V | Certified use §§5–6; coverage/source joins §8; unequal-grammar source-license audit §§3–5 |
| SAT_A | OPEN-SEMANTIC | Exhaustive comparison-independent production `Sat_A(c,o;xi)` over complete original `Rel_C`, endpoint/role/entry/path/origin/continuation/scope/authority/dependency clauses, including Option 2 extras | Approved Option A/2; production Function follow-up; reference interpretation is not this production clause |
| ADM_A | OPEN-SEMANTIC | Exhaustive production `Adm_A(c;xi)` from an independently typed punctured context, actual carrier and filling-independent world, including empty history/future providers | Approved Option A/2; PCInit/source admission attempts; INIT/HIST are shared rather than duplicated |
| DOM | OPEN-PROOF | `forall xi. D_C(xi) subset D_A(xi)` on original independently interpreted domains | Typed-core §9; approved production basis; no vacuous output argument establishes admission |
| OBS | OPEN-PROOF | `forall xi,c in D_C(xi). P_A(c;xi) subset P_C(c;xi)` for every licensed member and complete future history | Approved Option 2 explicitly preserves production-only observations; existing linked reference theorem supplies only its subcase |
| STATE_ID | OPEN-SEMANTIC | Dynamic activation/location identity attached to a source declaration; captured reads retain the source location while invocations and event IDs remain distinct | Local State source/Oracle audit: `StateSlotId` is a static origin; exact `start!` fixture is same-invocation evidence |
| STATE_RW | OPEN-SEMANTIC | Source `Read(slot,C)` and local replacement/update/restart equations, including exactly which live store reaches the saved suffix and later captured read | State capture observation §§1,4; ordinary bind alone does not perform replacement |
| STATE_RESUME | OPEN-SEMANTIC | Store received by raw resumption, branch/re-entry relation, and the equations for repeated/multi-shot resumed branches | Ordinary computation §2 takes actual resumed state; 324-case multi-shot model supplies its branch equations rather than derives them |
| REFWORLD | OPEN-PROOF | First-class reference/import alias plugging and transition closure for the source identity graph; `EnvStore/JointWF` at the same world/xi including semantic imports beyond closed reachability | Concrete compatibility §8 open graph/step-index candidate; static graph construction alone proves no world validity |
| SELECT | OPEN-SEMANTIC | Independent visible-implementation/candidate judgment for source scope, receiver and method; complete alternatives and exact selection evidence | Charter later gate; syntax role/impl surfaces do not establish visibility/coherence/receiver semantics |
| ROLE_ASSOC | OPEN-SEMANTIC | Role conformance and associated-type equations under the same type assignment and selected implementation witness, including recursive dependencies | Charter later gate; candidate alternatives cannot freshen associated types independently of their receiver/witness |
| RESOLVE_FP | OPEN-PROOF | Soundness, all-alternative completeness, principality and termination of joint method/role/associated-type/visible-impl solving | Charter later gate; no fixed-point order/finite canonical carrier has been selected or proved for this combined judgment |
| IFACE | OPEN-SEMANTIC | Complete simultaneous boundary fields, canonical form/equality and scope/use/reference correspondence adequate for every downstream inference observation | Authoritative rebuild addendum: printed schemes, arena IDs and individual value projections are insufficient |
| LIFE | OPEN-PROOF | Current live internal uses, independent fresh incoming uses, fixed imports, SCC split/merge cut correspondence, valid cached references and atomic full publication | Reviewed lifecycle theorem imports these hypotheses; current F4/F5 observations have bounded older scopes |
| LIMIT | OPEN-SEMANTIC | Structural/measured practical resource dimension, deterministic early rejection point, exact admitted result and no partial publication | Design-authority product priorities permit proportionate rejection; they select no successor limit or source semantics |
| HIR | IMPLEMENTATION-ONLY | Implement reviewed/approved raw lowering, complete constraint emission, solver/generalizer/instantiator/publisher/consumer wiring for the settled envelope | Actual current path in §7; no permission to cut over is provided by this audit; unsettled semantic contracts are tracked by the other leaves |
| ORACLE | OPEN-PROOF | Source-wide successor final well-typed-program capability and required observable behavior under the declared practical envelope, with concrete justified deltas | Charter §§2,4,8–12; frozen Oracle mechanisms remain historical evidence |

### Old gates that are actually closed, scoped or only implementation evidence

| Existing result | Status used here | Precisely what it removes | What it does not remove |
| --- | --- | --- | --- |
| Pure structural FMP and pure effective-search corollary | CLOSED | Pure regular-witness existence and pure effective-input SAT search | PHI/JDEC/JPROJ/source/Function/effect/world gates |
| Directional protection and fixed-fact replay | CLOSED | Selected upper producer, no-backflow and delivery-order dependence for certified facts | SIG original complete licensing; actual source-wide seed applicability |
| DREL-1 and source-entitled selected DREL-2 substitution | CLOSED in exact reviewed scopes | Additional proof that the same relation rewrite preserves active kernels | New primitive correspondence, arbitrary source roles, query existence |
| Selected SV receipt/rebind/capture | CONDITIONAL-CLOSED | Opaque selected receipt/capture association after original typed rows; Pending until actual rebind | Joint original validity, all worlds/contexts, general source coverage |
| K constructor-guarded recursive providers | CLOSED in selected envelope | Runtime recursive provider graph as an input | REC/GEN discharge, unrestricted initialization, original full membership |
| Exact complete-interface embedding | CONDITIONAL-CLOSED | Simulation from the candidate source machine to its exact possibly infinite carrier | Raw authoritative-source bridge, finite solver/presentation or production |
| Residual normalization factorization | CONDITIONAL-CLOSED | Exact constrained presentation with stable finite contexts and original predicates retained | CTX/PHI/JDEC/JPROJ and outcome-order/lifecycle generation |
| A-extension/A-allocation/matched abstraction | CONDITIONAL-CLOSED | Common/query extension for the specified guarantee/allocation/paired grammar classes | All valid public views, unmatched grammar licensing and production conformance |
| Complete boundary reuse substitution | CONDITIONAL-CLOSED | Extra downstream proof once complete equal interfaces and lifecycle premises exist | IFACE equality algorithm or actual cache/publication implementation |
| Current canonical pair/replay/copy owners | IMPLEMENTATION-ONLY evidence | Specific current binary key, constructor-DAG and symmetric row replay facts | Successor semantic finite contexts, source-size bound, general invalidation |

“CLOSED” here does not broaden an old review or certify this producer's note.
The new synthesis/reduction and proposed record deltas still need independent
review. Scope qualifiers are part of every status.

## 5. Implication DAG and minimum completion frontier

The following adjacency table is the deduplicated DAG implemented by the
checker. Edges mean prerequisites for the **named proof route**, not a claim
that solving one prerequisite proves the entire aggregate. A complete
alternative proof may replace a route; it must prove the same final targets.
In particular, source-constructor simulation is sufficient, not required,
for independently licensed production extras.

| Aggregate | Direct prerequisites | Result required |
| --- | --- | --- |
| SOURCE_J | SIG, INIT, HIST, RAW, REC, GEN, STATE_ID, STATE_RW, STATE_RESUME, REFWORLD | Independently formed complete joint source relation for the claimed envelope |
| COMPLETE | SOURCE_J | Independent admitted source has one same-scope complete joint witness |
| RESIDUAL | SOURCE_J, CTX, PHI | Exact finite constrained residual at original scopes |
| EFFECTIVE | RESIDUAL, JDEC, JPROJ | Terminating complete admitted solver/projection |
| COMMON | SOURCE_J, DESC | `forall xi,s in S_xi. exists a. Q_xi(s,a)` with legal common descriptor |
| ALLVIEW | COMMON, DIRECT, GEN | All independently valid public views lift through the actual export |
| PROD_RULES | SIG, INIT, HIST, SAT_A, ADM_A, PHI | Independent exhaustive production relation/domain |
| CONTAINMENT | PROD_RULES, DOM, OBS | Both full production containments in original fibers |
| EFFECT_HANDLERS | SIG, RAW, HIST, BOUND_ADAPT, EBRIDGE, SUBIMAGE, RELEASE, ORDINARY | Complete ordinary effect/handler and source-boundary theorem |
| SELECTION | SELECT, ROLE_ASSOC, RESOLVE_FP | Whole later mandatory resolution theorem |
| SOURCE_ADEQUACY | SOURCE_J, COMPLETE, EFFECT_HANDLERS, CONTAINMENT, SELECTION | Every included admitted source behavior and final typing is covered |
| SOUND | SOURCE_ADEQUACY, EFFECTIVE | Computed published solutions respect the stated source/abstraction |
| PRINCIPAL | SOURCE_ADEQUACY, ALLVIEW, EFFECTIVE | Every valid public view factors through the computed scheme |
| LIFECYCLE | IFACE, LIFE, GEN, PRINCIPAL | Complete generalized boundary and valid rebuild/use/publication behavior |
| PRODUCTION | SOUND, PRINCIPAL, CONTAINMENT, LIFECYCLE, LIMIT, HIR, ORACLE | Authorized implementation conforms on the declared practical source envelope |
| CUTOVER | PRODUCTION plus independent required review and explicit successor approval | Concrete reviewed rollout/rollback and production routing change |

Source-wide adequacy, principal factorization and production conformance are
not a chain in which pure FMP implies the others. They share definitions and
witnesses, but their final quantifiers remain independent. `COMPLETE` is an
explicit target inside SOURCE_J; it is not an external known-profile premise.
The finite DAG marks `SOURCE_J` open precisely because independent source
formation/nonemptiness and coverage are still unproved.

The minimum frontier is the leaf inventory of §4, with recursive producer
results incorporated at REC/GEN rather than duplicated here. CTX is distinct
from PHI: finite context identity does not interpret a predicate. DESC is
distinct from DIRECT: total common realization does not ensure all-view
query evidence. DOM is distinct from OBS: no returned observation proves
independent challenge admission. STATE_RW and STATE_RESUME are distinct:
threading supplied live state is not a source branch/replacement rule.

## 6. Effective joint solving: the exact missing bound

The hypothesis that “current source-context closure is Authoritative and
therefore supplies finite worlds” is false for the inspected sources.
[Source-context finite closure](../design/2026-10-03-source-context-finite-closure.md)
is Draft with reviewed **conditional** results. Its §2 explicitly supplies
`J_T` and a meaning-preserving `A_T` canonicalizer as input. Its §3 requires
source rule closure, finite labels/ports, no unbounded history identity in the
key, and terminating dependency updates. It proves a bound

```text
number of canonical comparison states <= |B| |J_T| |P|^2
```

only after those conditions hold. Current binary pair keys and constructor
DAGs do not provide these source-semantic premises. The old live-work count
also explicitly assumes immutable root/bound inventory and constructor DAGs.

Even a proved finite comparison-state carrier does not give a finite complete
space of source worlds, structural assignments, provider contracts or
histories. Pure FMP bounds a **pure structural** witness. A joint query may
read structural shape, original `K,D`, alias/store state, or future admission.
Changing that witness can change those predicates.

For the exact retained-identity solver route, the minimum sufficient new
certificate would be an effectively constructible finite candidate quotient
`q_C` with soundness and completeness for the **whole** input relation:

```text
JointSat(C) iff exists z in FiniteCandidates(C).
    Decode(z) satisfies Eq,B,Perm,Guard,Phi and original source predicates.
```

Every candidate check must terminate and retain all required query/evidence
alternatives; a projection step must then prove the exact public image of
that same joint relation. The existing pure `8^N` enumerator cannot serve as
`FiniteCandidates(C)` until an independent preservation/reflection theorem
transports **every** added primitive through its regularization/quotient.

A different finite-state predicate abstraction could cover infinitely many
worlds/histories without enumerating them. It must prove a finite
observation-equivalence that preserves and reflects every relevant primitive,
original witness incidence, scope and direct query. This is a legitimate
algorithmic proof direction and requires no semantic finite-world truncation.
There is no such complete source-generated quotient in the inspected package.
An arbitrary positive finite written recursive grammar alone does not prove
its membership, universal future-admission conditions or emptiness decidable.

The user's practical-resource permission concerns input admission and early
rejection under a documented deterministic boundary. It does not turn an
unbounded semantic domain into the first `n` worlds or histories of a search.
A timeout, bounded witness search or finite sampled response set cannot report
UNSAT/acceptance complete within the admitted envelope. Retaining exact
residual identity is useful and sound as a constrained presentation; claiming
complete final acceptance or effective principal projection additionally
requires JDEC/JPROJ. No new limit or world restriction is selected here.

This audit proves no undecidability theorem for actual Yulang. Uninterpreted
predicate placeholders alone cannot establish that the language realizes a
halting reduction. The obstruction is precisely the absent finite complete
candidate/primitive-decision/source-canonicalization certificate above, not
the broad assertion “effects are hard.”

## 7. Production, source coverage, later resolution and cutover

### Concrete production seam

At the baseline the actual inference path is
`SolvedModule::solve` to `InferenceSession::try_new(...).run()`, collected
constraints and frozen SCC scheduling, live worklist, F5 component
generalization, cross-SCC closed-scheme instantiation and result publication.
`SolvedModule` owns its HIR, ConstraintStore, closed type arena, schemes and
coarse projections. F5 generalization is reached in `yu-solver/src/lib.rs`
through `F5cGeneralizer`. Therefore replacing only the generalizer would
leave the collector, solver, instantiator, evidence and publisher unchanged.

The production `root_value_for` maps Function and other non-ground public
views to `Unknown`; it is not complete interface equality. The HIR file has
operator-associated Apply expressions and research-only source-call paths.
Those syntax/research structures do not establish production complete
`J_call`, Function membership/admission or symbolic profile discharge.
The current default-off inventory/shadow joins are evidence plumbing.

The remaining HIR task is a reviewed source-form coverage table connecting
each admitted literal/name/lambda/application/bind/annotation/handler/
operation/resumption/reference/role/impl form to its exact semantic emissions.
Nested/global/computed callees, complete annotations, patterns and conversions
need their own constructor rules where the current typed-core theorem imports
them. Then implementation must connect those outputs through the **entire**
path above. There is no parser, lowering or production inference change in
this artifact.

### Later method/role/associated-type/visible-implementation gate

This audit inventories the later mandatory seam; it does not start designing
its semantics before ordinary effects/handlers settle. Its minimum independent
judgments concern: visible implementations in the source scope/world; receiver
and method candidate formation; role conformance; associated-type equations
under a chosen implementation witness; and source selection/ambiguity outcome
with retained alternatives. These are placeholders for required source
judgments, not newly adopted rules.

Their joint fixed point must preserve one `nu`, original receiver/witness
identity and dependencies through method result/argument/effect constraints.
Selecting a candidate and then independently choosing its associated-type
solution is insufficient. Assuming positivity, a unique greatest fixed point,
or a finite candidate set from parser surface syntax would invent a premise.
The source clauses and proof are unconstructed in the inspected successor
packages. Existing syntax impl/role addenda expressly leave semantic selection,
visibility, coherence and associated types outside their scope.

### Boundary helper and source producer distinction

A default-off finite Path/Incidence query can implement the supplied-map image
law in typed-boundary §6 without establishing raw-source attachment, an
original profile's applicability, a release-attributed contribution, actual
crossing, or a live receiver. The operational consumers must receive those
facts from BOUND_ADAPT/RELEASE/SIG rather than manufacture them from reachability.
The helper's own finite graph/query coverage is an implementation subgate;
the source producer and full lifetime theorem remain the independent leaves
above. This inventory grants no blanket semantic discharge to shadow helpers.

### Final rollout gate

Completion requires the joint source/effect/selection theorem, common/all-view
principal theorem, complete production relation plus both containments,
effective solver/public projection, complete lifecycle interface and deterministic
resource boundary. Independent semantic/specification and material resource
review must cover the frozen successor design, then explicit approval must
authorize the concrete implementation/rollout. Final Oracle capability and
observable behavior must be checked on the stated admitted envelope, with
exactly documented justified differences. Stage formatting and F5-specific
closed-scheme alpha equivalence are not successor compatibility targets.

No production cutover is authorized or performed. The final approval remains
a procedural gate; its absence is not labeled a semantic user-decision blocker.
There is no need to ask the user another E/R or local-protection question.

## 8. Remaining-route falsifiers and their scope

Four compact inference falsifiers complement the shared-completion witness:

1. **Totality does not supply all-view Direct.** One source solution `s`, one
   legal allowance `a` and `Q(s,a)` satisfy common totality. One independently
   valid view `v` and an empty `Direct(s,a,v)` relation fail all-view lifting.
   Exact preservation of that empty query does not repair it. This is the
   smallest relational independence witness, not an actual resolver bug.
2. **Reference containment does not cover production extras.** At one admitted
   challenge, exact reference actual/checked bounds can both be `{good}`;
   production actual `{good,extra}` and checked `{good}` fail containment.
   Only independently licensed actual extras count in a real source theorem;
   this witness proves the logical need to quantify over them, not that this
   example is licensed by Yulang.
3. **Compressing local evidence can lose completeness.** The already approved
   optional-Record endpoint example has
   `{foo?:string} <: {}` and `{} <: {foo?:int}`, while the direct
   `{foo?:string} <: {foo?:int}` fails. Consequently a whole source pullback
   must retain the intermediate query/evidence and cannot replace two source
   `Sub` derivation steps by a third concrete Direct query. This applies to
   the proposed proof route; the previously reviewed playground already
   identifies the old Name/recursive-generator compression failure.
4. **Pure existence does not entail joint existence.** A nonempty structural
   fiber and an empty independent `Phi`-admitted fiber have empty intersection.
   The constructive FMP witness is a structural witness, not a proof of that
   joint predicate. This is logical scope separation, not an admitted source
   predicate counterexample.

These are not offered as another source-semantics model. The useful delta is
the unified minimal leaf frontier and one-completion reduction; the falsifiers
audit exactly which proposed implications would be unsound. No compatible
profile impossibility, all-view failure or undecidability of actual source is
claimed.

## 9. Checks, dependencies, omissions and handoff

The companion standard-library-only checker validates the deduplicated gate
IDs/status vocabulary, dependency targets and acyclicity; checks the positive
same-witness completion construction and five distinct inference cuts; and
prints SHA-256 of the frozen dependency set. It performs no parsed-source
acceptance, no production inference, no effect/world interpretation and no
semantic enumeration. The reference and candidate share the supplied finite
relations in those algebra checks; this is not independent source adequacy.

Verification budget: one lightweight Python process, at most 60 seconds and
1 GiB; zero Cargo/build/workspace-test processes. The primary owns heavy
verification. No children, Git mutation, shared record edits, production code,
test expectations, question-board bundle or authority change were made.

Executed verification:

```text
timeout 60s python3 -B -c 'import pathlib, resource, runpy; resource.setrlimit(resource.RLIMIT_AS, (1073741824, 1073741824)); p = pathlib.Path("tools/research_successor_global_synthesis.py"); compile(p.read_text(), str(p), "exec"); runpy.run_path(str(p), run_name="__main__")'
```

Result: PASS, **61 unique nodes and 64 acyclic dependency edges**; positive
shared-completion construction and five distinct inference cuts pass. Python
syntax compilation ran in that same process without `__pycache__` output.
Tool-reported wall time for the apply/check call was 4.3 seconds, including its
small preceding patch; separate Python CPU/peak memory were not measured.
The process had the explicit 1 GiB address-space ceiling and 60-second timeout.
No seed range or semantic case count is claimed.
Separate `git diff --no-index --check /dev/null <leased-path>` inspections
reported no whitespace diagnostics for either new artifact; their difference
exit status is expected for new files. A final read-only HEAD check still
returned the full pinned baseline above.

Dependencies are the exact baseline files named by `DEPENDENCIES` in the
checker. New proof directions also cite DFRAG/SV as existing reviewed
transport machinery; no unpublished concurrent producer edit is consumed.
At integration, compare that list's hashes against the pinned baseline and
the frozen review snapshot. An unrelated branch advance does not invalidate
this audit; a change to the original world/signature/query meaning does.

Salient frozen dependency SHA-256 values (the checker prints the full 38-file
snapshot; every dependency is also fixed by the full baseline SHA):

| Dependency | SHA-256 |
| --- | --- |
| `tasks/current.md` | `6ca2565ca2f338bf19ec542061e9c86bf506d5b5067b0fa5c129e405eaebc09e` |
| `notes/theory/inference-theorem-dependencies.md` | `de2e6bfed00e5239d27a2fd51cc99a92dc5836bb9434edf05e51467b68d0dd68` |
| `notes/theory/inference-theory-map.md` | `241a740fe8a67ab6c46e77317ddaea887a7b0285454cbcaab065fc037bf063f4` |
| `notes/design/2026-10-03-source-context-finite-closure.md` | `dba409842c631d81dfeedbeafc7ca34dcd9edeaaa0a80f49bba0cb3f6916f8cf` |
| `notes/design/2026-10-04-common-allowance-context-preimage.md` | `e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `00f9e4e8db427fe97a46bd25245cf235c02d2e38007c5b9bb9088d9b40db8636` |
| `notes/progress/2026-10-06-directional-profile-completion-factorization.md` | `f3a1261968db9edac0c8841151d90c35fc1cf9649c00bd7beb5d18f748239d4d` |
| `notes/progress/2026-10-06-directional-source-view-instantiation-construction.md` | `462d792e518409199f77bb20a41aaa54d64898fe30363f98f0afff7ab3f805e3` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` | `df33959fffeac0003723909de5af11edce2bd233ff70496a0dc5d3864126baff` |
| `crates/yu-hir/src/lib.rs` | `ce6fcff5d87a89d7185c0c748a5e0a9482e489f2c21a5548da8b72041dd65727` |
| `crates/yu-solver/src/lib.rs` | `3c6fee29904859ed30957469a60aac71a4f6236de0155f2a22a597dcd81e2910` |

Omitted verification: independent review of this new note; proof of SIG/INIT/
complete nonemptiness; exhaustive source constructor coverage; actual State
read/replacement/resume and method resolution semantics; generalized interface
implementation; complete production membership/admission; all-view lifting;
effective joint solver/projection; parser/Oracle/VM/native execution;
resource measurements; any production rollout. Existing old review scopes
are preserved, not reused as certification of this note.

Proposed commit: `research: deduplicate successor global gates around one joint source relation`.

Shared record deltas, deliberately deferred to the primary/curator:

- Add the one-completion reduction as proof-architecture progress, keeping
  complete source nonemptiness and exhaustive signature/world licensing open.
- Represent INIT/SIG/HIST/PHI as shared leaves of source and production routes;
  remove duplicated opaque completed-profile/world inputs at local seams.
- Keep actual-common-export Direct completeness distinct from common totality,
  and production extra-member containment distinct from source-reference
  realization.
- Correct any implication that the Draft conditional source-context closure
  is Authoritative or proves finite semantic worlds; record the exact
  finite-candidate/reflection certificate still needed for JDEC/JPROJ.
- Split State into source dynamic identity, local read/replacement and resumed
  branch equations, plus open-world/reference closure. Split later resolution
  into source candidate/visibility, role/associated-type coupling and the
  joint resolution fixed-point theorem.
- At integration split the baseline `IFACE` row into complete source-interface
  producer/semantic equivariance (`IFACE_FORM`, open) and effective equality
  of the selected representation (`IFACE_EQ`). A separately reviewed recursive
  packet may supply finite graph alpha equality and conditional joint fresh
  transport; that closes only those supplied-graph operations. It does not
  establish source production, general semantic interface equality or full
  equivariance. This proposed delta consumes no unfinished concurrent proof
  and the packet's exact status remains for the primary to adjudicate.
- Link the leaf/aggregate DAG only after independent review; do not relabel
  universal source adequacy/principality/production readiness as closed.

Outputs freeze at submission. The producer does not integrate or mutate Git.
