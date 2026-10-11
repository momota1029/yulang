# `invoke`: original Simple-sub derivation and the complete Call bridge

Date: 2026-10-11
Baseline: `72de8a8389825b395bc910654aa030ad82a289b0`
Branch: `research/simple-sub-intrusion`
Reference: `9bae772624c23b52a93c1b226157e16898b4d9db`
Producer: `/root/invoke_original_call_proof`; leaf, no delegation
Status: independently reviewed bounded ordinary derivation/source-bridge result; original Yulang theorem OPEN
Lease: `notes/theory/2026-10-11-invoke-original-call-proof.md` only
Requested runtime: `gpt-6.1-sol` / `high`; observed model/effort: unknown
Semantic adoption, implementation, Git integration and certification authority: none

## 1. Frozen statement and result

Fix the actual resolved source `S = my invoke f = f 1`, Lambda `L`, its
unannotated formal `d_f`, the resolved body Name `u_f`, inner Apply `c`, and
literal occurrence `a`. Preserve its actual `B,X,T`, `Resolve(u_f,d_f)`,
callee/argument incidence, original scopes and one joint `xi=(nu,K,D)`.
The formal's ordinary description is introduced before invocation challenges;
dynamic receipts, returned values, responses, current worlds and body witnesses
remain below their actual event binders. Empty lexical capture is a fact about
this source, not a restriction on carriers supplied to it.

The assigned conclusion is the original source-to-native Simple-sub theorem
for this source, including complete Call, lawful source Generalize, soundness
and required principal order. Construction must precede clients, assignments,
challenges and histories. The independent source judgment is
`rho; T |- S @ a_b : R ! C [d]`, as selected by source Generalize §3.1.
Both source-to-generated and generated-to-source directions must preserve
one joint assignment/strategy, actual objects/providers and original binder
dependencies. All independently admitted complete challenges, every genuine
actual provider decomposition, licensed W/Z alternatives, compatible punctured
contexts, pending/divergent developments, current guards, responses, raw
resumptions and compatible finite future histories remain in scope. No
Return, empty-effect, pure-provider or fixed-client hypothesis is added.
The public principal and production/F5 obligations remain distinct.

**Result.** The original Parreaux typing theorem needs no formal-interface
map: its T-Abs binds an already typed ordinary value. Its direct derivation
and ordinary principal scheme apply to the paper term `lambda f. f 1`.
They do not supply the entry premise of the selected Yulang Lambda rule.
For Yulang, the necessary content is the authentic contextual admission and
typed entry/transport law at the actual `L,d_f`, on complete independently
admitted challenges. A particular standalone raw-inlet map or registry record
is not shown necessary. The direct route still stops before forming the
post-entry typed body environment; the current native constructors do not
establish that semantic premise in the inspected dependency cone.

This is a bounded source-correspondence obstruction, not a source-qualified
counterexample or an impossibility theorem. The ordinary derivation below is
included to locate the exact application of the imported base, not as another
finite projection result or conditional carrier lemma.

## 2. Exact governing inputs

The top-level inference principles §§1–5 and Evaluation require native
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
and generalization; they permit no speculative search or per-constraint eager
solving. Governing workflow sections are agent-orchestration **Model routing
and Astra escalation / Proof delegation and decomposition**, research-lab
**One semantic baseline / Evidence quality and stopping unproductive loops**,
compiler-engineering **Natural compiler behavior and proof-obligation economy /
Deterministic Simple-sub inference**, design-authority **Authority order**, and
git-concurrency **Disjoint-file mode**.

Semantic and mathematical owners:

| Exact source | Governing fact |
| --- | --- |
| Permanent paper `/home/momota1029/rust/simple-sub-reference-paper.pdf`, Fig. 3, printed p.124:4; §5.3, pp.124:26–27 | Ordinary declarative rules; soundness/principality directions and general constraining lemmas. §5 restricts its proof discussion to non-let-polymorphic inference and omits full proofs. |
| Permanent reference `shared/src/main/scala/simplesub/Typer.scala:59–74,88–129,239–257` | Actual ordinary generation, opposite-bound replay and coalescing. |
| [Reviewed import](2026-10-11-parreaux-simple-sub-proof-import.md), §§2–6 | The imported theorem's exact quantifiers, scheme order and coverage; no Yulang extension theorem. |
| [Charter](../design/2026-09-29-scc-intrusion-redesign-charter.md), §§16–18,21,24 | Whole inert argument; one-layer Value entry inside the same receiver; source-fixed roles; actual callable role is retained. |
| [Source Generalize](../design/2026-10-08-source-generalize-definition.md), §§2–4; [construction](2026-10-08-source-generalize-definition-and-proof.md), §§2–3.3,6–7 | Independent source judgment and original Desc/Event scopes. L1–L5 remain genuine local premises; selection does not supply an unprovided source law. |
| [Call-input rules](2026-10-07-call-input-construction-proof.md), §§3.1–3.3 | Static Entry-Value requires actual ParameterOrigin, received carrier/designated view and receipt/rebind ports before Data-Lambda/Code-NameValue. |
| [Contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md), §§2–4; [realization](2026-10-08-call-semantic-input-realization.md), §§3.1–3.3,4.1–4.3 | Same actual provider accepts every independently admitted complete challenge; every complete/pending/future observation satisfies the full envelope. Raw ViewInlet is a sufficient route, not necessary. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md), §9:912–996; [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md), §6:675–819 | Received carrier, body and complete invocation differ. Transport acts on already typed paths/packets; Force removes matching result prefix, rebind uses identity at unchanged type. No profile is reconstructed from row support. |
| [Call source interface](../design/2026-10-08-call-source-interface-definition.md), §§2–4 | Placement retains independent whole operator/port contracts and does not establish their original typing/admission laws. |

The three supplied local notes and falsification audit retain their exact
status: [value projection](2026-10-11-invoke-value-projection-proof.md),
[entry expansion](2026-10-11-invoke-entry-entry-law-proof.md),
[formal-interface cut](2026-10-11-invoke-actual-formal-interface-proof.md),
and [map audit](../progress/2026-10-11-invoke-formal-map-falsification.md).
Their conclusions are neither repeated nor promoted here.

## 3. Direct original typing and native ordinary inference

For every ordinary monotype `B`, in the paper's declarative system:

```text
Gamma_B = { f : Int -> B }

Gamma_B |- f : Int -> B       Gamma_B |- 1 : Int
------------------------------------------------ T-App
Gamma_B |- f 1 : B
------------------------------------------------ T-Abs
empty |- lambda f. f 1 : (Int -> B) -> B
```

T-Var's quantified-variable list is empty at the lambda-bound `f`; it returns
that same monomorphic binding. Under `f : A meet (Int->B)`, T-Sub gives the
same function premise, yielding `(A meet (Int->B))->B` instead. No provider,
carrier, receipt or path witness is selected by any of these rules.

The actual upstream execution from empty store at level `l` allocates `alpha`
for the formal and `beta` for the result. Name returns the same `alpha` by
`SimpleType.instantiate` identity (:207); literal returns canonical `IntType`
(:21,:73–74). App submits `alpha <: Function(Int,beta)` and returns `beta`.
Both variables have level `l`, so :115–117 stores that upper on `alpha` and
replays its empty lower list. Lambda returns `Function(alpha,beta)`. Thus
ordinary coalescing gives

```text
C = (alpha meet (Int -> beta)) -> beta
D = (Int -> beta) -> beta.
```

Preserve the paper's scheme order: `P <=forall Q` means **there exists one
type substitution** `rho` with `rho(P) <= Q`. More general schemes are on the
left. `C <=forall D` uses `alpha := Top`, with the same `beta` in the demand
and result. `D <=forall C` uses identity and outer-arrow contravariance.
Therefore their free-variable closures are equivalent. The imported published
Theorem 2 applies to every ordinary derivation `empty |- t : tau` of this
non-let term and asserts `C <=forall tau`, hence `D <=forall tau`; Theorem 1
has the reverse soundness direction `tau <=forall C` for some derivable tau.
This application retains the published theorem's omitted-proof coverage.
It is not an independently completed proof of §5.3 or a Yulang theorem.

At reference top-level let, :48–55 runs the RHS at `l+1` and wraps its
unchanged graph in `PolymorphicType(l,...)`; :166–189,:201–202 freshen both
variables and bound occurrences together. This operational fact has no
complete let-correctness proof in §5 and no Yulang Generalize consequence.

## 4. Where the direct complete source derivation stops

The selected Yulang Parameter rule supplies `Desc(C,d_f,value,sigma_f,Delta_f)`
and `Value(A_f)` before challenges. Capture-Lambda yields Empty because this
Lambda's only Name resolves to its own formal. These are authentic source
facts, not an incoming-carrier or provider choice.

The next static rule is Entry-Value (Call-input §3.2). Its input is the
actual original ParameterOrigin and typed received/designated/receipt/rebind
ports; its output is the body environment
`ValueBind(Empty,d_f,r_f,A_f,actual entry/rebind origin)`. Name lookup can
then retain this binding, and Code-Result can Return the same decorated
value/provider. The ordinary T-Abs step above has no corresponding entry
premise: `Gamma_B` is already a typed value environment, while the Yulang
Lambda receives an independent whole computation before such an environment
exists.

The semantic necessity can be checked without adopting Entry-Value as the
only possible representation. Invert the selected complete Function meaning
for this actual closure `Act(v_L,U_L,r_L)`. For **each** independently admitted
complete challenge `d` of it, clause 2 requires `ActualAdm(v_L,U_L,d)`.
Clause 3 requires all actual observations and admitted developments at the
same `U_L,d` to satisfy its complete envelope. Operational inversion of the
Value entry reaches receipt and the designated Force before the body.
On a Return branch, the body's Name validity therefore needs the actual
returned decorated value's hereditary membership, its actual post-entry world,
and its original receipt/result-to-formal path correspondence. On a Request,
divergent or unfinished branch, the request/current guards and pending suffix
must retain their original typed positions; no body binding is manufactured.
These facts are required to apply the source Lambda/Name/Call rules for the
original domain. They cannot be obtained by treating the formal as an already
typed returned value.

The precise unresolved source premise is consequently:

> At the original Parameter/entry owner for `L,d_f`, construct the actual
> complete received view and its source/profile/guard/port interpretation
> before challenges, and prove that each independently admitted complete
> challenge has lawful actual receipt and one-layer entry. Every Return
> supplies the same-result hereditary ValueBind at the original typed paths;
> every nonreturning prefix preserves its original request/continuation and
> remaining entry obligations. Static and event-dependent fields retain
> their original predecessors. None of these conclusions is an added premise
> of the parent source theorem.

This is the semantic content needed at the seam. It does **not** demand a
total raw inlet action for carriers lacking complete compatible challenges:
realization §3.3 expressly separates that stronger action. Nor does it demand
a particular registry data structure. A direct constructional proof using
the authentic source domains and matching paths could supply the same content.
In the adopted static interface route, that proof must establish the actual
Entry-Value inputs/application; scalar endpoint or type-variable equality
does not supply them. Generic result-prefix/identity transport is already
available once its actual typed domains are formed.
This distinction waives no original typed-port/map premise of an active
consumer, and it does not establish that the previously missing formal
interface has been constructed.

There is a second, downstream cut for the inner body Call. The same received
`f` must meet a **complete** callable description at the actual body use, and
the Call-owned whole literal carrier must form an independent checked challenge.
Function elimination then gives acceptance and observations for that same
returned provider. Ordinary `alpha <: Int->beta` supplies only its ordinary
value demand, not these full Yulang interpretation/formation conclusions.
The current attempt cannot reach that cut with a completed source derivation
because the post-entry environment premise above is unresolved.

## 5. Exact current construction/consumer bridge

The current owners establish the following prefix; none is assumed from a
checker accepting supplied transitions.

| Actual owner at baseline | Construction or consumption established by inspection |
| --- | --- |
| `crates/yu-hir/src/module.rs:911–920`; `shadow_apply.rs:79–113`; `lib.rs:1126–1135` | Actual parsed-file LocalSource lowering enables the retained source carrier; CandidateInference selects graph/effect collection and executes the emitted source schedule. This is an opt-in candidate route, not production source acceptance. |
| `crates/yu-hir/src/module/local_source.rs:289–321,553–574` | Installs the actual formal lexical resolution before body lowering; retains distinct callee and argument source slots. |
| `crates/yu-solver/src/candidate_source.rs:189–216,239–245,543–559` | Registers the formal recipe, routes its Name to the same parameter endpoint, and installs its one native positive root. |
| `candidate_source.rs:336–350,369–411` | Emits both literal value bounds and pure literal/Name evaluation bounds; builds Apply from the actual source children and formal Name registration. |
| `candidate_source.rs:639–671` | Executes actions synchronously; advances the source cursor only after successful admission. |
| `shadow_apply.rs:1331–1400,1422–1468` | Builds negative Function4 with argument value/effect, invocation effect and result value; stores source-native incidence and actively submits value/effect constraints. |
| `lib.rs:11233–11362` | Uses the same formal in positive Lambda Function4; allocates entry and complete-invocation effect rows, actively constrains entry/body effects into invocation, and retains Lambda-owned inferred-entry provenance. |
| `candidate_extrusion.rs:763–838` | Inserts native row bounds before constructing opposite-bound replay tasks. The actual initial path calls `candidate_context_drive_replay(replay,None)`, not the separate child-drain route. |
| `lib.rs:12493–12541` | On a Function/Function comparison derives argument value/effect children contravariantly and invocation effect/result value children covariantly from that same pair. |
| `candidate_call.rs:16–59,376–437` | Validates actual formal/Name/Lambda incidence and borrows native endpoints; these structs contain no whole typed received-port or admission proof. |
| `candidate_call.rs:81–90,217–245` | Keeps actual formal introduction, whole registration interface, Gen-Call, argument Reify/whole carrier and receiver/result/future suppliers explicitly pending. |

The successful initial replay and acknowledgement bridge is already established
in the reviewed value-projection note §4; this attempt does not reprove or
extend it to later semantic providers. Its actual queued/terminal owners were
also rechecked at `candidate_context.rs:3089–3123` and
`lib.rs:12154–12165,12614–12633`: queued replay is not completion; the typed
drain completes the retained acknowledgements before ReturnReady.
There is no positive Function lower on
the formal in the isolated source construction, so that initial trace never
executes the Function/Function consumer. The consumer's four correlated
children are real code, but reachability for each semantic provider and their
complete semantic interpretation remain further proof obligations.

The same-level source has no annotation/copy/use that creates a younger-row
parent in the reviewed initial trace. This is not a restriction on later
clients. No proof of cross-level extrusion, qualifying intrusion, later
activation completeness or Generalize is imported from this observation.
In particular, Source Generalize's SRC/GS/GC uses original local laws L1–L5;
using it here cannot manufacture the missing L2 entry/Call instance.

## 6. Economy audit, stopping point and handoff

The earlier raw local-family route and carrier-elimination route left actual
source formation untouched. The direct ordinary-rule route here tests whether
that work was required by the imported base: it is absent from the ordinary
theorem, but the **contextual entry/admission/transport content** remains required
by the selected Yulang theorem. This audit makes no gate-status or semantic
change. Stop here instead of producing another equivalent conditional lemma.

The complete same-provider source entry/Call correspondence is A/B: soundness
and natural inference require it. An arbitrary raw-inlet totality theorem is
a stronger C route unless separately required by Authority. Reconstructing a
path map after an owner already produced and justified it would be D; the
inspected native owner retains source identity and scalar entry provenance,
but no such complete justified map has been established there. More IDs or
a new package would not prove its original semantic formation.

One next action: assign the source Parameter/entry owner the exact contextual
premise in §4, with the actual received typed domains and source guards, and
require its direct application at `L,d_f`. Permit either a constructive
source-law proof or its authentic typed-interface application; do not impose
the stronger raw ViewInlet route. Only after this premise is established can
the body Call use the original complete literal challenge and same-provider
Function elimination. Fresh independent review remains primary-owned.

Unverified: this required entry premise, literal Reify/whole challenge, complete
Call and all W/Z alternatives, source/native full interpretation, extended
constraining soundness/completeness, effect hygiene, cross-level extrusion and
intrusion, source Generalize correspondence, principal public output,
successful suspension/abnormal publication, ordinary HIR adoption and F5.
No actual source rejection or semantic counterexample is claimed.

## 7. Checks, resources and commit packet

Reads: the listed governing rules/skill/configuration and original source
definitions, upstream Fig.3/§5.3 via `pdftotext -layout -f 4 -l 5` and
`-f 26 -l 27`, and bounded constructor/consumer slices using `rg`, `sed`
and `nl`. Broad combined captures that truncated were followed by focused
reads of the decisive clauses. No build, test, executable probe, Oracle,
formatter, child process delegation or Git mutation was run. Note-only
integrity and baseline/dependency comparisons are recorded below.

Resource envelope: one Sol/high leaf lane, 45-minute maximum; lightweight
sequential reads and note construction only, zero build/test/probe processes.
Numeric CPU time and peak RAM are unmeasured. No Astra was requested or used;
runtime model/effort metadata is unavailable to this leaf.

Commit packet:

- Exact leased path: `notes/theory/2026-10-11-invoke-original-call-proof.md`.
- Baseline: `72de8a8389825b395bc910654aa030ad82a289b0`; reference baseline:
  `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Claim/review status: unreviewed constructive bridge attempt and minimized
  source premise; no original Yulang theorem closure or certification.
- Checks: focused source/authority reads; UTF-8 note/local-link/fence/whitespace
  integrity passed; all 28 direct tracked dependencies matched their pinned
  baseline bytes; reference HEAD matched its pin. No builds/tests.
- Proposed checkpoint: `research: separate invoke ordinary typing from contextual entry bridge`.
- Shared-record deltas for the primary/curator: retain parent/entry/Call and
  principal/F5 gates OPEN; record that no standalone raw-inlet map is a premise
  of Parreaux's theorem or necessary for the selected contextual Function
  meaning. The actual source-owned contextual entry law remains required.
  No task, index, theory-status, authority, question-board or compiler file changed.

Dependency evidence: the 26 tracked paths in §2/§5 plus
`crates/yu-hir/src/module.rs` and `crates/yu-solver/src/candidate_context.rs`
were compared byte-for-byte to `git show <baseline>:<path>`; changed dependency
hashes: **none**. Reference SHA-256:

```text
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 Typer.scala
5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698 simple-sub-reference-paper.pdf
```

The producer's writes are frozen on return. A new independent review and
primary adjudication are still required before any proof-status promotion.
