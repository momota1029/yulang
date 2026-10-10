# Current task: complete type inference and replace F5

Date: 2026-10-08 UTC
Branch: `research/simple-sub-intrusion`
Status: full objective remains active; selected source/projection theorems and bounded HIR/core shadow mappings exist, while source completeness, inference/principality, production correspondence, successor approval and F5 cutover remain open

## User objective and branch boundary

The active user objective is to complete type inference and replace the F5
implementation on `yulang3`. The current working/push branch is
`research/simple-sub-intrusion`; fetched `origin/yulang3` is its ancestor at
`32f0a06314434c5dec12383f6b20f2cbcf472752`, with zero commits unique to that
target and 2,203 commits unique to the research branch at inspected checkpoint
`7334dcfdb` (the remote target ref was rechecked directly). The bounded
`yu-core`/HIR/solver/types diff at that checkpoint is 82 files with
39,741 insertions and 249 deletions, largely shadow research paths, with
additional F5 source edits. Current checkpoints have been pushed only to the
research branch. No F5 replacement or target-branch integration has occurred;
the large branch range and all Gate E / semantic / production approval
requirements must be treated as explicit integration work, not as completed
cutover.

## Proof and task-decomposition dispatch (2026-10-10)

Use the [Sol proof/task-decomposition roles](../notes/design/2026-10-10-proof-and-task-decomposition-roles.md)
under the [bounded delegation policy](../rules/agent-orchestration.md#proof-delegation-and-decomposition).
`task_decomposer` proposes concrete dependency-aware packets when needed;
`prover` owns constructive proofs, with complementary `researcher` methods.
The custom `prover` role is registered through `.codex/config.toml`; a prior
standalone `codex exec` session is confirmed by its JSONL record to have launched
a real child with `agent_role=prover`, `model=gpt-6.1-sol`, and `effort=high`.
That leaf derived a conditional Function-path polarity and exact-witness
residual result; attachment, typed transport, owner, and consumer construction
remain premises, so it did not prove source construction or close effect
hygiene. The current collaboration schema omits the `prover` role. For proof
work in a configured checkout, use `tools/codex-prover.sh` as the fallback
launch surface even while another team is active; its nested Codex session must
dispatch the registered `prover` role, and the primary must verify the JSON
event stream or child session. If that launch surface cannot start a real role,
immediately fall back to a supported generic worker with the full proof
contract and report that identity honestly. The helper also works for fresh
standalone sessions. Apply the `yulang-proofs` skill, record requested and
observed settings separately, and never describe a generic fallback as a
custom `prover` launch.

A second live launch through `tools/codex-prover.sh` is confirmed in the child
session JSONL as `agent_role=prover` (`/root/retained_input_proof`). The request
was Sol/high; this session did not expose the child's effective model/effort.
It produced the unreviewed conditional derivation in
[`retained-input-indistinguishability-proof`](../notes/progress/2026-10-10-retained-input-indistinguishability-proof.md).
The finite supplied-model check passed; source-reachable readiness separation
and the readiness gate remain open.
The current collaboration tool schema also omits `prover`. This turn used the
same configured fallback and authenticated a fresh child
`/root/function_port_proof` with `agent_type=prover` in the Codex session JSONL.
The request was GPT-6.1 Sol/high; effective child settings were not observable.
Its conditional Function-port effect-order derivation is recorded in
[`function-argument-effect-contravariance-proof`](../notes/progress/2026-10-10-function-argument-effect-contravariance-proof.md).
An independent compiler-referee review confirmed the algebra and source bridge;
the reviewer’s minor frozen-source locator correction was repaired. This does
not prove arbitrary effect hygiene, source reachability, full runtime
consumption, or inference soundness.
The selected primary keeps scheduling, authority, independent review and Git.
Normally use Sol/high proofs and Sol/medium decomposition. A proof coordinator
may use at most two preallocated leaf workers, including a justified native
Astra escalation, within the existing global lab budget. This workflow change
does not close or reclassify any inference/semantic/production gate below.
For restoration replay, direct collaboration dispatch with
`agent_type=prover` returned `unknown agent_type`; the primary immediately used
a prover-equivalent generic leaf with the exact proof packet. Requested
Sol/high; observed model/effort unknown. Its bounded snapshot derivation is
recorded below and does not claim that a custom `prover` ran.

## Objective and canonical obligation ledger

This continues the global natural-compiler/proof-economy objective while
preserving the full implementation/cutover end state. Do not treat documentary
localization alone as completion. Reevaluate why obligations exist, retain
facts at their owning constructor, separate stronger research
characterizations where actual dependencies permit, and minimize the genuine
theorem families needed for safe, natural compiler operation. This does not
weaken soundness, required principality, any approved source behavior, Option 2
extras or independent open-world admission.

The single active normalized inventory is the
[successor proof-obligation DAG](../notes/theory/successor-proof-obligations.md),
with [machine data](../notes/theory/successor-proof-obligations.json) and
[validator/generator](../tools/research_successor_obligation_dag.py).
It covers every requested family, including previously hidden signature,
world, guard, State, method, resource and production leaves. Each node has
its retained premises, closed lemmas, smallest remaining claim, direct
prerequisites/downstream gates and production relevance. Exact cited theorem
scopes govern; navigation text supplies no new Authority.

### Current proof-economy architecture

Audit baseline: remote `911204e1b1d4455077829440b16eab32c7a64d09`;
revalidated through `7bf7083419f677eacaf1b76525ce4c06bc2da908`.

- [A/B/C/D audit](../notes/progress/2026-10-07-successor-proof-surface-audit.md)
  and [machine table](../notes/progress/2026-10-07-successor-proof-surface-audit.json):
  all 83 non-CLOSED canonical nodes and their major internal cuts.
- [Reduced production proof architecture](../notes/design/2026-10-07-successor-production-proof-architecture.md):
  construction responsibility, shared proof cases, exact Authority constraints,
  consumer-level research separation and cutover impact.
- [Pro handoff](../notes/theory/2026-10-07-successor-pro-theorem-handoff.md):
  four semantic theorem families plus the engineering lifecycle invariant.
- [Independent review and integration](../notes/progress/2026-10-07-successor-proof-economy-review.md):
  two initial review lanes, one batched repair and fresh delta review closed
  the three accepted findings. The latest INTRO/SEED_SOURCE/REC_INIT and
  identity-crosswalk changes were separately revalidated without a finding.

The four targets are original source constructor agreement; independent
open-context operational/Option 2 production safety; exact solving and whole
phase preservation; and natural source inference/principality through the
actual designated export. They are proof families, not four proved theorems or
four remaining atomic lemmas. Actual implementation/lifecycle correspondence
remains a separate engineering invariant.

The canonical DAG now has 90 nodes / 196 edges: 7 CLOSED, 21
CONDITIONAL-CLOSED, 43 OPEN-PROOF, 18 OPEN-SEMANTIC and 1
IMPLEMENTATION-ONLY. No status, prerequisite, original predicate or
production-relevance field changes in this audit. Stronger arbitrary-view and
generated-domain characterization remain intact as existing research targets;
the alternate cutover route is not available until every retained consumer
obligation in the architecture is established. Required completed-contract
principality, all compatible contexts and exhaustive production extras remain.

### Completed native source Generalize (2026-10-08)

The selected native source rule subsystem defines `Generalize_source(S,b)` at
the actual source result and proves direct construction/inversion plus joint
soundness and lawful-use completeness for its finite source-rule class. The
reviewed [definition](../notes/design/2026-10-08-source-generalize-definition.md)
and [SRC/SRC-J/GS/GC proof](../notes/theory/2026-10-08-source-generalize-definition-and-proof.md)
retain the original relation, exact eligible declarations, fixed dependencies,
scope nesting, whole admitted uses and source-owned rule witnesses. They do
not use the public export or an F5 query as a premise.

This closes the native source-rule construction in its stated local-law
envelope. It remains separate from the actual transformed, displayable public
scheme selected by the approved root-policy answer: that answer requires the
public use to be justified from the transformed export and rejects hiding the
whole source relation in its extra data. Actual public-root formation,
membership/admission, use preservation, required principality and production
correspondence remain open. No implementation or cutover authority follows.

### Completed native transformed projection export (2026-10-08)

The current user-authorized [native projection selection](../notes/design/2026-10-08-native-projection-public-export-definition.md)
and [integrated PE-ID/PE-PICK proof](../notes/theory/2026-10-08-projection-public-export-construction.md)
now close the first transformed-public semantic gate for authentic immutable
unannotated `my id x=x`, and for pick with the stated constructed finite public
imports. This is the actual transformed public root, not a retained source
root queried under another name. The finite object is a displayed scheme plus
whole inlet/IF/scope/result-dependency data and ordinary certificate slots;
there is no use-time source body or complete source relation accessor.

PE-ID preserves exact retained solution-and-complete-observation fibers for
every finite independent native source-lawful joint use grammar and arbitrary
well-scoped W. Only forced raw aliases are eliminated; all logical choices,
worlds, ports, intermediate evidence and original dependencies remain. The
defined native ordinary consumer has Value, Computation and complete Function
cases at the actual public roots, including whole-callable Any/union checks,
nonidentity result checks and genuine domain restrictions. Concrete Option 2
extras remain independent of source execution. PE-PICK covers literal captures
and finite acyclic imports of already constructed public contracts, with
their actual monomorphic free dependencies fixed.

Both independent mathematical and specification final reviews passed after
repairing the missing whole-value query case. The [review record](../notes/progress/2026-10-08-projection-public-export-review.md)
records the frozen theorem, code checks, accepted findings and exact scope.
The [reference checker](../tools/research_projection_public_direct.py) passed
29/29 targeted cases but implements only a conditional same-I Function proof
fragment under genuine independently typed whole-interface inputs. It does
not implement the full native calculus or establish production H7/F5 behavior.

The source Generalize algorithm, SRC/SRC-J/GS/GC and original fixed/foreign
local meanings are not replaced. New native inlet/witness/production meanings
are explicitly selected at owning formation before Build. All-language
principality, unknown foreign W/Z/witness kernels, arbitrary capture summaries,
general State/recursive constructors, automatic proof search and production
lifecycle/cutover remain separate. Canonical aggregate statuses and prerequisites
retain their full original scope.

The transformed-export continuation has additionally constructed and
independently reviewed [ordinary id invocation phases](../notes/theory/2026-10-08-id-public-phase-constructor.md).
The concrete native VP rules and direct actual id introduction cover zero-step
pre-receipt, complete/pending/divergent entry, raw resumption at the current
world, same-value Return and hereditary futures. A finite Echo refinement and
its semantic inclusion are proved; PICK-J needs its actual public capture
contract. The [review record](../notes/progress/2026-10-08-projection-public-export-review.md)
records both independent clean reviews and the minor phase/future clarification.
This closes the initial ordinary phase-guard supplier in that native scope.
That first theorem fixes the complete inlet I. The separately
[reviewed uniform inlet constructor](../notes/theory/2026-10-08-uniform-value-entry-constructor.md)
now forms one fixed generic raw inlet before Generalize, injects each exact
prechosen frame witness into it, and proves Uniform-ID/Joint-ID for that same
actual provider. Full observation-index Delta proofs preserve every carrier
alternative; no scalar complete-contract covariance is inferred. The
[reviewed native witness constructors](../notes/theory/2026-10-08-native-projection-certificate-constructors.md)
and CE now also provide exact local alias expansion while retaining every
proof choice, world, port and original telescope. The integrated proof above
now supplies their full public-root allocation and ordinary checking case.
No foreign W/Z or witness-kernel identification, aggregate status promotion
or production cutover follows from these bounded native results.

The subsequent independent pre-review produced two
[reviewed finite countermodels](../notes/theory/2026-10-08-projection-export-proof-countermodels.md):
actual target-payload typing cannot discard broader complete carrier
observations, and one canonical evidence constructor cannot erase an
independent proof-choice fiber observed by W. Same-whole-I admission
restriction and result weakening have direct valid proofs. These results
falsify concrete attempted inference steps; they do not reject source id or
claim that finite public export is impossible.

### Completed source-directed native boundary decision (2026-10-08)

The independently reviewed [SD-NPB theorem](../notes/theory/2026-10-08-source-directed-joint-decision.md)
now proves termination, original-clause soundness and satisfiable-strategy
completeness for its actual native projection **boundary judgments**. It
constructs source-owned complete DataArg/Car/gamma evidence, joins all lower
endpoints at each real new/alias frame, and emits the complete generic
receiver strategy and actual ordinary checking proofs. No satisfying input
strategy, unknown J/Car supplier, submitted inclusion proof, EPR or ER is a
decision premise in this envelope.

Written endpoints are finite positive ground/Any/record/union descriptions;
the data graph is acyclic and tight before one optional initial widening.
Pick captures are tight ground/record values with their actual provider fixed.
For every initially unsolved frame, let L be the union of all its declared
checked-inlet endpoints. Native id requires L to be included in every
same-whole-inlet Function result target; pick requires the tight capture type
to be included instead. The algorithm selects a=L once before challenges.
Necessity covers arbitrary original descriptions and proof choices, not just
the finite chosen syntax. Original world/port/provider/binder dependencies,
independent admission, production-only alternatives and all native
pending/resume/future branches remain present.

This is a decision of the complete included local judgments, **not the
enclosing source Call/Build package**. The callee prelude, independent
CallMem/C0 arms, source Call result consumer and unfinished suffix are outside.
Frozen-prefix solving, active extra W/proof observers, changed-input Function
views, post-Return/chained refinements and general effect/State/recursive
inference are also outside; none becomes a source rejection policy.
General JOINT_DEC remains OPEN-PROOF, with its aggregate premises and
production relevance unchanged.

The [review and integration record](../notes/progress/2026-10-08-source-directed-joint-decision-review.md)
records the independent mathematical/specification passes and the repaired
same-world characteristic-witness clarification. The separately reviewed
[reference arithmetic](../tools/research_source_joint_boundary.py) implements
only finite endpoint/frame decisions, not the semantic constructor or full
source solver. Its final bounded check passed 30 scenarios and 400 inclusion
pairs, with all 301 returned countervalues checked independently. These are
implementation checks; completeness is established by the mathematical proof.
The reviewed [ObservedPayload obstruction](../notes/theory/2026-10-08-joint-decision-source-fragment-obstruction.md)
separately rules out testing only successful observed calls. No production
compiler change or cutover follows.

### Completed native Call operational consumer exactness (2026-10-09)

The independently reviewed [SCX / SCX-P theorem](../notes/theory/2026-10-09-native-call-result-consumer-construction.md)
is pushed at `370bb913f5516915716a6ceb63eea1b84b25e825`. Reusing SD-NPB,
it constructs the actual native `id 0` source consumer, proves its operational
decomposition and finite literal execution, and constructs/inverts the
original relational Call/Bind image of every complete native VP+Echo
production derivation. The decorated input retains prelude/operator choices,
original proof fields, independent whole carriers and native nonexecuting
alternatives. Pending/raw developments preserve current C', the original
handle reference and unfinished consumer without receipt replay.

This is a complete theorem at the operational and native relational-image
layer. It does not prove typed M_E, selected ReadInvoke formation, full IF,
Application_N membership or CallMem/C0. Both independent reviews rejected
the initial attempt to instantiate ReadInvoke from a typed structural
subdiagram plus opaque arm slots; the replacement removes those positive
claims. The actual complete interface still requires its original typed
declaration/use contracts and changed-interface admission/future actions.
The [review record](../notes/progress/2026-10-09-native-call-consumer-exactness-review.md)
records the exact successful proofs and repairs. General JOINT_DEC and the
canonical DAG are unchanged; no production code, tests or F5 route changed.

### Direct source-semantic attacks (2026-10-09)

The selected [native literal Call checking definition](../notes/design/2026-10-09-native-literal-call-checking-definition.md)
and [MIN-ORIG-WHOLEARG/E/ER/S/LC proof](../notes/theory/2026-10-09-native-id-original-wholearg-construction.md)
now construct the original argument-checking occurrence and a successful
extensional whole-inlet check for literal `0` at the actual native id
Int/empty-residual frame. The original generic Call operand is Result(I_a);
DataArg assembles its registered complete view without changing any relation
field. Literal/Result/Delay produce Car separately, and finite identity/image
checking handles every original complete J alternative with its own evidence.
Frame checking precedes the same frame's Raw injection. Independent caller,
registration, world, authority and hereditary laws remain genuine inputs.

This removes a supplied argument-conjunct occurrence/retention derivation and
a supplied successful WholeArgCompatible proof **for this source case**. It
does not identify an arbitrary old checking declaration or opaque proof fiber.
The finite source-choice correspondence retains noncanonical proofs, their
intermediates and active predicates on those fields; it does not decide
arbitrary active W. Both fresh math/spec reviews passed. Under the current
user's natural-constructor authorization, the primary selected the faithful
new literal specialization; no fixed exact-image/foreign emitter was changed.
The proof and selection are pushed at
`b0213ad2bed8223445d9db1d64ac30778c8ddafa`.

The separately reviewed [native declaration construction](../notes/theory/2026-10-09-native-whole-argument-checking-declaration.md)
constructs a complete Parameter-owned NativeCheck, its fixed gamma and
presentation-indexed raw fibers, ordered evidence telescopes and lawful
actions. It removes a supplier of that native declaration. Review rejected
the original attempt to identify it with the old independent leaf and to
preserve every observer of an enlarged registry; those claims were withdrawn.
The final theorem preserves the exact old reduct and selected native fibers.
The general original declaration/reference contract remains open.

The [Call separation result](../notes/theory/2026-10-09-native-complete-call-typing.md)
exhibits an independent native Return(1) production at the actual literal-0
carrier, whose actual operation returns 0. Original ME-Call-Structural cannot
introduce that tuple **if an authentic original Call formation is supplied**.
That q is not constructed here or by the local literal argument-occurrence
rule; this is not an inhabited original-source counterexample, full M_E
exclusion or a C0 impossibility theorem. Full Application/Gen-Call-0/Code-Call
formation, complete IF, typed M_E/DescMem and all CallMem/C0 arms remain open.

The reviewed [receiver expiry and request-prefix theorem](../notes/theory/2026-10-09-annotated-formal-seed-and-removal-theorem.md)
proves expiry of the exact completed maker receiver on the selected
unannotated nested apply/step source, plus actual consumption of one eligible
shallow Request and preservation of its current raw suffix. It does not
construct the annotated `_ -> [io] _` target, ProtectedVarAt or exhaustive
annotated C5/C6. The request-provider example retains genuine primitive/body
and local typing inputs. SEED_SOURCE and general JOINT_DEC stay OPEN-PROOF.

The [independent review record](../notes/progress/2026-10-09-source-semantic-attacks-review.md)
records the original findings, repairs, frozen hashes, exact passes and
checkpoint pushes. Canonical DAG JSON/Markdown are unchanged: no status,
prerequisite or production requirement is removed. No production code, tests,
source rejection policy or F5 route changed. Use the new local checking
constructor instead of reconstructing its occurrence from successful checking;
continue full Call typing only with its genuine additional owner outputs.

### Completed closure, recursive interface and signature construction (2026-10-08)

Three further constructor bottlenecks now have complete scoped proofs and
independent mathematical/specification review; the
[integration record](../notes/progress/2026-10-08-native-constructor-theorems-review.md)
records the frozen inputs, accepted repair and selection boundaries.

- [Captured closure introduction](../notes/theory/2026-10-08-captured-call-closure-introduction.md),
  under its [selected definition](../notes/design/2026-10-08-captured-closure-constructor-definition.md),
  constructs the actual nested `step` and its installed world together from
  actual captured f evidence and independent whole-entry/guard/domain inputs.
  Step/Block/OuterTrace retain all argument effects, pending raw resumptions,
  divergence and future use. The actual finite source witnesses are constructed,
  with no prior step membership or completed own-root world premise. An
  arbitrary independent `F_apply`, different result descriptor, general
  effectful code and all independent whole-Call arm laws remain outside.
- [Native recursive interface](../notes/theory/2026-10-08-recursive-original-interface-embedding.md),
  under its [selected definition](../notes/design/2026-10-08-native-recursive-interface-definition.md),
  constructs the exact two-closure original interfaces and finite source
  witnesses. A total typed copy of the whole selected interpretation proves
  OE, O-pair and the original installed-world consequence of Knu/Fin. Missing
  native parameter meanings are explicit definitions; fixed-original meanings
  require their actual full laws and actual guard evidence. The exhaustive
  CompleteMem inventory and remaining independent fields are not supplied.
- [Native signature incidence](../notes/theory/2026-10-08-source-signature-incidence-construction.md),
  under its [selected definition](../notes/design/2026-10-08-native-signature-formation-definition.md),
  constructs the complete native support/license/attachment grammar and
  compiler correspondence. One constructor induction proves forward licensing,
  inversion to full FormationAnchor packages, origin-preserving whole actions
  and native profile incidence. Composite declarations keep each constituent's
  original owner separately from the receiving root; empty fibers remain
  supported. The exact own-upper subrecord retains its original objects and
  E_C inverse. The stronger all-license-to-receiving-E_C target, any actually
  used fixed foreign/scalar consumer, annotation realization and ROWS remain.

Use these completed constructor cases in F1/F2. Do not schedule their source
witness, own-world, native presentation or native signature reconstruction
again. Canonical
REC_DESC/INIT_VALID and the whole F1–F4 families keep their original statuses
and prerequisites. The two research proof checkpoints are `c008eee` and
`e5ed650`; no production code or cutover changes.

### Previously selected immutable recursive introduction (2026-10-08)

The [positive immutable constructor theorem](../notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md)
now introduces the actual pair `my f x=g; my g y=f` and its installed world
simultaneously in the selected interpretation. Complete Value-entry interfaces
retain arbitrary argument effects, divergence, pending resumptions and future
uses. A proved relative-coinduction lift preserves the complete same-operator
background; only the exact two value holes are assumed, with no world/authority
hole. Neither opposite membership nor completed own-root validity is an input.

The initial independent mathematical review found a Unit/background coverage
gap. One batched repair closed it; compiler-referee and spec delta reviews both
passed. The [membership definition](../notes/design/2026-10-08-contextual-function-membership-definition.md)
selects the exact local clauses under the existing authorization; the
[review record](../notes/progress/2026-10-08-call-interface-admission-review.md#8-positive-immutable-recursive-introduction)
records hashes and scopes. This is an adoptable semantic construction rather
than another premise-localization note.

The later native original interface theorem above supplies the missing
presentation construction and same-operator background correspondence on its
selected native route. Correspondence with already fixed or foreign meanings,
the actual exhaustive CompleteMem/KV inventory and remaining fields, Generalize,
broader recursion and State remain separate. REC_DESC/INIT_VALID remain
OPEN-PROOF with all aggregate counts, premises and edges unchanged. The pushed
parameter Apply lane continues independently with its explicit unresolved
generalization/effect/admission premises; production cutover remains forbidden.

### Current adopted Call formation and local O0 result

The user explicitly approved the two formation cases at
`2026-10-07T22:09:13+09:00`: 「承認するよー．定義にしちゃっていい」.
The [adopted original definition](../notes/design/2026-10-07-original-call-formation-definition.md)
records the exact scope and published §10 revision. The
[O0-selected proof](../notes/theory/2026-10-07-adopted-call-formation-o0.md)
supplies independent H_eff, the exact immediate signature root, typed
Call-effect occurrence/kappa, full-invocation root realization and whole-tuple
substitution for every actual emitted Gen-Call-0 record. The approved nested
source's existing singleton is included.

The source/shared-root part uses the actual scoped Gen-Call-0 derivation and
its registration/capture provenance; a locator pair is insufficient. It
introduces no original Slots member, semantic SharedContract/provider
validity or joint I_orig witness. Exact consumer substitution supplies only
their O0 port and retains all other premises. Calls with no emitted record
keep their old node and child evidence without annotation or restriction;
all-source record generation remains open. See the
[review and integration record](../notes/progress/2026-10-07-call-construction-proof-review.md#7-approved-definition-and-local-o0-integration).

The former definition-selection question is resolved. No independent H_eff or
OC-CallEff introduction remains unsupplied on this selected route. This is a
local theorem under the approved definition, not proof that the historical
undefined judgment followed from unchanged prior rules or that every
separately fixed original family is identical. That O0 checkpoint did not
promote ORIGINAL_ASSOC; its later captured-Call family scope is now
CONDITIONAL-CLOSED in the canonical DAG. No further promotion follows here.

The default-off `yu-core::shadow_call_formation` slice now derives the
established captured-formal singleton's symbolic source record and applies the
adopted root/effect constructors. It retains the callee Use, checking
occurrence, source `call.effect`, invocation-output leg and shared captured
registration. Original `B/X/xi`, type/scope correspondence, emitted-record
membership, semantic invocation interpretation and legal whole-tuple
substitution remain explicit unresolved premises. This does not generate
records for arbitrary Apply nodes or alter solver/production behavior. Its
focused three-test target and independent compiler-referee review passed.

### Exact source-to-candidate Apply crosswalk

The default-off, test-wired
[`CandidateSourceCrosswalk`](../crates/yu-solver/src/shadow_candidate_source_crosswalk.rs)
joins independent root Lambdas' exact declaration/formal/application/callee/
argument positions to the same solve's candidate Calls and selected borrowed
root export. Each declaration has a separately branded skeleton while source
positions retain the common parse identity. The crosswalk assigns every
candidate call to its owning HIR declaration and formal, retains existing
`SourceCallUseInput`/`PendingPremise` identities, and validates all root
incidences before publishing an export. Foreign parse/HIR roots and cross-root
binder access fail. Candidate calls and exports retain their full unresolved
premise inventory. The focused multi-root target passed 3/3 and the existing
single-root target passed 2/2. Regression review passed after a test-only
coverage repair asserted exact declaration/formal/application/callee/argument
positions, owner distribution, foreign positions and cross-root binders. This
advances only the `HIR_WIRING` implementation-only node. Multi-definition
fresh-use, local source-position/candidate crosswalk, local generalization,
semantic typing/admission, successor correspondence and production behavior
remain open.

The next default-off candidate slice now retains each resolved module Name
use's collection-branded identity, target scheme, receiving scheme, exact
current Q/R-to-fresh-row substitution, binder origin, and stored provenance
causes. A separate test-wired module-use crosswalk records raw Name/target/
receiving positions without fabricating `SourceCallUseInput`; empty fresh
routes remain distinct from absent module uses. It validates the exact HIR
instance and source artifact even when there are no module uses, rejecting an
empty HIR where no source identity witness exists. All source typing, admission,
and semantic source-to-export correspondence remain unresolved. The borrowed
observer now also returns the exact same-solve receiving-root `CandidateExport`
and its scheme; this records the implemented value projection while retaining
that unresolved correspondence premise. Successor transport and other semantic
premises remain unresolved; production behavior is unchanged. The focused
candidate/single-root/multi-root targets passed 15/2/3, with same-fixture
differential against ordinary collection/solve comparing all four root values
and alpha-equivalent closed endpoints; both regression reviews passed after
two ownership-coverage repairs. This advances executable
`HIR_WIRING` only; no DAG node status changed.

### Exact captured-local candidate value (2026-10-08)

The default-off value candidate now consumes the exact retained
`ShadowLocalBind` for `my apply f = { my step x = f x; step }`. It builds the
outer and local Function entries with existing Lambda recipes, retains the
actual outer `f` row and distinct local `x` row, and returns the local
initializer endpoint without a terminal Call or local freshening. The
candidate keeps every semantic premise unresolved and uses the current F5
solver/generalizer machinery; it is not successor generalization or production
inference. The focused feature target passed 17/17 at its earlier checkpoint;
the current target passes 19/19. Its differential now
records that the candidate's returned-Function scheme differs from the current
collector's result for this retained local Bind; it asserts only the observed
delta and leaves which result is semantically correct unresolved. The old
collection/solve path remains stable in diagnostics, facts, provenance,
counters and exported schemes. A focused crosswalk test now joins the original
source Bind/Lambda/formal/Apply/callee/argument/return positions to that same
candidate call and export while retaining all pending premises; its target
passes 3/3. The candidate slice's regression review accepted it after the
unsupported-sidecar path was covered; an independent regression review also
accepted the crosswalk within its structural scope. Broader local Bind forms,
local generalization, source typing/admission, capture/evidence transport,
successor correspondence and publisher behavior remain open. This advances
`HIR_WIRING` only and changes no DAG status.

The opt-in local-binding constructor and source crosswalk now select one exact
captured root in a multi-definition module and match its retained local Apply
by occurrence while leaving other module calls intact. A two-use fixture checks
that both uses share the target scheme, their fresh-row inventories are
pairwise disjoint and complete, and the source binder correlation survives
within each whole-scheme route. A duplicate/unsupported/foreign-artifact
fixture verifies fail-closed selection. The fixture also compares ordinary
collection/solve diagnostics, facts, provenance, counters, values and schemes
around candidate execution. These are identity and solver-observation checks,
not semantic typing evidence: all candidate premises remain `UNRESOLVED`.
Compiler review found a minor fresh-row coverage gap; regression review noted
missing multi-binding noninterference evidence. Both were closed with test-only
assertions, and the focused targets passed 19/19 and 3/3. No DAG closure or
semantic status changed. Broader local Bind forms, typing/admission, capture
and evidence transport, successor correspondence and publisher behavior remain
open.

A new feature-gated integration target now joins this same captured-local
source Apply across the symbolic `yu-core` call-formation generator, the HIR
source crosswalk, and the same-solve candidate Call/export. It checks borrowed
identity for the application, callee/argument and returned uses, declaration
and local scopes, plus pointer-retained pending premises. A borrowed accessor
now exposes the exact retained startup row for a HIR parameter, and the test
joins the local source formal through that row to exactly one same-export
current-generalizer origin and scheme-qualified Q/R binder. The accessor
preserves solve-branded row identity and adds no source meaning. Original
`BX/xi`, types/scopes, emitted Gen-Call-0 membership, invocation interpretation
and whole-tuple substitution remain unresolved in both carriers. The target
passed 1/1; an independent regression review, rustfmt and whitespace check
passed. This is executable structural `HIR_WIRING` progress only; all canonical
DAG statuses remain unchanged.

The canonical successor DAG now has 90 nodes / 196 edges with 7 CLOSED, 21
CONDITIONAL-CLOSED, 43 OPEN-PROOF, 18 OPEN-SEMANTIC and 1
IMPLEMENTATION-ONLY. No status changed in this shadow slice.

The next shadow slice adds a direct inventory over existing opt-in resolved
HIR `Apply` nodes, retaining the exact application/callee/argument IDs, source
form and attached `UnsupportedExpression` IDs for one selected definition.
Captured local initializers remain scoped to their owning root; foreign roots
and unsupported projections fail closed. The solver crosswalk test now joins
these same HIR identities to candidate Calls for direct and captured examples
while keeping every candidate/source premise unresolved. Focused HIR and solver
targets pass 3/3 and 5/5, and an independent regression review found no
actionable issue after exact nested counts and sibling-root isolation were
added. Ordinary `lower_module` behavior is unchanged. This remains
`HIR_WIRING` implementation progress only; no canonical proof status changes.

That HIR inventory now feeds a default-off `yu-core` carrier directly. The
carrier preserves the supplied root and borrowed call/callee/argument/error
identities, plus the four existing unresolved source-base premises; it does
not synthesize a Gen-Call-0 or `SourceCallUseInput`. The solver integration
test follows the same call through HIR, the Core premise carrier, the candidate
Call and its exported scheme while retaining unresolved inventories. Focused
Core and solver targets pass 6/6 and 5/5. Independent compiler-referee review
found no findings in the carrier or its semantic boundary. This extends the
executable identity crosswalk only; `CALL_TYPE`, source-base conformance and
all other proof statuses remain unchanged.

### Current shared static owner construction

The user's `2026-10-07T23:02:56+09:00` instruction authorizes continuing
legitimate definitions under the fixed natural source behavior. The
[static owner definition](../notes/design/2026-10-07-original-call-owner-definition.md)
and [complete O1-static proof](../notes/theory/2026-10-07-call-owner-construction-proof.md)
now supply `s in Slots_orig(beta)` and both lexical `Own(...,u_f,...)`
and checking `Own(...,u,...)` from one canonical owner certificate for
every actual emitted Gen-Call-0 exposure carrying the independently justified
selected formal seed. S1 supplies that seed for the approved nested source.
The lexical mathematics/specification reviews and fresh paired-facet delta
review pass; the minor review-provenance clarification is repaired. The
[completion record](../notes/progress/2026-10-07-source-constructor-completion-review.md)
records exact scope, frozen hashes and consumer substitutions.

Registration owns a shared position schema; an actual O0 exposure introduces
its typed membership and seeded upper ownership. Capture imports the original
registration. Local demands remain in their own scopes, and lexical `u_f`
and checking `u` remain distinct. No unused-formal Function validity, whole
slot inventory or semantic SharedContract membership is inferred. These are
constructor and elimination proofs, not a reconstruction from IDs or Q.

The incoming reviewed §3.1 owner candidate at `465c2af` is preserved in the
[source-introduction contract](../notes/design/2026-10-07-original-call-source-introduction-contract.md#31-candidate-o1-static-slot-and-upper-owner-formation).
It states a checking-`u` owner/J0 port and remains an unadopted candidate;
the paired construction supplies its checking existential port under the
selected definition, without identifying its separate concrete kernel terms.
This supersedes the earlier bounded O1 attack's missing-static-rule stop.
All-source generation, other seed/owner cases, complete C0, full source
interface/J0 and licensing/profile/row completeness remain open. C1 is now
supplied under its independent inputs as recorded next. The aggregate
ORIGINAL_ASSOC and canonical ninety-node status/dependency inventory are unchanged.

### Current complete Call construction

The [selected complete Call definition](../notes/design/2026-10-07-complete-call-contribution-definition.md)
and [reviewed constructor proof](../notes/theory/2026-10-07-owned-call-contribution-construction.md)
form C-Call from the authentic whole operation. Independent complete C0 yields
C1's exact evidence-fiber correspondence before Pi. The receiver-only C-Inv
remains distinct; all original callee, whole-carrier, receiver, return/future
and abstract alternatives remain.

Remote `3797bce` independently selected the finite acyclic structural SrcFrame+
completion in that proof §12. Its reviewed operands, Bind, latent carrier and
return/future maps are preserved. The later
[source-interface definition](../notes/design/2026-10-08-call-source-interface-definition.md)
and [Theorem IF](../notes/theory/2026-10-08-call-source-interface-construction.md)
now generate all four old SourceInterfaceFormation outputs at actual
source/operator and declaration/reference formation. IF-Insert and IF-Use
retain complete original clause and actual root-use interfaces, including
opaque/parameterized Option 2 arms, without a source execution anchor.
Finite monomorphic graph registration also constructs static cycles without
unfolding; it proves no recursive semantic validity.

This removes the independent source-placement supplier on that constructor
route. Genuine operator typing/witness actions, actual-provider phase/dispatch,
contextual hole/world binding, complete primitive license/provider/future and
admission contracts remain inputs. A slot does not prove their validity.
With those inputs, authentic SpecCall, exact seeded O1 and complete C0,
J-Owned constructs fixed c/a before every z in the unchanged full family.
Foreign-kernel and active-consumer laws remain where needed.

### Conditional complete-family association closure (2026-10-08)

The reviewed composition in [owned-call construction §8.2](../notes/theory/2026-10-07-owned-call-contribution-construction.md#82-selected-captured-call-full-family-composition)
conditionally closes `ORIGINAL_ASSOC` for the approved captured `f x` instance.
One shared slot, canonical owner, authentic complete-Call contribution, full
source image and association are fixed before the universal over unchanged
`F_C(X;xi)`. C-Call preserves each complete original witness fiber before
projection, so W/Z witnesses and their licenses, providers, pending suffixes
and future evidence remain distinct. Lexical `u_f` and checking `u` facets
remain separate and joined by the actual exposure.

The exact retained premises are complete C0 over every independently admitted
carrier and its full evidence tuple; the selected O0/O1 constructors; and
Theorem IF's authentic source/reference, independent operator/primitive/guard,
and lawful whole-map inputs. Compiler-referee review passed the universal
composition; spec-auditor review passed source, incidence and Option 2
conformance. This closes no all-source association, foreign-kernel embedding,
Attach/licensing/profile/rows, active-consumer or production gate. The DAG
counts now read 7 CLOSED / 21 CONDITIONAL-CLOSED / 43 OPEN-PROOF / 18
OPEN-SEMANTIC / 1 IMPLEMENTATION-ONLY.

### Selected attachment and licensing constructor cases (2026-10-08)

The complete-Call definition §5 now supplies an adoptable `A-UpperCallRef`
source-reference constructor and a separate `LC-OwnCall` static-applicability
introduction for the same captured Call. Exact Q authenticity, independent C0,
the complete Theorem IF graph, the original shared slot and separate
lexical/checking facets are retained. The constructor-local inverse recovers
these same inputs; LC-OwnCall's J-Owned evidence is formed independently,
without licensing or attachment. Injective old-case inclusions and every W/Z
alternative remain.
Independent compiler-referee and spec-auditor reviews passed after a repair
that retains `SpecCall_e` in the source-reference payload.
`Lic_C+` now has an explicit tagged extension and eliminator. The new
`OwnCallLicense` case returns its complete source/O1/C-Call/IF/J-Owned inputs
unchanged; the legacy case returns the original license witness without
inventing a source origin. This closes inversion of the added case; the exact
legacy leaf is `ell0 : Lic_C(X,(beta,s,p,c)) -> exists e in E_C(beta),alpha.
Attach_C(B,X,xi,Delta;e,(beta,s,p,c);alpha)`, with original scopes and lawful
transports retained.

This proves only the new source-reference and licensing constructor cases
conditionally. Aggregate ATTACH, LIC_FORWARD and LIC_INVERT remain
OPEN-PROOF; the exact residuals now target old attachment/licensing cases,
fixed-interpretation maps and active-consumer preservation. Profile/rows,
source adequacy, production conformance and cutover remain open. Node and edge
counts are unchanged at 90 / 196: 7 CLOSED, 21 CONDITIONAL-CLOSED, 43
OPEN-PROOF, 18 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY.

Next dependency attack: prove `elim_legacy` at the original `beta` signature
formation. Enumerate actual source-owned, inherited, annotated, generalized
and conservative licensing constructors and their same-X/scope transport
evidence; preserve complete W/Z declaration licenses without requiring
execution origins. If this cannot be derived, formulate the source-owned
`SigIncidenceFamily` introduction/elimination signature and test it against
each real legacy rule before adoption. A single LC-OwnCall member is not the
complete `Slots(beta)` inventory. Profile §3.3 supplies deterministic policy
assembly only after complete applicability; it does not discharge
`elim_legacy`. ROWS remains separate because independent admission and all
world/history predicates must still share one original tuple.

The frozen research-only [legacy-license elimination attempt](../notes/theory/2026-10-08-legacy-license-elimination-attempt.md)
was independently accepted by compiler-referee review and checkpointed in
`b649790e3`. It proves `elim_legacy` conditionally from an exhaustive
well-founded `Lic_C` grammar and same-index attachment action for every last
rule. The examined sources do not provide that original rule inventory: the
five requested families remain non-exhaustive, Theorem IF supplies contextual
placement rather than `Attach_C`, and `A-UpperCallRef` supplies only
`Attach_C+`. Joint hiding also needs an original-scope attachment action that
retains one shared witness and admission certificate. No licensed-unattached
Yulang counterexample is established; ATTACH, LIC_FORWARD, LIC_INVERT, profile,
ROWS, and production statuses remain open. Next, recover or construct the
actual original signature-applicability introduction at `beta`, then check its
attachment action against each real legacy last rule before adopting any new
constructor.

### Current original semantic Call inputs

The [contextual Function membership definition](../notes/design/2026-10-08-contextual-function-membership-definition.md)
and [reviewed realization](../notes/theory/2026-10-08-call-semantic-input-realization.md)
complete the original Name/Return/Delay input route. Function membership means
that the same actual provider realizes the independent complete contract.
Original hereditary binding inputs construct the persistent telescope; actual
Name inversion yields membership at the retained CalRet event; Name Delay
satisfies both inert and universal execution obligations. Same-value VIncl and
independent checked-challenge assembly then yield acceptance of that exact
argument at the exact returned U/current C1/w1, without an extra ViewInlet,
invocation-output-typing or complete-C0 premise.

The receiver theorem types all actual receiver observations and admitted
pending/resume/future developments at checked F using that same membership.
It preserves actual entry, one receipt, ordered suffixes and live current
state. This is elimination of the supplied callable's semantic contract.
The later selected Step construction above now supplies introduction of the
actual new nested closure; other closure/result cases keep their own proofs.
The broad independent context/carrier domain, divergence and original Option 2
alternatives are retained. The old raw ViewInlet sufficient fragment is not
imposed as a necessary source rule.

Both new proofs and their exact definitions passed independent mathematical
and specification reviews. A narrow mathematical delta revalidated IF against
the incoming `3797bce` completion. See the
[review/integration record](../notes/progress/2026-10-08-call-interface-admission-review.md).
The input theorem was already checkpointed and pushed at `375d21e`; shared
selection and navigation are the second integration phase. There is no new
user-decision blocker for these adopted missing definitions.

### Pure-read Call result subcase

The new [Authoritative constructor definition](../notes/design/2026-10-08-pure-read-call-result-constructor.md)
selects the staged `ReadInvoke` result for structural immutable `Name f`
Calls whose complete result interface is definitionally identical, including
decorations. Compiler-referee review found that this is a new bounded
definition, not an entailment for an independently fixed result descriptor;
spec-auditor review passed with phase order, full admission domain, original
indices, and every Option 2 alternative preserved.

Under the selected Name/Return/Delay and same-provider member clauses, same-
value `VIncl`, independently assembled complete challenge, actual Theorem IF
frame, and an unchanged source-base `M_E` witness, this gives `DescMem(R_c)`
for the same structural pure-read observation. It does not create `M_E`, type
unrelated `R_c`, provide W/Z typing, or close every Call form. The canonical
`CALL_TYPE` node stays `CONDITIONAL-CLOSED`; this reviewed subcase is now in its
`closed_lemmas`, and the remaining exact branches stay open. No broader gate
or production prerequisite changed.

### Default-off source annotation/call identity crosswalk (2026-10-08)

A new `yu-core` shadow-only crosswalk joins one retained HIR definition to its
exact CST binding boundary, retained Apply/callee/argument identities and source
positions, and all annotation occurrences under that boundary. It checks source
ancestry for each operand, retains the original HIR diagnostic IDs, separates
unsupported HIR projection from an empty retained-call inventory, and keeps
annotations as definition-scoped syntax data without linking them to calls or
profiles. Nine source/type/admission/evidence premises remain unresolved. The
focused target passes 5/5; the no-default-features check and formatting pass.
Pre-write spec review and post-write spec/regression review passed; the one
minor repeated-call coverage finding was fixed with a left-associated fixture
and distinct-identity assertions. This advances executable HIR_WIRING only;
all canonical DAG statuses remain unchanged. Production lowering and solving do
not consume this structure.

A separate selected `f x` CALL_TYPE derivation confirms the existing
conditional closure but adds no theorem or status. Its next concrete leaf is
construction of the original complete inlet declaration and dependent carrier
introduction evidence for the candidate Apply demand; current source recipes
retain value/effect rows but do not provide that complete independent
predicate. Keep it open and do not substitute F5 success or Q for the inlet
contract.

The research-only [annotation permission realization analysis](../notes/theory/2026-10-08-annotation-permission-realization-analysis.md)
now has an independently reviewed conditional equivalence between eager
release at a qualifying crossing and deferred realization at an actual
opportunity. The review repaired the release-state guard so eager subtraction
applies only after release, with qualification, a live receiver, and certified
transport; failed crossings preserve state. This characterizes the two
decorated transition candidates only. Source construction of the qualifying
incidence/crossing, static export observability, and production conformance
remain open; no annotation policy or inference gate is adopted. Review metadata
was checkpointed in `7eab2767f`.

### Immediate work order

1. Obtain and independently review the actual source-owned Application package
   for the flat inner `f 1`. The frozen conditional
   [source Code/Check derivation](../notes/theory/2026-10-08-flat-apply-code-call-source-instantiation.md)
   now constructs child Name/Result, literal Result/Delay, both Lambda
   skeletons, and the dependent ReceiveSchema from existing source constructors.
   Independent compiler-referee review found no issue in that conditional
   scope. It narrows the missing package to authentic original Application
   origins at the actual dependent indices: emitted Gen-Call-0 membership,
   registration/route/directional seed where applicable, and the original
   literal Reify/result-port, checking and complete-result links. It does not
   equate the reference schema with those original records. Do not infer this
   package from the shadow candidate's `Int` fact.
   The bounded [original-emission applicability audit](../notes/theory/2026-10-08-flat-apply-original-emission-applicability.md)
   confirms this conclusion-sort gap by inversion of the inspected
   constructors. Independent compiler-referee review found no issue in that
   bounded inventory. The smallest remaining owner output is an attachment
   from the actual flat `Apply(Name f, literal 1)` source derivation to original
   Gen-Call-0 membership and its checking, Reify/result, registration and
   scope origins. The current Name/Name generator cannot be instantiated by
   inventing a literal Name binder. Keep SeedExposure and the separate
   CallInitial/I0/action/insertion lane downstream.
   A conditional [literal-Call introduction proposal](../notes/theory/2026-10-08-flat-apply-literal-original-constructor.md)
   now factors those candidate origins as `P_c^cand` and requires a separate
   H-E enrichment for authentic original emission `P_c^orig`. Compiler-referee
   and spec-auditor review found only a package/H-E claim mismatch; the
   candidate/original package split repaired it, and compiler-referee delta
   review passed. This still does not construct H-R/H-E or prove the original
   argument-coordinate sort accepts a literal. No original emission, O0/O1,
   or source acceptance is claimed by the proposal.
   The follow-up [literal argument-origin extension](../notes/theory/2026-10-08-literal-call-argument-origin-extension.md)
   has passed independent compiler-referee and spec review. Its disjoint
   `Keep(old) + Add(literal candidate)` representation preserves and retracts
   the old Name image while retaining literal identity. It is still a proposed
   representation: it does not construct or install actual original literal
   emission under H-R/H-E, identify the extended family with the emitted
   family, or close the source-acceptance/cutover gate. This narrows the next
   constructor task but leaves the actual emission attachment open.
   Three frozen follow-ups now narrow that owner seam. The independently
   reviewed [forward construction audit](../notes/theory/2026-10-08-flat-apply-original-emission-construction.md)
   constructs the reference child/Call spine and stops at `R-flat`: authentic
   original typed Result/Call port registration. Even with that supplied,
   `E-flat` must separately install the literal-fiber rule in the actual
   emitted family, retain the complete original inventory, and provide the
   lawful whole action. The independently reviewed
   [bounded falsification](../notes/theory/2026-10-08-flat-apply-original-emission-falsification.md)
   shows that representability, candidate atoms, registration and action do
   not entail original emitted membership. The independently reviewed
   [source-generation bridge audit](../notes/theory/2026-10-08-flat-apply-source-generation-bridge-audit.md)
   confirms generic expression-root registration and a literal child do not
   enter the old Name/Name Gen-Call-0 family. These are bounded conditional
   results; no actual literal emission or source acceptance is established.
   Next, derive and review the original-owner registration and installation
   constructors at the literal fiber, preserving old Name records and all
   original indices/atoms. Keep flat SeedExposure, CallInitial/I0/action,
   semantic typing/admission and production cutover as separate gates.
   The reviewed [owner-completion candidate](../notes/theory/2026-10-08-flat-apply-original-owner-completion-candidate.md)
   now gives conditional PortReg+ and owner-indexed installation schemas,
   with the whole old family injected/retracted over the general Name/literal
   frame domain. Its minor frame-index ambiguity was repaired; compiler and
   spec reviews otherwise passed. It remains non-authoritative and explicitly
   stops at H-inventory and H-original-install. The separate
   [owner-completion falsification](../notes/theory/2026-10-08-flat-apply-owner-completion-falsification.md)
   is unreviewed; its bounded analytic mutations show why exact original
   atom multiplicity, independent meanings and occurrence provenance matter,
   without refuting a faithful completion.
   The [flat directional-seed derivation](../notes/theory/2026-10-08-flat-apply-directional-seed-boundary.md)
   is independently reviewed after its sequencing correction: source
   registration and upper-use exposure derive protection independently of
   literal installation, while paired O1's exact SeedExposure still needs
   actual e_c and an owner-retained formation attachment.
   The independently reviewed [complete-inventory candidate](../notes/theory/2026-10-08-flat-apply-complete-inventory-candidate.md)
   corrects the source locators: source Call construction §4.4 is uniqueness,
   scope and capture, while §5 carries G_call and its supplied
   TypedCallCert_Dec; initial-context §4.4 separately carries ReceiveSchema.
   It lists the five local reference Call heads and their owners/attachments,
   but proves completeness only for an explicitly chosen reference
   presentation with supplied finite leaves. It does not identify those
   heads with an exhaustive original Application inventory. Semantic and
   spec reviews passed within that bounded, non-authoritative claim.
   A bounded repository locator pass found no selected source giving all
   occurrence enumeration, atom meanings, typed inversion/attachments, and
   full alternatives/action for literal Apply. The reviewed
   [initial-context local-generation result](../notes/progress/2026-10-06-initial-context-source-construction.md)
   §§4.1,4.4 is the strongest local reference envelope, not an original-owner
   inventory; [Call-input construction](../notes/theory/2026-10-07-call-input-construction-proof.md)
   explicitly assumes an existing Application inventory. Next define a
   concrete primitive and original Application presentations with
   exhaustive origin/attachment inversion and old-family retention, then
   adjudicate whether an existing rule supplies them or a complete candidate
   requires user approval. Do not promote H-inventory or H-original-install
   by notation alone.
2. Only after that owner output exists, continue the distinct original
   CallInitial/I0/K0/P0/action/insertion derivation. Preserve selected O0/O1
   results at their actual emitted-record scope.
3. Keep the conditional Record-result lane behind its actual H-R/H-K owner
   laws; current production HIR, solver terms and closed types do not provide
   Record construction or complete `K_box` laws.

The frozen [bounded directional source inventory](../notes/theory/2026-10-08-directional-source-upper-exposure-coverage.md)
constructs and inverts direct-Name Call upper demands for its displayed finite
ordinary-core grammar. It composes the already selected seed derivation for
the approved unannotated and exact captured examples, without using solved
shape or Q. Independent spec review found no conformance issue. This is not
whole-source upper-rule coverage: annotation boundaries, recursive seed
applicability, computed callees and later seeds retain their owning source
premises. The retired E/R framing stays superseded by the directional rule.
The annotation owner must derive its upper occurrence and `ProtectedVarAt`
applicability under approved annotation-scoped `[io]` permission, without
deriving seeds from syntax alone.

The [annotation-boundary constructor audit](../notes/theory/2026-10-08-annotation-upper-exposure-constructor.md)
now proves a conditional finite inventory for original inferred-variable to
Function annotation checks under explicit boundary/normalization inputs. Its
independent spec review found no conformance issue. It keeps original
`SourceUpperUse` classification, `ProtectedVarAt` applicability, annotation
to contribution correspondence and realized `[io]` removal as separate owner
outputs. The minimal missing case is the approved annotated `f` plus one `f x`
use; annotation syntax and permission do not supply those outputs. The next
constructor question is the actual annotation/parameter judgment's endpoint,
exposure classification, seed stage and contribution link.

### Post-PE higher-order and constructed-result frontier (2026-10-08)

Two independently reviewed research notes now test the next source shapes beyond
the selected `id`/finite-import `pick` envelope:

- [Apply with a native public id](../notes/theory/2026-10-08-apply-native-public-export-bridge.md)
  gives a conditional public-import replacement for the `id` operand in
  `my apply f = f 1; my id x=x; pub out=apply id`. PE-ID supplies the actual
  decoded id root and ordinary identity check. Original Application origins,
  `CallInitial`/I0/action/insertion laws, complete Apply production laws and
  transformed `apply`/`out` roots remain missing. The independent math/spec
  reviews passed at the explicitly conditional scope; no source meaning or
  gate status was selected.
- [Record-result public extraction](../notes/theory/2026-10-08-record-result-public-export-construction.md)
  derives a conditional one-field Record export while retaining distinct
  Record and field providers, worlds and proof scopes. It requires the actual
  Record introduction/inversion law H-R and complete Lambda synthesis law
  H-K. Both independent reviews passed; neither owner law is supplied or
  selected by the current PE design.

- [Flat Apply original-owner derivation](../notes/theory/2026-10-08-apply-original-application-owner-derivation.md)
  derives the exact parser/HIR structure and source-generator boundary for
  `my apply f = f 1; my id x=x; pub out=apply id`. The inner Call currently
  yields only a pending source stub (`argument_use=None`); the selected nested
  Name/Name Gen-Call-0 route cannot apply because this flat body has no local
  Bind. Its conditional H_emit/H_reg/H_seed/H_app package preserves the
  selected O0/O1 and Code-Call inputs but does not supply them. Independent
  compiler-referee and spec reviews found no issue within this scope.
- [Apply owner boundary falsification](../notes/theory/2026-10-08-apply-owner-boundary-falsification.md)
  shows the grouped-callee fixture retains one Apply but yields zero direct-Use
  source-call stubs. The successful captured-source identities and candidate
  fact still lack complete Application checking and initial-rule evidence.
  Independent regression review found no blocking issue in this bounded
  fixture/API characterization. These are not compiler semantics or
  source-acceptance changes.

The approved ReadInvoke q1 decision selects the source-construction owner for
the finite presentation and requires retaining each actual rule insertion and
lookup record. Its [receipt](../questions/2026-10-08-readinvoke-source-presentation/receipt.md)
was integrated at `89b799fbc`; it does not supply `CallInitial`, I0/O0,
application origins or action laws. The next source-owner work is now narrowed
to the flat inner Application formation/checking package first, then the
separate CallInitial/I0 owner output. The Record extension independently needs
H-R/H-K. None of these checkpoints
replaces production F5 or changes GENERALIZE, PROJECTION, PRINCIPAL or CUTOVER.

### Reviewed original CallInitial I0 boundary (2026-10-08)

The reviewed [CallInitial I0 derivation](../notes/theory/2026-10-08-callinitial-i0-telescope-derivation.md)
confirms that selected Lemma W projects environments from a supplied joint
world; it does not introduce the independent initial world, admission or
hole-dependent imported roots. The approved inlet domain remains all
independently typed compatible punctured contexts, including Option 2
observations without a source-constructor witness. The five-node
Name/Result–Name/Result Call still lacks original K0/P0 and the whole-action
supplier. No new semantic definition or gate closure follows from this note.

The next I0 seam was the independently interpreted open-import/root extension
at its actual incidence. The frozen [regional candidate](../notes/theory/2026-10-08-open-import-root-extension-candidate.md)
now gives `OpenImportExt-0`, dependent overlap/gluing, the exhaustive clause
frontier and lawful action obligations. Independent semantic and specification
reviews passed for its conditional scope. A separate [falsification note](../notes/theory/2026-10-08-open-import-root-extension-falsification.md)
shows that anchored overlap plus separately valid root actions do not imply
transported overlap with the exact retained old certificate; the candidate's
joint-action premise excludes that structural countermodel. Both research
artifacts were pushed in `2f85ec179`. The fixed-meaning identifications,
actual importer root-introduction rule, and any inhabited original supplier
instance remain unproved. This does not close INIT_WORLD/SEM_JOINT/INIT_VALID
or authorize semantic adoption. The next useful evidence is one actual
fixed-semantic import-owner instance satisfying the full clause frontier,
dependent overlap and action, then its zero-step importer extension. Any
changed foreign-provider behavior still requires the normal approval gate.

The existing [CallInitial candidate signature](../notes/theory/2026-10-08-callinitial-rule-candidate.md)
has now passed compiler-referee and spec-auditor review within its expressly
incomplete, conditional scope. It preserves the zero-step suspended suffix and
keeps original I0/O0, the independent event/world/admission suppliers, lawful
whole action, source insertion and fixed-E attachment open. It is neither an
original rule existence proof nor an inhabited importer instance. The reviews
do not supply the concrete fixed-semantic `kappa`/`ID-world-forward`/
`ID-import` evidence identified below.

A bounded follow-up at `570fb742f` found no such supplier in the inspected
owners. The exact missing instance is one importer root `r` with a concrete
semantic `kappa` at its actual incidence, exhaustive frontier, and proofs of
`ID-world-forward` (retained old world plus importer clause yields the joint
extended world) and `ID-import` (the same clause/gluing tuple yields the fixed
import predicate), together with the lawful action. Lemma W only restricts an
existing binding and introduces no root/license; initial-context import is a
supplied leaf; the simultaneous constructor takes import and guard validity as
inputs; scalar exporter realization does not prove importer installation.
This is a bounded source-premise audit, not a repository-wide nonderivability
claim. No status changes or executable checks followed.

### Historical checkpoint: conditional Generalize/export bridge (2026-10-08)

This section records the pre-PE-ID/PE-PICK checkpoint from `4976b0756` and
`c77577636`. Its proposed first `id`/`pick` transformed-export rule and its
claim that native Generalize is missing are superseded by the selected source
Generalize and PE-ID/PE-PICK results above. The conditional certificates and
their falsifiers remain historical evidence; their broader public-export,
principality and production residuals remain open.

The reviewed [Generalize/export candidate](../notes/theory/2026-10-08-generalize-export-constructor-candidate.md)
constructs lossless component packaging, scoped accessors, use-indexed fresh
transport and conditional all-member publication from a supplied actual source
Generalize judgment. Its PG-1 projection references anchor the constructor at
the source's parameter/Name/Result owner chain. Independent semantic and
specification reviews passed after correcting stale cutover wording. The
[falsification note](../notes/theory/2026-10-08-generalize-export-constructor-falsification.md)
shows that output shapes/eligibility sets alone cannot recover the original
quantifier tree, dependent evidence, fixed imports/captures, anchors or joint
root covariance; these are structural countermodels, not source-admitted
Yulang examples. Both artifacts are in `4976b0756`.

The follow-up [PG-1 evidence derivation](../notes/theory/2026-10-08-pg1-generalize-direct-evidence.md)
constructs a finite conditional Eq/Eq-C/Function certificate for the first
whole-root query when the checked view and actual retained export have
identical complete clauses. The separate
[falsification note](../notes/theory/2026-10-08-pg1-generalize-direct-falsification.md)
refutes deriving that result from endpoint syntax alone. A spec-auditor and a
compiler-referee independently reviewed the respective artifacts; both pass
within their bounded scopes. They identify the same actual missing suppliers:
exhaustive active descriptor/admission formation, local resolver conformance,
and the source Generalize rule proving the designated export behavior. These
notes were checkpointed in `c77577636`; no DAG status or production authority
changes. The approved root-policy answer selects a transformed, displayable
scheme as the actual public target, with only separately justified use-time
information; retaining the complete source relation under another name would
not satisfy it. The source Lambda root may supply construction evidence, but
the public use must be justified at the transformed export. The next step is a
reviewed, non-authoritative candidate rule for ordinary nonrecursive
projection bindings (`id` and resolved `pick`) that derives this transformed
export and identifies its exact admission, membership, eligibility and
use-preservation suppliers. This is the first design slice, not a reduction of
the full replacement objective; transformed/common exports, recursive SCCs and
all compatible views remain subsequent required work.

The source-derived eligible-view/anchor judgment, complete admission and
designated-export coverage remain missing, so GENERALIZE, IFACE_FORM,
PRINCIPAL and CUTOVER statuses stay open/conditional. The default solver and
application candidate still route through F5; this packet authorizes no code
change. Next, derive the bounded transformed-export rule and actual use
consumer for `id` and resolved `pick`, without making the hidden source root the
public result or placing the whole source relation in its extras. If exact
eligibility, admission or abstraction clauses require a new semantic decision,
record the concrete alternatives before adoption. The full replacement
objective remains active; implementation still requires the charter's
reviewed successor design and specific Gate E approval.

1. Use the selected native SIG construction directly for support, attachment,
   licensing, all-anchor inversion and profile incidence. Do not reconstruct
   unspecified legacy payloads on this native route. Complete actual annotation/
   governed-field/role laws and joint ROWS; establish bridges only for an
   actually used independently fixed consumer. A consumer requiring the
   stronger E_C target still needs its exact upper restriction/connection.
   Preserve every licensed witness and all Option 2 contracts.
2. Reuse completed Step/Block/OuterTrace and native OE/O-pair/ME-pair directly.
   Complete the remaining semantic Call inputs: genuinely different result or
   outer interfaces and general effectful code; lawful original
   operator/phase/dispatch and contextual world actions; every independent
   whole-Call primitive/abstract arm with its provider/future/admission laws.
   Full C0, exhaustive descriptor/model realization and applicable
   active-consumer preservation remain. For the selected identity Name/Name
   pure-read branch, Theorem R/E and `ReadInvoke-Desc` provide the actual-U
   phase and descriptor result when the unchanged source-base `M_E` witness
   exists. Derive its source-owned finite constructor next, without assuming
   `M_E`; IF and contextual membership alone supply neither primitive laws nor
   arbitrary-world inhabitance. On the recursive route, establish the actual
   exhaustive CompleteMem inventory and remaining independent fields, plus any
   fixed-original correspondence actually used.
   F1–F4 families by shared constructor, transition, source-derivation and phase
   cases. Complete joint ROWS, generalization/instantiation/hygiene, recursion,
   methods, actual export and publication remain required at their real owners.
4. Before using the alternate smaller cutover route, establish all retained
   consumer replacements, including the five ALL_WORLD consumers and every
   required actual-export refinement. Keep stronger research theorems and
   Authority-required completed-contract principality, all compatible contexts
   and both complete Option 2 inclusions intact.

The canonical DAG remains 90 nodes / 196 edges, with status counts
7 / 21 / 43 / 18 / 1. This integration records the reviewed conditional
ORIGINAL_ASSOC closure for its exact selected instance; aggregate dependent
gates, original predicates and production relevance stay unchanged. No source
restriction, production semantics or cutover is introduced.

## Preserved earlier proof-attack history

The following records retain completed results and exact unresolved cuts from
earlier instructions. Their repeated “next attack” wording is historical;
the immediate work order above governs current scheduling. None of the
historical results is newly closed or reopened by this planning change.

### Historical O0 reduction before the approved definition

At remote `2eb1660453ad325f8a2a3e95cb79cd9c368f9aaf`, subsequently integrated
with the reviewed shadow checkpoint at `413c337bc0cdecaeb539829596fcd97521cf087b`, the
[reviewed minimal-clause result](../notes/progress/2026-10-07-original-call-output-minimal-clause.md)
reduces the candidate local head to the existing dependent `Gen-Call-0`
record plus independently formed signature-local `H_eff`. The missing
`OC-CallEff` introduces their original typed occurrence incidence and specifies
its source/signature projection equations. Neither the equations nor an
untyped graph proves that introduction. `H_eff` itself remains unconstructed;
this is a candidate-interface reduction, not O0 closure or a derivability
equivalence. Seed truth and actual Call execution are not consumed by the
local head; all original seed/provider/upper/scope/`xi` dependencies remain.
Keep locally dependent `U_c` in its actual context at `sigma_step`, with the
captured root still anchored at `sigma_apply`. Both independent reviews passed.
The DAG statuses and edges are unchanged. Next independently form `H_eff`
and justify `OC-CallEff`; only after O0 closes attack O1, then actual C0
checking inputs. No new user-decision blocker or implementation authority.
The linked note contains the four-part repository handoff.

The next default-off HIR inventory slice is recorded in
[`shadow-original-call-effect-premises`](../notes/progress/2026-10-08-shadow-original-call-effect-premises.md).
Two per-Apply rows now name signature-local immediate Call-effect position
formation and original typed Call-effect occurrence introduction. The
pre-write scope audit and compiler-referee review passed; producer focused
checks passed with one pre-existing rustfmt discrepancy explicitly retained.
These remain unresolved premise markers, not O0 evidence. DAG counts and all
semantic statuses remain unchanged.

### Priority attacks from `61651a3`

The reviewed bounded attacks are in
[`successor-priority-leaf-attacks`](../notes/progress/2026-10-08-successor-priority-leaf-attacks.md).
O0 is narrowed to original signature-local immediate Call-effect position
formation in the dependent `Delta_c`, followed by the separate typed
`OC-CallEff` introduction. P2's exact next head is original `Slots(beta)` /
`Own(beta,...)` introduction with lexical `u_f` distinct from checking `u`;
it is still conditional on O0. CALL_TYPE's actual-provider path now separates
the `F_c` membership link, whole-carrier inclusion to `U`, and same-witness
argument typing. Compiler-referee review passed these boundaries, but no
unproved rule was promoted. Before and after: CLOSED 7, CONDITIONAL-CLOSED 20,
OPEN-PROOF 43, OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1 (90 nodes / 196
edges). The next direct attack remains O0 position formation.

### Latest priority attack: round 8

At fetched remote `b1d37c03b979b842f169f74a407162b1d3d27dad`, the canonical DAG started and ended at 90 nodes / 196 edges: CLOSED 7, CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19, IMPLEMENTATION-ONLY 1. The source-producer audit found no original typed signature-local `q_c` producer; O0 remains at independent original position-family formation, with `OC-CallEff` still separate. CALL_TYPE's `F_c` checked-membership link is conditional on same-witness returned `A_f` membership, `VIncl`, and the common interpretation; actual-provider whole-carrier inclusion remains a separate universal leaf. ORIGINAL_ASSOC, INIT_WORLD, REC_DESC and ALL_VIEW likewise remained open at their existing exact source constructors. No status changed.

The default-off solver shadow now borrows each rooted pending Apply row together with its exact enclosing root and current finalized scheme; rootless rows are omitted and cross-solve identities remain distinct. This establishes only current definition ownership, not Apply typing or successor generalization. One compiler-referee review passed; the focused integration test, package check, formatting, and diff checks passed. `HIR_WIRING` remains IMPLEMENTATION-ONLY and production inference is untouched. See [round 8 priority attack](../notes/progress/2026-10-07-successor-priority-attack-round8.md). Next semantic target remains original signature-local position formation (O0), then separate `OC-CallEff`; no production cutover.

### Latest priority attack: round 9

At fetched remote `f1ec5d0e8ad5fb78806500a7ad55a9c16103bd64`, DAG counts remained 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, and 1 IMPLEMENTATION-ONLY (90 nodes / 196 edges). The constructive O0 last-rule audit confirmed that Gen-Call-0 provides the dependent schema but no original typed signature-position introduction; the complete-model mutation attack found no competing Authority-consistent outcomes. `call.effect[U_c]` formation and separate `OC-CallEff` remain open. The exact `REC_INIT_SELF` source proof remains closed, but production execution enforcement has no owning evaluator/admission entrypoint in this workspace; do not fail inference collection/solve to simulate it.

### Latest implementation characterization: round 10

At fetched remote `6187ed18e83e93fa0548cbb92a85bb0a1f54bfd4`, the canonical DAG remained 90 nodes / 196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, and 1 IMPLEMENTATION-ONLY. A focused default-off shadow fixture now covers a nonempty receiving R inventory and joins each receiving recursive binder's retained historical row to exactly one incoming recursive fresh row. Independent compiler-referee review found no issue. The test also preserves cross-solve identity separation, stable repeated observation, unchanged counters, and explicit unresolved successor generalization/Q-R correspondence/shared-contract transport premises. This is a current-solver identity characterization only; no DAG node or semantic status changes. Focused test, formatting, and whitespace checks passed. See [round 10 shadow R-origin characterization](../notes/progress/2026-10-07-shadow-r-origin-round10.md). Next semantic attacks continue at CALL_TYPE's exact joint provider-compatibility constructor, ORIGINAL_ASSOC P2's source-owned contribution introduction, and REC_DESC's dual-route minimum leaf.

### Latest semantic priority attack: round 11

At round-10 baseline `6187ed18e83e93fa0548cbb92a85bb0a1f54bfd4`, independent constructive/last-rule attacks and compiler-referee/spec-auditor review refined three exact OPEN leaves. CALL_TYPE is restricted to the granted CI-Operands/retained-CalRet cut: source whole-argument checking must jointly establish actual-C1 typing and compatibility with the same returned provider's actual carrier; a complete Function eliminator is sufficient but not proved necessary. ORIGINAL_ASSOC P2 requires one original association introduction covering the complete original family at the same `xi` and preserving `sigma_apply` versus `sigma_step`; conditional P3 coverage must choose that association before ranging over every family member. REC_DESC's reflection and direct-introduction formulations are equivalent under the same independent guards and `G ⇒ Q`, with existential-history/universal-extension quantifiers and joint binder compatibility preserved; direct two-closure construction is only a route priority. All three remain open; no DAG status changed. See [round 11 priority attack](../notes/progress/2026-10-07-successor-priority-attack-round11.md). A separate default-off implementation slice is adding only exact HIR parameter-to-current-row identity capture; it does not grant eligibility or Apply typing.

The opt-in parameter-row capture is now implemented and independently compiler-referee reviewed. It retains exact HIR parameter recipe identity with the solver's actual startup value-row ordinal, including unsupported-body cases without a LambdaRecipe; shadow-only reservation failure reports Unavailable without changing inference. Local shadow binders with no production recipe return NoProductionRecipe, and the pending Apply remains unresolved with no facts. Focused parity/identity tests, a simulated unavailable-state test, feature-on/off package checks, formatting for changed non-drift files, and diff checks passed. See [round 12 parameter-row bridge](../notes/progress/2026-10-07-shadow-parameter-row-round12.md). No semantic gate or DAG status changed; production cutover remains prohibited.

### Current-head reattack: round 13

At latest pushed baseline `911204e1b1d4455077829440b16eab32c7a64d09`, ALL_VIEW's correlated nonidentity-result/paired-Option-2 derivation and latent-history adversarial attack were independently reviewed. They reproduce the already reviewed round-3/result-checking route; no accepted actual-root Direct or qualifying source counterexample was found. The reviewer refined the sufficient domain/result premise and confirmed the owning unresolved leaf is a Function result-check certificate consumed by an actual `B_common` resolver, with source production and universal derivation coverage separate. ALL_VIEW stays OPEN-PROOF; PRINCIPAL stays CONDITIONAL-CLOSED. The fresh Frozen Oracle reread likewise found no new source producer beyond the documented ordinary App demand/provenance mechanism; its generated ports, frame metadata and provenance payload do not introduce current typed occurrence/owner evidence or shared `xi`. See [existing bounded Oracle archaeology](../notes/progress/2026-10-07-frozen-oracle-ordinary-call-source-producer-archaeology.md); no Oracle semantics are adopted.

The reviewed REC_DESC equivalence is now reflected in its canonical minimal cut: only under the same independent guards and an established finite-history `G ⇒ Q` premise are reflection and direct introduction logically interchangeable, with `exists h. forall e` retained. It supplies neither premise nor cyclic acceptance. DAG validator remains PASS at 90 nodes / 196 edges (7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY); no node status changes.

### Current frontier attack: round 14

At pinned baseline `b6e566936308aeac78d30cf497a6e617c2a7d0e9`, the ready dependency frontier was reattacked at INTRO, SEED_SOURCE, and REC_INIT. INTRO's `lambda(x,x)` constructor shares one fresh endpoint between parameter and result but does not classify its semantic binder; rigid request opening remains its distinct proved source class. For annotated `apply(f: _ -> [io] _, x) = f x`, SEED_SOURCE still lacks exposure-time `ProtectedVarAt` or a proof that no seed applies, even after granting annotation/profile correspondence and local permission. For `my f = g; my g x = f`, a candidate finite provider graph does not establish the target's availability at the initializer read; the missing clause needs source-selected consumer and initialization-prefix evidence through the actual read/denotation. Independent spec-auditor/compiler-referee reviews passed the bounded cuts; REC_INIT's owner/read incidence is conditional on the source-selected rule, not a new activity premise. No semantic status changed. See [round 14 frontier attack](../notes/progress/2026-10-07-successor-frontier-attack-round14.md).

The existing shadow fixture now joins one continuous current identity path: source HIR parameter → exact startup row → target scheme origin binder → incoming fresh row for that scheme-qualified binder → receiving public-alias scheme origin. It asserts the incoming row differs from the startup row and keeps all successor correspondence premises unresolved. The `pub` marker remains metadata, not export eligibility. Focused test and compiler-referee delta review passed; this is identity plumbing only.

Round 15 records that path and its proof boundary in [the shadow identity crosswalk note](../notes/progress/2026-10-07-shadow-identity-crosswalk-round15.md). The complete `shadow_receiving_root_scheme_crosswalk` integration target passed with both required features enabled (3 tests); semantic DAG counts remain unchanged.

Round 16 follows an experimental direct-parameter Apply into the current target/receiving schemes. HIR parameter identity joins the pending solver callee and exact startup row, but the multi-item Core skeleton has no corresponding registration and the startup row has no target scheme-origin binder. The test therefore stops before any freshening correspondence and preserves the unresolved Apply/generalization premises. Production HIR still refuses this Apply. Compiler-referee and delta review passed; all four tests in the focused crosswalk target pass. See [round 16 shadow Apply/formal crosswalk](../notes/progress/2026-10-07-shadow-apply-formal-origin-crosswalk-round16.md).

The default-off generalization capture now retains the current generalizer's exact Q/R binder-to-historical-row selection map, with per-member staging and successful-solve publication. The receiving-root alias fixture checks same-row fresh-use linkage, distinct owners despite equal local ordinals, cross-solve separation, stable identity, and complete-empty origins; an injected second-member finalization failure publishes nothing. Compiler-referee review passed. Two integration tests, one failure-path test, feature-on/off package checks, targeted formatting, and diff checks passed. The nonempty-R case is traced in code but lacks a dedicated fixture. All successor/eligibility premises remain unresolved; `HIR_WIRING` is still IMPLEMENTATION-ONLY. See [round 9 priority attack](../notes/progress/2026-10-07-successor-priority-attack-round9.md). Next attack: source-derived eligible-owned/fixed-import partition and complete dependency correspondence at generalized use, without equating F5 Q/R layout to successor binders.

### Other round 7 fronts from the same baseline

Started from remote `f3be02da1ba169a88acc154ac29621634f3cc89b` (historical
round-7 baseline; the newer O0 note and shadow checkpoint are recorded above).
The canonical 90-node / 196-edge DAG remains 7 CLOSED, 20
CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC and 1
IMPLEMENTATION-ONLY; no semantic gate moved.

The direct `SIG_RULES` source-origin audit grants O0 only to isolate P2 and
retains the approved nested source `my apply f = { my step x = f x; step }`.
Formal registration, captured Name/Result identity, Call-generated upper
occurrence and reviewed S1 protection are derivable. The first missing head
remains original static slot birth and owner incidence:
`exists s,o. s ∈ Slots_orig(beta) ∧ Own_orig(beta,s,u_f,p0,o;X)`. K-Leaf and
K-Image construct original contributions, K-Incidence consumes an owner, and
candidate K-Owner cannot establish the first owner without a new source rule.
No complete competing Authority-consistent semantics or admitted-source
counterexample was found; Option 2 production observations do not construct
original source incidence. This O1 result is conditional on O0 and does not
change the latest dependency order: first discharge `H_eff` and `OC-CallEff`,
then return to static slot/owner birth.

The CALL_TYPE audit identifies the same concrete unconstructed step inside
`SEM_JOINT`: source-directed whole-argument checking at the actual returned
provider/world must establish `ArgCompatible` jointly with argument typing
while preserving each retained `CalRet` witness. The direct REC_DESC route
derives captured Name identity and inert Return but still needs an independent
ordinary Name/Return membership rule at the same original `(xi,w)`. The exact
`REC_INIT_SELF` proof and independent reviews are already recorded and closed;
other initializer classes and compiler enforcement remain separate.

The distinct ALL_VIEW Record-width route derives only the structural
`Record{tag:alpha} ≤ Record{}` prefix. It reduces the first semantic leaf to
same-witness decorated `DescMem` restriction at the returned Record incidence,
then requires separate future-client admission restriction and actual
`B_common` resolver evidence. No `Direct` witness was constructed.

In the implementation lane, a compiler-referee-reviewed default-off observer
now joins a pending SCC use to the exact committed current route, same-store
fact and provenance. It distinguishes absent route from factless
Bottom-trivial route, leaves successor generalization/Q-R/shared-contract
transport pending, and does not change production inference. See
[`shadow-current-use-route-crosswalk`](../notes/progress/2026-10-07-shadow-current-use-route-crosswalk.md).
The focused test, feature-off package check, targeted formatting and diff check
passed. `HIR_WIRING` remains IMPLEMENTATION-ONLY. No semantic gate moved. The
next semantic attack is `H_eff` / `OC-CallEff`; the next shadow step must
replace no premise until its corresponding theorem/rule is closed.

### Latest multi-front attack: round 6

At starting remote `d8ddbb0a3a3ab80b7cca67de09a8310617ba1170`, the DAG had
90 nodes / 196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY and 0 BLOCKED. The O0 attacks locate
the exact bottleneck: typed-core forms a body/result skeleton, while complete
`J_call` and its original signature/output map remain unintroduced. Theorem C
preserves pre-supplied maps only. Frozen Oracle lineage yields a historical
App demand/provenance mechanism, but not the current original-sort map,
owner/slot or complete contribution; Oracle semantics remain
non-authoritative. The same attack sharpens INIT_WORLD to an importer-incidence
clause with overlap/restriction and fixed-import substitution equations.
Direct REC_DESC and Name/Name CALL_TYPE routes reach their already-known
cyclic-Return and checking-to-`ArgCompatible` leaves. No node or edge moved;
counts remain unchanged. Compiler-referee and spec-auditor reviews passed for
the semantic boundaries and authority attribution; they did not reproduce
the historical Oracle blob lineage. The requested nested/grouped pending-Apply
to eight-address shadow join already exists at the pinned HEAD, so no code or
test change was needed. See
[round 6 frontier attack](../notes/progress/2026-10-07-successor-frontier-attack-round6.md).
Next: attack an actual independent original signature-elimination clause at
the fixed Call; do not spend another round wrapping supplied maps in transport.

### Shadow crosswalk verification

The nested/grouped pending-Apply to core eight-address identity crosswalk
already exists in the current default-off differential test. The focused test
`pending_solver_applications_join_exact_shadow_call_and_use_occurrences`
passed (1 passed, 4 filtered out). The default `sccache` wrapper failed to
start with `Operation not permitted`; rerunning the exact target with
`RUSTC_WRAPPER=` bypassed that wrapper and passed. No compiler files or test
expectations changed. Typed ports, semantic `beta`/`Slots`, call typing and
original association remain unresolved; this checks structural bookkeeping
only.

### Priority C continuation: nonidentity export

At `b9ffbfc20f1cbd71f2b5deccea6ee8a033d55ceb`, the bounded Name-result union
route found a sharper ALL_VIEW source leaf. Logical relation-union injection
preserves a fixed witness, but neither Name/Lambda skeleton nor checking
introduces a public endpoint whose `DescMem` is that union. The separate
finite `Le` inclusion and actual whole-Function resolver acceptance at
`B_common` remain downstream. A returned-Function guarantee-widening route
likewise needs an original `DescMem` decomposition. No concrete accepted
nonidentity export or counterexample was found; ALL_VIEW stays OPEN-PROOF and
PRINCIPAL stays CONDITIONAL-CLOSED. See
[the nonidentity export attack](../notes/progress/2026-10-07-all-view-nonidentity-export-attack-round1.md).
Next: attack the original value-union descriptor/checking constructor at the
returned Name and its consumption by an actual-root resolver.
Compiler-referee review found and repaired a minor precision overstatement:
the exact union equation is specific to that candidate, while the general
inclusion leaf allows independently licensed extra values. The delta review
passed; status and DAG totals remain unchanged.

The [full-attack review](../notes/progress/2026-10-07-successor-full-attack-review.md)
records actual proof/review/repair/check results. The
[theorem dependency map](../notes/theory/inference-theorem-dependencies.md)
and [theory map](../notes/theory/inference-theory-map.md) are synchronized
navigation into this ledger, not independent duplicate gate lists.

### Latest dependency attack: round 4

At remote baseline `1001c274cbf8bc867a03e72edbbfb08b3618e950`, the
canonical DAG started and ended at 90 nodes / 196 edges: 7 CLOSED,
20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC,
1 IMPLEMENTATION-ONLY, 0 BLOCKED. The reviewed
[round-4 attack](../notes/progress/2026-10-07-successor-dependency-attack-round4.md)
did not promote statuses. It sharpens the exact next source producer for
ORIGINAL_ASSOC after the reviewed S1 seed/exposure derivation; proves only a
conditional immediate `C1=C0` projection inside CALL_TYPE; keeps INIT_WORLD
at independent importer-incidence introduction, REC_INIT at another-member
initialization, and ALL_VIEW at result-certificate production plus actual
`B_common` Function evidence introduction. No new semantic clause was
proved, no complete alternate semantics or source counterexample was found,
and production cutover remains blocked.

The default-off
[receiving-root/current-scheme shadow crosswalk](../notes/progress/2026-10-07-shadow-receiving-root-scheme-crosswalk.md)
extends the structural observer through three source Name occurrences,
current Q/R captures, receiving alias schemes and retained visibility markers.
It does not infer export eligibility or successor shared-contract transport.
Compiler-referee and spec-auditor reviews passed the semantic attack note;
regression-auditor review and the focused one-test Cargo target passed. No
production inference path changed.

### Latest O0 attack: round 5

At `cb789e453a080d751f9689918f94974283be7302`, a constructive rule audit,
same-port adversarial attack, current compiler trace, and architect review
isolated candidate `OC-Output-Intro` for the original typed Call-output map.
Authority locates the required immediate complete-invocation port but leaves
the original-sort constructor open. Compiler-referee and spec-auditor reviews
passed the bounded rule signature after minor precision repairs. No proof of
the candidate constructor, competing complete semantics, source
counterexample, implementation gap beyond the already retained unresolved
Apply row, or DAG status promotion was found. Counts remain 7 CLOSED,
20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC and
1 IMPLEMENTATION-ONLY. The exact remaining constructor is recorded in
[round 5](../notes/progress/2026-10-07-original-call-output-introduction-round5.md).

### Latest O0 continuation: round 6

At latest remote baseline `d8ddbb0a3a3ab80b7cca67de09a8310617ba1170`, two
independent read-only routes specialized and inverted Theorem C and the
source-indexed realization theorem at the captured `f x` Call. Both found the
same boundary: the realization theorem preserves typed paths and static maps
already supplied by the decorated source schema; it does not introduce the
original-sort output correspondence from the independently formed Function
signature to `p0`. Supplying that map assumes O0, while withholding it leaves
no construction step. This sharpens the route limitation, not a theorem that
no other source producer exists. No semantic clause, counterexample or
complete competing semantics was found; no user decision is indicated.
`ORIGINAL_ASSOC` remains OPEN-SEMANTIC and DAG counts remain
7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC,
1 IMPLEMENTATION-ONLY, 0 BLOCKED. See
[round 6](../notes/progress/2026-10-07-original-call-theorem-c-output-map-round6.md).
The next attack is the owning original Function-signature
interpretation/elimination producer at the fixed Call, not another
reference-bound transport wrapper.

### O1 after the selected exposure

A separate read-only attack at `f9d41cdbde0ad5448073c1575abfdb0062818933`
granted the fixed source derivation, shared capture, reviewed S1 seed/exposure,
and O0 map. It still found no introduction for an original
`s ∈ Slots_orig(beta)` and `Own_orig(beta,s,u_f,p0,o;X)`. This is a distinct
static owner/slot gap; it does not equate `u_f` with the upper-check occurrence
`u`, and it needs no receiver activation. The interface is an obligation
signature, not a new rule, and its sequential dependency on O0 is only this
route's decomposition: a joint rule could produce both. No status or edge
changed. See the existing [source-introduction contract](../notes/design/2026-10-07-original-call-source-introduction-contract.md)
and canonical ORIGINAL_ASSOC leaf; next attack the independent
source-directed `Slots_orig` / `Own_orig` constructor with dischargeable
premises.

### Latest reviewed continuation: round 3

The [round-3 review/integration record](../notes/progress/2026-10-07-successor-round3-review.md)
starts from current remote `6fb5d7f6`, preserving all intervening work since
round 2, and revalidates the additive remote through `d27f4090`. The current
canonical ledger has **90 nodes / 196 edges**: 7 CLOSED, 20 CONDITIONAL-CLOSED,
1 IMPLEMENTATION-ONLY, 43 OPEN-PROOF, 19 OPEN-SEMANTIC and no user-decision
blocker. Three existing OPEN nodes move to conditional closure: **65 → 62 OPEN**.
The one added CLOSED exact self-init subcase is reported separately.

- **CALL_TYPE is CONDITIONAL-CLOSED** by the repaired
  [whole Call composition proof](../notes/progress/2026-10-07-call-original-rule-round3.md)
  §2.1. Actual CalRet, whole-carrier DelayIntro, each receiver/body/native/consumer
  phase and complete pending Bind laws remain independently unconstructed,
  together with CI-Operands, CI-Bind, CI-ArgFrame, CI-Receipt and CI-StepFrame.
  The returned-callee world must support jointly compatible argument typing
  and the actual provider contract at that world. The compiler's accepted
  major finding was repaired by a fresh producer; fresh delta review passed
  the proof and required these full premises in the canonical records.
- **PRINCIPAL is CONDITIONAL-CLOSED** by the
  [whole-relation synthesis](../notes/progress/2026-10-07-actual-export-synthesis-round3.md).
  Its unchanged SOURCE_ADEQUACY / ALL_VIEW / full PROJECTION prerequisites
  yield one finite ordinary-use map for every valid finite public view,
  preserving the original strategy and actual `B_common` Direct evidence.
  Actual all-view acceptance, source adequacy and effective projection remain OPEN.
- **SOUND is CONDITIONAL-CLOSED** by the subsequently reviewed
  [publication/use synthesis](../notes/progress/2026-10-07-sound-publication-synthesis-round3.md).
  Its existing source/solver/production contracts plus the full existing
  HIR_WIRING stage correspondence reflect an actual accepted joint use into
  the same original scoped solution and semantics. One HIR_WIRING dependency
  is added; no new semantic postulate or node is introduced. Whole-use/evidence
  PROJECTION, actual indexed fresh maps, valid references and complete
  publication remain required. Fresh snapshots receive this proof before
  reuse; REUSE's assumed sound/principal rebuild cannot prove that base.
  HIR_WIRING remains implementation pending and all semantic prerequisites
  remain at their existing status. This certifies no current compiler path.
- **REC_INIT_SELF is CLOSED** by the
  [approved exact source rule](../notes/design/2026-10-07-recursive-self-init-executable-boundary.md):
  q1 singleton `my f = f` is rejected before initialization/self-read while
  F4 `Never` inference remains. Both independent reviews passed the governing
  rule and its envelope/inference/adequacy proofs. Other initializers and
  actual compiler enforcement remain separate; aggregate REC_INIT is OPEN-SEMANTIC.
- The same Call attack supplies an owned-image P2 discriminator, a stronger
  P3 finite-family-assembly obstruction and its finite semantic coverage
  quotient alternative. It preserves all original licensed witnesses;
  original slot/owner/view introduction, complete assembly, Attach and both
  licensing directions remain OPEN at their exact rule heads.
- The [world/recursive attack](../notes/progress/2026-10-07-world-recursive-rule-round3.md)
  exposes circular use of an ordinary world that already entails the member
  typing being introduced. Simultaneous root/world introduction must instead
  construct both from independent imports and provisional own roots. The
  next concrete cuts are source-root installation at the importer incidence,
  a uniform open action for semantic imports, and ordinary acceptance of
  the latent returned recursive provider.
- The [aggregate falsifier](../notes/progress/2026-10-07-aggregate-obligation-attack-round3.md)
  keeps the original tuple and nonempty production/admission while refuting
  source-to-actual coverage from domain and upper-observation inclusions alone.
  The actual descriptor's source-constructor membership head remains OPEN;
  Option 2 extras retain their independent all-member upper containment.
- The reviewed [initialization shadow](../notes/progress/2026-10-07-shadow-initialization-retention-round3.md)
  carries original HIR/self-Name/use/SCC identities through solve to the
  current scheme. The focused [q1 execution-boundary shadow](../notes/progress/2026-10-07-shadow-exec-self-q1-boundary.md)
  now recognizes only the exact approved singleton and carries cold
  `Reject(SelfInitNoValue, binder, rhs)` evidence; every near-miss stays
  `Unresolved`. Five focused tests and the feature-off core/HIR/solver check
  pass across the preserved implementation slice. Production enforcement and
  other initializer classes remain open; no normal inference path is switched
  or given an unproved semantic judgment.
- The reviewed [continued source/interface attacks](../notes/progress/2026-10-07-successor-round3-review.md#12-downstream-attacks-after-sound-no-further-promotion)
  retain SOURCE_ADEQUACY and IFACE_FORM as OPEN-PROOF. The first actual Lambda
  operational square is raw body Run versus the emitted decorated body under
  the same original environment/current world and complete consumer/return
  suffix. The interface producer must emit each original constructor's finite
  record, decode its exact RAW_SOURCE atoms, and preserve every actual
  downstream accessor. Full PROJECTION/GENERALIZE contracts alone do not
  enumerate those accessors. Both independent reviews passed; the referee's
  minor conditional-wording clarification is applied. These are exact local
  proof targets, not further status reductions or new source semantics.
- Latest remote `4a9d969d` is integrated. Its independently reviewed original
  Call O0/O1/C0/C1/J0 cut, witness-linked incidence obstruction and unsuccessful
  K-Owner pair audit refine ORIGINAL_ASSOC without changing statuses or edges.
  The opt-in current Q/R capture and historical Call crosswalk are preserved;
  their current-to-successor typing, association and q1 enforcement remain
  pending. Fresh integration reviews found no blocking or major issue. The
  ten focused initialization/capture/crosswalk tests and feature-off
  core/HIR/solver build passed on the merged code. §13 of the round-3 record
  accounts for the historical producer-hash discrepancy without rewriting it.
- Remote `ead43c6d` adds proof-obligation-economy policy. The §14 design-debt
  audit distinguishes already known construction evidence from missing
  semantic judgments. Retention can remove reconstruction of the former;
  it cannot invent original owner/licensing or world/member proofs. The
  user's explicit all-view/all-world/adequacy targets and governing contracts
  remain in force. No node, status, edge or production boundary changes.
- The final `d27f4090` research-only delta is integrated and independently
  checked in §15. It adds no semantic supplier: C-realization retains its
  original input, the source contribution needs its active ordered map,
  and open imports need an incidence action identified with their fixed
  independent meaning. The exact current nested path does not generate
  semantic association and then discard it. All statuses/edges remain intact.

The round-3 integration record is authoritative for actual review completion
and final publication; the DAG generator checks synchronization, not proofs.
Earlier per-attempt OPEN statements below are interpreted at their pinned
snapshots and are superseded only for the three named composition nodes and
the exact approved q1 subcase. Their semantic-input cuts remain current.

### Preserved reviewed continuation: round 2

The [round-2 review/integration record](../notes/progress/2026-10-07-successor-round2-review.md)
starts from `ad514061` and revalidates the additive remote through `3cf6bb70`.
The full preserved ledger and all 32 requested families were re-audited.
The round-2 canonical inventory was **89 nodes / 194 edges**: 6 CLOSED,
17 CONDITIONAL-CLOSED, 1 IMPLEMENTATION-ONLY, 46 OPEN-PROOF,
19 OPEN-SEMANTIC and 0 BLOCKED-BY-USER-DECISION. New restricted results
refine existing leaves rather than adding conditional gate names.

- [Original kernel construction](../notes/progress/2026-10-07-successor-original-kernel-construction-round2.md)
  constructs one whole contract before observation choice from explicit local
  lifts, retaining all original licensing witnesses. The direct OC-Call-Intro
  attack leaves original contribution-domain realization of the complete
  invocation image, static owner introduction and joint incidence coherence.
  Complete independent whole-carrier admission is distinct from the selected
  `Delay(Name_x)` source diagonal. These are actual additional semantic
  clauses, not association supplied by IDs or successful Q.
- [Recursive direct certificate](../notes/progress/2026-10-07-successor-recursive-coinduction-round2.md)
  retains the actual captured pair and saved suffix. An ordinary two-closure
  introduction with all original local/inlet/world checks could replace
  finite-failure reflection as the descriptor proof method. Unfolding and
  postfixedness do not prove its absorption: the two-member swap has both
  empty and full fixed points. This is an algebraic method obstruction, not
  an admitted-source counterexample; non-descriptor discharge stays separate.
- [Finite incidence and scoped orbits](../notes/progress/2026-10-07-successor-effective-projection-round2.md)
  construct a finite context carrier for explicit relational source-port
  operations and exact equality-only projection at the original binders.
  Actual source operations/observers still need correspondence. A decidable
  Record-chain primitive refutes the general claim that pure FMP plus finite
  syntax/pointwise checking yields a computable complete joint bound; no
  Yulang undecidability is claimed.
- The reviewed [CTX_FINITE sealed-packet boundary](../notes/progress/2026-10-07-ctx-finite-sealed-packet-boundary.md)
  derives relational representation only for a restricted unsealed outward-
  permission trace. A result/store packet needs a source-justified bound
  capture and pack/open correspondence retaining original witnesses and
  dependencies. This is trace-local, not the global first or sole CTX_FINITE
  leaf; the gate remains OPEN-PROOF.
- Reviewed default-off [alpha comparison](../notes/progress/2026-10-07-shadow-interface-alpha-round2.md)
  and [atom-orbit evaluation](../notes/progress/2026-10-07-shadow-atom-orbits-round2.md)
  implement their supplied-input mathematical slices. Their 14 focused tests
  pass, including 28,800 direct/orbit comparisons. Exhaustion is explicit;
  complete semantic interfaces, actual source predicates and production
  inference are not supplied by these utilities.

Both independent compiler-referee/spec-auditor panels passed, including the
later orbit implementation panel. The old pending-review text for PATH_QUERY
is retired; its repaired reviews were already closed. The current single
`constrain_live` work bound and later HIR/SCC/source-retention slices are
preserved at their exact reviewed scopes. No remaining semantic node has a
qualifying pair of complete competing same-admitted-source meanings.

## Binding authority: directional source protection

Preserve the current explicit user decision:

```text
ProtectedVarAt(k,v,sigma,u) and SourceUpperUse(u,v,U,sigma)
    => NewProtection(k,u,outEff(U)).
```

Protect the output-effect occurrence of the upper source exposure. Do not
back-propagate that seed into an existing lower/provider effect. Do not
remove protection independently owned by that provider. Keep source/internal
inferred views distinct from actual callable role and Value/Computation
entry. No E/R question is reopened, and no completed normalized Function is
blanket-protected at every effect position.

Authority order: current explicit user decisions; Authoritative/approved
designs; exact reviewed rule/theorem packages; confirmed code/test invariants;
Frozen Oracle history; general PL practice. The directional addendum is
notation for the direct decision, not approval of every surrounding Draft.
The exact nested `apply/step` sequential binding/capture/return source is
approved; this does not approve arbitrary braces or local polymorphism.

Same `X`, original `xi=(nu,K,D)`, original scopes/binders and contribution
provenance are mandatory throughout. ID/source-position/endpoint equality,
Q success, solved shape and Oracle output cannot provide typed source
association or licensing. Preallocation and fresh names cannot provide
simultaneous semantic discharge or Generalize eligibility.

## Current closed and reduced scopes

| Result | Exact usable scope | Still required downstream |
| --- | --- | --- |
| Pure structural FMP and effective pure decision | Reviewed normalized pure fragment, regular witnesses and finite effective alphabet/permission inputs | Arbitrary Phi/effects/worlds, finite source contexts, joint solving/projection |
| Directional S1/S2/S3 | Selected source upper-output seed, retained provider protection and replay of certified facts | Full source applicability and independent primitive DREL-2 correspondence |
| SV | Selected receipt, actual result/rebind, reached capture/read and Pending suspension/divergence histories on one original typed/profiled envelope | Complete original source/profile/row formation and all-world admission |
| RS/RS-active/RS-use and LX | Actual rule-occurrence provenance, coherent use action, lexical ownership/import identities | Semantic introductions/guards, Generalize eligibility and member discharge |
| K/KP/KV | Actual guarded immutable mutual providers, paired finite histories and same-provider obligation schema | Independent descriptor membership and simultaneous local validation |
| SC role substitution | Completed singleton's source-entailed role substituted into every unchanged original active kernel | Generic mixed-use role aggregation and changed-kernel correspondence |
| Complete Call family | Whole callee/invocation/consumer/pending suffix relation at fixed original X | Independently typed original contribution fiber and licensing |
| CI-alpha / CI-use | Decidable alpha-isomorphism of supplied complete finite presentations; conditional arbitrary finite joint fresh-use preservation | Complete actual interface producer, primitive equivariance, semantic eligibility and lifecycle |
| FH | Pointwise finite-history invariant on fixed original scoped `(xi,w)` and compatible event extensions | Actual local certificates and independent descriptor finite-elimination law |

CI/FH are documented in the [recursive synthesis](../notes/progress/2026-10-07-successor-recursive-synthesis.md).
The compiler referee's initial shared-witness and equivariance findings were
repaired and independently re-reviewed; the separate spec audit retained
all conditional boundaries. FH is not claimed as recursive discharge.

The compiler-referee-reviewed [ordinary Call typing attempts](../notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md)
reduce a Value-entry identity receiver to the independent whole-carrier
elimination needed to type its returned value, and retain a separate pending
suffix obligation. The complementary [rejected separation](../notes/progress/2026-10-07-call-type-local-law-falsification.md)
shows the displayed raw Call equations alone do not entail the descriptor
fact, but its erasure fails the complete `SEM_JOINT`/local-typing premise; it
is not a Yulang source counterexample. `DESC_CLAUSES`, `ADMISSION_CLAUSES`,
`SEM_JOINT` remain open. Round 3 conditionally closes CALL_TYPE's composition
while retaining their concrete semantic construction.

The compiler-referee-reviewed [computed-callee/retained-entry attempt](../notes/progress/2026-10-08-call-type-computation-entry-attempt.md)
adds the distinct computational-callee route: a callee Request retains
`kf >>= S_f` before receipt, while a Request from the receiver's body consumer
retains `ka >>= R_r` after binding. The operational suffix equations pass;
typing stops at the independently admitted callee Return/pending-Bind
consequences and later argument/provider membership. A minor phase-boundary
notation finding was repaired locally. This is a conditional localization,
not a source counterexample or `CALL_TYPE` closure; the clause-construction
gates remain open.

Three complementary [CALL_TYPE follow-ups](../notes/progress/2026-10-08-call-type-closure-construction-attempt.md)
now sharpen that exact cut. The constructive note lists a sufficient
conditional package for Name/Return, inert Delay, actual receiver phases and
typed Bind closure, but obtains none of those laws from the open clauses. The
[pending-closure falsifier](../notes/progress/2026-10-08-call-type-pending-closure-falsification.md)
shows in a sorted algebra that typing the local continuation does not imply
typing its saved suffix; the example is explicitly not a `SEM_JOINT` or
admitted-source counterexample. The [shadow correspondence audit](../notes/progress/2026-10-08-call-type-shadow-correspondence-audit.md)
finds no additional structural identity loss in the retained ordinary Apply
path: source syntax and endpoint addresses still do not produce typed ports
or the independently interpreted callee/provider/world and pending-Bind
judgments. All three notes passed bounded compiler-referee review with no
findings; their then-open CALL_TYPE composition is superseded by round 3's
reviewed repair. `DESC_CLAUSES`, `ADMISSION_CLAUSES` and `SEM_JOINT` remain open.

The compiler-referee-reviewed [fixed-cut last-rule reconstruction](../notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md)
accounts for the Name/Return, inert whole-argument, actual receiver-phase and
pending-suffix branches without supplying their semantic last rules. An
independent premise audit confirms that `CALL_TYPE`'s pre-round-3
“independently admitted operand/world assignment” does not explicitly say
whether captured-value/provider/world and callee-Return typing are included;
`Gamma` identity alone supplies neither. A weak one-row separation is not a
model of completed `SEM_JOINT` or an admitted-source counterexample. The
operand-premise granularity is now explicit in round 3's CI-Operands and
related bridge requirements. Their actual construction and matching Return
rule remain unresolved; the reconstruction itself changed no semantic rule.

The later remote-reviewed [operand-context candidate](../notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md)
adds C1–C7 proposals for a joint ordinary lexical environment, independent
punctured filling, Name/Return, whole-carrier admission, all-demand Delay and
complete saved suffixes. Both independent reviews passed its explicitly
conditional scope. Root revalidated it when merging `7423c12a`: it constructs
no common interpretation, actual world, descriptor law or original association.
Its C1 environment already contains the value/member facts used by C3; source
generation still has to justify that environment, and C4 remains a proposed
Return introduction. Current CI-Operands/CI-ArgFrame and recursive own-root
cuts therefore remain. CALL_TYPE is conditionally closed by the separate
round-3 composition proof; DESC_CLAUSES, ADMISSION_CLAUSES and SEM_JOINT stay
OPEN. C1–C7 are not adopted. The candidate's suggested approval handoff is
not an active user-decision blocker: no pair of complete Authority-consistent
semantics with different outcomes on the same admitted source is established.

A bounded constructive cut was reviewed against selected contextual Function
membership. At an actual callee Return, same-tuple hereditary
`ValueMem_Af`, independently supplied same-value `VIncl(Af,Fc)`, and a
constructed complete challenge `d ∈ D_Fc` yield `ActualAdm` and all actual
receiver observations in `P_Fc(d)` on the original tuple. The compiler-referee
confirmed this conditional elimination, but found that it does not construct
legacy CI-StepFrame's full next `Input` and incident CI-Bind interfaces; it may
bypass that proof route as receiver-preservation evidence only. The same review
confirmed the computed-callee discriminator: an inner effectful callee can
request before the outer Delay/receipt/entry, so structural Name/Return cannot
be extended to computed callees. CALL_TYPE remains conditional; callee-prefix
typing, returned-event argument/challenge realization, original result/Bind
law, whole-Call arms, and production correspondence remain open.

The compiler-referee-reviewed [principal factorization attempt](../notes/progress/2026-10-07-principal-whole-relation-factorization-attempt.md)
localizes two necessary source-to-query implications inside `ALL_VIEW`:
independent view validity must yield a complete checking derivation at the
same original witness, and that derivation must produce accepted `Direct`
evidence at the actual `B_common` export. The note gives only a conditional
composition; it does not close `ALL_VIEW` or `PRINCIPAL`.

The compiler-referee-reviewed [actual-export constructor attempt](../notes/progress/2026-10-08-principal-actual-export-rule-attempt.md)
constructs a finite candidate §5.3 certificate for matched acyclic allocation
views, including a strictly wider public allowance and paired Option 2 extras.
Acceptance remains conditional on resolution conformance and complete
independent descriptor/admission contracts. A checked `Value` with a
nonidentical interface reaches an unmatched `VIncl(A,B)` evidence leaf; this
is not a source counterexample or proof that no other resolver case applies.
`ALL_VIEW` remains open. Round 3 closes only PRINCIPAL's full conditional
composition, using all three unchanged prerequisite contracts.

The compiler-referee-reviewed [Integer/Top actual-root bridge attempt](../notes/progress/2026-10-08-principal-vincl-actual-root-bridge-attempt.md)
extracts the current integer literal's occurrence-local producer, then stops
before a decorated nonidentity `VIncl(Int,Top)` clause. Even conditionally
granting that inclusion leaves the actual `B_common` evidence gap under §5.3's
unchanged non-coverage interface premise. This does not derive accepted
`Direct`, a counterexample, or close `ALL_VIEW`/`PRINCIPAL`.

### Latest current-remote attack: precise frontier, no status promotion

Attack 4 starts at the latest verified `origin/research/simple-sub-intrusion`
HEAD `182cfebad42bd77e98dd96022f96c71bb4933759`. The canonical validator
reports 90 nodes / 196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED,
1 IMPLEMENTATION-ONLY, 43 OPEN-PROOF and 19 OPEN-SEMANTIC. The final counts
remain exactly the same; none of the attacked gates closed and no admitted
source counterexample was found. See the compiler-referee/spec-auditor-reviewed
[attack 4 synthesis](../notes/progress/2026-10-07-successor-frontier-attack4.md)
for per-gate before/after, exact remaining leaves, the existing shadow test
result and qualified method limits.

The attacks narrowed, without promoting, these existing leaves:

- `CALL_TYPE` stays conditional: the first exact Name/Name input needs an
  independent joint `Env/Name/Return` introduction at original `xi`; actual
  provider compatibility and the complete receipt/phase/Bind/pending laws
  remain separate.
- `ORIGINAL_ASSOC` stays OPEN-SEMANTIC: P2 needs a source rule introducing
  original `Slots(beta)` ownership, typed `p0`, complete Call contribution and
  joint owner/view incidence at the same `X`, scope and `xi`. P3 assembly and
  P4/ATTACH/licensing remain downstream.
- `INIT_WORLD` needs a filling-independent zero-step open-root introduction at
  the importing incidence; the step-index candidate's hole premise follows a
  real transition, while Name/capture/Delay is inert.
- `REC_DESC` keeps distinct FH failure-reflection and simultaneous two-closure
  routes; the first preserves `forall h. exists e`, and the second cannot
  assume a world that already entails the target member.
- `ALL_VIEW` remains open at actual designated export. The displayed source
  contract Function rule cannot build the widened Direct result from a leaf
  `VIncl` alone; the independent decorated value leaf is still missing.
- `SOURCE_ADEQUACY` remains open at raw `Run(f x)` versus the emitted complete
  Call body, including actual consumer, return delimiters and pending suffix.

The requested captured-source shadow slice was already implemented at this
HEAD. Its focused `shadow_captured_source_retention` target passed four tests
with `RUSTC_WRAPPER=` and one Cargo build job, checking retained source/HIR/Core
identities through solve and preserving the unresolved-premise/refusal
boundary. No redundant identity carrier or production inference change was
added. Production cutover remains prohibited by the open source, semantic and
conformance prerequisites.

### Latest exact-leaf attack at `8f40797c7`

Start DAG counts: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC, 1 IMPLEMENTATION-ONLY. Final counts are unchanged. No gate
closed in this attack wave, and no same-source competing-semantics pair or
admitted-source counterexample was established.

- **ALL_VIEW:** the compiler-referee-reviewed [ordinary result-checking bridge](../notes/progress/2026-10-07-all-view-result-checking-bridge.md)
  traces the concrete F5 result-child and its retained products. It does not
  construct successful decorated `VIncl` evidence: result work retains
  diagnostic/incompatibility information, ordinary Lambda synthesis supplies
  its body result directly, and final export rebuilds an F5 predicate. The
  smaller remaining construction is an original-scoped decorated result-check
  certificate from independently established nonidentity `VIncl(A,B)`, plus
  its consumption by an applicable whole-Function resolver at actual
  `B_common`. The independent inclusion and resolver/export obligations stay
  open; this is not a universal resolver counterexample.
- **CALL_TYPE:** a fresh minimal-constructor pass leaves the next exact input
  at joint argument typing and actual returned-provider carrier compatibility
  at the retained current world, represented by existing CI-ArgFrame. Separate
  marginal witnesses, Q success, and solved Function shape do not produce it.
  No status or edge changes.
- **INTRO:** the first missing classification remains ordinary unannotated
  parameter introduction: freshness and `Gamma(x)=Value(A)` do not classify
  `A` or its semantic introduction scope. Request-opening rigid coordinates
  remain the already selected subcase; no generalization or reclassification
  rule was added.
- **GUARD_INSERT:** constructive and falsification routes stop at the same
  source-realization head for q1, before preservation: the source judgment must
  identify whether `B(z)<:z` restores a declared bound or creates a new
  specialization obligation, preserving the original quantifiers and binder
  incidence. No admitted-source counterexample was found.

Earlier duplicate lifecycle assertions were dropped because the captured
artifact identity, seven pending premises, and foreign-root rejection were
already covered. A separate reviewed crosswalk now joins the exact pending
Apply's enclosing root to its current finalized scheme/component under the
existing SCC observer. The fixture has no operand SCC-use route and keeps
`SuccessorGeneralizationRuleUnresolved`; this does not establish an operand
freshening path or a local `step` scheme. Both feature configurations pass one
focused test. The canonical DAG remains 90 nodes / 196 edges with unchanged
statuses and dependencies.

## Priority frontier: complete original source contribution

Use the normalized route
`CALL_REL -> CALL_TYPE -> ORIGINAL_ASSOC -> ATTACH -> LIC_FORWARD/LIC_INVERT -> PROFILE -> ROWS -> independent admission`.

The complete Call interpretation already exists; constructing another index
is not a semantic gate. On the original kernel `I_orig(X)`, prove an inhabited
fiber whose witness owns the exact original slot/contribution at `beta,p0`,
types the complete receiver invocation and preserves source arm, scope,
providers and `xi`. Keep every legitimate original witness. Do not choose
`c=j_call`, `s=p0`, a per-use slot count or a new predicate by decree.

Then derive attachment-to-licensing and invert every original licensing last
rule. A single observed source exposure proves no exhaustive Slots inventory.
An Option 2 production observation need not have its own source execution;
conservative complete contracts still need original licensing. Callee
computation effects remain distinct from the designated receiver's upper
invocation view, even though both belong to the whole Call contribution.

See the [original-fiber construction audit](../notes/progress/2026-10-07-successor-source-association-falsification.md).
The later remote [typed source-view composition](../notes/progress/2026-10-07-source-view-to-original-attachment-composition.md)
closes the selected actual-read/profile/complete-Call composition under SV
premises, while still supplying no original static `(s,c)` interpretation.
Its companion [coverage attack](../notes/progress/2026-10-07-attachment-coverage-adversarial-attempt.md)
rejects erasing a retained static exposure merely because execution never
returns or emits an outward event; it supplies no exhaustive inverse.

### Latest Q/R lifetime sublemma review at `bed31069a`

The starting DAG counts remain 7 CLOSED, 20 CONDITIONAL-CLOSED,
43 OPEN-PROOF, 19 OPEN-SEMANTIC and 1 IMPLEMENTATION-ONLY. The independently
compiler-referee-reviewed [current Q/R capture-map theorem](../notes/progress/2026-10-09-qr-capture-map-identity-theorem.md)
closes one bounded `FRESH_LIFE` sublemma: in a successful immutable
`SolvedModule`, complete current-production Q/R captures preserve one
injective, use-disjoint historical row map, with repeated occurrences and
recursive bounds sharing one substitution. Review found a generic boxed-
finalizer counterexample when an unregistered Q ordinal is reused by R; the
theorem is therefore explicitly restricted to production-produced schemes,
whose producer registers all Q and whose indexed validation enforces disjoint
dense R ordinals. This does not prove source/successor correspondence,
activation liveness, internal SCC sharing, split/merge/rebuild correctness,
dependency completeness or atomic publication. `FRESH_LIFE` remains
OPEN-PROOF; no semantic or production rule changed.

### Source-use to current-capture shadow slice at `400fa1a91`

Starting DAG counts were 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF,
19 OPEN-SEMANTIC and 1 IMPLEMENTATION-ONLY; they remain unchanged. A
default-off focused observer test now joins two distinct parse-owned source
positions to two incoming current-solver uses, the same finalized target
scheme, and complete nonempty Q/R captures. Each use has a separate row map
and owner, while repeated binders inside each map remain shared. The fixture's
optional shadow `UseId` is absent, but raw source occurrence identity survives.
Regression review passed; the focused target passed after bypassing the
configured sccache wrapper. Both successor Q/R correspondence and shared
contract transport remain explicitly unresolved. This closes no semantic
gate and supplies no source-owned versus fixed successor partition. The exact
next source judgment must derive, from an original component and enclosing
context, member roots, eligible owned coordinates, fixed captures/imports,
binder scopes/order and the complete joint relation/evidence; only then can
use-time freshening act on owned coordinates while holding imports fixed.
The current F5 Q/R inventory does not determine that boundary, and successor
representation need not preserve F5's Q/R layout.
See the [focused crosswalk record](../notes/progress/2026-10-09-shadow-source-use-current-qr-crosswalk.md).

### FRESH_LIFE native source-partition adjudication

A subsequent source-theorem crosswalk finds that this exact partition
construction is already supplied on the selected native source side, within
its declared local-law envelope. Source Generalize §§3.3–5.2 derives the
publication/root-indexed retain/fix walk, original scoped eligible declarations,
whole relation, captures/imports and coherent incoming-use allocation before
solutions. SRC/SRC-J/GS/GC prove the corresponding joint finite source-use
fibers. Uniform inlet plus PE-ID instantiate the import-free `id` case; PE-PICK
constructs the finite public-import `pick` case while fixing `J_0` and its free
dependency closure. These facts are produced by source constructor records,
not inferred from F5 Q/R ordinals. An independent counterexample attack found
the structural partition determined modulo fresh-name choice for these bounded
cases; logical proof terms and endpoint specializations remain legitimately
nonunique. The attempted alias-splitting mutation is rejected because the
selected Alias/Name rule routes both occurrences through the same frame.

This supplies the bounded **source partition** leaf for those native cases. It
does not close `FRESH_LIFE`: ordinary F5 and the default-off candidate do not
construct or consume the selected `ScopedClosure` certificate, and actual
source/compiler identification remains open. Internal SCC sharing,
activation liveness, split/merge/rebuild, dependency completeness and atomic
publication also remain open. The node stays `OPEN-PROOF`; a focused independent
compiler-referee review found no issue in this bounded source-partition scope;
no aggregate promotion follows. Canonical-ledger wording is being synchronized
separately to distinguish the supplied native subclaim from its production and
lifecycle residuals.

The remote [constructor derivation](../notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md)
minimizes the missing producer to the five-node
`call(result(name f),result(name x))` proof cut. Source generation `H_gen`,
the stronger supplied typed/profile/history envelope `H_typed`, and the
sought `H_assoc` remain distinct. The [primitive-stop inversion attack](../notes/progress/2026-10-07-original-association-inversion-attack.md)
shows that source-base realization preserves the supplied original owner/view
kernel witness; licensing inversion must still enter that kernel's own rules.
The [bounded clause/sort audit](../notes/progress/2026-10-07-original-association-source-kernel-audit.md)
finds no association introduction in its displayed inventory, without proving
repository-wide nonderivability. These reviewed localizations sharpen the
existing open nodes and close no gate.

The compiler-referee-reviewed [constructive source-cut stop](../notes/progress/2026-10-07-original-association-constructive-source-cut.md)
confirms that even conditionally granting `CALL_TYPE` leaves the independent
owner/view-kernel input required by source-contracts §2.1 and §3.5. The
branch-accounted [rule-inversion certificate](../notes/progress/2026-10-07-original-association-rule-inversion-attack.md)
labels the forward missing introduction A0 (original slot owner plus complete
contribution) and the backward missing exhaustive licensing grammar L*. Its
unknown-rule branch is retained, so this is a diagnostic refinement, not an
absence theorem or new gate edge. `ORIGINAL_ASSOC` and `SIG_RULES` remain open.

The compiler-referee-reviewed [direct construction attempt](../notes/progress/2026-10-08-original-association-direct-construction-attempt.md)
forward-derives the approved source/Name/Normalize/application skeleton and
separately expands the complete invocation conditionally. It stops first at
complete `CALL_TYPE`; even granting that leaves the original independently
typed owner/view introduction unsupplied. This is a constructive prefix and
localized stop, not a source-rule adoption or nonderivability result.

The reviewed [conditional Call coverage lift](../notes/progress/2026-10-07-original-association-conditional-call-lift.md)
proves a narrow transport lemma: for any already existing original
slot/contribution witness with an independently typed complete receiver
coverage certificate, the exact source Return/Bind equation lifts coverage to
the complete `f x` Call while retaining that witness and original `X/xi`.
It then isolates the still-missing jointly sorted introduction of original
slot ownership and contribution typing. The reviewed [uniform-witness
discriminator](../notes/progress/2026-10-07-original-association-uniform-witness-discriminator.md)
shows conditionally that pointwise incidence coverage need not imply one
uniform complete-family witness; the candidate models are not certified as
original Yulang kernels. Neither note supplies the disputed source rule or
closes `CALL_TYPE`, `SIG_RULES`, `ORIGINAL_ASSOC`, licensing, or admission.

The architect/compiler-referee-reviewed [open original-Call kernel contract](../notes/progress/2026-10-08-original-call-kernel-contract-candidate.md)
keeps the existing `ORIGINAL_ASSOC` target fixed as one original witness for
the complete family. Pointwise coverage alone cannot establish it; a factored
schema yields it only under an independently supplied original assembly rule
that builds the same complete-family witness. This conditional proof shape
does not choose slot/contribution denotations or a licensing grammar. The
remaining cuts were `CALL_TYPE` (P1), original slot/contribution introduction
(P2), coverage meaning/assembly (P3), and exhaustive licensing/inversion
(P4); no semantic rule or new gate edge was adopted by that candidate. Round 3
conditionally closes P1 composition while retaining its explicit constructor
and joint-input laws; P2/P3/P4 still require original semantic construction.

The bounded authority audit of [inferred Function call views](../notes/design/2026-10-05-inferred-function-call-views.md)
confirms that the approved formation direction requires source-owned
`beta`/`Slots(beta)`, typed ownership/receiver paths and one shared `xi`, while
explicitly deferring their construction judgments. Source-contracts §2.1 takes
the independently typed owner/view kernel as an input and §3.5 assumes it;
§5.3 compares already presented clauses. Thus `ORIGINAL_ASSOC` remains an
`OPEN-SEMANTIC` clause gap, not a derivation from `CALL_TYPE` or a demonstrated
pair of competing complete semantics requiring a new user decision.

The independently compiler-referee-reviewed [P2 constructor attack](../notes/progress/2026-10-09-original-assoc-p2-constructor-attack.md)
grants complete Call typing only as a conditional isolation premise and traces
the remaining input cycle: source-contracts §2.1 supplies the independently
typed owner/view kernel, while C-realization and §6.1 allowance validity retain
or consume it. Neither route constructs original slots, typed `p0`, ownership
or complete contribution from the approved source cut. This is a bounded
premise-gap localization, not semantic impossibility or a closed P2 gate.

The compiler-referee-reviewed [round-4 constructor reduction](../notes/progress/2026-10-09-original-call-fiber-construction-round4.md)
separates source `H_gen`, conditional complete typing `H_typed`, and the
missing `H_assoc`. Its owner-first traversal isolates O0/O1: an independently
typed original output correspondence and source-owner/seed-at-exposure
introduction at the captured call. The ordering is only a selected traversal;
it asserts no dependency theorem between owner and contribution realization.
The separately reviewed [joint-incidence attack](../notes/progress/2026-10-09-original-call-fiber-adversarial-round4.md)
shows that even full pairwise projections plus retention of all license IDs
can fabricate a tuple when original witness incidence links are discarded.
Both are bounded conditional results. The reviewed [K-Owner pair audit](../notes/progress/2026-10-09-original-kowner-underdetermination-round1.md)
establishes neither uniqueness nor nonuniqueness from the open constructor
text. `ORIGINAL_ASSOC`, `CALL_TYPE`, licensing and admission remain open; no
Oracle rule or new source meaning is adopted.

The spec-audited [assembly witness-preservation falsifier](../notes/progress/2026-10-09-original-association-uniform-witness-falsifier.md)
confirms the candidate's conditional assembly lemma under its stated
existence/incidence premises. A separate finite presentation shows that
uniform complete-family coverage alone does not justify replacing the full
original witness relation by an assembly image: that extra replacement can
drop a distinct licensed witness while preserving projected coverage. The
candidate does not make that replacement and already leaves exhaustive
licensing inversion open. No original-kernel counterexample or gate closure
is established.

The compiler-referee-reviewed [bounded Call falsifier cut](../notes/progress/2026-10-08-original-call-association-adversarial-cut.md)
shows that at the fixed Name/Name source cut, the ordinary `x` formal makes
the normalized argument a `Return`; a latent returned value adds no recursive
Force. This excludes an effectful-argument mutation as a counterexample for
that exact cut. No admitted source counterexample, original incidence or
complete Call typing is established by that falsifier. Round 3's conditional
CALL_TYPE theorem supplies composition only; actual law instantiation and
`ORIGINAL_ASSOC` remain open.

The bounded [shadow/original-association correspondence audit](../notes/progress/2026-10-08-original-association-shadow-correspondence-audit.md)
maps retained source, core and solver identities to the required original
fiber fields. Pending Apply operand Uses do not enter the current SCC dependency
inventory; `beta`/slots, typed `p0`, receiver invocation, complete contribution
and shared `xi` remain semantic gaps. Its optional eight-label identity seam
has since been covered by the reviewed endpoint crosswalk above; that closes
no source-introduction or SCC-use rule.

The independently reviewed [Frozen Oracle selection-incidence trace](../notes/progress/2026-10-07-frozen-oracle-selection-incidence-producer.md)
adds a distinct historical source-to-hidden-port mechanism: a dot-selection
occurrence is registered before resolution, retained with separate receiver,
method-demand and selected-result endpoints, then consumed by method
resolution and source hover. Its resolved artifact omits a recursive-self
field that changes the method-use route, so the retained result cannot by
itself invert that introduction. This is historical characterization only;
dot selection does not construct the original `(s,c)` fiber for the fixed
ordinary `f x` Call, and `ORIGINAL_ASSOC` remains open.

The bounded [Frozen Oracle resolved-use/SCC trace](../notes/progress/2026-10-07-frozen-oracle-scc-use-association.md)
adds the historical lexical-use association path: a source `RefId` retains its
parent and use endpoint, then resolution joins that endpoint to a target
`DefId` and the SCC lifecycle retains it through an open use or later scheme
instantiation. The SCC payload drops the `RefId` and contains no Call identity,
static slot, typed position, complete contribution, or original joint
`(nu,K,D)`. This is a useful identity/lifecycle analogue only; it constructs
no `H_assoc`, grants no Oracle authority, and leaves `ORIGINAL_ASSOC` open.

The bounded [Specializer2 call-consumer reconstruction](../notes/progress/2026-10-07-frozen-oracle-specializer-call-consumer-reconstruction.md)
traces a separate downstream historical mechanism: a retained App rebuilds a
typed Function consumer from materialized callee/argument views and keys its
actual/expected subtype provenance to the callee expression. The App result
and emitted Apply remain downstream consumers. This does not construct the
original pre-query `(beta,p0,j_call;s,c)` association, `Slots(beta)`, a complete
contribution, or the shared `(nu,K,D)`; Oracle remains non-authoritative and
`ORIGINAL_ASSOC` stays open.

The bounded [Frozen Oracle ordinary-call source producer archaeology](../notes/progress/2026-10-07-frozen-oracle-ordinary-call-source-producer-archaeology.md)
traces header pattern extraction into `Def::Arg`, lexical `RefId` resolution,
ordinary App construction and the historical `(selected frame, formal DefId)`
subtraction marker. These records retain source/use/frame identities and live
inference endpoints, but no original static slot or complete receiver
contribution under the original shared `xi`. This is bounded historical
characterization only; `ORIGINAL_ASSOC` and all dependent gates remain open.

A focused reread of the already documented application-boundary producer adds
its per-argument CST range and the origin-before-demand / eager-drain /
conditional-span-after-demand ordering. The compiler-referee-reviewed
[source-boundary timing refinement](../notes/progress/2026-10-07-frozen-oracle-application-source-boundary-producer.md)
is cumulative archaeology, not a newly found semantic producer. Source origin
and available spans still provide no original owner/view-kernel witness, typed
path, `beta`/`Slots(beta)`, contribution or shared `xi`; `ORIGINAL_ASSOC`
remains open.

The bounded [Frozen Oracle Function derivation/path trace](../notes/progress/2026-10-07-frozen-oracle-function-derivation-paths.md)
connects that origin to labelled Function child constraints and explanation
parents, then finds a separate generalized-projection collector for typed
paths. The passthrough branch can connect an argument-effect label to an upper
return-effect endpoint, and projected paths are not reconstructed from
explanation labels. This is historical preservation/attribution evidence,
not the missing original source producer or current typed-path rule;
`ORIGINAL_ASSOC` remains open.

The independently reviewed [bounded ordinary-Call novelty stop](../notes/progress/2026-10-08-frozen-oracle-original-call-association-mechanism.md)
checked the remaining ordinary-cast activation and local synthetic-App seams
against the already traced call-upper, local-scheme, occurrence, SCC, selection,
Function-path and Specializer2 routes. It found no additional historical
producer satisfying the original owner/view-kernel contribution requirement:
cast activation consumes generated constraints and explanation provenance,
while loop desugaring reuses an Internal-origin App constructor. This is a
bounded dispatch-avoidance result, not repository-wide absence or
non-derivability. Oracle remains historical evidence only; `ORIGINAL_ASSOC`
and dependent gates stay open.

The compiler-referee-reviewed [Pattern-boundary follow-up](../notes/progress/2026-10-08-frozen-oracle-original-producer-mechanism-followup.md)
traces an adjacent case-arm mechanism: after shared pattern lowering, a
Pattern boundary joins scrutinee/pattern endpoints, then newly observed upper
bound IDs become PatternInput provenance. Shared pattern binders start as
`Def::Arg`, while Defined-lambda callers separately add Input/frame metadata.
This refines historical provenance attribution only; it supplies no ordinary
Call slot, complete typed contribution, or original shared `xi`. The trace is
bounded and non-authoritative; `ORIGINAL_ASSOC` remains open.

The compiler-referee-reviewed [Frozen Oracle declaration-slot trace](../notes/progress/2026-10-08-frozen-oracle-static-slot-producer-archaeology.md)
finds a distinct role/implementation declaration mechanism: declaration-order
substitution slots, logical annotation-binder references, requirement and
implementation identities/spans, and explicit/default/missing method routes
feed declared-view and shadow-target consumers. A minimal tuple discriminator
shows that the reference vector alone omits the variable's structural
position, while the full signature retains it. This is a declaration
provenance analogue only; it supplies no ordinary Call `beta`/`Slots(beta)`,
typed `p0`, owner/receiver path, complete contribution or original `xi`.
Frozen Oracle remains historical evidence, and `ORIGINAL_ASSOC` stays open.

The compiler-referee-reviewed [Frozen Oracle receiver-anchor trace](../notes/progress/2026-10-08-frozen-oracle-receiver-registration-archaeology.md)
finds an additional historical declaration/body mechanism:
`ReceiverMethodLoweringAnchors` are retained in a method-`DefId` pending
conformance record, then body value/effect snapshots are captured before
deferred requirement edges are applied. The exported snapshot plus tail count
does not recover receiver/tail identities, while the full descriptor retains
them. This is a receiver/body provenance analogue, not an ordinary Call
producer: anchors are constructed after body/Function constraints and supply
no original `beta`/`Slots(beta)`, typed `p0`, complete contribution, or shared
`xi`. It closes no semantic gate.

The spec-audited [Frozen Oracle typed-provenance route](../notes/progress/2026-10-08-frozen-oracle-typed-provenance-route.md)
traces explicit `ArgEffectContract` metadata from source annotation through
parameter identity and compiled-runtime remapping to call-spine hygiene, and
separately traces finalized typed-ACT identity/scheme transport. Its local
port discriminator shows the guard marker alone does not retain whether an
effect atom came from the argument-effect or return-effect port. Neither
route supplies the original Call contribution or proves a current-language
rule; `ORIGINAL_ASSOC` remains open.

The unreviewed [Frozen Oracle call-boundary novelty stop](../notes/progress/2026-10-08-frozen-oracle-call-boundary-mechanisms.md)
checks upstream CST/body dispatch and occurrence export against existing
ordinary-App archaeology. The additional seams return to the already traced
App producer; boundary handles exist before subtype submission, while typed
occurrence roots and App/span metadata are added later. This is a bounded
dispatch-avoidance result, not a repository-wide absence claim or source rule.

The compiler-referee-reviewed [per-formal call-upper follow-up](../notes/progress/2026-10-08-frozen-oracle-call-upper-consumption-followup.md)
traces the historical `DefId`-keyed list of application Function uppers into
Lambda parameter-upper construction. Annotation-provided wildcard ports can
be refined from that list; the nested projected branch substitutes the body
effect and submits projected-upper constraints. A bounded two-call
discriminator confirms the recorded uppers remain structural constraint IDs,
without a source Call key or the original complete contribution owner/path/xi.
This is historical interface-construction evidence only; Frozen Oracle remains
non-authoritative and `ORIGINAL_ASSOC` and downstream gates remain open.

The compiler-referee-reviewed [Frozen Oracle shared-boundary transport trace](../notes/progress/2026-10-07-frozen-oracle-boundary-transport-archaeology.md)
adds a compiled-unit lifecycle mechanism: already-generalized interfaces
produce a dependency-closed boundary table; import applies shared alpha
remapping, session initialization installs a longer-lived boundary
substitution, and per-use instantiation reuses those variables while
freshening local binders. This is historical interface transport, not source
Call formation: it supplies no original `beta`/`Slots(beta)`, typed `p0`,
complete contribution, owner/receiver incidence or shared original `xi`.
Frozen Oracle remains non-authoritative and `ORIGINAL_ASSOC` stays open.

The compiler-referee-reviewed [SIG-RULES completion-separation attempt](../notes/progress/2026-10-07-signature-licensing-underdetermination.md)
constructed no admissible pair of complete licensing meanings. Under equal
original primitive relations, clause graphs and certified transport at the
same `X`/`xi`, the resulting relations are extensionally equal; transport
alone cannot supply a competing source interpretation. This does not establish
uniqueness. Both separation and licensing still stop at an independently
typed original slot/contribution constructor, so `SIG_RULES` and
`ORIGINAL_ASSOC` remain open without a new user-decision blocker.

No real same-X licensing counterexample or competing complete-semantics
witness was found. The remaining clause is research-side OPEN-SEMANTIC,
not BLOCKED-BY-USER-DECISION.

### Round-5 source-producer and proof-economy continuation

The compiler-referee-reviewed [C-realization specialization](../notes/progress/2026-10-07-original-association-constructive-round5.md)
confirms that specializing §3.5 transports an already supplied source-member
witness and retains the independently interpreted owner/view kernel, decorated
source and primitive witness. Even conditionally granting complete Call typing
and typed `p0`, it produces no original inhabitant. `ORIGINAL_ASSOC` remains
OPEN-SEMANTIC.

The compiler-referee-reviewed [ordered-suffix representation attack](../notes/progress/2026-10-07-original-association-adversarial-round5.md)
retains source/static identity records and original witness tokens while
mutating the candidate's ordered continuation interpretation. It is a
conditional representation discriminator, not a Yulang source counterexample
or a claim that source order is not already available. The compiler-referee
found no findings.

The [current producer chronology](../notes/progress/2026-10-07-original-association-current-producer-crosswalk-round1.md)
was reviewed by a regression auditor; its one missing `shadow-f5` feature
premise was repaired and the delta review found no further findings. For the
exact approved nested source, HIR retains a cold local source carrier and the
solver retains one unresolved Apply row, but the ordinary Lambda still receives
an Error body. The sidecar scan adds no occurrence facts, Lambda recipe or
definition-use dependency; solving moves the row unchanged. This locates the
semantic producer boundary and does not show an already-produced fact later
discarded.

The compiler-referee-reviewed [open-import incidence attack](../notes/progress/2026-10-07-world-open-import-action-round1.md)
shows conditionally that a closed-identity substitution cannot transport a
hole-dependent occurrence when it coincides with a rigid occurrence. This is a
representation obstruction, not an admitted-source counterexample; the
importer incidence action and scalar world installation remain open.

The [reviewed source-introduction interface](../notes/design/2026-10-07-original-call-source-introduction-contract.md)
separates O0/O1 static ownership from C0/C1 complete invocation typing and
contribution realization, then leaves J0 to establish their original joint
incidence and complete-family coverage. Compiler-referee and spec-auditor
reviews found no remaining issues after correcting the displayed source to
the exact approved `...; step` candidate. The document remains
non-authoritative: it selects no original-sort constructor, certificate type,
or implementation, and proves no original fiber inhabitance.

Following the new [proof-obligation-economy rule](../rules/compiler-engineering.md#natural-compiler-behavior-and-proof-obligation-economy),
the design-debt audit classifies O0/O1/C0 as safety and natural-inference
construction obligations. C1/J0 also retain stronger characterization
requirements because the approved cutover contract explicitly requires the
complete contribution and family coverage. Later recovery of typed
correspondence or incidence may be reconstruction debt, but the inspected
current path does not show those semantic facts were first produced and then
discarded. The current structural carrier is therefore insufficient to turn
these missing introductions into D-only bookkeeping.

Do not launch another equivalent proof variant or repeat the bounded Oracle
attribution search. The repaired [Gen-Call-0/O0 bridge audit](../notes/progress/2026-10-07-original-call-gen-call0-o0-bridge-audit.md)
separates the generated `F_c`/`VIncl` constraint and immediate-port address
schema from round-4's original typed-path interpretation. Naming the emitted
constraint `u_c` and its demand `U_c=F_c` is valid bookkeeping; no distinct
upper type variable is needed. Even a decorated realization does not close
original-sort O0: an original Function-elimination map for this same Call at
the same root, scope and xi remains. The selector-swap discriminator
shows why equal row/type shapes cannot reconstruct the immediate path, but
does not give an admitted-source counterexample. Next, attack K-Owner's
original static-slot/owner introduction at this fixed incidence, consuming
the linked S1 evidence while keeping O0 independently supplied, and preserve
all original witnesses at the same `X,xi`. The reviewed directional S1 source
derivation already supplies the exact candidate's outer unannotated-formal
seed and protection-at-exposure through captured `f` and its Call. Keep its
dependent indices linked across `sigma_apply`/`sigma_step`, the formal
endpoint, lexical Name use and distinct Call checking occurrence; no ID cast
collapses them. This peels O1 to the original `Slots_orig`/`Own_orig`
introduction, but gives neither that owner nor O0's original typed output map.
Initial seed slots do not establish the complete slot inventory or ownership.
The reviewed interface remains non-authoritative; any new slot, contribution
or architecture meaning still needs the required user approval before
implementation. Soundness,
principality, source adequacy and production-conformance cutover gates remain
intact.

## Priority frontier: recursive/generalized source

K removes the opaque runtime provider graph. FH permits finite-history
induction without assuming the entire CompleteMem environment, but fixes
one original scoped assignment and requires compatible extensions on every
transition and sibling branch. Independently existential local checks cannot
be joined into a shared witness.

The upstream definitions are explicit DAG gates: DESC_CLAUSES and
ADMISSION_CLAUSES specify the complete independent relations; INIT_WORLD
specifies original open-world/import clauses; SEM_JOINT must construct their
one common interpretation. None is a source-validity witness. REC_LOCAL is
pointwise in that fixed semantics; INIT_VALID constructs the actual base,
and MEMBER_DISCHARGE establishes the complete simultaneous environment.

The compiler-referee-reviewed [INIT_WORLD clause localization](../notes/progress/2026-10-08-init-world-clause-localization.md)
factors one shared initial tuple into root, identity, incidence, current-world,
interface and puncture obligations. It localizes W0—independent exhaustive
root/world introduction for hole-dependent imports—as the first unspecified
clause; it does not choose that meaning or close `SEM_JOINT`/`INIT_VALID`. The
[shortcut audit](../notes/progress/2026-10-08-init-world-adversarial-shortcuts.md)
shows only a partial-factor non-entailment, not a complete Yulang model or
admitted-source counterexample; a same-X complete solution may be read out,
but its existence is the base-construction obligation. The bounded
[imported scalar/alias construction](../notes/progress/2026-10-08-init-valid-import-realization.md)
retains distinct supplier/import/alias identities on one X/xi and isolates
`Imp_Delta`/EnvStore/JointWF installation after granting source-link evidence
and local scalar constructors. Its punctured-call extension remains an
unproved seed schema with the added `ignore` Lambda/body/Bind relations
explicitly pending. These results retain `INIT_WORLD` OPEN-SEMANTIC,
`SEM_JOINT` OPEN-PROOF and `INIT_VALID` OPEN-PROOF.

The next descriptor proof cut is to localize the independent ordinary
descriptor clauses and prove exact-quantifier finite-failure reflection:
after separate root/static checks, any failed `DescMem` must have a finite,
independently admitted history that negates the full local-check judgment at
the original `(xi,w)`. FH then gives `DescMem` by contradiction. Root/zero-step
conditions, inert Return of the same latent handle, current resumed state,
original pending suffix and compatible event-local extensions must remain in
the reflected domain. This is the outstanding finite-elimination law, not a
proved characterization. It discharges only `DescMem`; `M_E`, carrier/world
clauses and simultaneous `CompleteMem` remain separate for
`MEMBER_DISCHARGE`. The bounded localization and authority audit are recorded
in [REC-DESC finite reflection](../notes/progress/2026-10-07-rec-desc-finite-reflection-localization.md).
The companion [typed-observation/history bridge](../notes/progress/2026-10-07-rec-desc-observation-finite-bridge.md)
derives finite translation only for descriptor clauses that independently
expose the required finite-domain, admission and full-local-check premises.
The follow-up [root and inert-Return attempt](../notes/progress/2026-10-07-rec-desc-root-return-clause-attempt.md)
separates FH's zero-interaction base (`W`, with no interaction check) from a
conditional all-extension failure proof for a fixed immediate Return clause;
the independent descriptor/readout premises remain absent. The separate
[finite-reflection adversarial analysis](../notes/progress/2026-10-07-rec-desc-finite-reflection-adversarial.md)
shows why finitary local clauses alone do not guarantee finite refutability
after existential witness projection. Its natural-number family violates
pinned FH's pointwise extension premise and is explicitly not an FH
countermodel. These records close no descriptor or recursive gate.

The compiler-referee-reviewed [REC-DESC quantifier attack](../notes/progress/2026-10-08-rec-desc-finite-reflection-quantifier-attack.md)
constructs compatible witnesses along one countable admitted path under
pointwise serial extension and finite-incidence stability. The union preserves
that path's recorded checks, but the independent returned-Function clause,
captured-lookup adequacy and completion/readout law needed to read it as
`DescMem` remain open. It does not commute existential witnesses across
alternative paths or prove finite-failure reflection/`REC_DESC`.

The bounded [latent Function clause audit](../notes/progress/2026-10-07-rec-desc-latent-function-clause-audit.md)
locates the actual source-indexed returned-closure reference clause and its
positive membership inversion. It does not provide an independent latent
Function `DescMem` clause/inversion or the original binder tree needed to
instantiate H1; H2–H5 remain uninstantiated, not falsified. The bounded
[captured-Name lookup stop](../notes/progress/2026-10-07-rec-desc-captured-name-lookup-stop.md)
derives `Synth(name g)=Value(R_g)` and inert `V[name g]=lookup(g)` at the
mutually recursive provider `my f x = g; my g y = f`, then uses the existing
knot equality `eta_f(g)=v_g`. That source identity still does not establish
`DescMem(R_g,v_g;xi,w)`. The next premise is independent semantic adequacy of
this captured lookup at the original scopes and `(xi,w)`, followed by checking
whether FH's independently interpreted `W` entails it without circularly
assuming recursive member validity. The bounded compiler-referee review found
and closed one scope finding; delta review has no remaining findings.
REC-DESC remains open.

Two further bounded REC-DESC attempts are now recorded. The compiler-referee-
reviewed [constructor proof cut](../notes/progress/2026-10-07-rec-desc-fh-constructor-attempt.md)
shows that the proposed clause-by-clause reflection proof cannot start from
the current source-contract package: exhaustive ordinary `DescMem` failure
inversion is absent, while C-realization assumes local descriptor typing. The
review confirms this cut for that proof method, not impossibility of another
proof. The independently compiler-referee-reviewed [pointwise-extension
attack](../notes/progress/2026-10-07-rec-desc-fh-adversarial-attempt.md)
gives a valid abstract uncountable partial-injection obstruction to finite
joint witness completion, even though every finite passing assignment extends
pointwise. Its required joint binder/domain is not grounded in an actual
descriptor clause, so it is not an FH or Yulang countermodel. Both results
preserve the original scope and keep `DESC_CLAUSES`, `ADMISSION_CLAUSES`,
`SEM_JOINT` and `REC-DESC` open.

Three further reviewed attempts reduce the descriptor proof boundary. The
[binder/domain audit](../notes/progress/2026-10-07-rec-desc-binder-domain-audit.md)
confirms the candidate returned-Function clause introduces nested universal
call obligations but does not provide the production latent-membership binder
tree. The [two-closure construction attempt](../notes/progress/2026-10-07-rec-desc-two-closure-constructive-attempt.md)
stops at C1, the missing ordinary constructor/root-introduction rule, while
independent guards also remain open. The [adversarial applicability attempt](../notes/progress/2026-10-07-rec-desc-two-closure-adversarial-attempt.md)
separates registered-root inclusion from membership of the actual returned
provider. Their bounded compiler-referee reviews found no blocking/major
issues; none supplies a same-source countermodel or closes
`DESC_CLAUSES`, `ADMISSION_CLAUSES`, `SEM_JOINT` or `REC-DESC`.

The compiler-referee-reviewed [REC_INIT first-read boundary](../notes/progress/2026-10-09-rec-init-boundary-attack.md)
uses the conditional singleton `my f = f` candidate to expose the earliest
publication obligation. Under explicit strict-initialization premises, a
successful provider publication would require an earlier successful lookup
of that same unavailable member. The source envelope and initialization
admissibility rule were not selected by the inspected clauses, so that analysis
derived no actual divergence, rejection or source counterexample. The approved
[q1 handoff and receipt](../questions/2026-10-07-recursive-self-initialization/receipt.md)
now select pre-execution deterministic rejection for this exact singleton
only, while preserving its existing F4 inference result. This does not approve
implementation or cutover. Round 3's independently reviewed
[governing-source record](../notes/design/2026-10-07-recursive-self-init-executable-boundary.md)
and source-adequacy argument now close exactly REC_INIT_SELF. The former q1
governing-record and execution-disposition obligations are retired; aggregate
REC_INIT and actual enforcement remain open. No other recursive initializer
form or general `Never` expression is covered.

Then construct those pointwise local/member/world checks and source
comparison/permission certificates. Generalize must choose its actual
semantically eligible view/binder/anchor arrangement; lexical identity, empty
outer captures and final scheme shape are insufficient.

For section 22, retain direct forbidden/ground consequences as closed. The
exact unresolved oriented insertion is `B(z)<:v` at `v=z,c,R_h`, with
origin-relative permission preservation or selected rejection; terminal
`z<:Top` needs its own source non-refinement/rejection certificate. A blanket
no-existential classification of every row is only a sufficient route, not a
mandatory additional gate.

## Open gates at this snapshot

Keep one original complete profile coordinate inside the jointly constrained
source relation `J_S`; do not independently choose completed P at each local
use. This removes duplicated premises, not the existence obligation. All
world/challenge/future-history quantifiers remain universal inside their
independent predicates and retain original binder placement.

For every independently valid public view, the actual remaining sequent is

```text
Valid_V(v) => exists original-scope x,p,w,a:
    J_S(x,p,w;xi) and K_G(x,p,w,v;xi)
    and Q_common(x,p,w,a;xi)
    and Direct(B_common(x,p,w,a),R_V(v);xi).
```

Legal common-descriptor formation, common totality and this actual-export
Direct lifting are distinct. Exact whole-relation rewriting preserves a query
that may fail; concrete endpoint successes are not transitive.

The Draft finite-context package assumes source-derived finite `J_T/A_T`.
Its state bound does not prove finite semantic worlds or effective joint
solving. Require preservation/reflection for every active original predicate,
a terminating complete candidate/residual procedure and exact public
projection. Practical resource rejection cannot silently truncate histories.

Two reviewed [JOINT_DEC research attempts](../notes/progress/2026-10-08-joint-dec-review.md)
now sharpen this boundary without closing it. The conditional residual-game
construction needs exact predicate-cell decision and prefix-local lifts; its
effective strategy output additionally needs computable challenge
classification/replay. The repaired ER premise captures that distinction, but
neither EPR nor ER is constructed for Yulang. A minimized three-predicate
example rejects pairwise witness amalgamation, not a quotient with full
pointwise reflection and coherent lifts. `JOINT_DEC` remains OPEN-PROOF. The
reviewed [native-id input-image owner cut](../notes/progress/2026-10-08-id-inlet-whole-output-image-owner-cut.md)
shows a conditional whole-image law and prefix-local lift for authentic
J/Car/context evidence plus one supplied joint strategy. That conditional
route still needs effective representation and reflection for the joint
J/strategy witnesses; finite proof recognition does not provide it. The
later SD-NPB result below constructs a strategy directly for its bounded
source-owned judgments, without claiming arbitrary-residual representation.
The [relative native-id witness transport](../notes/progress/2026-10-08-joint-witness-representation-constructive.md)
now proves a finite typed code transport only when the complete input strategy
already has an effective faithful code; independent review found no issue in
that conditional theorem. The [prefix-erasure counterexample](../notes/progress/2026-10-08-joint-witness-representation-counterexample.md)
shows that a proposed key merging Unit/Bool prefixes fails EPR.3 if an original
`Eq(J.payload, Unit)` observer is active; review passed, but that observer's
actual source emission is unproved. The [source-owner correspondence](../notes/progress/2026-10-08-joint-witness-source-owner-correspondence.md)
maps 21 witness coordinates to selected source owners and current Rust seams.
Its review confirmed that missing inhabited-cell reflection, whole-prefix
classification and replay are semantic A obligations, not facts currently
known by Rust and discarded; the sole minor precision finding was repaired.
The [source observer inventory](../notes/progress/2026-10-08-joint-observer-source-inventory.md)
finds no fixed-ground `Eq(J.payload, Unit)` in selected bare-id Delta, while
the actual `mu_result: J.payload -> A` admission condition depends on the
chosen result endpoint. Different concrete admission fibers alone do not
refute a quotient. Exact H3 emission from a concrete constrained source entry
remains unproved. Separately, the independently reviewed [complete Function
boundary obstruction](../notes/theory/2026-10-08-joint-decision-source-fragment-obstruction.md)
shows that checking only observed call payloads is unsound: a genuine Bool
challenge refutes an `Any`-input, `Int`-result boundary for the same native
identity callable. This rejects that mutation only; complete source decision
remains open. The [direct effective residual route](../notes/progress/2026-10-08-direct-effective-residual-route.md)
shows a conditional symbolic proof-producing alternative to EPR/ER, but it
still requires actual-atom coverage, faithful inputs, same-prefix joint
reflection and terminating complete search. Its [independent source-route
falsification](../notes/progress/2026-10-08-direct-residual-route-falsification.md)
separates native-id's parametric action on supplied certificates from
constructing those inputs; the source-lawful Identity/Compose family shows
unbounded retained derivation size, not an unbounded minimum witness or an
actual F5 trace. Both independent reviews found no BLOCKING, major or minor
issue in the notes' conditional claims and scope. The architecture audit still
classifies accepted-result reflection as A, complete inference for every
satisfiable actual generated residual as B, and encoding every arbitrary
semantic strategy as C; it does not reclassify any gate or prove an alternate
algorithm. Same-prefix lifting remains required when using a quotient. A
replacement route still needs source completeness, production correspondence,
principality/required observables, resource/failure ownership, Oracle evidence,
independent review and user approval before implementation. Those conditional
notes changed no production code and ran no compiler checks. The
[mu_result source map](../notes/progress/2026-10-08-direct-mu-result-source-map.md)
confirms that the premise is mandatory only for selected checked Value-entry
gamma and that current Rust retains no complete gamma or proof package. The
[mu_result kernel construction](../notes/progress/2026-10-08-direct-mu-result-kernel-construction.md)
is independently reviewed as a conditional validator/application for supplied
finite proofs under H1–H5; it does not decide proof existence or construct the
whole admitted input strategy. The inspected HIR/solver path retains no
complete gamma or proof package. The [falsification](../notes/progress/2026-10-08-direct-mu-result-kernel-falsification.md)
shows why rejecting one Identity proof is not a negative inclusion decision.
The source map locator was corrected to the actual `ResolvedExpr` declaration
before its checkpoint.

The independently reviewed [source-directed joint-decision theorem](../notes/theory/2026-10-08-source-directed-joint-decision.md)
and its [reference arithmetic/review record](../notes/progress/2026-10-08-source-directed-joint-decision-review.md)
are now checkpointed at `2590b3d07` and `c7c848489`. They prove a terminating,
sound and satisfiable-strategy-complete decision for the exact Native
Projection Boundary envelope, with a bounded Python reference implementation
and focused finite checks. The `id` case where a literal argument is checked
and exported at `Any` but the whole-result view is `Int` is decided `NO` by
retaining the genuine Bool production alternative. This discharges effective
joint witness search for that envelope; it does not establish that an ordinary
parser/HIR annotation occurrence emits the same complete judgment. The
enclosing Call owner, arbitrary residuals, all source cases, production
correspondence, principality, lifecycle/resource policy, and F5 cutover remain
open. A bounded [annotated Function field map](../notes/progress/2026-10-09-annotated-function-source-field-map.md)
now records the exact endpoint/target, tau/psi, gamma/J/Car and binder fields;
it was adjudicated against this theorem in `6464b3ec1`. The [source bridge
decision map](../notes/progress/2026-10-09-sourcebridge-decision-dependency-map.md)
records that the four approved decisions still do not select the caller API,
authentic source producer/H-bridge, storage/failure policy or production
adoption. The next source gate is a parser-to-typed-check occurrence with its
authentic caller context and complete producer outputs. The bounded
[JointWF-to-Parameter manifest](../notes/progress/2026-10-09-jointwf-parameter-owner-manifest.md)
maps named caller dependencies into sigma_a/Delta_a and the later gamma/J/Car
scopes, but the selected sources give neither a closed JointWF field schema
nor an exhaustive Delta_a enumeration. Its initial unconditional-success
overclaim was repaired in `8a26b1a9a`; independent compiler-referee and
spec-auditor delta reviews pass. It now preserves NO for failed checks and
emits a joint strategy only on SD-NPB YES. A bounded [current compiler cut](../notes/progress/2026-10-09-npb-current-compiler-correspondence-cut.md)
finds that no inspected ordinary or default-off candidate path produces the
full NPB input: annotation target evidence is first lost at CST-to-typed-HIR,
and authentic Parameter/Lambda/Call packages are also absent. This is scoped
static evidence, not repository-wide absence or semantic rejection. The exact
parser-to-check owner, caller-context dependency instance and emitted Call
consumer remain the next bridge. `JOINT_DEC` remains OPEN-PROOF; no compiler
production code changed.

Within SD-NPB, the supplied J/Car/gamma, winning-strategy and finite
inclusion-search premises are now eliminated by the source constructors and
joint elimination proof. The next complete-Call law must construct each
actual anchored/unanchored production arm's output-dependent
typed-state/descriptor/guarantee evidence at the source consumer, with
same-provider admission and the original continuation/future action. Receiver
membership alone does not prove a separately owned C0 arm. The field and
decision maps above are research correspondence, not additional independent
semantic or production proofs.

Option A/2 require independent exhaustive production membership/admission,
`D_C subset D_A` and `P_A subset P_C`, including licensed production-only
members. Reference source simulation is a sufficient subcase, not an
exhaustive membership restriction. Source State/read/replacement/resumed
store, reference/world validity, method/role/associated-type/visible-impl
resolution, complete interface lifecycle and production HIR coverage remain
separate exact ledger nodes. No successor production inference switch occurs.

## Implementation lane

The user-approved default-off shadow lane preserves source-owned structural
identities and explicit pending semantics. Latest remote declaration-owner
work is retained: a resolved callee can expose its original retained Lambda
parameter declaration; missing projection metadata stays `None`, not semantic
absence. The historical Call crosswalk remains compatibility evidence only. The
remote nested-unary retention extension preserves those declaration owners
through already supported unannotated ordinary trees, with grouped/computed
callee controls and all ordered pending rows retained.

The bounded [shadow State declaration-candidate slice](../notes/progress/2026-10-07-shadow-state-slot-source-candidate.md)
retains an artifact-branded caller-selected sigiled declaration position and
validates only same-artifact syntax shape. Its follow-on projection retains the
direct `BindingStatement` → sigiled declaration → optional direct annotation
and opaque `BindingBody` initializer identities. Recovery-free State
read/write expression positions are not exposed by the current parser, so
occurrence association remains unfilled. Ordinary HIR still rejects the
sigiled target; two distinct same-spelling declarations retain distinct
candidate IDs, and no State role, transition, effect or runtime behavior is
inferred. The focused three-test target and formatting/whitespace checks pass;
the follow-on projection passed compiler-referee review. `STATE-ID`,
`STATE-RW` and `STATE-RESUME` remain open.

The reviewed [Frozen Oracle State-frame archaeology](../notes/progress/2026-10-07-frozen-oracle-state-frame-mechanism.md)
recovers historical local-State lowering, synthetic effect registration,
dynamic frame/scope identities, live payload replacement and snapshot
restoration. It is useful for locating operational responsibilities only:
neither `SnapshotFork` nor Oracle's equations are current semantics. The
current typed captured-environment preservation at `C1` and its compatible
join with retained `CalRet` evidence remain open in STATE_RW/REF_WORLD and
CALL_TYPE CI-ArgFrame.

The remote [pending binder-use grouping](../notes/progress/2026-10-07-shadow-pending-binder-use-groups.md)
borrows existing direct-Use registrations under exact artifact-branded binder
identity. It preserves distinct Apply/Use identities and retained-node order;
empty groups establish neither semantic absence nor complete-use coverage.
The final compiler dependency audit found no conflict with typed evidence or
the source-plumbing test, and all pending semantic premises remain pending.

The later [all-retained-Use grouping](../notes/progress/2026-10-07-shadow-retained-source-use-groups.md)
also includes argument, returned and grouped uses without manufacturing direct
call registrations. Its exact borrowed ExprId/BinderId/UseId inventory preserves
the same structural-only boundary, with no mixed-role or complete-use judgment.

The [pending structural source-core projection](../notes/progress/2026-10-07-shadow-pending-structural-projection.md)
extends the default-off lane over retained unary Lambda/Bind/Use/Group/Integer/
Apply forms using flat same-arena offsets. It preserves declaration entries,
annotation metadata and call-local premise joins; Use normalization remains
pending on `Gamma`; its existing `from_raw` entrypoint still rejects sources
without a retained unary Lambda. The additive header-aware projection now
retains ordered root statement/header/name positions, existing parameter
identities and body identity for the approved two-parameter shape, including
exact direct-Use membership without creating Lambda or currying stages.
Annotations remain uninterpreted; application premises and capture joins stay
borrowed. Compiler-referee and regression reviews passed; the regression
review's header-membership coverage gap was repaired with unary/captured and
grouped/computed controls. Focused verification: 15 `yu-hir` tests, 10
`shadow_derivation` tests, 10 raw-inventory tests, and default-feature-off
`cargo check -p yu-core` pass. No typed derivation, semantic acceptance,
inference result or production route is claimed.

The new [finite typed evidence query](../notes/progress/2026-10-07-successor-typed-evidence-query.md)
computes supplied `Path`/`Inc_C` by typed reachability and exact current
handler/owner/original-receiver activity. It does not generate source profiles,
licensing, observations, receipts, liveness, grants or release. Its event-key
and zero-sized-token findings were repaired. The four new tests and the repaired compiler/spec reviews passed; final
remote-integration checks are recorded in the full-attack review.

The [directional HIR shadow obligation](../notes/progress/2026-10-06-shadow-directional-protection-obligation.md)
also records one unresolved protection-introduction premise for each direct
resolved-Use call, retaining the original application identity. It emits no
protection fact and does not establish the seed, exact output-effect port,
scope/xi transport, receipt, receiver, admission or semantic acceptance.
Focused shadow tests and the exact pending inventories passed; this remains
default-off bookkeeping.

The unresolved source-view premise inventory is now directly available from
every retained direct-Use call registration, including registrations without
the exact captured nested-block topology. The captured-call locator still
requires that topology; the inventory only lists the existing seven open
requirements and supplies no judgment, applicability, annotation-absence
claim, Q result or evidence. The focused regression is in
`crates/yu-core/tests/shadow_raw_structural_inventory.rs`; its direct-call
filter passed (1 test, 10 filtered). Rustfmt and `git diff --check` passed for
the three implementation/test files.

The [current-inference shadow correspondence](../notes/progress/2026-10-07-shadow-current-inference-correspondence.md)
joins admitted unary Name/Integer leaves through exact source sidecar keys and
characterizes the present HIR support boundary for applications. Production
HIR currently emits `UnsupportedExpression`/`UnsupportedTarget` on the tested
application shapes; the separate shadow rows are structural retention only.
This adds no typing or old-inference parity claim and leaves production support
and all semantic gates open.

The [opt-in resolved application slice](../notes/progress/2026-10-07-shadow-application-resolution.md)
adds leaf-only and one-level ungrouped nested ordinary `Apply` structures to
the experimental HIR route, joined to exact call/operand source identities and
existing name resolution. Each retained call keeps an explicit unsupported
semantic diagnostic; solver collection emits no facts. The HIR-to-core
crosswalk now covers both leaf-only and one nested argument application,
through raw and pending structural projection with separate call-local rows.
Whitespace/comment trivia does not alter name resolution, and unsupported
deeper/grouped/computed shapes remain atomic. Default and identity-only
lowering remain unchanged. Nested solver parity, typing, inference, semantic
acceptance, soundness, principality and source adequacy remain pending.

The default-off `shadow-f5` solver boundary now retains an explicit
`ApplicationTypingRuleUnresolved` row for each application it sees, carrying
the exact HIR Apply/callee/argument occurrence identities and direct Name
resolution where available. Collection remains a refusal characterization:
these rows create no application facts, Function recipes or operand
components; existing definition-root bookkeeping stays intact. The feature-on
focused test covers a nested `f(f 1)` identity join and unchanged refusal, and
the feature-off solver check passes. A second focused differential test starts
from one parsed file and joins every pending row's Apply/callee/argument HIR
identity to source-core positions, including distinct direct callee UseIds and
their Binder. Production refusal is checked by error kind, not exact diagnostic
text or span. Compiler-referee review found a test-only identity assertion
weakness; it was repaired to compare full parameter identities and the focused
test passed again. Regression review found no major issue and notes that a
complete row reorder would still pass. The later compiler-referee-reviewed
endpoint crosswalk below adds an outer/inner topology discriminator for the
nested/grouped fixtures, closing that specific reorder gap there. The row does
not retain shadow
UseId, typed endpoints, a callable role, `beta`/`Slots(beta)`, or any semantic
judgment. This is source identity plumbing, not successor/current-infer parity
or application inference. See the
[pending solver application identity record](../notes/progress/2026-10-07-shadow-solver-pending-application-identity.md).

The compiler-referee-reviewed [solved application-use retention slice](../notes/progress/2026-10-07-shadow-solved-application-use-retention.md)
moves those exact pending rows through `InferenceSession::finish` into
`SolvedModule` and exposes the same borrowed direct-Name inventory after
solve. Row allocation, ordering, operand positions and unresolved state are
preserved. This closes only an evidence-lifecycle gap in the shadow lane; it
adds no typing premise or production behavior.

The focused [operand source-Use differential](../notes/progress/2026-10-07-shadow-solved-application-use-retention.md)
now also joins both operands of `x(x)` after solve to distinct source `UseId`s,
their shared Binder, and the retained Lambda declaration. The supported
fixture requires those source mappings to exist; a missing skeleton, Apply or
declaration fails the test. `ApplicationTypingRuleUnresolved` remains, and no
semantic completeness claim follows. The focused differential target passed
all 4 tests; compiler-referee delta review passed after repairing its initial
vacuous optional checks.

The grouped nested-call slice now retains the approved ordinary source shape
`f (f 1)` through an explicit Group occurrence and both Apply occurrences in
the opt-in HIR/solver structural path. The differential joins exact Group,
UseId, shared formal Binder and parameter identities across source, HIR, core
and pending solver rows. Each application remains
`ApplicationTypingRuleUnresolved`; ordinary lowering and inference still
refuse it. Outer one-tuples, malformed groups, deeper nesting and other
unsupported shapes remain rejected. This adds source correspondence only, not
typing, call-view formation, role resolution, `beta`/`Slots(beta)`, or original
association. See `crates/yu-hir/tests/shadow_application_resolution.rs` and
`crates/yu-solver/tests/shadow_f5_differential.rs`.

The nested `f(f 1)` test now joins each pending solver row through the raw
core call registration to the same source Apply, callee UseId, Binder and
retained syntactic Lambda parameter declaration. This adds structural
HIR-to-core-to-solver correspondence only; formal applicability and typed
call-view evidence remain unresolved. The test-only `yu-core/shadow`
dependency stays outside production builds. A compiler-referee review found
one missing same-UseId assertion; it was added, and the focused test passed.

The [shadow annotation/header membership slice](../notes/progress/2026-10-07-shadow-annotation-header-membership.md)
now carries exact root-header membership through existing parameter-annotation
incidences and per-call registration views. An unannotated header parameter's
retained annotation inventory remains an inventory fact only. Regression
review found one minor test gap; a direct call to the unannotated header
parameter was added and the core shadow targets passed. Annotation meaning,
boundary effectiveness, profiles and typed ports remain unresolved.

The [shadow SCC use-endpoint slice](../notes/progress/2026-10-07-shadow-scc-use-definition-endpoints.md)
exposes each retained SCC use's exact parent/target definition handles after
collection-brand and frozen-plan validation. This supports future generalized
SCC identity plumbing but does not form a successor interface, map Q/R, or
freshen uses. Compiler-referee review passed; all 10 focused SCC observer tests
and the feature-off core/solver check passed.

The [pending SCC generalization carrier](../notes/progress/2026-10-07-shadow-pending-scc-generalization.md)
retains one exact current component behind the unconditional premise
`SuccessorGeneralizationRuleUnresolved`. It preserves current members, use
endpoints and artifact identity even for empty-use components or absent source
skeletons. Compiler-referee review and the focused 12-test observer run passed;
feature-off solver check passed. It introduces no successor eligibility,
generalized interface, Q/R mapping, beta/Slots, freshening or production route.

The default-off [SCC outgoing-use view](../notes/progress/2026-10-07-shadow-scc-outgoing-use-view.md)
adds a borrowed query for every retained dependency occurrence leaving an
exact current component. It validates component and endpoint identities,
keeps each UseId in retained order, and leaves the unconditional successor
generalization premise intact for empty results and absent source skeletons.
Compiler-referee review passed after adding a synthetic retained-inventory
test for two UseIds sharing one `(parent,target)` pair; current source
collection emits at most one use per parent, so that test does not claim such
a source-produced shape. The focused 16-test observer run, targeted formatting,
and whitespace check passed. No broad/default-feature check or measurement was
run. Querying one component scans retained uses for validation and lazily
again for selection (`O(U)`); querying all `C` components is `O(C·U)`. No
production SCC plan, counters, generalization or inference path changed.

The compiler-referee-reviewed [pending use-instantiation carrier](../notes/progress/2026-10-08-shadow-pending-use-instantiation.md)
joins each retained SCC UseId to its exact current parent, target, target
component and finalized member scheme. Successor generalization, Q/R
correspondence and use-time shared-contract transport remain explicit pending
premises, including for internal recursive uses, absent skeletons and empty
inventories. The focused `shadow_` target passed 29 tests (444 filtered), and
feature-off `cargo check -p yu-solver`, targeted rustfmt and diff-check passed.
No production inference route changed.

The compiler-referee-reviewed [pending-application source-use view](../notes/progress/2026-10-07-shadow-pending-application-source-uses.md)
retains the existing enclosing definition root on default-off Apply rows and
borrows each direct Name operand with its row, callee/argument position,
occurrence and unchanged resolution. This exposes lexical occurrences absent
from today's one-Use-per-binding SCC collector without minting production
dependency edges or claiming complete dependency coverage. The focused F5
differential target passed 4 tests, the focused unsupported-application test
passed, and the feature-off solver check passed; broad tests and old-infer
application equivalence remain unverified.

The compiler-referee-reviewed [pending Apply endpoint crosswalk](../notes/progress/2026-10-08-shadow-apply-endpoint-crosswalk.md)
extends the solver differential across retained Apply rows, HIR source
positions and core's existing eight-label endpoint-skeleton view. Nested and
grouped calls distinguish the outer argument labels from the inner whole-Apply
labels; the seven source premises, unresolved application state and solver
counters remain unchanged. This is structural bookkeeping only, not an old-
infer semantic differential or typed-port interpretation. The focused target
passed 4 tests; production semantics remain unresolved.

A read-only successor-frontier audit found no additional disjoint
identity/evidence-plumbing gap in this dependency cone: Apply/operand,
parameter declaration, annotation, and SCC identities are already retained
and checked through solve. The missing `beta`/`Slots(beta)`, typed `p0`,
receiver, contribution and shared `xi` require semantic producers, so no
convenience projection was added as a substitute. The direct-Name fixture now
has an ordinary-current-F5 control through lowering, collection and solve:
ordinary F5 retains its `UnsupportedExpression` and no pending-application
rows, while shadow retains the structurally mapped unresolved Apply and both
source Uses. Its focused differential test passed; this verifies the refusal
boundary and identity plumbing, not successor/current-infer semantic parity.

The reviewed [captured-source lifecycle slice](../crates/yu-solver/tests/shadow_captured_source_retention.rs)
first carried the exact approved `apply/step` `ShadowArtifact` through opt-in
HIR collection and solver finish while preserving production refusal. The next
[Call-to-current-scheme crosswalk](../notes/progress/2026-10-07-shadow-call-current-scheme-boundary.md)
joins the pending Apply's enclosing root to its current finalized SCC scheme,
but proves no operand use/freshening or local `step` scheme. The
[local-binding identity slice](../notes/progress/2026-10-09-shadow-local-binding-source-identity.md)
adds a cold `HirLocalId`, its local parameter owner, return-use occurrence and
the inner `f x` Apply to the shadow HIR sidecar; under `shadow-f5`, exactly one
`ApplicationTypingRuleUnresolved` row survives collection and solve. It keeps
the ordinary HIR Error body and outer-parameter recipe behavior, introduces no
local recipe or typed fact, and rejects six adjacent source shapes. M2
compiler-referee and regression reviews passed, including delta review of the
outer bookkeeping; the focused two-test target, feature-off package checks,
targeted formatting and diff check passed. Frozen Oracle correspondence is
historical identity/demand evidence only and did not reveal the missing
original `beta`/`Slots(beta)`, typed `p0`, complete contribution or shared
`xi`; `ORIGINAL_ASSOC` stays open. Broader source/typing/old-infer
differential, generalization and all application semantics remain open.

The follow-up [HIR-to-core structural differential](../notes/progress/2026-10-09-shadow-local-binding-source-identity.md)
now joins the sidecar's Bind, local Lambda/parameter, returned Use, capture,
Apply and operand identities through `ShadowArtifact` and the pending Core
projection, then checks the same evidence after solver collection/solve. Its
focused integration test passed and received regression-auditor closure with
no findings. This is source/HIR/Core identity correspondence, not an old-infer
semantic differential or a typed derivation.

The [Frozen Oracle local-call crosswalk](../notes/progress/2026-10-07-shadow-legacy-call-solver-crosswalk.md)
joins the recorded old-infer application/callee source spans to that same
shadow HIR/Core structure and its single pending application row before and
after solver finish. The test keeps historical IDs and scheme text opaque,
requires production HIR refusal, retains all seven pending premises, and
checks that no semantic facts are emitted. Its focused target passed and
received regression-auditor closure with no findings. This is structural
incidence/refusal differential only; it does not establish old/new inference
parity or discharge any call judgment.

The opt-in [current Q/R freshening capture](../notes/progress/2026-10-07-shadow-current-qr-freshening-capture.md)
retains complete successful current-solver route evidence behind the shadow
feature and exposes it through SCC identity queries. It remains separate from
successor Q/R correspondence and shared-contract transport. Compiler-referee
review and focused capture/shadow tests passed; ordinary solve stays
uncaptured, and no production inference route changed.

The local captured-Call test now also compares ordinary solve with explicitly
requested current fresh-capture solve, using separate collections of the same
immutable HIR so SCC query accounting and collection brands stay independent.
Current facts/errors/counters, pending unresolved Apply, retained source/local
identities, and the enclosing root's alpha-equivalent finalized current scheme
agree. Both runs retain zero SCC operand uses and unresolved successor
generalization; this confirms opt-in capture does not create a use or alter the
current result, and does not claim application-operand freshening or successor
Q/R correspondence. Its focused test passed.

The [CALL_TYPE CI-ArgFrame shadow marker](../notes/progress/2026-10-07-shadow-calltype-argframe-marker.md)
now records the still-unresolved joint argument-typing and actual-returned-
provider carrier-compatibility obligation at each structural Apply. The HIR
marker fabricates no provider/world/evidence, emits no constraint and does not
change the solver's unresolved application state. Compiler-referee and
regression-auditor reviews passed; focused HIR/Core/solver shadow tests passed.
This is an HIR_WIRING implementation slice only; CALL_TYPE stays
CONDITIONAL-CLOSED and no semantic or DAG status changed. The same attack wave
kept ORIGINAL_ASSOC P2 and REC_DESC open at their independent source-rule
introductions, localized INIT_WORLD's separate zero-step semantic-import
root-extension clause, and retained ALL_VIEW open at actual-export result
evidence. A bounded Name/Name CALL_TYPE construction derived the normalized
`Comp(empty, Ax)` and inert `Return(lookup x)` skeleton; the exact remaining
source head is sound whole-carrier argument checking plus independently
justified Name/Return typing jointly realized at actual `C1` for every retained
CalRet witness. This adds no semantic rule or closure.
The reviewed [captured-environment frame audit](../notes/progress/2026-10-07-calltype-captured-env-frame-leaf.md)
refines the fixed Name/Name premise: lexical resolution preserves the
parameter's reference identity, but does not establish its live provider and
latent-dependency adequacy after a state-changing callee reaches `C1`. The
initial adequacy and callee typing must share one original CI-Operands
witness; current-world preservation and actual-provider compatibility remain
separate open inputs. CALL_TYPE's status is unchanged.
Production inference and cutover remain gated.

From baseline `33d8cd4ef95d85712d2ab99dca0190e15c4d06bf`, a dependency-ordered
research pass reattacked `ORIGINAL_ASSOC` P2, INIT_WORLD W0 and REC_DESC.
ORIGINAL_ASSOC's candidate positive abstraction still cannot lift an
unanchored extra into the independently interpreted original contribution
sort; INIT_WORLD reduces source aliases to identity copying but still lacks
independent open-import introduction and zero-step root extension. For REC_DESC,
the finite-history route retains the necessary `exists h. forall e` failure
quantifiers but needs an independent descriptor readout; direct two-closure
introduction is narrower for the concrete recursive knot, but still lacks the
ordinary latent-Function membership/introduction clause. No exact competing
Authority-consistent complete semantics or admitted-source counterexample was
found. These results add no DAG closure; retain all statuses.

The reviewed [two-tail Apply shadow slice](../notes/progress/2026-10-07-shadow-two-tail-application-retention.md)
extends only the default-off structural lane: `f 1 2` and `f f f` retain two
left-associated Apply nodes through HIR, Core, collection and solve. The
computed outer callee has six common unresolved premises and no direct-use
registration; the direct inner callee has its six common plus two
direct-use-specific premises. Each remains unsupported by production HIR and
untyped by shadow solving. The DAG remains 90 nodes / 196 edges: 7 CLOSED, 20
CONDITIONAL-CLOSED, 1 IMPLEMENTATION-ONLY, 43 OPEN-PROOF and 19 OPEN-SEMANTIC.
Start/final DAG counts for this attack were identical: 7 CLOSED, 20
CONDITIONAL-CLOSED, 1 IMPLEMENTATION-ONLY, 43 OPEN-PROOF and 19 OPEN-SEMANTIC.
Next semantic attack remains the original source producer for P2; the shadow
slice is not evidence for that producer.

The subsequent bounded proof/review wave kept the same canonical counts
(7 CLOSED, 20 CONDITIONAL-CLOSED, 1 IMPLEMENTATION-ONLY, 43 OPEN-PROOF,
19 OPEN-SEMANTIC). A source-elaboration induction on the approved nested-call
example reaches the typed core skeleton and lexical identities, then first
fails at Application/Normalize: no rule introduces typed output
correspondence to the original `p0`; neither Name child supplies it. The same
induction introduces no original slot/owner incidence, so P2 remains open.
The strict two-model user-decision criterion was not met. Even granting P2/P3,
the next distinct leaf is an original `Attach_C` introduction retaining the
source attachment and contribution witness; `Lic_C` introduction and
exhaustive licensing inversion remain separate. The CALL_TYPE follow-up also
isolates checking-to-`ArgCompatible` against the actual returned provider's
whole carrier as an independent leaf after argument typing at `C1` is granted.
No semantic rule or DAG status changed. Architecture review found no consumer
that would justify splitting the existing premise inventory into duplicate
bookkeeping records. Next attack: derive the original typed upper/output
introduction at the actual `f x` Call, then its owned slot incidence while
preserving the same original `xi`, scope, and provider witness.

At remote/local baseline `08c1e1aa8faa97366f78b907b7b13e8b7477f11d`,
dependency-ordered attacks rechecked CALL_TYPE, ORIGINAL_ASSOC P2/P3/P4,
INIT_WORLD, REC_DESC and ALL_VIEW. They did not close a node. CALL_TYPE's
fixed-Name carrier path reaches C6 demand-time captured-binding adequacy at
every independently admitted demand world; if DelayIntro is granted, CI-Receipt
is next. P2 still lacks original `Slots/Own` and joint contribution
introduction; P3 lacks a fixed-witness complete-family embedding/coverage rule;
P4 lacks original licensing introductions and exhaustive inversion. INIT_WORLD
still lacks filling-independent import-root extension. REC_DESC still lacks
ordinary captured-Name descriptor introduction at the same world; direct
simultaneous closure introduction is the nearer conditional route, but its
guards and world validity remain premises. ALL_VIEW still lacks target
descriptor/result-check evidence and an actual `B_common` Direct consumer.
These are exact unresolved leaves, not new semantics or status promotions. No
same-source pair of complete Authority-consistent semantics with differing
approved outcomes was found.

The default-off [CALL_TYPE demand-time detail locator](../notes/progress/2026-10-07-shadow-calltype-demand-time-detail.md)
adds a borrowed candidate-detail accessor to the existing joint argument/
actual-provider premise. It identifies the unadopted C5/C6 route without
adding rows or evidence, changing inference behavior, or asserting demand-time
typing. Compiler-referee review passed. Focused HIR/Core/solver tests passed
(27/3/4), targeted formatting and whitespace checks passed. CALL_TYPE remains
CONDITIONAL-CLOSED and HIR_WIRING remains IMPLEMENTATION-ONLY. DAG totals are
unchanged; production inference still refuses Apply.

Production `SolvedModule`/collector/live solver/F5/generalizer/instantiator/
publisher and consumers remain separate correspondence work. A final scheme
projection is not a complete generalized SCC interface. Feature-gated shadow
plumbing does not supply production authority.

The current F5 replacement map makes the implementation boundary explicit:
F5c generalization is called inside `InferenceSession`'s SCC component
lifecycle (`crates/yu-solver/src/lib.rs`, `execute_scc_plan_inner`),
`ClosedValueScheme` finalization/publication, incoming Q/R instantiation,
and frozen `SolvedModule` root/projection queries consume that representation.
Replacing only `F5cGeneralizer` would leave current closed-scheme and Q/R
behavior active. Collection/SCC infrastructure may be reusable, but no
successor correspondence is established. The Authoritative
[`F5` foundation](../notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md)
keeps F0–F4 authority and narrowly supersedes named F4 limits. The reviewed
[Gate E charter](../notes/design/2026-09-29-scc-intrusion-redesign-charter.md)
requires a successor design naming superseded lifecycle, Oracle behavior,
compatibility deltas, rollback and structural input limits with deterministic
rejection/failure semantics; independent M3 semantic/specification and
material-performance review; then explicit user approval before implementation.
This map is source ownership only and closes none of those gates.

## Current reattack: demand-event realization (2026-10-07)

At freshly fetched remote/local baseline `f4d4558895e4e8dd72e3e9dc38df061b63ea207e`,
the DAG checker passed with the same 90 nodes / 196 edges: 7 CLOSED, 20
CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC and 1
IMPLEMENTATION-ONLY. A reviewed correction to the unadopted CALL_TYPE C5/C6
candidate records that `eta` includes a world while the proposed demand clauses
vary current configurations, and that `RunCert` omitted C5's original root
parameter. The exact missing semantic head is a total, coherent lift from every
independently admitted demand to an original-scoped event realization preserving
the original projection, `xi`, captures, provider incidences and retained joint
evidence, with a joint EnvStore/JointWF realization. Round-3 supplies extension
discipline but not this lift; source-contracts §3.3 enumerates admission forms
but does not construct it. Compiler-referee and spec-auditor reviews passed the
research-only correction. Option 2, all compatible contexts and every prior
status remain unchanged. See the [C5/C6 parameterization correction](../notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md#parameterization-correction-independent-demands-and-event-witnesses).

Complementary attacks on CALL_TYPE, ORIGINAL_ASSOC P2, INIT_WORLD/REC_DESC,
and ALL_VIEW/PRINCIPAL found no discharged node. P2 still lacks original typed
slot/contribution/owner-view introduction at one `xi` and scope. INIT_WORLD
still lacks zero-step independent-import/root extension. REC_DESC still lacks
ordinary captured-Name descriptor introduction with independent guards/world
validity. PRINCIPAL's actual `Direct(B_common,...)` rule still requires its
non-coverage interface after nonidentity `VIncl` and finite result-check
evidence are granted. Frozen Oracle archaeology found historical resolved-name,
call-upper, specialization and thunk environment/provider-map machinery, but no
semantic evidence for demand-world captured-binding adequacy or actual-provider
compatibility; Oracle remains archaeology only. The shadow identity crosswalk
already joins Apply/operand identities, all eight endpoint labels and solver
premises, so no additional identity-only slice was justified.

The approved exact singleton recursive-self-init execution boundary remains
closed as a source theorem, but production pre-execution enforcement is absent:
the only recognizer is default-off shadow evidence, and this workspace has no
initializer execution acceptance entrypoint. Its approved receipt prohibits
production routing/cutover at this stage; do not reject in inference or parsing.
No status changed, no semantic clause was proven, and no tests/builds ran. The
only substantive research artifact change is the reviewed, non-authoritative
C5/C6 correction, synchronized here without changing theorem status.

At the resulting `0756150ee0113f62f959dd69c28bd10795b1f1cd` baseline, a second
constructor-by-constructor CALL_TYPE pass separated demand indexing from event
recording, semantic EnvStore/JointWF realization, and local Val/DescMem typing.
Init/Response/Resume/FutureUse inputs provide occurrence or handle identity;
none constructs the total coherent `Theta` family. One already jointly typed
initial event admits identity reuse conditionally, but supplies no later-world
or all-context theorem. Round-3 assumes the retained coherent extensions and
CI-Operands/CI-ArgFrame; it does not derive them.

The matching INIT_WORLD inversion distinguishes premise levels. If an open
`Delta_i` certificate is already supplied at the actual importer incidence and
`C0`, the remaining first leaf is joint root-extension introduction with old-
tuple restriction:

```text
independent external base at original (B_orig,xi,C0)
open Delta_i at importer incidence, both hypothetical hole interfaces,
  licensed provider/dependency maps, joint overlap and source-owned open roots
-------------------------------------------------------------------------- ?
joint EnvStore/JointWF root introduction at the importer;
restriction recovers every old external incidence; holes remain hypothetical
```

If the grant is only exporter/external validity, importer installation is
earlier. PCInit-source derives the open source-owned schema conditionally on
these import/world leaves, but cannot install an opaque Option-2 import or
manufacture the independent EnvStore/JointWF root. Neither version yields a
source counterexample or status change. A conditional identity extension works
only when the exact initial filling already has the joint world and local
typing at `C0`; it does not provide the admission constructor or later demand
transport. Response, raw-resume and future-use cases additionally need
prefix-preserving current-world extensions, same-operation/handle/provider
incidence, and activation expiry. This was a bounded producer rule audit; no
independent closure review or semantic status change is claimed.

Targeted Frozen Oracle archaeology of signature-local P2 construction found
correlated polarized Function ports, formal-owned effect-marker rows and
receiver endpoints, but no joint original slot/contribution/owner-view
certificate. In the inspected `ArgEffectContractMarker` sidecar, argument- and
return-effect ports at the same path/depth collapse to the same marker; the
complete annotation/type AST may retain their distinction, so this is not a
whole-compiler information-loss claim. Historical sharing and allocation IDs
do not supply typed `p0`, a Call occurrence, original `xi`/scope or complete
family coverage. P2 remains OPEN-SEMANTIC. These attacks were bounded producer
audits, not independent closure reviews; no DAG node or authority changed.

## Current-pipeline shadow differential (2026-10-07)

At current remote baseline `e8ec553d5ea3e6c3dc02e44523460f5dcb32fa65`, a
reviewed focused differential now compares independently ordinary-lowered /
solved HIR with source-identity-lowered HIR solved with fresh-row capture. It
alpha-compares every current finalized root scheme, including public/our/private
receiving aliases, and covers generic Q inventory, recursive R bounds,
unproductive recursion, and integer aliases. Occurrence registration and
per-artifact projections are also checked without transporting IDs across
artifacts. This establishes current-inference instrumentation
noninterference for these fixtures only. It does not establish old-infer parity,
successor export, Apply typing, use-time transport, soundness, principality or
source adequacy. See the [shadow current-pipeline differential](../notes/progress/2026-10-07-shadow-current-pipeline-noninterference.md).

The focused test passed and the change received independent compiler-referee
review with no findings. Canonical DAG counts remain 90 nodes / 196 edges: 7
CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC, and 1
IMPLEMENTATION-ONLY. The next implementation slice requires a source-derived
successor construction judgment; current Q/R capture and endpoint parity do
not establish eligible coordinates, fixed imports, complete shared-contract
transport, or actual export evidence.

## Experimental closed-scheme transport bridge (2026-10-07)

The test-only [intrusion transport model](../crates/yu-solver/src/tests/intrusion_transport.rs)
now exports a bounded real `ClosedValueSchemeView` into its finite graph model,
retaining view-qualified Q/R identities, reachable constructor sharing, all
four Function ports, and ordered recursive-bound associations. It rejects
unsupported Union/Intersection and over-limit graphs without publishing a
partial graph. Three focused tests exercise a real solved identity scheme,
unsupported-constructor rejection, and recursive-reference transport. The
local-vs-anchor partition remains explicit experimental input; current Q/R
membership does not establish successor eligibility. Empty provenance and
opaque negative-effect encoding remain representation limits. This executable
slice does not close a semantic DAG node or establish successor adequacy,
evidence validity, soundness, principality, or production cutover.

The focused command `RUSTC_WRAPPER= cargo test -j 1 -p yu-solver scheme_export -- --nocapture`
passed all three new tests. An independent compiler-referee delta review found
no issues within the test-only boundary. The DAG checker passes unchanged at
90 nodes / 196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19
OPEN-SEMANTIC, and 1 IMPLEMENTATION-ONLY. The next result must be a gate
closure, adoptable semantic clause, or further executable implementation; do
not add localization-only research notes.

The follow-on test `retained_source_use_captures_supply_receiver_namespaces_for_exported_transport`
now joins two actual retained SCC uses to their exact shared current scheme,
exports that scheme, associates both complete captured Q inventories with the
export sidecar, and runs parent plus per-use overlays. Historical rows are
represented by opaque tokens derived from `FreshRowRef::same_identity`; no raw
row ordinal or successor binder identity is inferred. The source-exported
graph and overlays pass the independent substitution reference and freshness
checks. Both successor correspondence/transport premises remain unresolved,
and the all-local partition is still an explicit experimental premise. This
fixture exercises Q but not an R-bearing incoming use. Compiler-referee review
found no issues. No semantic DAG status changed.

## O0 reviewed clause candidate (2026-10-07)

The existing [O0 minimal-clause record](../notes/progress/2026-10-07-original-call-output-minimal-clause.md#7-candidate-two-head-original-formation-clause)
now contains a concrete two-head candidate: `OSig-Demand` forms the immediate
complete-invocation position for the actual dependent `U_c`; `OC-CallEff`
must consume exactly `rho_c = demand(e_c)` and `q_c = inv_eff(rho_c)`. A
compiler-referee caught the prior arbitrary-position defect (which admitted a
latent result-effect position); the repaired clause received clean
compiler-referee and spec-auditor delta reviews, and the architect classed it
as an unadopted formalization of the approved direction, not a demonstrated
new observable choice. Original constructor typing, realization, substitution
coherence and conservativity remain unproved, so O0 and `ORIGINAL_ASSOC` stay
open. The next attack is on those proofs against the fixed clause, not another
description of the missing head. The canonical DAG remains 90 nodes / 196
edges with counts 7 / 20 / 43 / 19 / 1 for CLOSED / CONDITIONAL-CLOSED /
OPEN-PROOF / OPEN-SEMANTIC / IMPLEMENTATION-ONLY.

## Default-off shadow Apply value lane (2026-10-08)

An opt-in `yu-solver` feature now builds a bounded Apply candidate through the
existing solver worklist, SCC generalization, ordinary incoming-use freshening,
and closed-scheme export. It supports only simple integer/name/group/apply
initializers and one-parameter lambdas with supported retained HIR bodies;
recursive definition SCCs and other unsupported shapes return no candidate.
The reviewed [parameter-body extension](../notes/progress/2026-10-08-shadow-apply-parameter-candidate.md)
now admits retained HIR Integer/own-Parameter/module-Name/Group/Apply bodies.
Deferred recipes use actual startup parameter rows and ordinary incoming
freshening. A session-fixed candidate-only generalizer experiment preserves
polarized own-row references through existing incidence-aware summaries;
ordinary production expansion remains unchanged. The initial global prototype
failed unchanged normative recursion and was rejected. The underlying
production generic-chain defect and guarded-cycle forwarding judgment remain
open; this executable experiment does not claim their repair.

Each Apply and export carries explicit unresolved semantic premises, including
source typing/admission, complete invocation/effect formation, whole-provider
compatibility, role/protection, and successor generalization correspondence.
the candidate own-row/R/generalization model. Acyclic definition SCCs do not
exclude recursive types such as `x x`. Retained expression depth above 128 is
rejected before recursive candidate emission; no total solver-cost bound follows.
Candidate conflicts are not source rejection. The feature is default-off and
does not alter ordinary collection or production results.

Latest focused feature-on tests passed 12/12; internal candidate tests 6/6,
ordinary source-function tests 7/7, five exact memo/raw/one-sided tests 1/1 each,
and feature-off production-refusal differential 1/1. Tests compare ordinary refusal diagnostics, stable production
traversal/definition/fact counters, facts/provenance and exported schemes around
the candidate call, including parameter/group bodies; ordinary schemes are
unchanged. Latest compiler-referee and performance-auditor reviews found no
blocking issue in this bounded executable experiment. The regression test is
same-binary noninterference evidence, not a cross-feature equivalence claim.
This executable implementation
advances HIR_WIRING only; it closes no proof or semantic gate. The canonical
DAG remains 90 nodes / 196 edges: 7 CLOSED, 21 CONDITIONAL-CLOSED, 43
OPEN-PROOF, 18 OPEN-SEMANTIC, and 1 IMPLEMENTATION-ONLY. No performance measurements were
run. `cargo check -p yu-solver --all-targets --features shadow-apply-candidate
-j 2 --offline` passed at this phase boundary. Production cutover remains blocked by the existing semantic and
conformance obligations.

A focused production-entrypoint audit confirms that F5 replacement alone
cannot enable application typing: ordinary `lower_module` uses default HIR
options, `lower_simple_chain` rejects an Apply tail before literal children
reach collection, and `ConstraintBatch::collect` calls `collect_mode(...,
false)`. The supported shadow path is separate and explicitly retains
`UnsupportedExpression`; its solver candidate uses `collect_mode(..., true)`.
Thus the required cutover sequence includes ordinary source/HIR Call
construction and typed argument/result origins before the replacement solver
can consume them. This audit used source locators only; it ran no checks.

The focused code-path locator sharpens that boundary: [`yu-hir` lowering](../crates/yu-hir/src/module.rs)
turns ordinary Apply into an HIR `ResolvedExpr::Error`; the [`yu-solver`
collector](../crates/yu-solver/src/lib.rs) emits no Call/operand components,
and `emit_lambda`'s fallback returns without a recipe. The existing regression
for `my invoke f = f 1` requires that refusal. Shadow HIR retains structural
Apply identity only; its value candidate remains default-off and explicitly
unresolved. Selected theoretical source-interface/complete-contribution
constructors require the authentic full original witness and ownership
accounting, while granting no production cutover authority. This check ran no
tests/builds and did not inspect legacy F5 implementation history. Hence the
immediate missing implementation seam is ordinary source/HIR Call formation
with typed argument/result origins; solver replacement alone cannot satisfy
the objective.

A parser-to-HIR map refines this: `my invoke f = f 1` already parses without
syntax errors as a structural `MlArgument` tail, and shadow source joins retain
the exact callee and integer occurrences. Ordinary `lower_simple_chain`
rejects the associated two-child expression before operand resolution; the
existing shadow constructor reuses the same source evidence and local-first
parameter resolution but keeps `UnsupportedExpression`. HIR containment is
through Lambda/Apply child fields; occurrence IDs alone do not encode parent
ownership. The exact semantic HIR seam is body lowering/classification, not
parser acceptance or identity creation. Authoritative F5 explicitly excludes
expression application typing, and the production Apply design remains Draft
without implementation authority. Thus this objective extends the approved
F5 source envelope and needs a reviewed semantic successor plus its existing
approval gate before ordinary Apply typing can be enabled. The map used only
source/test inspection; no tests/builds ran.

That scope expansion does not mean every call rule is undecided. The approved
[Function-call view](../questions/2026-10-05-function-call-view-formation/approved-answer.md)
selects call roles, protection and independent admission boundaries; the
conditional [initial-context generator](../notes/progress/2026-10-06-initial-context-source-construction.md)
§4.4 and [typed-core synthesis](../notes/design/2026-10-02-typed-computation-core-elaboration.md)
already give a relative Application recipe (`WF_Dec`, `VIncl`, whole-argument
compatibility, `ReceiveSchema`, complete-result inclusion, and a computation
result). They do not enumerate or install the exhaustive original emitted
family. The successor work should retain these approved/conditional call
meanings while supplying original occurrence ownership, actual source
attachment and the ordinary HIR correspondence; it must not replace the
missing owner proof with a weaker endpoint-only constraint.

A bounded field-to-owner crosswalk for a corrected Name-only candidate shape
`my id x = x; my wrap y = id y` is now in
[the unary Name Call boundary candidate](../notes/theory/2026-10-09-unary-name-application-boundary-candidate.md).
Both `compiler_referee` and `spec_auditor` found no findings at the reviewed
hash recorded in that file. The first proposed spelling `my use y = ...` was
rejected by parser dispatch as a `UseDeclaration`; the corrected `wrap` form
was not executed or established as a successful typed source case. This
candidate remains non-authoritative: q1/d1 covers formal Name/Int, not
module-root Name/local-parameter Name. A conditional derivation in
[`wrap Name carrier derivation and complete Call cut`](../notes/progress/2026-10-09-wrap-name-call-typed-consumer-cut.md)
shows how selected clauses could construct the same-origin Name argument and
native inlet, given a completed post-entry `y` certificate and independently
authentic `id` frame; this is not source acceptance. The first unresolved
complete Call premise is Theorem IF's typed `IF_c` (complete primitive/root
interfaces and lawful whole-map actions), followed by typed `M_E` and the same-
incidence decorated certificate. No implementation, gate closure or cutover
authority follows.

The [guarded-cycle assignment attack](../notes/theory/2026-10-08-candidate-own-row-guarded-cycle-attack.md)
and the finite [acyclic forwarding experiment](../notes/theory/2026-10-08-candidate-own-row-acyclic-model.md)
(with [checker](../tools/research_candidate_own_row_acyclic.py)) exercise
own-row retention, owner identity, repeated ports, and direct-bound preservation
under explicit small powerset interpretations. The acyclic probe checked 2,880
models and found a concrete counterexample when forwarding bounds are dropped
despite retaining own rows; independent review verified its stated finite
claims. A source/code bridge now proves a bounded forward assignment transport
through actual bipolar Q selection, shared substitution, normalization,
finalization and closed representation for the successful acyclic
`PureFun(a,c)` / `a≤b≤c` fragment. This is conditional on the stated lattice
model and quantifiable rows; arbitrary exported Q assignments do not retain
those direct edges. The exact semantic leaf is actual closed-Q adequacy plus
incoming-use restoration and converse coverage, so no broad generalization or
production repair follows. The guarded-cycle probe checked 1,188 graphs and
satisfying assignments including Function-port reentry; review confirmed its
conditional boundary and an output label was clarified. These results do not
select recursive R semantics or soundness/principality, and no canonical DAG
status changed. The acyclic proof/checker and guarded-cycle experiment passed
independent compiler-referee reviews; the acyclic note's polarity locator was
corrected to the walker dispatch.

The symbolic captured-Call generator now also accepts an exact retained
declaration position and projects through that declaration's existing
`declaration_skeleton`, while the original singleton entrypoint keeps its
singleton guard and behavior. One multi-binding fixture joins the selected
captured Call record to the same source/HIR/candidate identities, a sibling
module-name use, its actual current Q/R freshening inventory and receiving
export. These are same-solve identity/value projections only; every original
typing, source-base membership, invocation, scope, tuple-substitution and
successor-correspondence premise remains unresolved. The feature-gated
call-formation crosswalk target passes 3/3 and the existing shadow-Apply
feature target passes 19/19. Independent regression review accepted the
selector and same-solve call/use/export joins. Since current projection rejects
an annotation on the captured block itself, a sibling-annotation fixture
asserts the selected declaration still has a captured Call input before
checking the artifact-global annotation guard's fail-closed result. Delta
review accepted this isolated guard check without semantic claim. No DAG status
or production route changed.

The latest CALL_TYPE constructor attack also corrects an earlier blanket
description of the source-base route: source-contracts §3.5 does translate a
genuine finite source-core derivation to `M_E`, but only under its finite
source-base emission-conformance certificate. The selected structural
Name/Name result theorem still consumes an already supplied `M_E` witness.
The current shadow `CandidateRelation::Apply` and symbolic identity record do
not provide the complete emitted Call clause, its original joint witness, or
the initial source/descriptor evidence needed to instantiate that certificate.
CALL_TYPE remains CONDITIONAL-CLOSED, its DAG prerequisites/status are
unchanged, and no source counterexample or semantic contradiction was found.
The default-off shadow record now carries a borrowed `PendingSourceBaseStub`
with the exact Call, callee-use and argument-use identities, plus explicit
unresolved entries for the complete emitted Call clause/joint witness, initial
source/descriptor relation, finite emission-conformance certificate and full
invocation interpretation. This is evidence plumbing only: it creates no
semantic witness and cannot authorize solver comparison. The focused core and
crosswalk targets pass 3/3 each, and the independent regression delta review
accepted the repaired ten-premise core assertion. The next attack remains to
derive the actual emitted Call clause and its witness-preserving source-base
correspondence from source generation. The default-off candidate differential
now also records `my id x = x; my n = id 1; pub exported = n`: candidate
emission observes `Int` while ordinary current inference projects the call
root as `Never`, with different exported schemes. Candidate typing/admission
premises remain unresolved, so this is a measured inference delta rather than
a claim that the candidate result is semantically correct.

The default-off source-call projection now also retains owned clones of the
branded Call, direct callee-use, argument-expression and optional direct
argument-use IDs for each `source_call_use_inputs` occurrence in an exact
declaration. Cloning preserves artifact identity; the generator remains
partial for grouped/computed callees and rejects any artifact with retained
annotations. Tests assert both successful identity joins and the grouped /
computed / annotation boundaries; the focused `yu-core` target passes 5/5 and
the candidate crosswalk target passes 5/5. `CandidateSourceCall` now has a
test-wired structural matcher for this carrier; tests join each exact source
call to its same-solve candidate observation and reject another Call and
identical source parsed into a foreign artifact. The ordinary-Apply case also
compares the candidate's exported endpoints while retaining all
candidate/export and source-base unresolved premises.
This remains source identity
bookkeeping only; the four source-base semantic premises stay unresolved and
the canonical DAG statuses remain unchanged. Independent regression review
accepted the implementation and crosswalk; the minor grouped/computed/annotation
coverage finding, positive ordinary-Apply join, and negative crosswalk cases
passed delta review.

The nested-call crosswalk fixture now also checks the full HIR inventory → Core
pending source-call carriers → same-solve candidate path for both retained
Apply occurrences. Exact HIR occurrence, callee and argument identities,
retained HIR errors, root ownership, and all four unresolved source-base
premises are checked for each call. Its source crosswalk also carries the
exact root's same-solve exported scheme and preserves the unresolved candidate
premises. The focused solver crosswalk target passes 5/5. This extends
executable identity plumbing through the nested Apply export projection; it
does not establish source typing, emission conformance, invocation
interpretation, or semantic acceptance, and no canonical DAG status changes.
Independent regression review and its delta review passed for this nested
crosswalk addition.

The opt-in Core shadow lane now also exposes a borrowed annotation-boundary
inventory for an exact retained `BindingStatement`. It follows source parent
identity, preserves both `PatternTypeAnnotation` and `TypeAnnotationTail`,
separates sibling declarations, and lets nested binding boundaries be queried
directly. It retains the existing pending typed-port/profile marker and adds no
typing, applicability, permission, or call-view meaning. Its three focused
tests pass; independent regression review found no blocking or major issue.

The partial source-call generators now apply that same retained ancestry rule
to the exact selected declaration: a sibling annotation no longer suppresses
an unrelated declaration's structural inventory, while annotations inside
the selected declaration still fail closed. Boundary lookup errors remain
fail-closed, all semantic premises remain unresolved, and grouped/computed
callee behavior is unchanged. The focused `shadow_call_formation` target
passes 6/6, the focused candidate crosswalk passes 5/5, the annotation-boundary
target passes 3/3, and `yu-core` checks with default features disabled.
Independent pre-write spec review and post-write regression delta review both
passed. This is a default-off identity-plumbing correction only and changes
no DAG status.

Against the latest remote constructor proof, a separate compiler-referee
review closes the exact captured-Name `g` readout for the selected native
registered root: the source Name targets that root, O-pair constructs its
value and installed-world certificates simultaneously, and the actual entry
extension/capture projection derives the same-scope `ValueMem` without a
completed member/world premise. This does not identify the historical proposed
`R_g` endpoint with the registered root or prove a fixed-original/foreign
meaning, so aggregate `REC_DESC` remains OPEN-PROOF and no DAG status changes.
The synchronized canonical REC_DESC leaf now records the selected native
two-closure constructor while retaining fixed/foreign original meanings,
exhaustive CompleteMem/KV, and broader recursive cases as independent premises.

The latest native signature theorem already supplies exhaustive native
ATTACH/LIC_FORWARD formation and inversion; no additional canonical node
closes. The residual is the fixed-consumer bridge, first at DeclaredPort:
constructing `PortProv` and `DeclContribution` does not yield an original
`e∈E_C(beta)` or factorization through an authentic upper Call. This is not a
source counterexample. LIC_FORWARD for a fixed consumer additionally needs
`Attach_M → A_N` and `L_N → Lic_M` over that consumer's real indices and scope;
those maps do not follow for arbitrary fixed interpretations.

The selected captured-closure constructors also yield a reviewed conditional
receiver-admission result for a checked Apply demand that explicitly retains
the argument's complete `Result(I_argument)` interface and matching `Strict`
view. At one fixed original tuple/event, independent carrier membership,
context/receipt guards, and same-tuple callee membership then introduce the
complete challenge and derive actual-provider acceptance plus all receiver
observations in that same scope. This removes a redundant post-admission
reconstruction premise, but does not form `Strict` from arbitrary `f x`,
identify the candidate four-port recipe with that view, or close `CALL_TYPE`.
The exact source producer still needs a pre-comparison `DemandFormation` link
from the typed argument interface to the declared inlet and entry/role.

The default-off Call-use crosswalk now also observes the exact retained
candidate Apply fact from the same private solver result. It retains Apply
recipe occurrence identities before batch consumption, then joins the exact
`CandidateCall` to its unique slot-zero provenance edge and stored fact;
missing or ambiguous links fail closed. The source Call/Core/HIR identity,
callee Name use, receiving export and actual freshening route remain joined,
and every semantic premise remains unresolved. The focused crosswalk target
passes 6/6, and two focused solver unit tests cover copied/foreign calls plus
six isolated missing/ambiguous recipe, provenance and fact cases. Independent
regression review passed after that repair. A grouped-source collision fixture
remains inspection-only because the supported HIR fixture does not retain a
Group node and candidate solving rejects it; the constructor still filters
the exact Apply recipe occurrence before consulting slot zero. No semantic DAG
status changes; the 90-node / 196-edge canonical ledger remains 7 CLOSED,
21 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 18 OPEN-SEMANTIC, and 1
IMPLEMENTATION-ONLY, and its validator passes.

## Preserved history and next integration steps

### Superseded checkpoint: transformed `id` export research (2026-10-08)

This block records the earlier pre-construction checkpoint at `c436dd58c`.
Its “neither result law is selected” and next-discriminator wording is
superseded by the independently reviewed native PE-ID/PE-PICK construction
selected at current HEAD; see “Completed native transformed projection export”
above and the linked design/theorem there. The older conditional analyses
remain historical evidence only.

The q1/a1 approval selects a displayable transformed scheme plus only the
use-time information shown necessary; it does not approve a concrete decoder
or implementation. Reviewed research checkpoints now cover the finite
`Sigma = forall q. q -> q` export candidate and its source/actual-root query
suppliers: [projection construction](../notes/theory/2026-10-08-projection-lambda-export-construction.md),
[descriptor source bridge](../notes/theory/2026-10-08-id-descriptor-source-bridge.md),
[ordinary-arrow candidate](../notes/theory/2026-10-08-id-arrow-decoder-candidate.md),
[conditional result discriminator](../notes/theory/2026-10-08-id-result-clause-discriminator.md),
and their paired falsification notes. The independent reviews found the
conditional claims sound after requiring bidirectional guard/grammar pairing
for equality and distinguishing a base-clause difference from a complete
Option 2 observation difference.

No source-admitted unequal-provider license or observation has been shown.
The logical saturation countermodel proves only that `W/Z/G` can erase a
base-predicate difference. Next, construct or exclude one independently
licensed off-diagonal provider package under a fixed complete interface and
caller, prove its complete admission and survival outside the diagonal
`W/Z/G` closure, then show a separating actual-root query after projection.
Until those suppliers exist, neither result law is selected and no user choice
is needed. Keep `GENERALIZE`, `PROJECTION`, `PRINCIPAL`, production
conformance and `CUTOVER` open; no compiler code, test contract, or DAG status
changes follow from these checkpoints.

At local checkpoint `c436dd58c`, `research/simple-sub-intrusion` is eight
commits ahead and one behind its upstream. The upstream-only source-Generalize
commit `2ea53e3dd` remains unintegrated; nine shared coordination paths have
uncommitted edits; several overlap its integration seam. No push was made. The
research artifacts were committed in three scoped commits: `3d081345f`,
`f416d14cb`, and `c436dd58c`. No tests or builds were run.

## Preserved history and next integration steps

Historical reset record: at an earlier 2026-10-08 check, HEAD was
`9e36c9537edfbde3048af2963abbf10f32477d5e` after a reset to the remote branch;
the incoming files were restored individually and no blanket reset/clean was
used. The then-current claim that `.git` was read-only is superseded by the
successful scoped commits below.

Current Git state at `1b54274fb`: branch `research/simple-sub-intrusion` is
synced with `origin/research/simple-sub-intrusion` (0 ahead / 0 behind). Recent
pushed checkpoints are `ab5bc6e31` (CallInitial prefix analysis), `97d8e1ba6`
(conditional Bind initial bridge), `91a75709f` (exact shadow Apply fact), and
`1b54274fb` (reviewed I0 telescope boundary). Nine shared paths remain modified
in the worktree: the successor architecture/index/progress/theory handoff,
theory map and obligation ledger/generator, plus this task file. The live ledger
delta changes INIT_VALID's selected-result references, so use committed `1b54274fb`
as the authority until that shared-record delta is reconciled. No question-board
bundle is part of this work.

- [Original pre-correction ledger](2026-10-06-current-before-directional-protection.md), unchanged.
- [Task snapshot before this normalization](2026-10-07-current-before-full-dag-normalization.md).
- [Previous dependency map](../notes/theory/2026-10-07-inference-theorem-dependencies-before-full-dag.md).
- [Previous theory map](../notes/theory/2026-10-07-inference-theory-map-before-full-dag.md).

Historical open wording is retired where the canonical ledger names a later
closed theorem. These archives are evidence/navigation, not parallel active
TODO lists. Check newly advancing remote commits for semantic dependencies,
keep exact file leases and one Git/build owner, run the focused checkers/tests,
repair independent major findings, synchronize these records, commit and push
`origin research/simple-sub-intrusion` without force.

## Ordinary Application source-presentation candidate (2026-10-08)

The bounded candidate at
[`ordinary-application-source-presentation-candidate`](../notes/theory/2026-10-08-ordinary-application-source-presentation-candidate.md)
was checkpointed and pushed as `cadbd5b26` before shared-record synchronization.
Its SHA-256 is
`cbcfc770820cde081c80e3c678b21e23ce941581edf7c17505e411f2157fc766`. Independent
compiler-referee and spec-auditor reviews both pass within its explicitly
conditional, non-authoritative scope; neither approves adoption or
implementation. They confirm that the five-head initial-context reference,
the separate source-call certificate, and the direct-Int decision are reported
without claiming exhaustive original ownership, primitive/certificate
inventory, installation, or production correspondence. No implementation,
tests, builds, or DAG status changes follow.

Next, continue from the source owner to supply the authentic Application
occurrence/owner production and complete primitive/certificate inventory,
including installation/membership, attachment inversion, old-family
preservation, whole actions, and exact consumer applicability. Keep Gate E and
production implementation open until the concrete successor presentation is
complete, independently reviewed, and explicitly approved. The latest
checkpoint is synchronized with `origin/research/simple-sub-intrusion`; keep
substantial coherent slices committed and pushed promptly so external work
continues from a current branch tip.

## Flat Application source-owner residual (2026-10-08)

Two separate, non-authoritative source audits are now checkpointed and pushed:
[literal relation boundary](../notes/theory/2026-10-08-flat-apply-literal-relation-tree-audit.md)
(`5b76b2cb7`) and [Application owner inventory](../notes/theory/2026-10-08-flat-apply-owner-inventory-gap-audit.md)
(`accb579b0`). The literal audit isolates a bare `literal(1)` residual: the
selected direct-Int decision and typed-core clauses fix `Value(Int)` and the
Result/Return skeleton, while the complete primitive occurrence/alternative
relation and its lawful action remain an imported input. The owner audit
confirms that selected source-interface formation and inversion consume an
actual emitted Application/Gen-Call-0 inventory, authentic complete operation,
and independently typed primitive contracts/actions; they do not construct
that upstream inventory. `ReceiveSchema`, `TypedCallCert_Dec`, the primitive
relation, and Call-owned Result/Reify attachments remain separate inputs.
Both notes are unreviewed bounded research; no test/build, implementation,
authority promotion, or DAG status change occurred.

The next source artifact must supply the authentic flat Application owner
production, including complete occurrence/alternative inversion and typed
attachments, actual installation/member lookup, old-family preservation and a
lawful whole action. It must explicitly state whether a primitive relation is
an opaque complete contract or expose its own finite occurrence tree; it may
not get exhaustiveness by unioning downstream reference lists. Keep admission,
CallInitial/I0, transformed export, principality and production cutover open.

The conditional [owner declaration gap](../notes/theory/2026-10-08-flat-apply-original-owner-schema-candidate.md)
is now checkpointed and pushed as `2f86ea24e`. Its SHA-256 is
`e0cca3ba30798a04c14a3d7e3ea003d3309063e05fa6b75eab2ed5300da33eb3`. Independent
compiler-referee and spec-auditor reviews pass within the note's bounded
research claims. They confirm the exact stop at a complete Application owner
declaration plus authentic installation/inversion; they do not certify an
exhaustive source inventory or authorize adoption. The note also records that
an opaque primitive is a valid route only when its whole contract, licensing,
evidence and action are retained. Finite internal expansion is not a
prerequisite by itself. The next artifact is still to complete and review that
owner package; flat seed, CallInitial/I0 and later gates remain independent.
No tests, builds, implementation or DAG status changes occurred. The latest
checkpoint is synchronized with `origin/research/simple-sub-intrusion`.

A fresh bounded owner-family proposal is checkpointed and pushed as
`426135a17`: [flat Application owner completion](../notes/theory/2026-10-08-flat-application-owner-completion-decision-object.md).
It supplies candidate constructors for the Name/Int literal, opaque complete
contracts, registration, installation/lookup/inversion, old-family
inclusion/retraction and consumer seams. This is a new proposed definition,
not a claim about the independently fixed historical family. The frozen note
is non-authoritative and passed independent compiler-referee and spec-auditor
review within its stated scope. Adoption, exact correspondence if required,
flat seed, CallInitial/I0,
admission, solving/export/principality and Gate E remain open. No tests, builds,
implementation or DAG status changes occurred. The proposal checkpoint is
synchronized with `origin/research/simple-sub-intrusion`.

Both assigned reviews now pass for the proposal's stated fresh-family,
conditional scope. The compiler-referee found no blocking, major or minor defect;
the spec-auditor found no conformance issue. Primary adjudication retains one
future realization obligation: the proposal's `R_a = Comp(empty, Int)` must be
identified against the kernel's exact Return image `J_a` before claiming
original consumer realization. This is not a defect in the proposed grammar,
and the note leaves natural applicability/open realization work unresolved;
do not silently treat the bridge as identity. The reviews do not establish
historical-original correspondence, adoption, or downstream gate closure.

Question q1 selected `Application_N` as the successor definition for this
bounded Name/Int literal Application seam (approved d1; integrated in
`44526fd7f`, receipt at
`questions/2026-10-08-flat-application-owner-family/receipt.md`). This
selection is recorded against proposal SHA-256
`61d5fd8e3a359c9ad7fce203ee7927553964b4eeae4a923319aca49a846f826a`; the
proposal's frozen header remains historical provenance. No historical-family
equivalence, implementation, cutover or Oracle-visible change is authorized.
Exact literal Return-image realization, SeedExposure, CallInitial/I0,
admission, solving, generalization/export, principality and Gate E remain open.

The bounded Return construction and falsification packet is now pushed as
`574768eda`. Independent `spec_auditor` and `compiler_referee` reviews passed
within their assigned scopes. The construction derives only the conditional
`J_a^N` Return image and identifies `H_arg_origin` as the first selected-original
consumer cut; the falsification lane found no legal fixed-path source witness
and does not turn a missing bridge into a negative typing result. A separate
read-only regression audit confirms that default HIR retains literal spelling
and occurrence, while default solver recipes/projections classify Int/empty
effect without a Result/Return certificate. Qualify that carefully: aggregate
`SolvedModule` retains its HIR, so source spelling remains recoverable there.
Test-only Result traces and feature-gated shadow rows are not default
production evidence. No compiler implementation, tests/builds, semantic
promotion or F5 cutover occurred. Next: obtain the independently declared
`WholeArgCompatible` origin signature and typed map for this literal Result
occurrence, preserving its dependent indices, witnesses, licenses and future
evidence; then review that bridge before claiming original-consumer
realization. The full q1 scope and all later gates remain open.

## Current F5 implementation locator audit (2026-10-08)

Read-only mapping at `15e83939a` confirms production still enters through
`yu-hir::lower_module` → `ConstraintBatch::collect` → `SolvedModule::solve` →
private `InferenceSession`; Apply typing is not present in this production
route. F5 runs inside the SCC lifecycle: member drafts call
`component_generalization_draft` and `F5cGeneralizer`, then component
normalization/finalization publishes `ClosedValueScheme`s before fresh
incoming Q/R instantiation. `SolvedModule` stores and projects those closed
schemes. Replacing only `F5cGeneralizer` would leave the surrounding
representation lifecycle in place.

Current F5 path locators: `crates/yu-solver/src/lib.rs` (`collect` 855,
`InferenceSession` 7419, `solve` 16027, `execute_scc_plan_inner` 13135,
generalization draft 15475, finalization 15505, incoming route 15162, `finish`
15740); `crates/yu-solver/src/f5c_generalization.rs`; and
`crates/yu-solver/src/f5c_normalization.rs`. The flat candidate branch and
`intrusion_transport` remain `#[cfg(test)]`. `shadow_apply` calls the existing
F5 solver and returns a private experimental result, so it is not a production
successor. These code locators agree with the existing Gate E blocker; no
production implementation or cutover authority follows. Read-only inspection
only; no tests, builds, or probes. The smallest coherent replacement seam is
component interface construction, durable member/root publication,
incoming-use transport, and frozen-result consumers together.

## F5 frozen-consumer and publication boundary (read-only, 2026-10-08)

A second bounded audit confirms there is no ordinary workspace result consumer
outside `yu-solver`, but expands the frozen-consumer inventory beyond root and
occurrence projections. The public `SolvedModule` also exposes structured
`ConstraintStore` evidence, diagnostics, counters, and feature-gated observation
APIs. Shadow initialization and SCC APIs join results by the exact collection
brand; shadow Apply consumes F5 schemes, fresh captures, store and provenance.
These are frozen integration surfaces, not additional production inference
owners.

The replacement lifecycle must account for six interfaces: component
input/freeze and member-interface output; durable member/root identity and
storage; internal and incoming-use transport with transactional fact,
provenance and diagnostic ownership; consuming solve completion and atomic
result publication; both occurrence and root projection paths; and retained
evidence plus an explicit disposition for feature-gated F5 endpoint/Q/R
observations. `yu-types` `ClosedTypeFinalizationSession` owns per-scheme
validation/rollback, while `InferenceSession` owns SCC/module installation and
publication. These are separate transaction boundaries. Public projections
remain lossy (`SolvedValue`/`SolvedEffect` expose only bounded enums), whereas
retained store data is not.

The audit inspected failure/rollback witnesses and API/call sites but did not
execute them. Existing assertions cover all-member publication failure and a
clean fresh-attempt retry; public solve is a consuming attempt rather than a
resumable live session. No implementation, API change, test expectation,
approval or Gate E closure follows. The narrow successor design should include
this interface/consumer ledger and classify preserved behavior, deliberately
revised APIs and retired F5 observations before implementation approval.

## Flat literal argument realization residual

The scoped bridge audit found that `R_a = Comp(empty,Int)` is the literal's
computation interface, not equality with its exact source Return image `J_a`.
Source generation and original Call-input consumers retain the image and
require an actual `WholeArgCompatible-origin(J_a,...)`. This is an open typed
consumer realization for the proposal, not a malformed grammar or established
semantic conflict. Retain both indices and discharge the kernel-signature and
typed transport bridge before claiming original-consumer applicability. No
divergence counterexample or acceptance change was established. No tests,
builds, probes, or Git mutations occurred during this audit.

A bounded constructive follow-up establishes a one-way conditional realization
for the exact literal source image. Under independently supplied literal
`ValueMem_Int`, authentic Result/Reify registration and one shared world,
configuration and witness family, selected `Code-Result` constructs
`ReturnMem_Int` at each admitted compatible event. Administrative/zero-step
prefixes preserve that evidence, and the source-owned inert `Delay(Return(k))`
plus `Carrier-Delay` establishes `CarrierMem_R_a` for the literal carrier. This
is the literal case of the existing constructor route; it is neither
`J_a = R_a` nor an inverse.

The remaining owner is the Result/ArgDelay/Checks source construction plus the
independent `WholeArgCompatible` kernel signature and its exact origin map from
the installed literal occurrence to the original `J_a` consumer. That map must
transport whole dependent indices, scopes, world, primitive witnesses and
future evidence; adoption of the proposed owner and that correspondence remain
open. Treating image and interface as equal would lose behavior: a
terminating `Delay(Return(1))` and a divergent pure `Int` carrier can share
`Comp(empty,Int)`. This is a conditional producer derivation only; imported
literal/kernel premises were not independently validated, and no checker,
tests, builds or probes ran.

## F5 regression-contract inventory (read-only, 2026-10-08)

Inspection of `crates/yu-solver/src/lib.rs` tests and the shadow differential
fixture separates existing user-visible behavior from F5 representation
assertions. Preserve identity/constant-function inference, forward module-name
resolution, lexical parameter shadowing, function recursion, root identity,
error isolation/diagnostics, and atomic publication/rollback with clean retry.
`SolvedValue`/`SolvedEffect` intentionally project functions and open facts to
`Unknown`; this public projection is distinct from internal scheme detail.
Current unsupported Apply still yields the HIR diagnostic and byte range
`14..18` for `x(x)` in `crates/yu-solver/tests/shadow_f5_differential.rs`;
shadow collection is
separate and still solves through F5. Numeric binder ordinals, row counts,
fact/provenance counts, visits and capacity lanes are representation/resource
details unless a specific public diagnostic/API exposes them.

The strongest existing independent-use witness is synthetic and constructs
identity facts directly; it does not prove source-level polymorphic Apply.
This contract inventory is assertion inspection only: no tests were run, no
Oracle parity or successor correspondence is established, and existing
unsupported-Apply expectations must change only under the reviewed cutover
approval. Exact witnesses include
`f5d_identity_lambda_admits_exact_effect_and_function_facts`,
`f5d_constant_and_module_name_bodies_close_to_pure_functions`,
`f5d_parameter_alpha_rename_shadows_module_name_and_does_not_leak`, and
`f5d_productive_function_recursion_and_unproductive_names`; independent-use
and publication/retry witnesses are
`f5c_shared_closed_child_is_instantiated_once_per_use_with_disjoint_rows`,
`f5c_internal_route_failure_restores_and_retries_cleanly`, and
`f5c_incoming_union_representative_failure_has_no_public_route`.

## Flat Apply production source path (read-only, 2026-10-08)

The concrete target `my apply f = f 1` parses successfully: syntax gives `f 1`
as an `OperatorChain` containing `IdentifierExpression(f)` and an `MlArgument`
whose child is `IntegerLiteral(1)` (`crates/yu-syntax/src/expression/operator_chain.rs`).
Default production lowering does not preserve that Apply: `direct_atom` in
`crates/yu-hir/src/lib.rs` only accepts one direct integer or identifier,
`lower_simple_chain` therefore returns Unsupported, and HIR stores
`Lambda(body = Error)` with `UnsupportedExpression` over bytes `13..16`,
attached to `apply`. `ConstraintBatch::collect` marks it Error and `emit_lambda`
creates no `LambdaRecipe` or facts for the body. The whole body is rejected
before callee or argument uses are separately collected.

The opt-in shadow HIR retains a `ResolvedExpr::Apply` but still reports the HIR
error; `CandidateValueObservation` uses the separate shadow collector and
existing F5 solver. There is no workspace production CLI renderer for this
diagnostic. This source-path inventory is read-only and was not executed; no
new behavior, test expectation, or production support is implied by it.

## Record-result source-owner inventory (read-only, 2026-10-08)

The checkout has named-record type syntax, but no semantic Record expression or
value constructor in production HIR, `yu-types`' polarized values, solver terms,
or shadow HIR. `{ value: x }` is parsed through the braced-statement/colon
application route; because it has no direct atom, production lowering marks it
`UnsupportedExpression`, retains a Lambda wrapper for `my box x`, and emits no
`LambdaRecipe` for its Error body. This is not a Record inference owner; the
legacy record-field VM fixture is not current F5 or successor acceptance
evidence. The existing conditional Record-result proposal still needs both
H-R (actual Record formation/inversion with provider/world/field evidence) and
H-K (the complete ordinary Lambda root with licensed extras and actions).
No test or exact CLI-output probe was run, and no Record semantics or gate
status was selected.

## ScopedClosure production evidence bridge candidate (2026-10-08)

The frozen [production/source correspondence candidate](../notes/theory/2026-10-08-scoped-closure-production-evidence-bridge-candidate.md)
maps the selected native `ScopedClosure` fields to their current HIR,
collection, SCC, use-routing and result-publication owners. It identifies the
missing production suppliers as the complete source rule graph `N`, original
binder tree `T`, and actual invocation/initializer provider, world, event and
scope evidence. The smallest inspected construction-gap witness is
`my id x=x`: HIR and collection retain parameter/Name identity and use
linkage, but not the selected original scope tree, complete invocation record
or local-law evidence. The conditional walk does not infer source eligibility
from Q/R membership, IDs, row levels or successful solving.

An independent compiler-referee review found no issue within the bounded
candidate scope. It confirmed the identity witness and the distinction between
existing production linkage and the selected source evidence records. The
review did not establish repository-wide absence, L1–L5 validity, runtime or
public-projection correspondence, resource bounds, or production transaction
correctness. The candidate remains a non-authoritative research audit; no
implementation, source-family selection, test change or cutover follows.

Next evidence: specify the actual SourceBuild outputs for complete invocation,
scope and event evidence on `my id x=x`, tied to their owning source
constructors. Keep Gate E, FRESH_LIFE and production correspondence open; the
pending Application-owner question is independent of this bounded `id` work.
No tests, builds or probes ran for this review; the candidate's focused
document checks and dependency revalidation are recorded in the artifact.

## ReadInvoke source-rule schema review (2026-10-08)

The bounded [original local-rule schema proposal](../notes/theory/2026-10-08-readinvoke-original-rule-schema-proposal.md)
for the captured Name/Name Call has now received an independent
compiler-referee review with no finding. The review verified that the 15
families in §4 are obligations rather than a claimed complete kernel
signature; §5 derives only the supplied ordered Bind equations; and §6 leaves
the decorated prefix `P`, actual-receiver signature `V`, admission/development
signature `A`, and operator/action laws `G` unresolved. The smallest exposed
gap remains `P.CallInitial`; neither descriptor formation nor interface
incidence manufactures its missing source rule.

This review closes no source-rule theorem, fixed-`E` attachment, production
conformance or implementation gate. Next evidence must come from the owning
kernel's full `P.CallInitial` signature and witness action, or from an
explicitly approved new constructor presentation. Keep `V/A/G`, emission
installation and fixed-`E` attachment as separate obligations. No tests,
builds or probes ran; the review revalidated all 13 dependency hashes and the
primary confirmed the reviewed file hash matches committed `ecf18d9d8`.

## Concrete `id` SourceBuild instance (2026-10-08)

The frozen [identity SourceBuild instance](../notes/theory/2026-10-08-id-sourcebuild-instance-candidate.md)
instantiates the selected source package for `my id x=x` under explicit
H-source. It yields one eligible Parameter `Desc` at its original scope, a
fixed generic raw inlet, the complete latent invocation/event schema, one
joint `N_id`, and the final synthesis root. Its row-by-row ordinary HIR,
collection and F5 crosswalk finds parameter/Name identity, SCC topology,
recipe positions and shared argument/result endpoints, while leaving the
semantic source records and their scopes/evidence unsupplied by current
ordinary artifacts.

An independent compiler-referee review found no issue in the conditional
instance or bounded crosswalk. It confirmed that the one-template result
depends on H-source's no-fixed-free-dependency premise, and that current row
sharing is not a complete source certificate. This is reconstruction-gap
evidence, not a compiler failure, L1–L5 validation, or production repair.
The next design seam is the exact Parameter/Lambda SourceBuild producer for
`sigma/Delta`, generic inlet/IF0, and invocation/event outputs joined to the
retained `r/q/n/ell` identities. A read-only architecture assessment recommends
drafting this as an id-only production record-construction gate. Its adoption
requires explicit approval; it would not make F5 consume the closure or close
Gate E. No compiler code, cfg(test) hook, API, expectation or Gate E approval
follows. No tests/builds/probes ran.

### Review status: id-only SourceBuild owner draft (2026-10-08)

The non-authoritative [owner-design draft](../notes/design/2026-10-08-id-sourcebuild-owner-design.md)
received independent M3 review from a compiler referee, specification auditor,
and performance auditor. The reviewers found no counterexample to the
conditional source-record model, but the draft is not approval-ready. They
identified a major contradiction: the draft makes metadata allocation or
validation failure abort the whole solve while also promising unchanged
acceptance and resource behavior. The semantic and specification reviews also
found the production owner map incomplete: the draft does not yet identify
authentic outputs for the original parameter scope/telescope, generic inlet,
invocation/event schema, fixed anchors, final root, and publication event.
The performance review additionally requires exact admission ownership and
frequency plus structural/resource accounting for the concrete representation
and its peak coexistence with F5 state.

The architecture assessment says the failure policy is a genuine adoption
decision: required metadata explicitly changes the resource/failure boundary;
optional metadata must remain absent and uncertified on failure; deferring
production integration avoids choosing either policy before the supplier and
representation design is complete. No policy is selected here. Exact supplier
correspondence and resource counts remain unverified, so do not ask for
implementation approval or treat this draft as an authorized gate. Next:
finish the bounded production-owner crosswalk and structural accounting, then
repair the packet and obtain delta review. Gate E and F5 consumption remain
open. No implementation, tests, builds, measurements, or Git changes occurred
in the reviews.

A bounded read-only owner map now confirms the construction seam in the draft
is not present in current production outputs. HIR and collection retain branded
`r/q/n/ell` identities, SCC topology, lambda recipe positions, and a root join
key. They do not retain the source `Desc` telescope, generic inlet/IF0,
complete invocation/event binders, fixed world/closure anchors, source
FinalRoot contract, or immutable source publication event. The current
two-stage proposal cannot consume a later authentic FinalRoot/publication
event: scheme installation and terminal `SolvedModule` publication are
different seams, and no source event is currently exposed between them.
`AdmissionReceipt` is store-admission provenance, not the semantic receiver
receipt. A new HIR-directed source constructor may use the existing branded
joins without reparsing, but its schema and H-source-to-HIR/local-law bridge
must be designed and justified; existing owners do not supply H-bridge.

The uncommitted draft now states that proposed boundary and exact conditional
constructor contract in
[`id-only SourceBuild owner draft`](../notes/design/2026-10-08-id-sourcebuild-owner-design.md)
§§3–4. It instantiates the identity input/output graph, original scope and
event order, named local-rule obligations, anchor alternatives, FinalRoot and
source-publication incidence. Fresh compiler-referee and specification delta
reviews closed both prior major findings at draft SHA-256
`fb4332cb7eb616c2c95466519c2443d7a466860b1a365a03dac52117deb9b976`:
failure outcomes are distinguished, and the proposed source constructor is
now a concrete conditional contract rather than a claim that current HIR
already supplies the missing records. This does not prove H-bridge or current
production conformance.

Still open before approval/implementation: the exact Rust representation and
its node/edge/scope/incidence counts, construction frequency and peak/retained
bytes; the actual authentic binding-anchor formation selected at `p_id`; and
the user decision between an optional sidecar whose every metadata-only
failure discards the package, a required-metadata failure boundary that
changes observable acceptance, or deferring production integration. No policy
is selected. Process-level OOM has no recovery promise. The draft remains
uncommitted, non-authoritative and unapproved; no compiler code, tests, builds,
measurements or cutover occurred. The pending flat-Application owner question
remains independent.

The next concrete representation proposal was reviewed at SHA-256
`1d5b3d16bb83d489ca1538405c9b916a81dcd4a6d1699dda2443ce6a1c7481ed` by an
independent compiler referee and specification auditor. The referee found a
major gap: `IdAnchorFormationKind` did not retain the authentic
`Executed`/`OneShot` identity and same-world returned-provider/evidence tuple
required by `ReturnedInstallation`. The static schema could not recover those
distinct fixed anchors from identical origins.

A focused repair adds a typed `IdAnchorOwnerRef` to the proposed origin tuple.
At draft SHA-256
`323aaa4068dc62433ad65b2dbfc210ffeebbc03027341c677a363368a4ecd9ab`, both the
compiler referee and specification auditor close that specific finding
conditionally: dereferencing must preserve the actual immutable anchor-owner
record, formation identity and all dependent operands for the package's full
lifetime. They verify the proposed 96-byte tuple arithmetic under its stated
64-bit assumptions; it excludes the referenced owner payload.

The expanded frozen draft at SHA-256
`a703fe7512613e02eb24b546f4134d429d24d912ef2cb27ddcd31e56626ad3c6` now
records the minimum owner payload and lifetime by the two permitted source
formations. Independent compiler-referee and specification reviews found no
new issue: preserve the inert closure/delay registration and fixed captures, or
the actual `Executed`/`OneShot` installation tuple; keep original Shared
binders and separate `Internal` from fixed `Established`/`OneShot` edges. A
bounded production-owner map found no corresponding owner object in current
HIR/solver outputs. `FetchValue`, `AdmissionReceipt`, `LambdaRecipe`, F5 rows,
scheme installation and terminal Rust result transfer each lack the required
source ownership facts.

The targeted performance review confirms the 96-byte calculation only under
the proposed handle/layout assumptions. Total retained/peak bytes remain open:
the representation has no concrete owner type, transitive payload bound,
unique-allocation/capacity manifest, validation-scratch bound or
finish-output coexistence accounting. One source binding bounds record count,
not necessarily the referenced dependency closure's size. No benchmark is
justified while that representation is unspecified.

A later representation delta makes the `ScopedClosure` graph a borrowed view
over static `IdRuleSchema` plus the package origins, so the compact candidate
does not allocate a second per-module graph. A symbolic phase model now
accounts for the unchanged live F5 batch/session/finish set, new
publication/anchor-owner allocations, pre-existing data whose lifetime is
extended, vector header and capacity, and pre-session validation scratch. At
draft SHA-256
`7c12e7086ff507c62a0a1eb6748c1c811c9b1d29b4af410b4e8362e2728fe9ae`, spec and
performance auditors confirmed the disjoint-set accounting and absence of the
prior double-counting/batch-omission issue. The draft then received an M0
wording repair at SHA-256
`b9a23d7095546772b15e18705c85d305ac27fe3f437dd9a8eb0e404468aa6742` to define
unique storage regions, count the `Vec` field in-object, and define peak as
the maximum of phase snapshots; that clarification was primary-inspected but
not separately re-reviewed.

Reviewing the new representation against the logical output `(p_id,C_id,... )`
exposed one further missing identity: the earlier `IdAnchorOwnerRef` did not
retain the actual source publication event `p_id` or its `(C_id,R_id)`
incidence. The draft now uses `IdPublicationOwnerRef`, whose pointee must retain
that event and its link to the independently owned anchor formation. At draft
SHA-256 `1269b2d4aaef62450083e7dadc81dac5a545dc61440d48e2cd9b8d449bca5a4a`,
independent semantic and specification reviews found the conditional contract
consistent; the performance review confirmed the 96-byte tuple estimate only
if this handle is still 16 bytes, with publication/anchor payload separately
accounted.

That performance review also found that the symbolic resource category
`A_new` must include newly allocated publication records and links as well as
anchor-owner records. The primary repair now includes those records and
transitive dependencies in `A_new`, and describes the omitted payload as
publication/anchor-owner storage. Current draft SHA-256 is
`eac75ad72ab91575ff08426efdca51c2959425d175e7939dff349cb04f26aac1`; this is
an M0 terminology/accounting-category repair, checked with `git diff --check`
and primary inspection, not a fresh independent review.

Next: specify one immutable concrete publication/anchor-owner representation,
map its authentic formation and publication suppliers, and enumerate unique
retained allocations, capacities, dependent closure, construction staging and
terminal transfer peaks; then obtain focused resource review. A bounded
architectural assessment finds that a direct strong `Arc<IdPublicationOwnerRecord>`
is conditionally compatible if the publication record retains actual `p_id`
and `(C_id,R_id)` while owning a typed edge to the separately formed anchor
record. The anchor still owns its actual inert-registration or
ReturnedInstallation evidence; publication must not be identified with
`Executed`. The records are proposed types, not production suppliers. On the
stated 64-bit assumptions, replacing the provisional Arc-plus-index handle
with one Arc pointer would reduce the tuple estimate from 96 to 88 bytes, but
the complete payload/allocation cost remains unbounded. This representation
and retention choice needs architecture approval; the source formation arm,
failure policy, implementation authority and gate closure remain unresolved.
The pending flat-Application owner question remains independent. The design
draft and question remain uncommitted; no tests/builds/probes ran.

A fresh bounded HIR/collection/SCC/session audit refines the missing supplier
map in the draft. `DefinitionRootId`, `HirParameterId`, resolved Lambda,
`LambdaRecipe`, `CollectedDefinition`, and the SCC plan provide branded
structural joins only. The inspected ordinary path has no source publication
`p_id`; scheme installation and terminal `SolvedModule` transfer are distinct
events. It has no inert Lambda/Delay anchor with provider/role/IF0/world and
lifetime evidence, nor a ReturnedInstallation `b`/arm/`Executed`/`OneShot`
tuple. `AdmissionReceipt` is store-transaction provenance. `finish` does not
retain the SCC plan, collection records or Lambda recipes. This is a bounded
path finding, not global absence. Direct Arc ownership therefore solves only
retention; it cannot supply the source event or anchor. The next compiler
evidence must identify an authentic permitted formation and owner, then a
separate source-publication output selecting complete `(C_id,R_id)`, and trace
both through terminal lifetime.

The non-authoritative draft now records this field-level audit and a
conditional acyclic `Arc<IdPublicationOwnerRecord>` candidate linked to a
separately formed anchor. Its structural origin-tuple estimate is 88 bytes
under the stated 64-bit `repr(C)` assumptions, versus 96 for the alternative
Arc-plus-index handle; both exclude owner payload and control blocks, and
neither is a measured `size_of` or complete memory bound. The field-level
audit, direct-Arc candidate and conditional arithmetic were independently
reviewed by compiler and specification auditors at draft SHA-256
`a4c1c3d9dd9bdfef2dc4ee1c2df4de8800421eabab17a480f468a897aa260173`; neither
found a finding in that scope. A performance review accepted the arithmetic
but identified two repairs: constrain the cycle claim to the displayed direct
edge and require transitive acyclicity; include pre-existing transitive
dependencies in `A_keep`. Those repairs were reviewed with no residual finding
by all three roles at final draft SHA-256
`cd7a5de4580e6072887528457fe06aecb6cef2df50628bb64a85b1560f4b63eb`. These
reviews do not establish transitive acyclicity, complete payload or cost,
authentic supplier/H-bridge, failure policy, or implementation authority. The
design draft remains non-authoritative and uncommitted. No implementation,
tests, builds, probes or measurements ran; the pending flat-Application owner
question remains independent.

A further bounded architecture pass narrows the missing `p_id` representation.
For this exact one-binding source, the new publication constructor can
conditionally reuse `DefinitionRootId` as a branded join key and use the
unique `Arc<IdPublicationOwnerRecord>` identity as the immutable-binding event
identity. Source Generalize does not require a fresh numeric token. This is
valid only if the constructor proves a bijection: exactly one relevant
publication for this binding, selecting the complete `(C_id,R_id)`, with no
conflation with registration, RHS execution, scheme installation or result
transfer. Root identity alone remains only a join key. The source theory
distinguishes member publication from joint tuple publication, so this mapping
cannot be generalized from singleton shape without a new proof. It may avoid
a separate event-ID allocation, but still needs the owner-record allocation
and authentic anchor payload.

Compiler-referee, spec-auditor and performance reviews found no issue in this
conditional representation at draft SHA-256
`7dfc6e6a00d749089d15d24372e3258c511b5014364d834d666a1eec95b9e39d`. Their
scope confirms the proposed join/event distinction and 88/96-byte origins
arithmetic; it does not prove the publication bijection, current H-bridge,
full owner types or a total resource bound. No production code or tests were
added; the design remains a non-authoritative uncommitted draft.

A read-only decision audit at the same draft SHA confirms the packet is not
ready for implementation approval. The selected Source Generalize rules own
the semantic partition; they do not grant this production architecture. The
proposed HIR-directed producer is a possible new owner, but authentic anchor
formation, full publication incidence, the singleton publication bijection,
concrete payload/lifetime and total static resource bounds remain unproved.
Missing suppliers obstruct extraction from existing artifacts, not a future
selected constructor. Existing user priorities support recommending optional
discard-only metadata so F5 results remain authoritative; they do not approve
the new architecture by themselves. Required metadata would change the failure
boundary and needs explicit approval. Process-aborting OOM remains outside any
recovery promise.

An exact-path source audit further distinguishes absent anchors from
near-matches: lexical `ScopeStack`, `FetchValue`, `LambdaRecipe`, SCC topology,
`AdmissionReceipt`, scheme installation and terminal transfer carry no
selected world/registration/lifetime anchor or source publication `p_id`.
Shadow `Form::Lambda` and `SymbolicRegistration` are non-production and do not
supply original semantic witnesses. The next evidence must provide the
authentic formation/local-law owner, then a separate source publication and
FinalRoot bridge selecting complete `(C_id,R_id)`, before type storage or
terminal retention can be treated as implementation work. The pending
Application-owner question remains independent. No production code or tests
were added; the source-owner draft stays non-authoritative and uncommitted.

The frozen [schema census](../notes/progress/2026-10-08-id-sourcebuild-schema-census.md)
derives one eligible Desc under H-source and enumerates separate source units:
four origin roles, four checked-inlet obligation families, eight gamma fields,
seven outer phases and ten VP constructor families. It explicitly does not sum
these into node/edge/binder/allocation totals. Independent specification and
performance reviews found no blocking or major issue at census SHA-256
`0e8cd67ef46d492d501636f5208c12e0336bff5a1832e4a154b2f13e66f3a18a`; the
performance review identified one low-severity omission, now repaired in the
census: the future storage manifest must also account for temporary worklists,
peak live snapshots, Arc clone/allocation activity and bounded teardown.
Exact totals still require a concrete schema/owner manifest with authentic
telescopes and transitive payloads. After that M0 clarification the census SHA-256
is `a4e3363cfeb1e5e22685fd8a3c907eab85fe602282cd79b08adfeb9cd0b7425e`; its
checkpoint is `cd77aa456`. The census metadata now records that spec/performance
review and the primary-inspected M0 repair; the final SHA-256 is
`4c22cd490005955899b75a04c3606957751556911dbf3b8d0dde0944a0eae7e6`.

The separate [publication-bijection audit](../notes/progress/2026-10-08-id-sourcebuild-publication-bijection.md)
shows why the draft's Arc identity claim requires two distinct premises:
H-pub, an authentic source-owner derivation with exactly one publication
selecting full `(C_id,R_id)` and anchors, and H-linear, one canonical allocation
route with only clone/move retention afterward. Identical duplicate Arc records
are the minimal counterexample to payload validation as a proxy for event
identity. Selected source rules retain publication meaning but do not provide
either production correspondence or allocation canonicality. This research
note is pushed at `14830271a`; compiler-referee review passed the conditional
claim at its frozen SHA-256 `b5cf16b216cd0e9105fa73d34c63968e0ebc635aaddec86768e93566c0fefa35`,
with H-pub/local-law suppliers and production mapping explicitly unclosed. The
final metadata-updated note SHA-256 is
`863ea38c9e2f41580d05722b88b743fc8d30eaed8a9fea76456fdc21346d9ec3`. No status
or authority changed. No production code, tests or builds were added or run.

## CALL_TYPE / DemandFormation cut (2026-10-08)

The frozen [conditional construction](../notes/theory/2026-10-08-call-demand-formation-construction.md)
factors selected checked-challenge assembly through independent admission of
the actual whole carrier at the declared inlet. Given that admission, the
same-value callee relation and contextual Function membership derive
acceptance and receiver observations for the retained actual provider at the
same tuple. An independent compiler-referee review found no issue in that
conditional derivation. It does not derive the admission, build Strict for an
arbitrary Apply, or close CALL_TYPE.

The separate [argument-only falsification](../notes/theory/2026-10-08-call-demand-formation-falsification.md)
uses Charter §21's ordinary-Value-entry versus annotated-retained-entry
distinction: both may expose the same `Comp(empty,Int)` argument result while
their source receiver incidence requires different entry. Its no-single-input
conclusion is conditional on jointly realized checked contracts and contexts;
it is not a complete admitted-source counterexample. An independent
specification audit found no issue in that boundary. Neither note invents a
semantic rule or changes the approved behavior. The construction and
falsification notes are pushed at `3161ea584` and `b4eec1c88`, respectively.

A bounded HIR/Core/F5 source audit of `crates/yu-hir/src/shadow.rs`,
`crates/yu-core/src/shadow_derivation.rs`, `crates/yu-solver/src/lib.rs` and
`crates/yu-solver/src/shadow_apply.rs` confirms that the inspected paths
retain Call/operand identity and candidate value endpoints, but expose no
complete argument `Result`, declared whole inlet, actual role/entry and
comparison-independent `DemandFormation` joined for one receiver. In
particular, the experimental Apply candidate constructs its negative Function
term during candidate solving; that is not a pre-comparison source
certificate. This is a bounded path finding, not a production-wide absence
theorem. `CALL_TYPE` remains CONDITIONAL-CLOSED and `INLET_CARRIER` remains
OPEN-PROOF; no DAG status changed and no tests/builds ran for this research
slice. The latest unlocated returned-Function sublemma in this task record is
not promoted as independent proof authority.

Next: after the pending flat-Application owner decision is validated, inspect
the selected Application source-construction owner for an independently typed
whole-argument-to-declared-inlet transport and retained receiver entry/role at
the original Call incidence. If those outputs are absent, return the exact
missing formation judgment for design; do not infer it from the candidate
endpoints or successful solving.

## D0 native `id` / `pick` descriptor guard construction (2026-10-08)

The bounded [descriptor-guard construction](../notes/theory/2026-10-08-id-pick-descriptor-guard-construction.md)
instantiates the already selected native VP/Echo/Fixed phase and whole-image
constructors for local `id` and rigid-import `pick` leaves. It derives their
local descriptor typing, same-carrier admission, Force, current-world rebind,
same-provider Return, and hereditary future requirements without assuming
tested callable membership, source `M_E`, or Direct. An independent
compiler-referee review found no issue in this local derivation or its scope.

This is a construction result within the selected native equations, not a new
semantic decision or gate closure. Foreign independently fixed descriptor
embedding and arbitrary complete import-certificate construction remain open;
the note does not cover arbitrary opaque imports. D0's native descriptor
selection remains as recorded, while Direct, principality, and production
correspondence retain their existing open gates. The artifact is pushed at
`8a53da821`; no tests or builds ran for this research slice.

The conditional [actual-root Direct fragment](../notes/theory/2026-10-08-id-pick-transformed-root-direct-fragment.md)
has also passed an independent specification audit. The review confirms that
its finite `Eq`/`Le` proof is tied to the submitted transformed roots, one
scope-preserving assignment, the complete active interface, and an explicit
resolver-conformance premise. The coverage derivation pairs the source base,
unanchored `Z`, every recursive `W` step, and the final guard. The result
remains conditional: D0 formation, licenses, capture summaries, actual-root
resolver acceptance, and any strict-view witness are unsupplied. This review
establishes no implementation, principality, or gate closure; it proposes no
test/build work. The artifact's checkpoint is `6d57f1b69`.

### SourceBuild anchor publication delta (2026-10-08)

The non-authoritative [id-only SourceBuild owner draft](../notes/design/2026-10-08-id-sourcebuild-owner-design.md)
now retains both anchor formations permitted by the selected identity instance:
inert registration and actual returned installation of the same raw `U_g`.
Uniform Value-entry §5.1 supplies the common semantic/source-side `U_g`
formation; it does not select which binding-publication event occurred.
Returned installation retains the actual `Executed`/`OneShot`, world and
evidence operands, with the separate `Internal` description edge. Authentic
publication evidence must select the arm.

An independent specification delta review closed the prior unsupported
inert-only selection at draft SHA-256
`f08e015e34b8034bb603e23107486a82553261b698ff1eddffbfa29e27ad20f1`; no new
material mismatch was found in that scope. This remains conditional on genuine
source constructors and local laws. The production owner, complete operands,
H-bridge and resource bounds remain open, so this repair provides no
implementation approval. The owner draft and pending flat-Application
question remain uncommitted. No tests, builds or measurements ran.

### SourceBuild schema and publication-resource blocker audit (2026-10-08)

An independent resource attack on the identity owner draft confirms that its
fixed `IdRuleSchema` cardinalities are not yet derived. The selected source
proof permits finite rule catalogues when their owning alternatives and
telescopes are finitely presented, while the identity instance leaves actual
`Delta`/`IF0` arities and `Shared`/`ViewLogic`/`EventProof` introductions with
their authentic owners. Empty captures and one eligible template do not set
the complete schema count. A finite schema remains a viable route: challenge
contracts and checking proofs can remain registered parameters, so their
runtime developments need not be expanded into stored history.

The same attack finds that a borrowed schema view avoids copying a per-module
graph but does not bound slot-resolution work, validation scratch, transitive
owner retention, or staging/finish peak. No exact retained/peak total follows
until the schema, complete owner fields and allocation/lifetime graph are
concrete. The next artifact is a node/edge/binder/scope/port manifest tied to
source constructors and dependent telescopes, with the exact reference
boundary and an allocation/worklist/phase-capacity table. If that requires
choosing a different catalogue boundary or omitting the full relation, return
to architecture review rather than silently changing the contract.

A separate read-only production lifecycle map identifies an ownership-level
whole-package seam: freeze before `InferenceSession::try_new`, retain owned
data in the consuming session, and move it only into the terminal successful
`SolvedModule` construction. Existing flow cannot retain borrowed references
to batch definitions/recipes/SCC topology, and `ConstraintBatch::clone` would
need explicit duplicate-allocation accounting if it owned a package. Current
`SolveAvailabilityError` does not model all metadata failures; existing
catchable reservations do not make `Arc::new`, nested owner allocations or
other infallible constructors recoverable. Passing a metadata failure through
`solve` changes acceptance, while adding a local error changes diagnostics.
The optional shadow-capture precedent is narrower and does not cover terminal
capture construction. Source preflight must also avoid counted SCC/root query
helpers if public F5 counters are to remain unchanged.

These are production-structure and resource findings, not a selected failure
policy or an implementation approval. The current draft SHA remains
`f08e015e34b8034bb603e23107486a82553261b698ff1eddffbfa29e27ad20f1`; its
schema/owner payload, H-bridge and failure-policy questions remain open. No
code, tests, builds or measurements ran, and no question-board state changed.

The [typed manifest skeleton](../notes/progress/2026-10-08-id-sourcebuild-schema-manifest.md)
is now pushed at `afeb0ba87` and passed an independent specification delta
review with no material conformance finding. It fixes seven candidate indexing
roles and the conditional one-template result, but explicitly does not count
them as graph nodes. The minimal exact-count blocker is the unenumerated
`Delta_a` telescope; a three-premise conjunction also shows that preserved
source clauses do not choose a storage node/edge normalization. The reviewer
kept the authentic suppliers, H-bridge, publication and resource gates open.
Next evidence is the source owner's frozen Parameter/Lambda/invocation
operand-and-binder table, starting with `Delta_a`, followed by a concrete
storage encoding and complete owner-allocation/lifetime table. No compiler
code, tests, builds or measurements ran.

### Parametric SourceBuild schema review (2026-10-08)

The owner draft now carries a separate parametric finite-schema candidate:
authentic owner records expose actual telescope lengths and incidences, while
the seven origin roles remain fixed joins. An independent architecture review
confirmed that variable finite arity is compatible with the selected source
semantics, but does not provide missing owners, local laws, H-bridge, or a
storage decision. Compiler-referee and specification reviews found no
semantic/conformance defect in the frozen candidate; neither certifies
production correspondence.

The performance review keeps production approval open. The symbolic linear
validation bound needs counted incidence/work units, bounded target lookup and
scope checking, and explicit scratch/reconstruction accounting. The draft also
needs a constructor-by-constructor allocation/failure table and teardown-depth
bound. Its phase accounting should define extended-lifetime allocations as
disjoint from still-live baseline allocations and include transient
reallocation peaks. These are requirements for the next reviewed design
revision, not measurements of an implementation. Draft SHA-256 is
`1495de93b9d0b5b04f3f3c814327e044eca73b8dcc74e60cc6eea2d4e1f866ac` and
remains uncommitted pending explicit approval; the unrelated pending
Flat-Application question also remains uncommitted. No tests, builds or
measurements ran. Next: repair the resource contract, obtain focused delta
review, then present the bounded architecture and unresolved owner/failure
choices for user decision. No implementation or F5 cutover is authorized.

The follow-up resource revision withdrew the unsupported linear validation
claim and now requires a concrete pass/work-unit algorithm, bounded target and
scope checks, scratch accounting, allocation/failure inventory, and bounded
teardown. Phase accounting excludes baseline-live storage from lifetime
extension counts and includes transient replacement buffers in the peak.
Focused performance and specification delta reviews passed with no remaining
wording finding at draft SHA-256
`785a5a4d5133d8c1790e1e0a5f85f19bab83e0d0c84c502951ab6f80f1596bca`.
Production readiness still lacks the actual schema/owner allocation manifest,
validator algorithm, admitted-size envelope, and teardown implementation.
The reviewed owner draft remains uncommitted pending explicit approval; no
tests, builds or measurements ran.

### SourceBuild owner, bridge, and failure evidence (2026-10-08)

Three disjoint research checkpoints are pushed: the Parameter owner/telescope
derivation (`23697b64b`), production H-bridge audit (`cb37ae6c7`), and failure
policy/control-flow map (`7c10ba7a3`). The Parameter derivation stops at the
first unsupplied output: an authentic ordered `sigma_a/Delta_a` manifest with
typed dependency targets and local clauses. It rules out inferring that
telescope from import-freedom, complete inlet `Delta`, or `Intrinsic`. The
production audit confirms current HIR/solver data provides structural joins,
not those semantic records, a source publication, complete root, or anchor
formation. It also records that generic HIR equality can discard Parameter
owner identity; the direct Parameter-handle comparison is stronger. The
failure map shows optional metadata retained before F5 can change F5 resource
availability, and apparently read-only batch queries may mutate shared atomic
counters.

The owner draft was repaired to qualify optional-sidecar acceptance under
memory pressure and make counter isolation explicit. Focused performance and
specification delta reviews passed at SHA-256
`440e1ef94981ff00ad1515777d3afe5c933f67798619c9369cc0aba67083b9e0`.
This closes only those wording findings. The three research notes are
unreviewed, conditional evidence; the design remains non-authoritative and
uncommitted. Exact owner/telescope suppliers, H-bridge, schema and allocation
manifest, uncounted constructor path, admitted-size envelope, failure/error
policy, and production consumer remain open. No compiler code, tests, builds
or measurements ran. Next: obtain the authentic Parameter owner schema, then
re-freeze and review a decision-ready producer contract before asking for any
architecture approval. No F5 replacement is authorized.

The focused emptiness attack is now pushed at `2c340b256`. It confirms that
the selected rules determine the Parameter owner and pre-challenge scope but
do not establish `Delta_a=[]` or an authentic nonempty case. One earlier static
dependency edge is enough to show that eligibility does not imply an empty
telescope, while remaining only a record-level discriminator until an
authentic Parameter owner supplies it. The precise next evidence is still the
ordered free-operand manifest and its local formation clauses. This note is
unreviewed and non-authoritative; no source counterexample or new semantic
rule is claimed. The owner design draft remains at reviewed-delta hash
`440e1ef94981ff00ad1515777d3afe5c933f67798619c9369cc0aba67083b9e0` and
uncommitted pending architecture approval.

Independent compiler-referee and specification delta reviews now pass both
owner/telescope research notes at their frozen hashes, with no finding. This
certifies only the conditional source-rule inversion and the minimal
record-level dependency-direction discriminator; the authentic Parameter
operand manifest remains absent. Review did not establish `Delta_a=[]`, a
nonempty source counterexample, production H-bridge, or implementation
authority. The checkpoint is pushed at `2c340b256`; no tests, builds or
measurements ran.

The terminal source-package timing has a second candidate seam. A read-only
architecture inspection found that immediately before `SolvedModule` transfer,
the baseline F5 solve, finalization, accounting and counter snapshot have
already completed, while the batch still owns structural HIR/component inputs.
Late materialization could avoid competing with earlier F5 allocations only
if it uses authentic immutable source inputs at that seam, performs no counted
batch queries, introduces no later baseline allocation dependency, and drops
the candidate on failure without changing solve errors. It does not establish
equal end-to-end memory availability or remove retained-storage cost. Required
source suppliers and H-bridge remain absent. This is a new unapproved
architecture alternative to the draft's pre-session package construction, not
a selected design or implementation authority. Next: revise the uncommitted
draft to expose both timing alternatives and their resource boundaries, then
obtain focused review before presenting any decision. No tests, builds or
measurements ran.

The owner draft now presents pre-session staging and terminal `finish`-time
materialization as unresolved alternatives. Compiler-referee, specification,
and performance delta reviews passed the frozen revision
`f0ebb412e938ca3c7d823d07c597976158e1fad8f0d6178d5a68fdee0d5f467c` with no
remaining finding in placement, failure, counter-isolation or resource-peak
scope. The terminal candidate is explicitly after feature-gated capture
collection and includes its validation scratch in the separate peak account.
The draft remains uncommitted and non-authoritative. Authentic Parameter
telescope, source owners, H-bridge, allocation manifest, teardown bounds,
placement selection and failure policy remain open. No compiler code, tests,
builds or measurements ran.

### Native ordinary Direct consumer design gate (2026-10-08)

The selected native projection contract already defines ordinary
`Direct(u,V)` checking for Value, Computation and complete Function proofs. A
new checker-only design proposal maps that contract to a flat proof arena,
iterative validation, exact immutable root environments and one shared
per-compilation work/byte budget. It remains non-authoritative and does not
route production away from F5. Independent compiler-referee and spec-auditor
reviews found no conformance/soundness issue; performance review prompted a
batched accounting repair, and a focused delta review passed after charging
root construction, environment preparation, proof-arena construction and all
query attempts to one compilation budget. The proposal explicitly leaves
numeric limits, full local-law owners and actual caller integration as gates.
No code, tests, builds or measurements ran.

Question q1 selected the reviewed flat-arena proposal as the checker-only
architecture direction (approved d1; integrated in `852f70117`, receipt at
`questions/2026-10-08-native-direct-consumer/receipt.md`). The proposal is
`notes/design/2026-10-08-native-direct-consumer-plan.md`, SHA-256
`1947eff96d4450f33f446988e75f5d818bf5d75b641bdbfbfbb0d0dc2e6aae60`. This
does not authorize implementation, a public API, source semantics, inference
routing, production use or F5 replacement. Next: map exact caller and
local-law owners and set numeric limits against the supported caller envelope;
checker implementation remains gated on those reviewed design choices. The
independent source/HIR-to-public-root lifecycle manifest and existing F5
crosswalk continue, with authentic Parameter telescope, general H-bridge,
principality and full F5 replacement gates open.

### Current F5 id/pick public-surface crosswalk (2026-10-08)

The bounded current-path crosswalk is checkpointed at `dd92e447b` in
`notes/progress/2026-10-08-current-f5-id-pick-public-surface-crosswalk.md`.
It derives current scalar outputs `id: forall a. a -> a` and literal-backed
`pick: Any -> Int`; neither output carries the selected native inlet, fixed
import, whole certificate, or public-root frame records. A one-digit literal
change (`z=0` to `z=1`) leaves the closed pick scheme unchanged while changing
the selected `Fixed(J_z)` operand, so the scheme alone cannot recover that
export. This is a bounded static information-loss witness, not a compiler
execution counterexample, production conformance result, or cutover evidence.

The next source-formation/publication design packet should identify canonical
retained records for Parameter/Lambda formation, fixed-import installation,
final-root extraction, decode, and Direct checking. Authentic source-owner
telescopes, full H-bridge, import/general SCC cases, principality, approved
Direct checker choice, and replacement/cutover remain open. No compiler code,
tests, builds, or benchmarks ran; no inference gate is promoted by this note.

The bounded owner-to-consumer inventory is now checkpointed at `9b1202ff3`
in `notes/progress/2026-10-08-id-pick-owner-consumer-manifest.md`. It maps
selected fields to actual current producers/consumers, scopes, lifetimes and
transfer/drop boundaries, and marks missing H-bridge/local-law/source-owner
suppliers explicitly. The `z=0`/`z=1` fixed-import distinction and alias versus
separate-new frame obligations are recorded. The note is an unreviewed static
manifest, not an implementation or readiness certification. The next gate is
an architect-owned producer/layout packet for the canonical source record
package, with every absent supplier assigned or retained as an explicit open
owner. No representation, placement/failure policy, pick producer scope,
Direct consumer integration, or implementation authority is selected here.

The follow-up architecture cut classifies most absent fields as selected
semantic outputs still needing source correspondence; the storage, placement,
failure, and expanded consumer integration policies remain unselected. No new
semantic user choice is shown necessary yet. The earliest substantive missing
supplier is the authentic L4 initial-world/registration owner for U_g and its
publication anchor, including formation arm, dependent operands, and incidence
to `(r,ell,C,R,p)`. An exact cardinality/layout packet cannot be filled by
assuming inert formation or empty telescopes. Next: inspect current production
HIR/lowering/solver ownership for that L4 supplier and report the first absent
field. No implementation or inference gate is authorized by this cut.

The bounded production-path inspection found no such owner in the inspected
HIR → collection → inference → solved-result path. The earliest missing input
is the initial world/installed environment at `yu-hir` lowering; `HirParameter`,
`Lambda`, `FetchValue`, `LambdaRecipe`, SCC membership, Function rows,
`AdmissionReceipt`, scheme installation, and `SolvedModule` transfer contain
only structural/type/provenance information and cannot certify L4's provider,
IF0, lifetime, formation arm, or publication anchor. Core/backends are also
boundary-only in the inspected default path. This is bounded evidence, not a
repository-wide absence claim. No code or executable checks ran. Next: compare
the selected L4 source contract with compile/session entrypoints to identify
the smallest authentic world/registration input owner before drafting further
production layout or placement choices.

The L4 contract/entrypoint comparison confirms that L4 is a genuine semantic
premise, but the selected definitions do not assign initial-world construction
to the compilation caller or to a compiler-owned factory. Lambda formation,
literal installation and capture have selected source rules; none creates the
initial world or supplies its genuine registration evidence. Current
`lower_module`/`SemanticImports`, `ConstraintBatch::collect`, and
`SolvedModule::solve` expose no such context seam, and default core/backends
provide no runtime owner. Thus caller-versus-compiler context ownership remains
an architecture question only if source-constructor tracing cannot locate an
existing authentic owner. Next: trace one genuine initial-context constructor
and Lambda registration to the selected id anchor, then extend through
literal-install/capture for pick. No fabricated empty world or opaque
validity flag is accepted as a supplier.

The source-only trace is checkpointed at `3cd225d28` in
`notes/progress/2026-10-08-l4-id-anchor-source-constructor-trace.md`. It
clarifies that selected Lambda formation does construct `U_g`/`IF0`, and
selected literal formation constructs `J_0`; the earliest unsupplied premise
is the authentic initial `JointWF` registry/scope/authority/incidence world.
The Empty environment/telescope case is conditional on that world and does
not bootstrap it. The source rules assign no initial-world supplier to the
caller or compiler factory, and current production has no such entrypoint.
This is scoped to the inspected source chain, not a claim about all semantics.
Next: resolve the authentic initial-world owner before selecting a compiler
context API or adding production metadata. No tests, builds, measurements, or
implementation ran; no gate promotion.

Question q1 selected caller-supplied authentic initial `JointWF` evidence
(approved d1; integrated in `9598eee7a`, receipt at
`questions/2026-10-08-l4-initial-jointwf-owner/receipt.md`). This settles only
the producer owner. It does not define the context API, evidence validation,
storage/lifetime, versioning or invalidation, and authorizes no implementation
or cutover. A reviewed durable context-input contract and exact dependency
owners remain prerequisites before implementing the caller seam. Dependent
SourceBuild freezing still requires genuine local-law and source/HIR
correspondence suppliers; independent inference gates remain active.

### Independent proof and source-owner research checkpoints (2026-10-08)

The bounded [current F5 application-to-source cut](../notes/progress/2026-10-08-current-f5-apply-source-cut.md)
at baseline `4c114d684` finds that default HIR/collection does not admit
expression Apply, while the feature-gated candidate emits only a structural
callee-to-negative-Function-demand constraint and explicitly leaves source
Call premises unresolved. Function ports and exported schemes preserve
structural endpoints but not a source `VIncl` certificate or whole-clause
action. This is a scoped production correspondence gap, not a cutover verdict.
The follow-up [one-occurrence field crosswalk](../notes/progress/2026-10-08-f5-apply-source-field-crosswalk.md)
maps the exact `my apply f = { my step x = f x; step }` candidate through HIR
occurrences, row allocation and polarized demand to `A_f/F_c/E_c/A_c`. It
finds the interpreted environment/shared `xi` absent before the callee row can
be interpreted as `A_f`; conditional on those inputs, complete dependent
`F_c` at original `R_f` is the first missing Call-produced object. The
[pre-admission owner cut](../notes/progress/2026-10-08-f5-apply-preadmission-owner-cut.md)
then found a symbolic `Gen-Call-0`/demand constructor that retains lexical
incidence, but not `InitialSourceDescriptorRelation`, original `xi`/types/
scopes, complete `F_c`, or emitted membership. Its terms have no solver or
production consumer. The earliest missing authentic input is the interpreted
source descriptor/environment relation at the original scope; structural
solving supplies none of it. This remains a scoped static characterization;
no code or executable checks ran.

The conditional source-only [captured-formal chain](../notes/progress/2026-10-08-captured-formal-source-chain.md)
maps genuine initial JointWF, Parameter Desc, generic Lambda entry,
typed Force/Return/rebind, same-certificate capture and Name, then the
Call-owner input and unsolved dependent `F_c` at `R_f`. Its independent
[compiler-referee review](../notes/progress/2026-10-08-captured-formal-source-chain-review.md)
found no issue within the conditional scope. Generic inlet applicability to
`apply` remains a premise; the id/pick body theorem does not prove apply/step
typing. The chain does not supply initial JointWF, interpreted production
records, `VIncl`, whole-argument compatibility, invocation containment,
principality, or cutover. Next: resolve the already-pending initial-context
owner, then trace one authentic formal certificate through capture into the
pre-admission Call constructor. No compiler code or executable checks ran.

The bounded source-owner audit for `P.CallInitial` is pushed at `62337b13a`
([audit](../notes/progress/2026-10-08-callinitial-owner-correspondence.md)).
No complete initial observation/evidence/action supplier was found in the
inspected selected contracts or HIR/core/solver owners. This is scoped absence,
not a repository-wide result. Source-rule construction remains distinct from
production F5 correspondence; I0/O0, joint-action laws and actual F5
preservation remain open.

The RT.2 countermodel attack is pushed at `2a0ecd24e`
([finite separation](../notes/theory/2026-10-08-rt2-relative-transfer-countermodel.md)).
It separates ordinary final-model VIncl from relative Function readout in a
positive finite system, and identifies a conditional source-shaped discriminator.
It does not certify a legal full Yulang countermodel: authentic full-domain
carrier/world interpretation and global inclusion over the original value
universe are unsupplied. Independently ordinary `M.Car` certificates would
supply the sufficient RT.2 route.

The constructive RT.2 attempt is pushed at `2b7413cc6`
([partial derivation](../notes/theory/2026-10-08-rt2-relative-transfer-proof-attempt.md)).
The non-hole gap is the evidence-producing relative action on the complete
observation family, `P_A_f[B_as] -> P_F_c[B_as]`; final-model VIncl and
positivity do not provide it. An enlarged source coalgebra is a candidate for
the apply-hole case, but complete fronts and postfixedness remain unproved.
An independent compiler-referee review of both exact artifact hashes found no
issue within their conditional claims; the [review record](../notes/progress/2026-10-08-rt2-relative-transfer-review.md)
lists the scope and omissions. They remain conditional research, not a closed
RT.2 proof. No proof gate or production readiness changed. No tests, builds,
experiments or performance measurements ran. Next: establish the actual full
outer-domain carrier interpretation and source-owned relative comparison
before any gate-status update.

Two follow-up constructions are now checkpointed. The [outer carrier
provenance audit](../notes/theory/2026-10-08-outer-domain-carrier-provenance.md)
(`c254d443c`) finds no uniform independent `M.Car` supplier over the unchanged
outer challenge family. It derives that such a supplier plus ordinary
`VIncl_M` would suffice for the non-hole RT.2 route, while keeping relative
`B_a.Car` evidence distinct. It constructs no out-of-M admitted carrier.
The [source comparison action attempt](../notes/theory/2026-10-08-rt2-source-comparison-action-attempt.md)
(`a3327ee03`) gives a conditional `N_Z` criterion: all hereditary lookup
indices must be exactly retained, alternatives complete, and immediate target
predicates independently preserved. The selected source Call owner does not
supply those conditions for `A_f,F_c`; it retains final-model `VIncl` and
supplied decoration.

The [joint apply-source front attempt](../notes/theory/2026-10-08-rt2-joint-apply-source-front-attempt.md)
(`38d1afbd3`) records a conditional construction order: first construct
`Phi(S)`'s apply front, then use it to construct the distinguished step that
captures apply. It does not establish the fronts for other returned providers
or prove S postfixed. `N_S`, complete RT.1/RT.3 and checked/native interface
identification remain open. Independent compiler-referee and spec-auditor
reviews found no issue within the three artifacts' conditional claims; the
[review record](../notes/progress/2026-10-08-rt2-followup-review.md) states
the exact scope and omissions. No RT.2 or production gate has closed.

### Complete-Call C0 cut after native boundary decision (2026-10-09)

Three complementary bounded attacks now separate the exact remaining layers.
The [constructive id/literal Call attempt](../notes/progress/2026-10-09-npb-call-c0-construction-cut.md)
builds the selected native receiver branch and identifies its distinct
source-Call result consumer as the first missing operand **within that forward
branch under its stated local laws**. Independent review caught and repair
removed a premature claim that this already formed a typed complete Theorem IF
frame. The note now retains only an untyped operand/frame skeleton; typed IF
requires authentic complete declaration/primitive-interface typing and lawful
whole-map actions as parallel unresolved premises. Delta review passed.

The [bounded falsification attempt](../notes/progress/2026-10-09-c0-receiver-lift-falsification.md)
found no legal source falsifier in the inspected selected rules because the
actual exhaustive `ArmDecl_e`/W/Z declaration is opaque and supplies no
concrete production rule. Its conditional final-guard argument does not claim
boundary membership proves C0. Review passed after qualifying the changed
coordinate admission certificate by its being live in admission. The
[current producer cut](../notes/progress/2026-10-09-current-c0-producer-cut.md)
also passed bounded regression review: ordinary/default-off HIR, collection,
candidate solving and export do not produce complete C0 inputs. The exact
selected design inventory confirms that the missing arm declaration cannot be
filled by the generic Call/IF constructors or the reviewed conditional W/Z
grammar; those preserve or eliminate supplied clauses but select none.

These results sharpen rather than close `JOINT_DEC`: the source result
consumer rule and authentic exhaustive complete-Call arm contracts remain
separate inputs, and production correspondence remains open. No compiler code,
tests/builds, semantic promotion or F5 cutover occurred. Next: locate an
already selected actual Call result-consumer rule and complete arm declaration
if one exists; if none is selected, continue on an independent open inference
gate without inventing their semantics.

### SourceBuild owner review and caller-to-Parameter input cut (2026-10-09)

The bounded [id/pick owner-to-consumer manifest](../notes/progress/2026-10-08-id-pick-owner-consumer-manifest.md)
now passed separate semantic and code correspondence reviews. The
`spec_auditor` found its retained source/public fields conform to selected
Source Generalize and projection rules. The `regression_auditor` found no
blocking mismatch in the bounded HIR/solver/types paths; current structural
rows and scalar schemes do not carry the selected provider/world/inlet/
certificate records. The draft SourceBuild layout/resource/failure policy
remains non-authoritative and is not implementation-ready.

The [caller-context-to-Parameter trace](../notes/progress/2026-10-09-caller-context-parameter-input-cut.md)
grants approved q1 caller-supplied JointWF, distinguishes `sigma_a`,
`Delta_a`, and whole-inlet `Delta`, and stops before claiming a missing source
constructor: the selected source rules require an actual registration,
component/binder tree and authentic anchor application, followed by the
ordered owner/predecessor/incidence manifest for the Parameter operands. A
specification review passed this scope. The bounded current-code census also
found no corresponding caller evidence/telescope carrier in the inspected
HIR/solver/types entrypoints.

Next: produce one authentic `my id x=x` caller/source-formation application
and enumerate each Parameter scope/telescope operand with its existing owner,
predecessor binders and registered incidence. Do not infer empty telescopes,
choose an anchor arm from HIR shape, or resolve API/storage/failure choices
before this evidence exists. The F5 replacement, H-bridge, principality and
resource/failure gates remain open. Details and review scopes:
[SourceBuild input-cut integration](../notes/progress/2026-10-09-sourcebuild-input-cut-review.md).

### Native projection renaming sublemma toward IFACE_EQUIV (2026-10-09)

The bounded [PE fixed-fiber derivation](../notes/progress/2026-10-09-native-projection-interface-equivariance.md)
and complementary [identity-observer/falsification characterization](../notes/progress/2026-10-09-native-projection-interface-equivariance-falsification.md)
are checkpointed and pushed. Independent `compiler_referee` and `spec_auditor`
reviews passed. The derivation proves structural renaming for selected PE-ID
and finite PE-PICK records, forced-alias F/G maps, supplied extraction/decode
outputs, and finite Direct proof recognition when every external operation
receives the same complete operands. The companion inventories rigid identity
readers and shows why moving two equal-sort registered slots while fixing the
world is an inadmissible mutation. Existing phase-constructor §6 and uniform-
inlet §7.1 results are reused at their exact scopes.

This is a design-level structural sublemma. Changed-operand covariance for
opaque registry, admission, VP/history, hereditary, Strict/Exit and allocator
operations remains unsupplied; the current default F5 publication/use path has
no PE export or CI-use consumer. Neither IFACE_EQUIV nor CI_USE, FRESH_LIFE or
production correspondence closes here. No implementation or tests/builds
occurred. Next: trace one selected decode/new operation to its actual identity
inputs and supply or isolate its changed-operand law; separately preserve the
default-path integration gap as a required F5 replacement deliverable.

That Decode/new trace is now checkpointed and pushed as
`eddaea292` (bounded falsification) and `3d15598b1` (construction). Independent
`compiler_referee` and `spec_auditor` reviews passed both artifacts. Source
Generalize §5.2 supplies frame/declaration/event allocation keys, whole-frame
incidence and alias reuse; PE §4.2 supplies the seven ordinary-root equation
entries, fresh public root requirement and actual-root reads. From those clauses
the construction derives commutation of the frame and equation schema under a
sort/scope-preserving presentation renaming, with Shared and runtime-event
fields fixed. It still cannot derive the actual registered root identity or a
changed-root allocation/readout square. A two-new/one-alias witness shows why
equal `Int` endpoints cannot collapse distinct fresh roots or allocate again
for an alias. The conditional two-fresh-atom no-choice argument remains
hypothetical and is not a counterexample to PE.

A focused current-code audit also traced F5 incoming instantiation: it allocates
Q/R rows and reuses a substitution row per ordinal, but routes into an already
collected use component. This is not a PE public-root allocator and has no
retained whole-frame/Omega/alias action. It therefore does not fill the root
supplier gap. Next: identify an authentic ordinary-root allocation, install,
and readout owner with its complete identity observers and action laws; keep
the F5-to-PE producer/consumer correspondence as a separate cutover obligation.

The [PE root-handle owner map](../notes/progress/2026-10-10-pe-root-handle-owner-map.md)
is now checkpointed as `1e59eb288`. It distinguishes parse-branded
`SourceNodeKey`, artifact-local `HirOccurrenceId`, definition `DefinitionRootId`,
collection-branded `DefinitionUseId`, and per-scheme Q/R ordinals. None is
already the semantic `Instance`/`Alias` frame or ordinary public root. The
selected owning source rule distinguishes independent `new` frames from
antecedent aliases; the PE decoder requires a fresh ordinary root per frame.
The approved Direct architecture direction permits a compiler-owned dense slot
inside an immutable environment, but no existing/approved producer maps these
frame identities into such slots. This keeps the actual source-owner map,
public-root publication and Direct consumption as separate boundaries; numeric
limits stay open until a successor caller and attempt schedule exist. No code,
tests/builds, API or F5 routing changed. Next: define and independently review
the typed `Instance`/`Alias` producer output and its validated frame-to-root
slot correspondence before implementation approval.

The [proposed PE frame-to-root-slot contract](../notes/progress/2026-10-10-pe-frame-slot-contract.md)
now records that typed producer output and its candidate validation laws. It
restricts this map to aliases of admitted PE instance frames; established
`Mono` roots remain under their authentic installed-root owner. Frame and
binder routing must preserve source allocation before assignments, challenges
and histories. An independent `spec_auditor` review found the initial alias
domain underspecified and allocation timing omitted; both findings were closed
in a delta pass. The artifact remains a non-authoritative research proposal:
actual producer/local-law correspondence, established-root mapping, lifecycle,
failure policy and numeric limits remain open. No implementation, tests,
builds, or F5 routing changed. Next: map the actual source caller and local-law
owners, then connect those outputs to an ordinary-root producer/store/readout;
implementation still requires explicit approval.

The [bounded Direct caller/root-owner map](../notes/progress/2026-10-10-pe-direct-caller-owner-map.md)
now completes the required caller/law-owner survey at the recorded paths.
The intended semantic caller is `view(h,q,V)` after actual source frame
routing and PE decoding, but no authentic compiler caller or ordinary-root
producer/store/readout exists in the bounded default-path inspection. Current
F5 use routing freshens scalar Q/R rows into already collected components;
`SolvedModule` publishes closed schemes and public `SolvedValue` collapses
Function/Union/Q/R to `Unknown`. The native Python checker remains a
conditional manually supplied research fragment. The selected Value,
Computation, Function, world/action, scope/substitution, recursive-equation and
primitive law families have no complete production Rust supplier identified.
The independent `regression_auditor` found one minor readout-surface wording
issue, closed in delta review. Numeric limits remain unset because caller,
admitted law catalogue and per-attempt construction/retry schedule are not
selected. No implementation, tests/builds or F5 route changed. Next: decide
the caller/admission envelope and its authentic law producers, then define the
resource schedule and source/root publication bridge before any implementation
approval.

The [annotation-caller audit](../notes/progress/2026-10-10-pe-annotation-caller-audit.md)
checked whether existing `as Type` syntax can serve that caller. It cannot in
the default path: syntax retains the annotation structurally, production HIR
rejects child-bearing expression annotations and typed pattern annotations,
and no `ResolvedExpr`/solver check constructor consumes them. Shadow records
only pending typed-port/profile incidence. Thus routing Direct through `view`
would require a new source/compiler contract; an internal checker boundary
would avoid syntax changes but still would not replace F5. An independent
regression review passed after correcting one exact branch locator. No code,
tests/builds, API or source semantics changed. The caller/admission choice is
now the explicit next design decision; all independent owner/local-law and
resource work remains open.

The syntax authority audit also found no already approved annotation meaning
to activate: the direct-Rowan amendment selects CST topology and explicitly
does not change HIR/runtime meaning; the superseded AST product Draft left
expression `as Type` field selection pending. Therefore the requested `view`
mapping needs an explicit source/compiler contract if chosen; parser support
alone cannot authorize it.

Authoritative FVIEW §1.1 further keeps written annotations, inferred public
schemes and internal evidence-rich views as distinct layers. Thus an existing
`as Type` parse node cannot stand in for Direct's internal view without a
selected bridge. This reinforces the caller decision: source-level routing
needs a source/compiler contract; an internal proof checker needs a separate
producer and routing path before it can replace F5.

The CTX_FINITE sealed-packet trace now has two frozen, research-only
checkpoints: [source result-incidence construction](../notes/progress/2026-10-10-ctx-sealed-packet-construction.md)
and [bounded falsification](../notes/progress/2026-10-10-ctx-sealed-packet-falsification.md),
pushed as `0929781e8` and `d90ae4cb8`. The bounded constructor follows one
actual Result/Name source path and encodes its complete finite incidence graph
under the original request opening. The falsification pass found no
source-admitted counterexample among five mutation families; each depends on
the missing result/store boundary if promoted to a lifecycle claim. Together
they identify the first absent source supplier as outward result-interface/
bound-capture formation and actual observer/opening correspondence. They do
not prove Pack/Decode, semantic hiding, alpha transport, CTX_FINITE, or
JOINT_DEC. Both artifacts remain unreviewed evidence, not closed proof gates.
No code, tests/builds, API or F5 routing changed. Next: trace the actual owner
of the outward Result boundary and determine whether it supplies target
formation, bound capture and accessor/opening laws; preserve GUARD_COVER and
RAW_SOURCE as open CTX_FINITE prerequisites.

The IFACE_EQUIV lane now has two frozen research checkpoints:
[bounded constructor transport](../notes/progress/2026-10-10-native-pe-interface-equivariance-construction.md)
(`fcf7f26fc`) and [identity-observer falsification](../notes/progress/2026-10-10-native-pe-interface-equivariance-falsification.md)
(`523a9d661`). The construction derives structural commutation for finite
Extract/Decode/CE and Direct dispatch, conditional on a typed nominal action
and two-way covariance of every active semantic leaf. The first missing
premise is that action and exhaustive identity-read inventory; with it, the
complete `I_q[A;Delta]` input/image law is the first semantic seam. The
falsification found no counterexample to coherent transport fixing rigid
identities, and gives an admitted wrong-root operand discriminator. A bounded
default-path code map found no production PE Extract/Decode/certificate/
Direct counterpart: current inference still uses F5 Q/R routing, with the
closed-scheme decoder test-only. Independent `compiler_referee` and
`spec_auditor` reviews of the frozen construction passed with no blocking,
major, or minor findings. They certify only the stated structural commutation
and exact PE-scope boundaries; the semantic covariance premises,
implementation behavior, and aggregate gates remain unproved. The
falsification report remains bounded research evidence. No code, tests/builds,
API, or F5 routing changed. The follow-on owner map locates
`I_q[A;Delta]` at Parameter-owned `ValueInletSchema` formation. The complete
port/result image `m` is checked from an independently supplied J, carrier,
hereditary evidence and whole-image proof at their original telescope. PE
retains and decodes this data but does not prove its covariance. The scoped
Rust survey found no production counterpart for this inlet/image or its
certificate. Next: inventory every identity read in `m` and its checking
tree, then establish whether the owning local laws supply typed forward and
inverse actions; keep production correspondence and aggregate statuses open.

The follow-on source-conformance audit now resolves the graft question more
precisely. Source Generalize §5.2 does construct a deterministic whole-frame
and event/proof graft at actual source scope, while the uniform inlet retains
its complete independently checked `gamma`. Neither source grafting nor
same-tuple local-law soundness supplies the exhaustive typed forward/inverse
nominal actions and reflection required by successor §5.1. The remaining
input-image seam is an action on the entire dependent `gamma`, image and
checking derivation, preserving all proof choices and rigid registrations;
actual history/current-event binders must remain coherent. The bounded Rust
cross-check still finds no production inlet/image counterpart. This is scoped
source evidence, not a completed covariance proof. The [presentation
renaming construction](../notes/progress/2026-10-10-input-image-renaming-construction.md)
and [bounded falsification](../notes/progress/2026-10-10-input-image-renaming-falsification.md)
are now frozen and pushed as `822035a7d` and `6f9128d2b`. The construction's
`compiler_referee` and `spec_auditor` reviews passed without findings: its
pullback transports only presentation spellings over identical denoted
operands, and the changed descriptor/root action remains explicitly open.
The falsification artifact's independent `compiler_referee` and
`spec_auditor` reviews also passed without findings: its whole-image equation
is conditional on typed invertible input actions and local-rule covariance,
and its no-counterexample claim stays bounded to the inspected native cases.
No code, tests/builds, API, or F5 routing changed. Next: trace one authentic
J/hereditary local contract to its owner and establish its typed forward/inverse
action; keep IFACE_EQUIV and FRESH_LIFE open until actual local-law actions and
compiler correspondence are established.

The bounded [VCert root-action construction](../notes/progress/2026-10-10-parameter-vcert-root-action-construction.md)
and [falsification](../notes/progress/2026-10-10-parameter-vcert-root-action-falsification.md)
are now checkpointed at `cd77994de`/`5cadcf97d`; the construction's complete-record
hereditary repair is pushed at `c25b94240`. Independent reviews found no
remaining findings after repair. The selected Identity/Compose constructors
transport conditionally under typed inverse actions for every endpoint's full
VCert domain and coherent shared intermediates; no blanket covariance premise
for unrelated registry leaves is needed for this two-constructor fragment.
However, when `J.payload=A`, moving only the target root breaks Identity's
dependent typing. Coherent movement must also act on J's payload and carrier.
Hereditary transport further requires restriction squares over every retained
record field and subordinate binder, not only VCert evidence. No authentic
target-descriptor formation/action or complete-record restriction supplier was
identified here. The falsification model exposes missing ground evidence only
at a hypothetical kernel boundary; it is not an admitted source counterexample.
No code, tests/builds, APIs, or F5 routing changed. Next: inspect one authentic
descriptor/ground-evidence owner and its restriction law, and keep the root
action, full `gamma`, `IFACE_EQUIV`, `FRESH_LIFE`, source correspondence, and
implementation gates open.

The next owner census traced the selected literal `my z=0` through its actual
fixed contract `J_z=(0,p_z,Int,ground hereditary certificate,original
world/slot dependencies)` in projection construction §8. Its ground witness
and persistence over compatible events are source-selected; Name projection
restricts the same installed binding/provider at the later event. The sources
do not expose the complete ground witness telescope or a changed-descriptor
action commuting with that restriction. The default HIR/solver path only emits
scalar Int bounds and reads `SolvedValue::Int`; its bounded search found no
VCert, ground hereditary program, or RestrictIntro producer. This is scoped
absence, not a repository-wide claim. Next: recover the actual ground witness
and restriction fields from their source owners, then decide whether their
selected laws supply the full retained-record square. Keep `Int` and the
literal import rigid unless a separate typed descriptor action is established.

The follow-up source trace for `id 0` separates the local argument proof from
the missing whole-call bridge. In the selected PE boundary theory, the literal
keeps its rigid `Int` descriptor and original provider; the id frame chooses
`A_i = Int` before challenges, while the decoded fresh `u_i` is the callee's
Function root. The local `Int -> Int` result check can use the genuine ground
Identity constructor. None of this transports the literal's certificate to a
different root. The accepted `Application_N` branch instead requires a callee
Name resolving to an immutable ordinary Value formal. A published top-level id
Name is a `Published/Instance` owner, not that formal; no selected incidence
connects its publication/instance root to the branch's `d_f/R_f/r_bind`.
Application_N's `Result-N`/`ArgDelay-N` also has not been identified with
SD-NPB's `DataArg(Int)`, and SD-NPB supplies only argument/receiver boundary
judgments, not the enclosing CallMem/C0, source Call result consumer, and
suffix. Default HIR rejects Apply as unsupported and solver collection marks
it incomplete; shadow application remains unresolved. This is scoped to the
inspected native branch and default path, not a claim that all source-call
semantics are absent. Next: establish an authentic published-id Name → source
instance → decoded Function-root caller incidence, keeping the original
`J_0=DataArg(Int)` fields fixed. Complete-Call realization and any genuinely
changed argument-root action remain separate gates; no code, test, or F5 route
changed.

The [native PE-ID record-equivariance sublemma](../notes/theory/2026-10-09-native-projection-interface-equivariance.md)
is checkpointed at `776cc00e6` and passed independent `compiler_referee` and
`spec_auditor` review with no findings. It proves only dependent-record
transport, transparent extraction/forced-alias substitution, decoded
public-root record correspondence, and conditional finite Value-certificate
recognition under corresponding supplied typed inputs and actual local-law
preservation/reflection. Existing phase-constructor §6 is reused for VP
admission/production/Echo action. Opaque registry/evidence observers and
complete Function/Computation/recursive consumer laws remain unsupplied;
IFACE_EQUIV, FRESH_LIFE, PRINCIPAL and CUTOVER remain open. No production
correspondence, F5 routing, API, tests or builds changed. Next: trace the
selected closed local-law inventory for one id inlet/Delta and Value
certificate, retaining the published-id caller and complete-Call incidences
as separate open source-to-production seams.

The fixed PE-ID `view(i,q_check,Any)` / hereditary-Top Value case is now
recorded in the [actual local-law audit](../notes/progress/2026-10-09-pe-id-actual-local-laws.md)
(`3b2e53798`). Independent `compiler_referee` and `spec_auditor` reviews
passed without findings. This establishes finite schema support and a
conditional derivation for that submitted Top term with its authentic decoder,
target, and full hereditary evidence supplied. It creates no actual argument,
invocation, gamma challenge, or completed CE execution in this check; the
public Function root still retains its full inlet/source-introduction slots.
The broader operand-indexed Local/Ref/evidence catalogue, opaque identity
observers, whole-Delta completeness, changed-operand action, and production
supplier remain open. This result answers the minimal fixed query but does not
close `IFACE_EQUIV`, `FRESH_LIFE`, or cutover.

The [published-id/Application coverage audit](../notes/progress/2026-10-09-published-id-application-coverage.md)
(`0c5d80019`) also passed independent `spec_auditor` review without findings.
For a direct published `id` Name with actual `Published/Instance` provenance,
the accepted fresh `LiteralApply` branch cannot provide its required immutable
ordinary Value-formal/`ValueBind` provenance. This is only a New-branch
exclusion under the explicit resolve graph. Full `Application_N` still imports
Old emissions through `KeepEmission`, and neither an authentic old emission
nor an old-family absence theorem was found. So the source-language status of
`id 0` remains unresolved; this is not evidence of rejection. Next: locate the
actual published-instance callee Application emission at its owner, starting
with a concrete Old supplier or a separately established absence proof, while
keeping Call/result/Return realization and production correspondence separate.

The follow-up [published-id instance construction](../notes/progress/2026-10-09-published-id-source-instance-construction.md)
and [Old-family audit](../notes/progress/2026-10-09-published-id-old-family-falsification.md)
are checkpointed at `c0b0b0341` and `f394a3a1f`. Under authentic source and
local-law premises, the first constructs the actual `Published` → `Instance`
→ decoded Function-root → same-frame Name prefix, keeping `A_i=Int` and the
complete literal `J_0=DataArg(Int)` fixed. At the complete source index `j_c`,
New/LiteralApply is unavailable, so `Application_N` coverage reduces exactly
to `Old.E(j_c)` inhabitation. The bounded Old audit found neither that member
nor a source-supported absence theorem; `Initial`, `Direct`, and boundary
certificates conclude different judgments. A whole-repository token search
found only the abstract imported Old interface and research references, not an
actual tracked Old producer declaration. This does not establish global
absence or rejection. The architect review found no immediate user choice:
recover the existing Old declaration/producer interface or a typed SRC-Call
realization first; adding a direct Published/Instance New rule would be a
separate semantic expansion requiring review and approval.

The [authentic id Parameter manifest](../notes/progress/2026-10-09-id-parameter-authentic-schema-manifest.md)
is checkpointed at `2d08a5b54`. It maps all eight gamma fields and the
Parameter/telescope owners conditionally, without empty-telescope assumptions.
The first missing authentic input is a concrete source registration/component/
anchor application (`Hreg`); the complete predecessor image remains unsupplied.
A bounded default-code map confirms ordinary HIR currently rejects Apply,
collection marks it incomplete, and the opt-in shadow path emits no selected
Application certificate. F5 still handles supported Name uses by fresh Q/R
rows and structural Function constraints; that does not supply the selected
Instance/frame or public-root lifecycle. No code, tests/builds, API or F5 route
changed. The frozen [Hreg trace](../notes/progress/2026-10-09-id-registration-application-trace.md)
records two distinct attempts that leave the concrete registration action
unsupported; stop equivalent probes. The current structural path creates
DefId, parameter, lexical Name and Lambda joins, then static SCC topology, but
`yu-hir::lower_module -> lower_plan` accepts no caller JointWF and creates no
semantic registration, binder telescope, component identity or anchor
application. Next: inspect the original registration owner's complete local
constructor signature/action and one caller-context application; if that
owner contract is absent, return that exact seam for authority resolution.
Separately locate the Old module producer/eliminator declaration or a typed
realization to its existing emission fiber. The overall inference/F5 replacement,
Call/C0, H-bridge, principality, implementation and cutover gates remain open.

A bounded original-registration owner scan at `a3c7efa6a` found no selected
constructor signature/action deriving `T`, `C_src`, `q`, registration and anchor
for this source from caller-owned JointWF plus the resolved binding. The source
call owner document assigns responsibility but supplies no definition-register
constructor; selected signature packaging and inert-root installation consume
registrations rather than create this one. Current Rust `SemanticImports` is
unit-backed and `lower_module` ignores it; its branded definition/parameter
handles are structural only. This is not a repository-wide absence claim.
Next for this seam is to recover or define the exact original registration
constructor and one caller-context application before deriving any telescope.
Do not fill it with an empty telescope, SCC cardinality, or an anchor inferred
from empty captures. No DAG status or production authority changes.

The existing [id-only SourceBuild proposal](../notes/design/2026-10-08-id-sourcebuild-owner-design.md)
received independent M3 compiler-referee and spec-auditor review at
`abd388a68`; it is **not ready for production approval**. Both reviews found a
blocking missing caller-context/registration input, and the referee separately
found that adding the context alone still leaves the noncircular registration
constructor absent. Major issues also remain in schema representation,
freeze/failure policy and the context integration seam. The selected
Generalize/Parameter/Lambda meanings are preserved conditionally; no rule,
API, representation or failure policy was adopted. Next: resolve the original
registration action and one application, then repair and re-review the producer
boundary before any approval request or implementation.

The reviewed [open-context source generator](../notes/progress/2026-10-06-initial-context-source-construction.md)
was checked as a possible alternate Hreg supplier. It can preallocate source
roots and emit a whole open relation plus Lambda/parameter entry skeleton, but
its input already contains the source binder tree, its current world `C_0` is
not the validating component `C_src`, and its parameter root does not supply
the authentic UV telescope or `IF0`/anchor. Its PCInit rule also targets a
punctured Call graph, unlike standalone id. F0/SCC registration remains a
structural topology output. This route does not close Hreg; no third equivalent
premise probe or DAG status change follows.

The separate INIT_WORLD source/legacy lane located the exact importer seam at
the module loader to `yu-hir::lower_module`: syntax keeps alias spelling and
operator provenance, while HIR's import input is empty and ignored. Collection
keeps structural definition/use edges only; no external base, importer
incidence, provider/world map or zero-step root extension enters the solver.
Its bounded falsification distinguishes a closed, hole-independent import
certificate (whose action is identity under the retained substitution) from a
genuinely hole-dependent external certificate, which needs its authentic
import-owner action. No valid counterexample or new rule was supplied. INIT_WORLD
remains open at that owner and the joint root-extension/restriction proof.

The native-id ALL_VIEW lane isolates a conditional actual-export case. For a
finite native source-checked view grammar, SG inversion and PE-ID's whole
strategy/proof translation yield `Direct(u_i,R_V(v))` at the actual decoded
public root `u_i`, including Function checks and their production clauses.
This is a bounded consequence of the reviewed PE-ID theorem, not arbitrary
valid-view completeness. The aggregate ALL_VIEW formula still needs its
owner-provided `B_common`/`Q_common` formation and a proof that the active
common root is this same `u_i`; PE-ID explicitly forbids substituting an
interior identity synthesis root for a distinct common or annotation root.
ALL_VIEW, PRINCIPAL and production correspondence remain unchanged.

The follow-up common-root owner map confirms that the selected contracts do
not identify the native identity `B_common` with PE-ID's actual decoded root
`u_i`. The common-allowance proposal requires its own guarantee inventory,
allowance scope, active descriptor/admission/membership/production equations,
and direct-check certificates in `Q_common`; its totality witness is not a
solution equation. PE-ID supplies the actual `u_i` and explicitly excludes
substituting an interior synthesis root when another common or annotation root
was selected. The approved root-policy answer says adopting the common-
allowance proposal does not follow from selecting transformed public export.
No authentic native-id common-formation instance or identity bridge is
recorded. This is a genuine unresolved design/owner seam, not evidence against
the bounded `Direct(u_i, ...)` result. Do not identify the roots by convention
or implement the common-allowance construction without a separate reviewed
design and explicit approval. Next: resolve the intended common-root producer
and its relation to decoded `u_i`, then supply its actual `Q_common` checks;
ALL_VIEW and PRINCIPAL remain open.

An authority adjudication confirms q1 plus PE-ID does not identify aggregate
`B_common`/`Q_common` with `u_i` or its local formation checks. `u_i` is the
actual selected root for the bounded native export theorem; `COMMON_TOTAL` and
`ALL_VIEW` retain their existing common-allowance premises and universal view
scope. Three distinct routes remain: prove an authentic instance of the
existing common contract equal to `u_i`; develop a reviewed native-export
replacement route under the approved transformed-export direction; or retain
the bounded PE-ID result without claiming aggregate closure. No route is
selected by a name assignment, and no aggregate gate status or dependency is
changed here. Continue with the native-export replacement proof as independent
research, including its actual-root and consumer obligations. A user decision
is premature until that route and its proof consequences are concrete. The
existing common-instance route still requires its real formation records and
`Q_common`; neither `Q_common=true` nor successful `Direct` supplies them.

The first research slice for the authorized native-export replacement route
is checkpointed in [the conditional factorization derivation](../notes/progress/2026-10-09-native-export-principality-replacement-construct.md).
For native `id`, PE-ID composes with VPRES: every required independent view
would need one same-origin source-lawful whole-use presentation, a coherent
scope-respecting lift of its complete fiber, and genuine finite L proofs for
all decorated checks including independent Option 2 members. Under that
unproved bridge, the actual `u_i` export gives exact ordinary-use fiber
factorization without `B_common`/`Q_common`. Neither arbitrary-view
completeness nor the canonical PRINCIPAL gate follows.

The complementary [falsification slice](../notes/progress/2026-10-09-native-export-principality-replacement-falsification.md)
found no licensed counterexample to PE-ID's finite replay. Its fixed-result
candidate isolates a possible gap between actual-callable membership and the
complete Function-production implication, but its target import incidence,
independent validity and full actual operation law remain unlicensed; a
separate Value proof could still succeed. Treat it as a conditional
discriminator, not a source counterexample. Next: independently resolve
VPRES's same-origin source realization and semantic-to-L completeness, first
at the Fixed target's original incidence and the exact Value-inclusion
consumer. Keep COMMON_TOTAL, ALL_VIEW and PRINCIPAL statuses unchanged; no
compiler changes, tests, builds or production authority follow.

Independent compiler-referee and spec-auditor reviews of both frozen
replacement-route slices found no findings within their conditional scopes.
They validate N-Factor's fiber-map composition and the Fixed/H discriminator
under C1–C4; they do not supply VPRES, license its Fixed import incidence,
prove the required Int/J inhabitance, or establish the universal
`Valid_V`-to-Value-proof route. Next research should use the actual
`Valid_V` definition to test whether C1 can be formed at id's original
telescope and whether the same-tuple Value proof can be constructed for every
required view. Do not treat the Function-branch discriminator as a source
counterexample or expand it into a semantic rule without a licensed instance.

The bounded `Valid_V` authority audit and the Fixed-target owner/consumer
follow-ups are recorded here and checkpointed in
[the C1 capture-owner audit](../notes/progress/2026-10-09-native-export-fixed-target-c1-owner.md),
[the conditional Value bridge](../notes/progress/2026-10-09-native-export-fixed-target-value-bridge.md),
[the Force-provenance construction attempt](../notes/progress/2026-10-09-native-export-force-law-construct.md),
[its bounded falsification](../notes/progress/2026-10-09-native-export-force-law-falsification.md),
the [independent Fixed-pick target construction](../notes/progress/2026-10-09-native-export-fixed-target-independent-view-construction.md),
[the pick/id Value-comparison attempt](../notes/progress/2026-10-09-native-export-fixed-target-pick-id-value-comparison.md),
the [scope-map falsification](../notes/progress/2026-10-09-native-export-fixed-target-pick-id-scope-falsification.md),
and the [literal-1 contract construction](../notes/progress/2026-10-09-native-export-fixed-target-literal1-contract-construction.md).
The q1/d1-approved `Application_N` crosswalk is recorded in
[the N-carrier map](../notes/progress/2026-10-09-fixed-target-application-n-carrier-map.md):
for the exact `f 1` body it already constructs an N-owned argument reify/Delay
origin, argument check, and complete result/consumer ports under its whole
contract inputs. This does not identify those N origins with the selected
original Call consumer origins or pair the carrier across id/pick telescopes.
The bounded N-to-original construction attempt localizes the first missing
operand at the authentic original literal Result-node/port license, before
Delay, checking, or Call attachment; its conditional map and endpoint-tag
falsifier are recorded in
[the Result bridge attempt](../notes/progress/2026-10-09-fixed-target-n-original-result-bridge.md).
This is the `ResultLiteral` subcase of the already identified R-flat typed
original-registration/realization gate, not a separate gate; the owner scan
found no selected constructor or current Rust operation that emits the
certificate. This bounded scan does not establish repository-wide absence.
The exact minimal producer proposal is now drafted at
[the original literal Result owner candidate](../notes/theory/2026-10-09-original-literal-result-owner-extension-candidate.md)
(SHA-256 `0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924`);
both compiler-referee and spec-auditor found no BLOCKING, major, or minor
finding for its exact Draft scope. This only makes the proposal reviewable; it
does not select the rule or prove its bridge. A separate conditional
naturality audit found that authentic static registration alone does not
transport the complete N Return witness fibers across distinct incidence keys.
The exact missing Return-kernel reindexing law and discriminator are recorded
in [the incidence naturality note](../notes/progress/2026-10-09-literal-result-incidence-naturality.md).
The selected Return-kernel audit found no such supplier in the governing
clauses, and current Rust has no literal Result-port owner. The exact choice
to adopt the bounded static original registration is in the pending
[question-board entry](../questions/2026-10-09-original-literal-result-owner/question.md).
Keep only that dependent owner/consumer proof waiting; continue independent
inference and implementation-correspondence work. If selected, still prove
the Return-kernel domain, lossless witness map and action square, then extend
through original Reify/check/result incidences and separately prove the
`IF_pick`/`IF_id` carrier/event pairing.
Keep H-original-install/E-flat, `mu_adm`, `Valid_V`, Direct and ALL_VIEW open.
The approved answers specify the inlet challenge domain and independent
membership/production laws, but do not select an exhaustive `IndependentValid`
predicate or adopt proposed `V_alloc`. The source `my z=0; my pick ignored=z`
constructs a complete Fixed target at its own `IF_pick`; its root-relative map
to id's unchanged `IF_id` and same-source validity remain unproved. The
selected bare ignored-input pick inlet has the same derivation as id's inlet;
its Fixed result is a separate body premise, so Fixed itself does not restrict
admitted inputs to `J_0`.

The Value route's first unlocated premise is a raw actual subexecution
certificate for the designated Force component of every arbitrary retained U,
at the same operation witness, demand, world, incidence and dependent proof
tuple. Source Value-entry closures and declaration-backed Value operations
have raw Force decompositions, but the selected Function domain also permits
independently supplied/opaque operations whose own laws remain inputs. The
inspected L registry has no adopted arbitrary-U E_U constructor. A conditional
inversion-plus-equality schema exists if the source operation supplies that
certificate; the production-only false-result alternative is not licensed as
an actual invocation. These are bounded owner gaps, not a counterexample or
an absence theorem for all original kernels.

The Return(1) separation is still conditional. Given the actual whole local
relation, the authentic ground-literal rule plus PE-PICK constructs the
monomorphic `J_1` for `my one=1`, retaining provider `p_1` and its whole
hereditary contract. That binding is a different provider path from the literal
occurrence in `f 1`. For the latter, selected `Application_N` supplies its own
N-owned argument reify/Delay origin. The [conditional N-to-original
construction](../notes/progress/2026-10-09-n-to-original-consumer-construct.md)
separates six original operands: literal registration; complete Return,
prefix and future transport; original ReifyOrigin; emitted checking/Call
origins; output/consumer attachment; and semantic applicability. Granting the
Draft `Original-ResultLiteral` removes only the first cut. The conditional
Delay derivation still assumes the actual Return-kernel action and does not
establish source acceptance.

The [downstream action discriminator](../notes/progress/2026-10-09-n-to-original-consumer-falsification.md)
grants singleton lossless Return transport and static origins, then shows that
a hypothetical legal action swapping two N checking alternatives while fixing
the two original alternatives prevents any lossless equivariant map, despite
equal fiber sizes. The follow-up [whole-check action audit](../notes/progress/2026-10-09-whole-arg-check-action-falsification.md)
shows that this asymmetry is unlicensed when both uses faithfully retain the
same complete kernel witnesses and induced action. Shared kernel identity alone
does not prove that: dependent result constraints may select different witness
subfamilies. The [conditional reference construction](../notes/progress/2026-10-09-whole-arg-check-action-construct.md)
gives `wrap_original ∘ extract_N` and derives losslessness/naturality if both
actual references are faithful pullbacks at a fully matched operand/incidence
index. None of the notes identifies that typed reference certificate for the
actual source Call. HIR/core retain structural Apply/literal IDs and incomplete
endpoints, but no typed Result, Delay, emitted check, carrier or consumer
certificate.

The [IF-Use certificate audit](../notes/progress/2026-10-09-ifuse-wholearg-reference-certificate-audit.md)
derives faithful `wrap/extract` maps for an already supplied actual typed
reference slot and its retained evidence. It does not form the reference or
pair its complete index with N. The [kernel owner locator](../notes/progress/2026-10-09-whole-arg-kernel-owner-locator.md)
traces `WholeArgCompatible` to an abstract independent descriptor-kernel
input: N supplies a complete typed `WholeContract` schema, but no concrete
checking declaration instance, `P_arg/T_arg`, admission or action supplier is
identified along this route. This is bounded characterization, not global
absence.

A separate bounded owner trace located authentic native checked-inlet evidence:
selected native projection forms Parameter-owned `I_q` and
`GenericValueInlet(q,IF0)`; the uniform-entry constructor defines the complete
ordered `gamma` record, its whole-observation checks and actual `PackGeneric`
admission; source-directed joint decision constructs `DataArg` at the actual
Result/inert-argument owner. This narrows the next seam to the native
checked-inlet/checking owner, but does not identify that native `gamma` with an
instantiated original descriptor-kernel `WholeArgCompatible` declaration
(`alpha_arg/t_arg`, ordered `P_arg/T_arg`, domain and lawful witness action),
or pair it across N/original references. The selected Call/IF constructors
consume authentic typed declaration/reference instances and construct their
placements; they do not invent the declaration identity or the paired
substitutions. Keep the native evidence and independent descriptor input
distinct until that crosswalk is supplied.

The paired [constructive crosswalk attempt](../notes/progress/2026-10-09-gamma-to-wholearg-crosswalk-construct.md)
and [index discriminator](../notes/progress/2026-10-09-gamma-to-wholearg-crosswalk-falsification.md)
now sharpen this seam. The construction maps all eight native gamma fields to
the still-unsupplied target attribution and identifies an earlier prerequisite:
the selected `F_c` tuple has not been shown inside or outside the native
generic-inlet envelope. The discriminator shows conditionally that arbitrary
`PackGeneric` admission cannot stand in for a prechosen frame's gamma: with one
native Int carrier, the Int and Any schema tags return differently indexed
gamma records. It does not falsify a correctly indexed original-kernel bridge,
nor provide an actual `WholeArgCompatible` counterexample or declaration.
These remain conditional research checkpoints; neither changes a theorem
status or authority. The index discriminator has received independent
compiler-referee and spec-auditor reviews with no actionable findings; the
constructive crosswalk remains unreviewed. The discriminator strengthens only
the prechosen-schema-tag requirement and leaves the actual original-kernel
declaration and paired application unresolved.

A systematic bounded census across the committed design/theory/progress,
handoff and task corpus (1,139 files; questions excluded) found no actual
independent `WholeArgCompatible` declaration instance. The closest source is
the genuine native eight-field gamma/`PackGeneric` constructor; the original
Call/IF sources provide consumers and generic typed-declaration placement,
not a concrete `alpha_arg/t_arg`, ordered `P_arg/T_arg`, or paired
substitutions. A separate Rust owner census found real ordinary structural
Function compatibility decomposition in `constrain_live`, and a default-off
Apply negative-Function demand at `admit_candidate_fact`; neither retains the
selected complete descriptor declaration/reference or its carrier/action
evidence. This is bounded to the searched document corpus and inspected Rust
paths, not a repository-wide semantic absence or source rejection claim.

The [Valid_V eligibility audit](../notes/progress/2026-10-09-valid-v-fixed-target-eligibility-audit.md)
confirms that no exhaustive selected `Valid_V` constructor was found and Draft
`V_alloc` is not adopted. It distinguishes the hypothetical actual-0 H/t
carrier with a nonexecuting Return(1) from actual `f 1`'s Return(1) witness.
If the latter were lawfully paired/admitted at id, its result conflicts with
Fixed(0); that excludes this instance from the sufficient same-callable
containment-valid route, not from every possible `Valid_V` criterion. The
`IF_pick`/`IF_id` whole scope/event/admission pairing, arbitrary-U Force law,
and semantic-to-L completeness remain open. Two requested independent review
roles were unavailable because their selected models were at capacity; these
new artifacts remain unreviewed conditional research. Next: obtain one actual
independent `WholeArgCompatible` declaration package at the selected
callee/argument tuple, including ordered `P_arg/T_arg`, full domain/license/
action and whether this tuple lies in the native generic-inlet envelope. No
selected document currently supplies that package. Once its source is
identified, have the typed reference/emission owner instantiate the same
declaration at N and the original use with complete scoped operand maps,
preserving the prechosen schema tag, and extend the matching witnesses through
dependent `e_out`. Keep the pending
literal-owner decision and all aggregate gate statuses unchanged. No compiler
changes, tests, builds or production authority follow.

An independent implementation-authority audit now confirms that no production
slice is authorized independently of the open `WholeArgCompatible`/Hreg gates.
The id-only SourceBuild producer still lacks its authentic caller/registration
application, reviewed concrete representation and retention placement,
resource accounting, failure policy and explicit implementation approval. PE
frame-to-root slots still lack an approved typed supplier/slot contract and
lifetime/stale-reference policy. Native Direct still lacks a concrete caller
and admission envelope, genuine local-law suppliers, attempt schedule, numeric
limits and error/fallback policy. These are additional gates; resolving
WholeArg/Hreg alone would not authorize coding them. Preserve the existing
producer/consumer manifest and resolve the authentic id caller/source-formation
application before reopening SourceBuild implementation. No production code,
tests or authority changed; the current user decision remains pending.

A separate read-only SEED_SOURCE compiler crosswalk now pins the annotated
`apply(f: _ -> [io] _, x) = f x` cut in actual code. Ordinary HIR's
`plain_binding_header` admits only a bare binding or one bare ML parameter;
the annotated/two-parameter form becomes `UnsupportedTarget` before it gets a
definition root, so ordinary F5 never constructs its seed, annotation check or
Call upper-use demand. The default-off shadow path retains binder/annotation/
Call incidence, and emits a negative Function demand for Apply candidates, but
the seed, complete symbolic output effect, source upper-use and protection
judgment remain assumptions or pending. Closed `yu-types` Function/effect
views do not retain named `io` or source provenance. The next owning seam is
the source declaration/annotation elaborator before normalization: retain the
actual annotation, binder and Call occurrences, then derive the seed judgment
or establish that no seed applies. This is bounded code correspondence, not a
source rejection or a semantic rule. SEED_SOURCE remains OPEN-PROOF; no code,
tests, builds or authority changed.

A focused architect audit confirms that this source-owner location does not
itself authorize a production slice. The Authoritative inferred-call-view
direction explicitly withholds inference implementation authority, and the
directional-protection addendum remains a formalization without a complete
annotation seed derivation. The approved function-call-view answer already
settles that annotation absence is the source of full protection; this
annotated formal cannot use that absence constructor. The bounded
[annotation-seed inversion](../notes/progress/2026-10-09-annotated-formal-seed-inversion.md)
was independently reviewed by compiler-referee and spec-auditor with no
findings. It excludes that one origin and its conditional transports, but does
not prove no protection from every possible origin. A5/A6, actual endpoint and
Name export, and contribution/removal realization remain open. The answer also
withholds compiler implementation. Keep annotation checking, Call upper demand
and provider lower evidence as distinct incidences even when endpoints solve
equal. Next, resolve the owning source judgment's remaining origin cases and
form a reviewable implementation contract; no user decision is needed to
reselect the already approved annotation-absence branch. This does not promote
the broader SEED_SOURCE or F5-cutover gates.

The syntax/HIR audit clarifies that the displayed `apply(f: ..., x)` is
semantic shorthand, not current declaration grammar. The nearest supported
surface shape is `my apply (f: _ -> [io] _) x = f x`; recovery-free behavior
for this exact wildcard/effect variant remains unexecuted. Static grammar and
fixtures show grouped annotated formals as Pattern ML application. Production
HIR rejects that header before creating its binding/root, and its body Call
lowering is separately unsupported. Shadow HIR retains annotation and Call
identities but leaves their typed relationship pending. Current support is not
a source rejection rule. Any implementation packet must cover both
header/annotation ownership and Call-body lowering, along with the selected
seed and contribution evidence.

The bounded annotation-owner search localizes the first unsupplied semantic
operand after that surface cut: the admitted annotation derivation at formal
registration, which must produce the actual current endpoint `E_a`, complete
normalized target `T_a`, and their original dependent scope/occurrence path.
Typed-core §6 assigns the formal's outer Value role and body Name lookup, but
delegates nested annotation typing to that missing derivation. Source
Generalize retains an actual boundary and its local evidence after it exists;
it does not construct this annotated boundary. The `io` contribution map and
lawful realization, A5 original upper-use classification, and A6 seed/no-seed
evidence are downstream obligations. The native unannotated Parameter/Lambda
and `DataArg` constructors do not cover this annotated higher-order formal.
No selected constructor supplies this package; this bounded owner result does
not establish that no seed/protection applies. Keep SEED_SOURCE OPEN-PROOF and
the prior implementation-authority gate unchanged.

The repaired directional-protection section of the non-authoritative
[production Call proposal](../notes/theory/2026-10-08-production-call-elaboration-proposal.md)
has now passed focused independent compiler-referee and spec-auditor review
over §§3–5, C5/C6, and the directly relevant §7 choices, with no findings.
This closes only that proposal-delta review; it does not close C5/C6, prove
§6's reused theorems, or authorize inference implementation. The C5
[seed-to-exposure derivation](../notes/progress/2026-10-09-c5-protection-exposure-derivation.md)
is checkpointed and pushed at `6d603a095`: selected direct/captured Name Call
composition is conditional on retention, and universal source coverage still
needs `ExposureCover` over an independently formed exposure inventory. This
does not settle recursive/multi-use applicability, conflicts, or principal
refinement. The [C6 conditional derivation](../notes/progress/2026-10-09-c6-annotation-realization-derivation.md)
is checkpointed and pushed at `c88dc9551`: it separates authentic annotation
incidence from a lawful local change/frame proof, and leaves activation and
source adequacy open. Neither permission nor a direct boundary check supplies
the missing realization producer. Both research notes are unreviewed,
conditional checkpoints; no production implementation, tests, builds,
authority or aggregate gate status changed. Next evidence must come from the
owning annotation/source constructors or an authentic production bridge, not
from relabeling supplied evidence. Keep the source/solver production gate and
all aggregate statuses unchanged.

The bounded C6 [activation falsification](../notes/progress/2026-10-09-c6-activation-falsification.md)
is checkpointed and pushed at `f564114b6`. It finds only one conditional
separator: a realized annotated contribution with a nonempty independently
lawful release but no eligible live handling opportunity. No accepted-source
derivation for that state, nor a typed observation that distinguishes the
release, was found. The proposed guards therefore remain unselected, but this
does not yet justify asking the user to choose between complete observable
semantics.

A further read-only code map narrows the actual source/solver seam: parser
syntax nodes retain grouped annotations (`crates/yu-syntax/src/pattern/mod.rs`),
but ordinary `HirParameter` in `crates/yu-hir/src/module.rs` stores only
id/name/range, and `parameter_recipes` in `crates/yu-solver/src/lib.rs` retains
only the parameter id. The live Value row and Function fact are built on the
unannotated Parameter→Lambda route. The first missing admitted operand is the
annotated formal derivation carrying actual current endpoint `E_a`, complete
normalized target `T_a`, and original scope/occurrence correspondence. Typed
contribution incidence, lawful local realization, and C5 seed/exposure remain
later obligations. No compiler slice is authorized by this mapping or the C5/C6
checkpoints; keep the production and cutover gates open.

The historical annotation route is separate from current-branch F5. On this
branch, `plain_binding_header` in `crates/yu-hir/src/lib.rs` rejects grouped
annotations and ordinary `ResolvedExpr` lowering does not admit body Apply,
so there is no current F5 annotated-formal removal path. Frozen `main` at
`a58eefc31e22141574b6f20c6a5748151c6d79f1` contains the older Oracle route:
`crates/infer/src/annotation/constraints.rs` connects an
`AnnType::Function` with `[io]` at `ret_eff`;
`crates/infer/src/lowering/expr/lambda.rs` builds family/depth stack predicates,
`crates/infer/src/lowering/expr/tail.rs::make_app_with_origins`
applies formal call predicates, and `crates/poly/src/expr.rs::ArgEffectContract`
records family path/depth markers. Those markers do
not retain the selected C6 annotation-to-contribution incidence or lawful
local removal witness, and historical stack behavior is not semantic authority.
The [same-family position analysis](../notes/progress/2026-10-09-same-family-annotation-position-counterexample.md)
is checkpointed and pushed at `7264d77cc`: the old DefId-keyed sidecar maps
`F(A,io,0,B)` and `F(A,0,io,B)` to the same family/depth marker, losing
position and multiplicity (and never recording provider or scope). This is
non-injectivity of that projection only; the richer historical constraint
lowering keeps `arg_eff` and `ret_eff` separate, and no accepted source
behavior or complete Oracle impossibility follows. The next useful bridge is
an authentic annotation constructor certificate for the original `ret_eff`
occurrence/provider/scope and direct boundary, plus separate frame evidence
for an unrelated same-family contribution. No runtime/test behavior was
executed, and no compatibility or implementation approval follows.

The [annotated-formal owner-to-consumer draft](../notes/theory/2026-10-09-annotated-formal-constructor-draft.md)
now records the conditional constructor contract for one annotated higher-order
formal and one direct body Call. Independent compiler-referee and spec-auditor
reviews found no actionable findings. It keeps normalization, authentic
contribution incidence, lawful realization/frame, A5/A6 exposure, transport,
principality, and production correspondence as explicit missing producer or
aggregate gates; it grants no implementation authority. The draft is pushed
at `0ba3e85ba`. Next evidence must supply an authentic owner judgment for the
annotation boundary and typed contribution correspondence, or a direct
source/artifact bridge for those judgments. Do not infer them from the draft's
candidate logical vocabulary or the frozen-main Oracle. C5/C6, production
membership/admission, and F5 cutover remain open; no tests or builds ran.

An independent architecture cut of the `my id x=x` Hreg seam confirms that
the existing selected chain does not provide a noncircular original
registration constructor/application from caller-owned `JointWF` and resolved
source. This is a missing definition, not yet evidence that user selection is
required: the approved source-Generalize/native-projection contracts allow a
legitimate constructor completion that preserves their meanings. The
unselected ownership candidates are source-owned registration from the
authentic caller context, or a caller-supplied complete registration package;
the second only moves the gap unless an actual caller producer is identified.
Neither changes Parameter/Lambda meaning or authorizes production routing.
Registration must precede Parameter `Desc` and Lambda `U_g`; requiring the
completed `U_g` as its own input would be circular. Stop equivalent absence
searches. The next useful Hreg evidence is one noncircular owner rule and a
real caller-context application retaining all original guards, binder
incidences and anchor provenance. Do not ask the user to choose between these
ownership descriptions until a concrete derivation or an observably distinct
contract is available. The pending literal-Result owner decision and other
independent proof/conformance lanes are unaffected; all aggregate gates and
F5 cutover remain open.

The reviewed [Hreg constructor attempt](../notes/progress/2026-10-09-hreg-source-owned-constructor-attempt.md)
now tries that constructive step directly. It gives a noncircular proposed
order—source reservation and pre-Parameter registration/IF0, then Parameter
Desc/inlet, Lambda U_g, and the authentic anchor—but does not claim any arrow
whose local law is missing. Independent compiler-referee and spec-auditor
reviews found no actionable findings. The actual application still stops at
the original definition/source-port introduction schema: its ordered
dependency telescope and independently derived formation/license/scope/
registry/incidence guards have no supplied owner constructor. A one-atom
extension discriminator confirms only that caller JointWF plus fresh IDs
cannot prove an unspecified new guard; it is not a Yulang counterexample.
Next evidence must construct and apply that local schema from an authentic
caller context, or establish the precise authority conflict that needs a user
decision. No further general absence search is useful. The proof and
production correspondence gates, and F5 cutover, remain open; no code, tests
or builds changed.

The follow-up [local scope/port construction](../notes/progress/2026-10-09-hreg-local-scope-port-schema-attempt.md)
narrows the owner again. Selected Signature-Incidence injections preserve a
complete dependent port and guard package once an actual typed local port is
supplied; `LocalOrigin` and `Op` consume its original introduction, typing and
license. Uniform Value Entry assigns the designated one-layer port and its
Intrinsic evidence to actual Parameter formation. Therefore the previous
pre-Parameter registration/IF0 ordering remains only a candidate recipe: its
field split cannot move Parameter-owned Intrinsic evidence earlier without a
new derived phase. Independent compiler-referee and spec-auditor reviews found
no actionable findings in this bounded characterization. The exact unresolved
input is now one authentic Parameter-local port/scope introduction at the
caller insertion site, with its ordered dependency telescope and complete
guard presentation; neither caller JointWF nor structural support supplies it.
No specific guard atom or actual caller application was produced. Next work
must construct that local owner rule and apply it once, without another
assumed-rule or broad absence probe. Commit `5e64fc6be` preserves this result;
Hreg, all aggregate gates, implementation authorization and F5 cutover remain
open.

The reviewed [forward Parameter-introduction attempt](../notes/progress/2026-10-09-hreg-parameter-introduction-rule-attempt.md)
starts from a fully parameterized authentic caller context and resolved
`my id x=x` occurrences, then attempts to apply the actual Parameter rule.
It stops at the missing source-binder/scope-introduction owner law, before
Parameter Desc or inlet evidence; it produces no concrete caller application
or user decision. Independent compiler-referee and spec-auditor reviews found
no actionable findings and confirm this adds no gate progress beyond the
prior owner cut. Treat this as the final bounded Hreg application attempt for
the current inputs: do not repeat equivalent Hreg derivations. Resume only
when an authentic source-binder/scope owner rule or concrete caller
registration is available, or when new evidence establishes a real authority
conflict. Continue an independent inference lane meanwhile. Hreg, all
aggregate gates, implementation authorization and F5 cutover remain open; no
tests or builds ran. Commit `39ee3b64e` preserves the attempt.

The reviewed [PE-ID changed-root owner crosswalk](../notes/progress/2026-10-09-pe-id-changed-operand-owner-crosswalk.md)
uses the selected fresh ordinary root `u_i` and its Top/Direct Value client as
the consumer discriminator. Independent compiler-referee and spec-auditor
reviews found no actionable findings. The selected PE decoder supplies the
semantic root equations, while current F5 fresh rows and scheme handles do
not supply their complete interpreted root, whole-frame action, original
scopes or local-law evidence. This is a bounded source-to-Rust correspondence
gap, not a claim of semantic rejection. The next PE-ID step is an exact
constructor-owned manifest from authentic `ProjectionExport` and whole-frame
inputs to each active `u_i` field and its owner; do not start by adapting a Q/R
row. No implementation authority or gate promotion follows. Commit
`9d4d74b06` preserves the crosswalk.

The reviewed [Fixed-target owner audit](../notes/progress/2026-10-09-native-export-fixed-target-owner-audit.md)
finds that PE-PICK's authentic `z=0` capture and ReadCert supply Fixed(J_0) at
pick's original telescope, and Call Input Realization supplies the same-
binding Name Delay Return law for an authentic argument. The cross-id
application still lacks formation/grafting of that fixed capture telescope
onto id's empty-capture interface; only after that earlier judgment is
supplied could a specialized L.Value inclusion proof be built for Direct.
Independent compiler-referee and spec-auditor reviews found no actionable
findings. This neither rejects the candidate nor closes PE-ID, PE-PICK,
ALL_VIEW, PRINCIPAL, production correspondence or F5 cutover. The next action
is to obtain the owner judgment for that target-formation graft, then only if
it exists attempt the scoped finite inclusion. Commits `9d4d74b06` and
`e4f8e6881` preserve these checkpoints; no tests or builds ran.

The reviewed [integrated id-to-Direct bridge](../notes/progress/2026-10-09-integrated-id-source-to-direct-bridge.md)
joins one conditional unannotated `my id x=x; my alias=id` source path across
Source Generalize, polymorphic Name `Instance`, monomorphic rebind, PE export
and decode, and the approved Direct consumer direction. Independent
compiler-referee and spec-auditor reviews found no actionable findings. It
derives only a conditional checker consequence for a supplied scoped
hereditary Top proof; it does not establish inference acceptance. Current HIR
and F5 produce structural names, a Lambda recipe, scalar Q/R freshening and
constraint comparisons, while source owner records, whole-root decoding,
alias-publication correspondence, finite proof production and inference
caller wiring remain absent from the inspected route. Hreg is still the first
source-record premise. Continue by connecting authentic Instance/rebind/root
outputs to an actual source inference caller; do not count checker approval
as F5 replacement. Commit `51ba6b85b` preserves this checkpoint. No
production code, tests or builds changed.

The bounded [native caller/resource-schedule cut](../notes/progress/2026-10-10-native-caller-resource-schedule-cut.md)
narrows that caller task: SRC §3.4 `view(h,q,V)` annotates an actual source
checking rule and is not itself an executable operation; published `id` plus
monomorphic alias does not supply that checking occurrence. The inspected
default path still has no established semantic annotation elaborator,
ordinary PE-root store or Direct consumer. Consequently the caller's
retry/retention schedule is also missing, so numeric work/byte caps cannot be
selected from the conditional Python checker or F5 counters. Static
counterexamples show
dependency tuple length, payload bytes and repeated calls are separate budget
dimensions. The reviewed [annotation-to-Direct owner crosswalk](../notes/progress/2026-10-10-as-boundary-direct-crosswalk.md)
confirms approved expression `as Type` supplies an authentic source check
occurrence `q`, correcting the broader caller wording in the prior note. The
actual HIR path still rejects that expression before solver constraints; its
source target/current endpoint are not mapped to Direct's complete ordinary
roots and proof. The compiler-referee and spec-auditor reviews closed with no
remaining findings after one minor HIR owner-locator correction. This remains
non-authoritative research: no semantic or implementation gate changed. Next
action is to establish one authentic occurrence's source `TypeExpression`
elaboration into an ordinary typed target in its original scope, alongside an
already available endpoint/root and prior-plus-local evidence. The current
HIR/shadow/F5 scheme path has no such source elaborator; see the
[annotation target elaboration owner gap](../notes/progress/2026-10-10-annotation-target-elaboration-owner-gap.md).
The `id as Any` discriminator sharpens this: the existing negative `Top`
constructors are not ordinary `Any` target-root records, and PE's conditional
Top proof assumes that exact root already exists. Establish the source target
and ordinary-root owners first. The architecture choice is now recorded in
[question q1](../questions/2026-10-10-source-annotation-typed-root-bridge/question.md),
independently reviewed by compiler-referee and spec-auditor; its answer is
pending and the directory remains uncommitted. No production implementation
is authorized by the existing annotation/Direct answers. Continue independent
inference lanes while that choice is pending, and preserve the Hreg no-repeat
stop. No tests, builds, benchmarks or mutation probes ran.

An independent [INIT_WORLD closed-import and Rust-seam pass](../notes/progress/2026-10-09-init-world-closed-import-factor-and-rust-seam.md)
now proves only a conditional fixed-support result: an external certificate is
filling-invariant when all semantic dependencies and original incidences are
fixed. It does not construct the joint initial world or discharge the
zero-step root-extension obligation. Adversarial cases rule out treating
hole-dependent imports as fixed, admitting them through checked-hole
membership, or inferring inhabitation from a puncture/receipt. The bounded code
map finds production import syntax but no semantic-import input beyond
`SemanticImports::empty()`; the authoritative first HIR slice intentionally
keeps that boundary. Compiler-referee and spec-auditor reviews found no
actionable findings. `INIT_WORLD` remains OPEN-SEMANTIC. Next evidence is the
noncircular root-extension introduction and old-tuple restriction, with one
scalar install, a source-open alias, and a hole-dependent external import.
No tests, builds, probes, or measurements ran.

The reviewed [INIT_WORLD zero-step extension attempt](../notes/progress/2026-10-09-init-world-zero-step-extension-attempt.md)
narrows this to generic importer-incidence joint extension plus old-tuple
restriction. Existing Lemma W, `PhiW`/inert registration, captured-closure
Step, and Name/capture constructions provide selected partial suppliers, but
none establishes arbitrary cross-world import merging. `PhiW` foreign-store
application additionally requires an evidence-preserving embedding and
exhaustive guard correspondence. Compiler-referee found no findings;
spec-auditor's one minor wording finding is repaired. `INIT_WORLD` remains
OPEN-SEMANTIC. No tests, builds, probes, or measurements ran.

The bounded [scalar PhiW importer derivation](../notes/progress/2026-10-10-initworld-phiw-import-construct.md)
now instantiates the selected fixed-point constructor at one original fiber
and event. Given complete importer-indexed scalar `V*` evidence plus all
immediate joint guards and witness agreement, it derives the extended world
while preserving the supplied base certificate and a structural old-record
projection. An independent compiler-referee review passed without findings.
The follow-up [Imp_Delta index/amalgamation audit](../notes/progress/2026-10-10-initworld-impdelta-amalgam-attempt.md)
finds that `Imp_Delta(rho,C_ext;xi,w_imp)` may provide imported evidence, but
the selected sections do not map its configuration/event/incidence to
`C0,e0,i`. Even granting that map, the union with the old base needs joint
amalgamation guards and a separate clause-preserving `pi_B` deletion action.
The import interpretation could supply these actions; none is selected or
shown by its displayed signature. The audit's first draft over-narrowed the
scalar membership path to `Ground`; its repair now records the fixed-external
leaf alternative and states that PhiV consumes complete leaf evidence before
yielding `V*`. Compiler-referee review passed after both wording repairs, with
no remaining findings in the conditional scope. `INIT_WORLD` remains
OPEN-SEMANTIC; no implementation or source rule is selected. No tests,
builds, probes, or measurements ran.

The [OpenImportExt-0 regional extension candidate](../notes/theory/2026-10-08-open-import-root-extension-candidate.md)
has now received compiler-referee and spec-auditor review. The conditional
amalgamation argument has no blocking or major finding; the compiler-referee's
minor direction ambiguity is repaired by spelling out the required
old-world/import/frontier-to-EnvStore-and-JointWF introduction implication.
The spec audit still blocks semantic adoption: the actual importer has no
concrete independent `P_kappa`, exhaustive clause package, fixed-semantic IDs,
or adjudicated status as a derived theorem versus a new definition. Treat the
candidate as a reviewed research method and supplier boundary only. Do not ask
for adoption or claim INIT_WORLD closure until that concrete package exists.
Continue an independent inference lane; no tests, builds, probes, or
measurements ran.

The bounded [ProjectionExport-to-Rust owner manifest](../notes/progress/2026-10-10-projection-export-rust-owner-manifest.md)
confirms PE already supplies the semantic `ProjectionExport` to fresh ordinary
`u_i` constructor, its seven active root equations, one whole-frame action and
alias reuse. The nearest current Rust path instead ends in `ClosedValueScheme`
plus Q/R fresh-row substitution and a scalar `root_value_for` query; it does
not own the selected export package or interpreted root fields. Spec and
regression reviews found no blocking finding; the sole minor correction now
distinguishes the scheme's arena identity from the arena storage owned by
`SolvedModule`. This is a bounded correspondence artifact, not a missing
abstract export-equivalence theorem or implementation authority. Authentic
caller registration, local-law instances and a legal whole-frame action remain
unsupplied in the manifest; no code, tests, builds or DAG status changed.

The Hreg architect audit confirms that the selected source rules provide
Parameter/Lambda constructors and complete signature-incidence packaging, but
no noncircular local-registration rule plus its application for `my id x=x`.
It finds no demonstrated semantic difference between source-owner extension
and a caller-supplied complete registration package, so this is not yet a user
choice. The next evidence is one explicit local introduction rule applied in
an authentic caller context, retaining the full predecessor telescope and
guards, followed by the selected Parameter/Lambda constructors. Do not derive
Hreg from completed `U_g`, HIR IDs, or empty captures. Hreg and all production
and F5 cutover gates remain open.

## User priority correction (2026-10-09)

The user directed that practical, running type inference take priority over
proof-system completeness. Continue toward the full inference/F5 replacement
objective; do not make stronger characterization the default critical path
when a correct ordinary inference slice can proceed without it. This priority
does not authorize dropping selected call effects, protection, admission, or
other observable contract fields. The proposed default `f 1` scalar projection
still omits selected role/protection/admission evidence, so its production
admission remains undecided; do not treat successful endpoint solving alone
as a complete call judgment. No production implementation or F5 cutover gate
is closed by this priority correction.

The user then selected the complete-contract route for `f 1`, rejecting the
four-port approximation. The reviewed native literal argument construction
now supplies an original `WholeArgCompatible` occurrence and a successful
complete-inlet check for literal `0` at `id`'s actual Int/empty-residual frame.
This is useful argument-side evidence, not the full `f 1` Call: the authentic
complete Call formation/result contract, pre-comparison demand tied to the
formal's inlet and role, C5 refinement/protection, and production HIR/solver
publication remain open. The current shadow candidate still drops operand
effects and uses an empty call effect; it cannot be promoted. Continue from the
selected native literal case toward the missing complete source Call owner and
its executable inference path. No code, tests, or cutover authority follows
from the user's direction alone.

The bounded [practical complete-Application candidate](../notes/progress/2026-10-09-practical-complete-application-inference-candidate.md)
now maps the conditional source collection, complete contract ownership,
solving, generalization and publication path for the selected ordinary `f 1`
case. Independent semantic and exact-conformance reviews found no blocking or
major issue; the semantic review's minor ordering ambiguity was repaired by
making source-produced protection/refinement evidence an input to solving.
This remains a research candidate with explicit H1–H6 suppliers, not a solved
implementation gate. The immediate code-facing gap remains the executable
source Call collector that ties the formal's pre-comparison demand to its
actual complete inlet, role/protection and complete result. Literal-1
refinement, full solve and invoke export/principality also remain open. No code,
tests or builds ran for this record/candidate review.

## Application and annotation status after question-board integration (2026-10-10)

The user selected **complete contract** for `f 1`; this rules out promoting the
four-port approximation as the success criterion. Preserve the actual role,
entry, protection, admission, complete operation/result and source evidence
through solving and publication. This direction is a product constraint, not
implementation approval or proof-system completeness work.

The approved [Original-ResultLiteral answer](../questions/2026-10-09-original-literal-result-owner/approved-answer.md)
selects the original literal Result formation case for the `Application_N`
Name/Int seam, including Data_orig and Result-port registration. It does not
provide the emitted original Gen-Call-0 record, O0/O1 protection application,
complete kernel interpretation, solver or publication. The prior native
WholeArg instance attempt therefore needs a status correction: literal Result
formation is selected now, while pairing it with N's actual literal-1 Call and
an original registered declaration/reference remains open. Do not alias native
Gamma to the independently interpreted original WholeArg contract.

The approved [source annotation answer](../questions/2026-10-10-source-annotation-typed-root-bridge/approved-answer.md)
selects source-owned expression annotation formation with conditional Direct
consumption, including the ordinary Any target-root case. It authorizes a
detailed design only. Type-name resolution, a fully typed ordinary Any root and
its Top membership law, production routing, failure/resource behavior and
implementation remain open. Keep this lane separate from complete Call work.

Current `f 1` blocker: construct the source-owned complete Call record and
identify the executable original-kernel consumer, preserving the literal
coordinate, formal's actual inlet/role/protection, complete result contract and
all origins. Then close the scoped complete solve and public-root path. The
reviewed Application candidate remains conditional research; no production
code, tests, builds or F5 cutover were authorized or changed by these answers.
No tests or builds ran during this record synchronization.

The bounded [literal Call emission candidate](../notes/theory/2026-10-10-original-literal-call-emission-extension-candidate.md)
has passed independent compiler-referee and spec-auditor review after repair.
It identifies the exact existing Name/Name Gen-Call-0 boundary and proposes a
tagged literal-origin emission definition direction with a future O0 extension.
The artifact does not yet define or prove the actual typed constructor/O0
object, and it claims no new emitted membership or implementation authority.
The approved `original-literal-call-emission/q1/d1` answer selects Option 1:
continue into a construction gate for the exact tagged literal-origin source
emission judgment, its typed field producers, whole-action/old-family
conservation and a local O0 extension. This is direction approval only. It does
not adopt emitted membership or complete O0, authorize implementation or
acceptance of `f 1`, or close O1, kernel correspondence, C0/admission, solving,
publication or F5 cutover. The literal emission gate is active again; keep
those downstream gates open. The question bundle was integrated in commit
`885e35264`; validation and scope are in its [receipt](../questions/2026-10-10-original-literal-call-emission/receipt.md).
The candidate's M2 review convergence used one compiler-referee and one
spec-auditor, with one batched repair. No tests or builds ran.

The first construction attempt and independent inversion attack are checkpointed
in [the conditional constructor ledger](../notes/theory/2026-10-10-original-literal-call-emission-construction-attempt.md)
and [the origin-cycle falsification](../notes/progress/2026-10-10-literal-call-emission-falsification.md),
commits `bb5fdbe7d` and `126be49ca`. Under explicitly imported original
Reg/Route, primitive and Return contracts, Original-ResultLiteral supplies the
literal child's Data/Result prefix. Carrier-Delay still needs a Call-owned
original argument-Reify origin and its complete literal code-to-carrier
domain/license/action attachment; Code-Call cannot produce that input by
inverting itself. This was a bounded supplier cut, not a rejection of `f 1` or
an impossibility claim.

The follow-up source inversion found a positive, narrower case: selected
MIN-ORIG-WHOLEARG §4.1 constructs its native Call-owned argument registration
before DataArg assembly and inlet checking. Its unreviewed extraction and
independent portability attack are recorded in [the native registration
extraction](../notes/theory/2026-10-10-native-argument-registration-extraction.md)
and [the exact-view discriminator](../notes/progress/2026-10-10-native-reify-portability-falsification.md),
commits `04beeef66` and `0946e42b8`. That native id/literal-0 construction does
not yet establish a generic formal/literal-1 producer or attach the same
literal ReturnImage to the independent Delay domain. Matching `Comp(empty,Int)`
is insufficient to substitute its DataArg complete view for that image. The
approved [Call argument-Reify owner answer](../questions/2026-10-10-original-call-argument-reify-owner/approved-answer.md)
selects a bounded source-rule design/construction gate for the original Call
owner, with ordinary Value formal plus integer literal as its first case. Its
[receipt](../questions/2026-10-10-original-call-argument-reify-owner/receipt.md)
records validation and scope. The design must retain exact Call/argument/code/
scope/environment/registry indices, attach the same complete ReturnImage to
the independent Delay domain, and preserve existing registry entries, licenses
and whole actions. This answer does not adopt emitted membership or O0/O1,
accept `f 1`, authorize compiler implementation, solving, publication or F5
cutover. The bounded [Call argument-Reify source-rule candidate](../notes/theory/2026-10-10-original-call-argument-reify-source-rule-candidate.md)
now has one compiler-referee review and a focused delta review; the initial
major finding on old active-license preservation was repaired in
`fc564e68f`. The candidate preserves the full Call contract and remains a
non-authoritative conditional design. Its explicit `H_oldext` premise is not
discharged by the conditional countermodel: the authentic registry supplier
must establish old guard/domain/license preservation through extension and its
whole action. The independent Delay input/license/complete ReturnImage
attachment and original source-introduction interpretation also remain
unsupplied. Next, locate those actual owners and determine whether they apply
to this literal Call before requesting adoption or implementation authority.
Emitted membership/O0/O1, acceptance of `f 1`, solving, publication and F5
cutover remain open; no code, tests or builds changed.

The three supplier audits are now checkpointed separately:
[old-license extension](../notes/progress/2026-10-10-call-reify-old-license-supplier-audit.md),
[independent Delay attachment](../notes/progress/2026-10-10-call-reify-delay-supplier-audit.md),
and [original source introduction](../notes/progress/2026-10-10-call-reify-original-intro-audit.md).
They identify authentic nearby owners but no selected constructor for this
exact formal/literal-1 tuple. Native SIG licenses replay conditionally from
retained Whole/primitive evidence; immutable-world Lemma W applies to compatible
event extension, not the static registry insertion; IF-Insert and Carrier-Delay
consume registrations/origins already supplied. The Delay consumer interprets
an already licensed origin but exposes no operation from literal Result
license plus staged incidence to an independent Delay license and complete
`J_a` attachment. The subsequent [actual-registry audit](../notes/progress/2026-10-10-call-reify-actual-registry-manifest.md)
locates an earlier cut: `P` itself remains a supplied input in the inspected
selected sources, so no actual lookup branch or old-consumer manifest can yet be
instantiated. A separate local board question,
`questions/2026-10-10-call-reify-registry-construction/q1/question.md`, asks
whether to expand the bounded design gate upstream to this registry constructor.
That whole question directory is pending and must remain unstaged and
uncommitted. Until an approved direction and actual owner evidence exist, keep
implementation blocked without changing Call semantics.
The tagged emission, full old-family conservation and local O0 remain
conditional; O1/SeedExposure, original kernel realization, C0/admission,
complete solving, publication and F5 cutover remain open. No implementation,
tests or builds ran.

New evidence arrived in upstream commit `7b723269c`: the independently
reviewed [Call Reify constructor proof](../notes/theory/2026-10-10-original-call-reify-constructor-proof.md)
and its [review record](../notes/progress/2026-10-10-literal-constructor-proof-review.md).
The proof repairs the old-image domain overclaim and constructs a typed tagged
extension plus a distinct source-owned `J_lit`, while retaining arbitrary old
image packages. Its four construction choices remain unadopted. It takes
`P_old` as input, so it does not construct the actual selected-source registry
or discharge q1's authentic registry/consumer question; it also does not prove
complete Call emission/O0/O1 or authorize implementation. The user's explicit
「完全契約で」 fixes the complete Call contract and rules out four-port solving
as the success criterion. A linked pending [q2](../questions/2026-10-10-call-reify-registry-construction/q2/question.md)
asks whether to adopt the reviewed tagged construction as the next bounded
design gate or retain it as research while continuing actual-source registry
investigation. q1 remains preserved and pending; neither question bundle is
committed. Complete-Call implementation and acceptance remain blocked pending
the scoped design and source-owner decisions.

The approved annotation q1/d1's next design slice is recorded in the
[one-case Any annotation design](../notes/theory/2026-10-10-source-owned-annotation-any-design.md).
It assigns ownership from the literal's current Int root and prior evidence,
through written-Type and ordinary Any-root formation, to proof-only Top/Direct
checking and publication of Any with accumulated evidence. Both independent
M2 reviews closed without blocking/major findings; one minor attribution was
repaired and both delta reviews closed. Source parse acceptance, typed Any
root production, name resolution and exact Top-law supplier remain explicitly
conditional inputs. This is detailed design only: no code, tests, builds,
production routing, failure/resource policy, API or F5 cutover is authorized.
The literal-emission direction decision is integrated; its receipt and current
construction status remain tracked under the selected complete-Application
gate. No pending question bundle remains from this decision.

The approved annotation design's one-case owner audit is checkpointed in
[the scoped Any-root construction attempt](../notes/theory/2026-10-10-source-annotation-any-root-construction-attempt.md),
commit `1c185235c`. Source grammar clauses admit `0 as Any` in the ordinary
binding-body context, but this is not an executed parse or semantic Any
resolution. Associated HIR retains the annotation kind/range and completed
operand, while the written TypeExpression remains only in CST; ordinary
lowering rejects the annotation shape before solver collection. No selected
constructor supplies the actual ordinary Any target root. The next annotation
owner is a scoped written-Type resolution and complete Value(Any) root with
its genuine source incidence and full membership/Top-law dependencies. This
remains inside the approved detailed-design scope; no implementation,
production Direct route or F5 cutover is authorized. No tests or builds ran.

The follow-up code-owner map confirms the operational cut: syntax/HIR retain
the annotation occurrence, but `ResolvedExpr` has no annotation case and
`lower_simple_chain` rejects it before solver collection; the closed positive
scheme grammar has no ordinary Any root constructor. The selected source rules
also do not supply a written-Type resolver or Any builtin. The bounded
[resolution-owner audit](../notes/progress/2026-10-10-source-annotation-any-resolution-owner-audit.md)
and the approved [one-case design](../notes/theory/2026-10-10-source-owned-annotation-any-design.md)
leave this as a genuine scoped name-introduction decision. Pending board
question [source-annotation-any-name-resolution/q1](../questions/2026-10-10-source-annotation-any-name-resolution/q1/question.md)
asks whether `Any` is a built-in Type name or
must resolve through an ordinary scoped declaration/import. The question does
not settle the Any membership relation or authorize implementation. The
independent HIR/root mapping found no existing constructor to bypass that
decision; no tests, builds or code changes ran.

### Reviewed constructive literal argument rule (2026-10-10)

The concentrated proof attack checkpointed the [source-owned Reify and
literal image construction](../notes/theory/2026-10-10-original-call-reify-constructor-proof.md)
and [independent review record](../notes/progress/2026-10-10-literal-constructor-proof-review.md)
at `7b723269c4d9dcefbb9bd740113e5f26111cbb3f`, pushed to this branch.
This is a completed mathematical construction in a precisely defined,
unadopted extension.

Actual ChildCode, source-edge and original reference/license derivations
construct the Call-owned registration, explicit structural license and Reify
origin before Delay/checking/emission. The complete old image is copied with
its original dependent telescope and alternatives. Independently typed code
events form a new literal image J_lit, with structural Return/prefix clauses
and an indexed old-image branch. Original live Force/Return/primitive laws
prove CarrierMem† at the original R view and full SourceImageCarrier_J_lit
for the actual literal on every independent ambient demand, including future
events. No comparison success, native gamma or C0 supplies the origin.

The mathematical review rejected an earlier universal exact-old-image claim;
the repaired theorem retains the two-event countermodel and does not rename
that claim as a premise. J_lit is distinct from the fixed old J. Likewise the
registry interpretation retains P_old as its original context parameter and
adds separately typed new maps. It proves full old guard/domain/license
identity in that new interpretation, not H_oldext for an enlarged original
registry or generation of P_old from an empty lexical context. The selected
native id/0/DataArg case remains unchanged at its own Keep indices.

Both independent fresh mathematical and specification delta reviews passed.
The four exact new choices (tagged registry, structural argument license,
suspension attachment, literal domain/clause/root) remain unadopted. Fixed
original registry/image/consumer correspondence, complete Call/C0/admission,
effective inference/publication and F5 retain their exact existing scope.
The canonical DAG is unchanged. Only proof/review/navigation Markdown changed;
no production implementation, tests, builds or executable semantic checks ran.

### Reviewed literal emission and complete L collection (2026-10-10)

The second independent proof checkpoint is
`c0d304113322d149acd017db2455f263e265b3e5`, pushed after following remote to
`111da7c6e882bf6048fb4013ab93781160983fb6`. The
[emission and collection construction](../notes/theory/2026-10-10-literal-emission-pipeline-proof.md)
and [review record](../notes/progress/2026-10-10-literal-constructor-proof-review.md)
prove total static construction for the actual `my invoke f = f 1` spine in
an explicitly defined L extension, relative to the retained original context
and genuine local declarations. They construct the Call-owned argument,
complete demand and distinct checking occurrence, predicate declarations,
full operation interface, result/effect ports, role/protection origins,
Application Code, result Reify and its genuine source Computation row, one-layer
consumer, sealed tagged emission, complete IF placement and local O0.

The initial specification review rejected a purported original generic
`TypedCallCert_Dec` declaration. One fresh repair pass replaces that assertion
with new concrete argument-compatibility, structural/old-operator, result-
inclusion and nine-row `CertCall_L` declarations. The repaired artifact passed
fresh independent mathematical and specification reviews with no findings.
Semantic checking and certificate witnesses are outputs of solving the formed
constraint family, not premises of static emission or its declaration formation.

Theorem 5 proves finite ordered collection and exact evidence extraction/
reconstruction for the DEFINED `RuleCall_L` fiber. Same-carrier checking,
complete image alternatives, independent admission, actual-provider phases,
pending/raw resumption and output-dependent futures retain their full dependent
types and witness choices. Old operator arms retain their original event/frame
indices rather than being cast to the literal structural frame. Old source
families retain their exact P_old interpretation; total new-to-old equivalence
is not asserted. No N evidence is cast into an original certificate.

These completed local theorems remove supplied Reify/license/completed-emission
and unavailable generic-certificate inputs from the NEW static construction.
They do not identify its new image or checking/certificate family with a
fixed-original literal consumer. Actual old-registry bootstrap, that consumer
correspondence and eligible L-rule/local-law registration for Generalize are
not proved. The exact new semantics remain unadopted; the pending registry
questions are not treated as approvals. No stronger optional research property
is added as a mandatory implementation premise by this checkpoint.

Full CallMem/C0, JOINT_DEC, solving, principality, transformed public export,
publication and production correspondence retain their existing scope. The
canonical DAG is byte-for-byte unchanged. Only proof/review/navigation Markdown
changed. Verification covers independent mathematical/specification review,
direct source hashes, exact frozen-to-integrated metadata deltas, links,
fences, whitespace and Git tree/ref identity; no code, test, build, runtime
probe or F5 cutover occurred.


### Integrated user decisions: complete Call direction and built-in `any` (2026-10-10)

The validated Call Reify q2 bundle was integrated at `a4e789ee4`. Its four
reviewed construction choices are now the bounded, user-approved direction in
[the design record](../notes/design/2026-10-10-call-reify-construction-direction.md):
retain the old registry binder in a typed tagged registry extension; add the
structural Call-argument registration/license case; retain suspension
attachment; and construct source-owned literal image domain/clause/root
`J_lit`. The complete Call contract remains fixed, and `J_lit` is not identified
with an arbitrary old `J`. See the [receipt](../questions/2026-10-10-call-reify-registry-construction/q2/receipt.md).
The predecessor q1 remains preserved as pending history.

The separate approved Any-name q1 bundle was integrated at `b0575d9b3`.
Lowercase `any` is a built-in Type name with precedence and no shadowing; no
uppercase `Any` alias is introduced. See its [design record](../notes/design/2026-10-10-source-annotation-any-name-design.md)
and [receipt](../questions/2026-10-10-source-annotation-any-name-resolution/q1/receipt.md).
The ordinary Any root, membership guards/evidence, hereditary Top law, Direct
proof and implementation remain open.

The external `c0d304113` `RuleCall_L`/`CertCall_L` proof remains separately
unadopted. The immediate complete-Call gate is source-grounded construction and
conformance for the actual `P_old`, its lookup/inversion and old-consumer
dependency closure, followed by the remaining complete Call obligations. No
compiler implementation, tests, builds, semantic checking, `f 1` acceptance or
F5 cutover occurred in these integration/record updates.

### Selected-source P_old construction attempt (2026-10-10)

The frozen [constructor-directed attempt](../notes/theory/2026-10-10-selected-source-p-old-construction-attempt.md),
pushed at `fe3a73734`, forms a conditional `F_form` presentation from actual
selected source-owned formation records while preserving complete dependent
fibers and all complete Call fields. It does not construct the original
`P_old`. The minimized first cut grants the actual formal registration and
Name route, then lacks an owner rule proving that this same `reg_f` decodes
from an original `P_old` key/payload with exact lookup equality. The new
`N_arg` and `N_lit` sorts cannot fill that original-key gap.

A separate consumer audit confirms that old consumers can be retained through
the unchanged `P_old` interpretation in the approved tagged route, but actual
consumer applicability still needs fixed-original typed maps and a concrete
dependency manifest. Exhaustive old-entry coverage, O0/O1, complete Q and C0,
admission/licensing, solving, principality, export and F5 remain open. The
unadopted `c0d304113` L extension does not close bootstrap or consumer
correspondence.

Next: find the authentic source-registration-to-original-registry
representation certificate, starting with the one-formal lookup/decoder square;
then establish exhaustive entry and consumer closure before moving to the
remaining complete Call fields. The artifact is exploratory and unreviewed. No
tests, builds, executable probes or compiler changes ran.

### Integrated registry representation design gate (2026-10-10)

The bounded construction audit reached the one-formal registration-to-`P_old`
lookup/decoder cut. The validated [q3/d1 bundle](../questions/2026-10-10-call-reify-registry-construction/q3/approved-answer.md)
was integrated at `534d8c945`; its [receipt](../questions/2026-10-10-call-reify-registry-construction/q3/receipt.md)
records exact content, source-premise validation and committed-file equality.
Option 2 authorizes source-owned registry constructor design and independent
review, as recorded in the [scope document](../notes/design/2026-10-10-source-owned-registry-design-gate.md).
It adopts no particular constructor/API equations and authorizes no compiler
implementation or full Call/inference closure. The q1 history stays pending.

### Complete-contract production Call path (2026-10-10)

The user reaffirmed the complete Call contract for `f 1`; the four-port shadow
projection is not a success criterion. A bounded production-owner map at
`c3cb59dfa` finds no current successful default path carrying that contract:
ordinary HIR rejects Apply before constructing typed argument, Result/Delay,
license, role/protection, provider/world, complete image, or pending/future
evidence. The shadow candidate has unresolved premise markers and scalar
endpoints; its empty-call-effect assumption cannot be promoted. Existing
generalization/publication handles current endpoint schemes but receives no
complete Call evidence. No code or tests changed.

The next Call-side gate is a reviewed production source-construction design
for formal-Name/Int that supplies the complete typed inputs and preserves them
through solving/publication. The approved selected-source Reify construction
direction still has a separate open `P_old` registration lookup/decoder
bridge, with the registry design gate now authorized by q3; no production implementation is authorized by the
complete-contract clarification. See the [complete contract direction](../notes/design/2026-10-10-call-reify-construction-direction.md)
and the [production Function-call contract](../notes/design/2026-10-05-inferred-function-call-views.md).

The reviewed [practical complete-Call proposal](../notes/design/2026-10-10-practical-complete-call-production-gate.md)
now maps source-owned complete interfaces, correlated solving evidence and
atomic ordinary publication for that first source slice. Independent
compiler-referee and spec-auditor reviews found no issue within the conditional
proposal; the [review record](../notes/progress/2026-10-10-practical-complete-call-production-gate-review.md)
records their scope and omissions. This remains a proposal, not implementation
authority. The first new source-rule decision is how independently typed
ordinary literal evidence reaches the shared inferred formal and how that
contributes to provisional protection. Effective complete solving and invoke
public extraction remain separate suppliers. The bounded
[solver/publication map](../notes/progress/2026-10-10-complete-call-solver-publication-seam-map.md)
finds current scalar constraint/effect worklists, scalar Generalize/closed
scheme and fresh-use paths, but no direct complete residual, complete Call
effect allowance, ordinary decoder or whole-frame checker. The next typed
correspondence therefore runs from a certified complete residual through
dependency-aware generalization and finite extraction to a fresh whole-frame
decoder, then atomic publication. The q3 answer is integrated at `534d8c945` and consumed for the bounded
source-owned registry design/review gate only. Its concrete constructor/API
choice and actual `P_old` correspondence remain open; see the
[scope record](../notes/design/2026-10-10-source-owned-registry-design-gate.md).

The bounded decision on the first ordinary-value refinement is now on the
question board as ordinary-value q1 (subsequently withdrawn and removed; see
[cleanup](../notes/progress/2026-10-10-question-board-cleanup.md)).
It asks whether to start with actual Int Data at the Call argument child, use a
uniform ordinary-Value rule, or defer that rule. Only this dependent source-rule
design waits; other solver/export and registry research may proceed under their
own authority.

### Built-in `any` name versus semantic root (2026-10-10)

The approved lowercase name rule resolves source `any` only. A focused design-
obligation audit classifies retaining the exact `q_type`, lexical scope and
resolved builtin incidence as reconstruction debt at syntax association and
written-Type lowering. It classifies the complete ordinary `Value(Any)` root
and hereditary Top law as genuine soundness/natural-inference obligations;
current constructors do not supply them. The negative F5 Top node and a
quantifier upper bound are not substitutes for that source-owned root. No
implementation or new Any semantics are authorized by the name decision.

The next useful independent gate is a reviewed builtin descriptor-introduction
package naming every genuine membership interpretation, guard, evidence
binder, scope/dependency field and Top-law supplier for `my widened = 0 as any`.
Drafting that package needs no additional choice while it reuses existing
selected meaning; if it needs a new semantic clause, stop and route that exact
clause through a separate approval. Broad arbitrary-view characterization is
not a prerequisite for this one-case design unless a concrete dependency is
found.

The frozen [builtin Any package attempt](../theory/2026-10-10-builtin-any-descriptor-package-attempt.md)
at `3457cbb36` narrows the previous H2 root gap to its first missing semantic
input: a genuine builtin Any descriptor declaration with its complete
membership/guard/evidence signature and registration. Independent
`compiler_referee` and `spec_auditor` reviews found no issue within the selected
constructor envelope. This is a bounded obstruction, not a claim of global
absence or source rejection; it adds no Any semantics and authorizes no
implementation. The exact builtin meaning and hereditary Int-to-Any law
remain open.

The accepted `zero : any -> int` criterion is separately recorded in
[`principal-scheme-acceptance-criteria.md`](../progress/2026-10-04-principal-scheme-acceptance-criteria.md): it selects the negative Function argument presentation for `zero` and explicitly does not define general Any or polarized Top semantics. It does not substitute for the ordinary Value Any target needed by the expression annotation.

### Reviewed source-owned registry construction for invoke (2026-10-10)

The [registry construction and complete proofs](../notes/theory/2026-10-10-source-owned-original-registry-construction.md)
and [independent review record](../notes/progress/2026-10-10-original-registry-construction-review.md)
were checkpointed and pushed at
`fdda52fd8ec9eb1b3a691825a7b895b3a40fc753`. This is a completed mathematical
construction in an explicitly NEW, unadopted source-owner interpretation. It
addresses the actual formal/Name/literal pre-Call spine of `my invoke f = f 1`;
it does not declare the complete source Call or program accepted.

The constructor generates seven source rows (Formal, Name Data/Result, literal
Data/Result, and both source-generated Images), plus the computed closure of
actual local declaration tokens. It seals finite source/context/recipe syntax
before any registry-indexed source formation. The subsequent decoder constructs
contextual formal/port/entry/registration, Name, literal and Result/Image
families by the explicit ranks Law, Formal, Data, Result, Image. No completed
P_old, Reg_f, source Code, lookup correspondence or exhaustive registry manifest
is a constructor premise. The same nominal Formal key decodes to the same whole
registration family, and all Name/Image references reuse its original scoped
proof choices.

The formation lemma and B prove noncircular construction and termination.
E proves exhaustive entry coverage and inversion for this exact pre-Call
domain. SR/T prove direct/staged formation and complete ordered evidence-fiber
preservation. DC/CR retain the complete dependency object and same final P for
well-typed post-decoding consumers, including full-registry observers. A proves
lawful whole action, scoped substitution and nominal nonmerging at its stated
domain boundaries. J_a/J_f are built from the actual primitive/Name and whole
Return/prefix clauses; they are distinct from printed Comp interfaces, J_lit
and independently fixed foreign image roots.

The initial mathematical review found that an unevaluated guard can still need
a later typed decoder argument. One fresh repair supplied explicit NEW owner
interfaces, proved every complete type-level argument available at its original
scope, and postponed the full typed decoder API until B. It also corrected
Name Image traversal and made immutable shared proof-choice specialization
explicit. Fresh independent mathematical and specification delta reviews both
passed. The reviewed freeze and integrated proof hashes are in the review
record; this is documentary mathematics, not a machine-checked proof.

The new `OwnerPortLicense_src` is the source-owner declaration permission
defined by the candidate rule, not original contribution licensing, C0 or live
admission. Complete local declarations and their genuine primitive/operator
laws remain independent local inputs. The source notes do not prove that every
separately fixed opaque original signature realizes the new raw-P API; an
incompatible whole application is left unproved rather than dropping its
fields, W/Z arms or independent guards. The q3 adoption object now has a
concrete reviewed registry/API construction. The unavailable pending q3 body
or answer has not been guessed, committed or treated as approval.

The actual one-formal representation premise is eliminated **within this
candidate**. Complete original checking/emitted membership, O0/O1, actual
WholeArgCompatible/kernel correspondence, result/effect/profile/guarantee
consumers, independent CallMem/C0, actual-provider admission and all live
pending/raw/future cases are not obtained from that static construction. The
existing L collection theorem remains separately unadopted and is not an
original-consumer bridge. No effective solver, Generalize eligibility,
principal publication or transformed public export is added by this result.

Two parallel claimed advances were rejected during review: a proposed Name
counterexample lacked actual entry/receipt/rebind evidence, and the proposed
generic receiver elimination was already contained in input-realization
Theorem E. Their novelty/soundness claims were withdrawn; no additional failed
proof or obligation note was committed. Their disposition is retained in the
review record, without claiming a source rejection or impossibility theorem.

This addresses D reconstruction debt and the candidate's A typed-formation
requirements. Actual complete Call correctness and natural inference remain
A/B work. Equality with every foreign registry model is C research, not an
extra mandatory production prerequisite; the actual chosen consumer still
needs its exact correspondence. The canonical DAG is byte-for-byte unchanged:
CallMem/C0 remains unclosed, CALL_REL keeps its prior conditional scope, and
JOINT_DEC remains OPEN-PROOF. No implementation, test, build, runtime probe or
F5 cutover occurred. This task/index update follows the already pushed proof
checkpoint; no reviewed independent result waited for a final combined commit.

### Registry adoption object and actual formal API cut (2026-10-10)

The former Git permission blocker is resolved. The validated q3/d1 bundle was
integrated at `534d8c945`, its receipt/narrow authoritative design scope and
the reviewed practical Call architecture were checkpointed at `582f32d8a`,
and concurrent remote registry research was merged and pushed at `070281ce0`.
q3 authorizes constructor design/review, not the candidate's exact equations.

The bounded [actual-kernel attempt](../notes/theory/2026-10-10-original-registry-kernel-conformance-attempt.md)
was independently reviewed and its honest initial checkpoint pushed at
`de26db327`. It stops at the first formal: the original Entry-Value rule
consumes ParameterOrigin and carrier/receipt/Force/rebind ports, while the
inspected selected source cone does not elaborate their complete introduction
against raw P. The remaining sequent is
`Gamma_form^src(P) |- mu : Delta_in^orig`, then authentic `intro_orig[mu]`.
The full original signature and concrete substitution remain unprovided.
This is a bounded API cut, not an actual incompatible declaration, a late-
decoder counterexample, global absence or impossibility of ordinary source.
The candidate's own registration/lookup construction remains established.

The [six-choice concrete adoption proposal](../notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md)
is now Reviewed. Compiler-referee and spec-auditor found no issue in the frozen
proposal/conformance component; [coverage and hashes](../notes/progress/2026-10-10-original-registry-adoption-conformance-review.md).
It identifies new nominal recipe/raw-registry, owner/port/Entry/registration,
source-generated image, whole-consumer and action definitions for the selected
pre-Call source interpretation. The exact definitions remain unadopted.
Registry q4 (subsequently suspended and removed; see
[cleanup](../notes/progress/2026-10-10-question-board-cleanup.md)) asked whether to adopt that connected object or retain it as a candidate until
the actual original introduction is elaborated. The ordinary-value refinement
q1 remains separate and pending. Questions stay unstaged/uncommitted.

Next: validate any finalized question answers before dependent adoption;
elaborate the actual formal origin/port introduction at its source owner under
the exact selected interpretation. Complete Call formation, O0/O1, C0/admission,
effective correlated solving, principality, ordinary export/fresh checking and
F5 replacement remain open. No compiler code, tests, builds, runtime probes or
measurements were changed/run for these design and source-map checkpoints.

### Current user correction: restore Simple-sub inference ordering (2026-10-10)

The user explicitly corrected the repeated questions as ignoring Simple-sub's
solution. The [pinned algorithm/current-code reassessment](../notes/progress/2026-10-10-simple-sub-question-reassessment.md)
shows that basic application inference already uses one uniform operation:
allocate a fresh result beta and constrain the callee alpha below
Function(argument,beta). The argument can be Int or an unknown monomorphic
formal gamma. Installing upper/lower bounds, Function variance, per-use graph
freshening and polarity-sensitive boundary handling determine that spine.

The offered literal-versus-general ordinary-value q1 choice is withdrawn, with
its unapproved drafts preserved. Registry q4 is suspended as an inference
prerequisite: adopting a new observable Seal/decoder/kernel interpretation was
not shown necessary for basic source bound collection. Its candidate equations
remain unadopted; q2's Reify choices and q3's design/review permission remain
binding. Both pending directories retain questioner-owned dispositions and
remain unstaged/uncommitted. No answer preference/draft is consumed as approval.
The newly dispatched original-formal rule construction was interrupted, with
no resulting artifact present; no further new-rule question was created.

The real code seams are ordinary recursive Apply/Group collection and lexical
formal lookup, retained callee/argument/invocation effect endpoints, replacing
fixed-empty candidate Call effects, and successor generalization/freshening
which preserves effect variables/bounds. Current extrusion lowers rows in
place and must not be described as the pinned algorithm's polarity-keyed
copied approximants. Existing shadow generation already has the scalar Apply
bound, but it remains incomplete and cannot be promoted as full Call inference.

Next: advance compositional collection/live solving and the successor scheme
path from these existing source constraints. Keep the complete effect, role,
protection, provider/world, image, admission/licensing and future obligations
at their source/solve/elaboration owners. Do not require full kernel certificate
formation before creating fresh endpoints, and do not export a missing compiler
constructor as a supposedly meaningful residual. No new decision is established
for the basic Apply constraint spine. Full inference/F5 replacement stays open;
no proof-DAG promotion or code/default-route change follows from this audit.

### Compositional solver collector checkpoint (2026-10-10)

The [implementation record](../notes/progress/2026-10-10-compositional-inference-collector.md)
now replaces the one-formal candidate lookup with lexical scope and recursive
Lambda/Apply/Group collection. Explicit Lambda result endpoints preserve an
outer formal's actual startup row. Independent compiler review and a fresh
delta review closed the nested-postorder projection-cursor defect; no accepted
blocking/major solver finding remains. Candidate/default owning Cargo checks
passed. No tests, runtime probes or measurements ran. Complete Call, effect,
generalization/extrusion and production cutover claims remain open.

The disjoint HIR multi-parameter source carrier extension is not part of this
solver checkpoint: its correctness review passed, but resource review found
unbounded boxed Lambda depth before candidate preflight. Repair its owning
preconstruction boundary under the existing candidate depth envelope, then
freeze/review/check/integrate that source slice. Ordinary F5 diagnostics stay
under the existing zero/one-parameter contract. Continue afterward with
kind-qualified effect graph retention through generalization and fresh use;
registry adoption remains outside the basic inference critical path.

### Opt-in multi-parameter HIR checkpoint (2026-10-10)

The disjoint source slice above was committed at `fc0848450` and pushed through
the inspected remote merge `90629b216`:
canonical ordered identifier parameters reach nested Lambda HIR through the
existing application opt-in route. Each parameter retains its actual source
key and checked owning ordinal; lexical scope and source-order occurrence
allocation preserve outer references. A fresh compiler/resource delta round
closed the source-sized recursive ownership risk by enforcing the existing
retained-expression depth 128 before boxing (`p + body_height <= 128`), with
atomic `StructuralProjection` failure outside that candidate envelope.
Default and identity-only F5 retain their zero/one-parameter contract.

Final candidate and ordinary owning Cargo checks passed without warnings.
No tests or execution probes ran, so actual inferred apply/const/compose
schemes, boundary clone/drop behavior and default runtime parity remain
unverified. No proof-DAG node, complete Call gate, successor publication gate
or target-branch cutover is closed. Next implement effect-variable graph
retention in successor generalization/fresh use and remove fixed-empty Call
effects at their owning generation step; preserve full correlated Call data
and revalidate polarity-copy extrusion rather than claiming the in-place
F5 routine matches Simple-sub.

### Operational successor mixed graph schemes (2026-10-10)

The [mixed-graph implementation record](../notes/progress/2026-10-10-successor-mixed-graph-schemes.md)
connects private top-level SCC capture and actual incoming-use freshening to
`shadow_apply::CandidateInference`. Kind-qualified value/effect rows, all four
Function ports and direct/exact bounds survive capture and reconstruction.
It bypasses the pure F5 exporter without fabricating a closed pure scheme;
ordinary F5 and the legacy candidate remain on their existing paths.

M2 semantic/resource review finished. The accepted diagnostic-visibility defect
was repaired with a borrowed conflict accessor; fresh semantic delta review
closed it. Successful capture/structural reconstruction costs are linear per
graph before existing solver closure work. Failure-path high-water accounting,
general environment closure and runtime behavior are explicitly unverified;
no stronger resource certificate is claimed. Candidate/default owning Cargo
checks passed without warnings; candidate check also passed after the repair.
No tests, execution probes or measurements ran.

The mixed-graph slice was committed at `ae70f4c82`. Concurrent remote
`eed17418c` adds independently reviewed/executed test-only complete-bound and
deferred-call modules; its scoped [execution record](../notes/progress/2026-10-10-simple-sub-deferred-call-implementation-review.md)
does not exercise the new graph scheme path. The inspected merge `ff5211424`
adds only their test registration to production-file text, with no change to
the reviewed production dependency cone.

The independently prepared next packet selects graph collection before batch
construction, retains Apply/Group child effect components, adds one invocation
effect row per Apply and routes callee evaluation/invocation output into the
application effect. Argument evaluation stays in the Function demand. Lambda
construction and formal fetch remain distinct from invocation. Full Call,
polarity-copy extrusion, public publication and target-branch F5 replacement
remain open; no registry adoption or new semantic question is needed for these
existing scalar effect-flow relations.

### Successor source Apply/Group effects (2026-10-10)

The [source effect implementation record](../notes/progress/2026-10-10-successor-source-effect-flow.md)
now selects graph collection before batch construction, retains callee/argument
and Group child effects, and generates a fresh invocation-effect row per Apply.
Argument evaluation enters the negative Function demand; callee evaluation and
invocation output enter application evaluation through separately attributed
facts. Captured-local Apply uses the same flow. Graph Apply/Group no longer
receive fixed-empty upper facts. Formal fetch, Lambda construction and the
legacy/default paths retain their existing contracts.

M2 compiler/resource reviews found no BLOCKING/major finding in the frozen
delta. Candidate/default owning Cargo checks passed without warnings; no tests,
execution probes or measurements ran. Source-operation counters and retained
recipe size accounting cover the added work, while full propagated-task cost
and failed-attempt high-water evidence remain unmeasured.

Next implement the graph-only Simple-sub polarity-copy bound owner and connect
actual source levels/nested initializer generalization using retained lexical
ownership. Read-only packets locate those seams; do not substitute in-place
F5 aging or a speculative registry construction. Full Call, ordinary public
extraction and target-branch replacement remain open; the full goal is active.

### Reviewed deferred Simple-sub bounds and actual solver tests (2026-10-10)

The [complete construction](../notes/theory/2026-10-10-simple-sub-complete-bound-accumulation.md)
now proves BOUND (finite same-index whole inclusion propagation with exact
original witness retention), PATH (total discovery in the explicit finite
Refl/Original/Compose proof language), and ROW (the actual same-level row-only
Simple-sub storage seam). Both independent mathematical/specification reviews
passed; the minor whole-observation projection clarification was repaired.
The reviewed proof and [record](../notes/progress/2026-10-10-simple-sub-complete-bound-review.md)
were pushed at `5c8efdcbc18fc493c3188a132f44491db60d739f`.

The [test-only implementation and review](../notes/progress/2026-10-10-simple-sub-deferred-call-implementation-review.md)
were pushed at `eed17418cf92bc3fd80fdbd3381a307f74d2bd1b`: two complete-bound
adapter tests and five actual scalar/HIR deferred-call tests pass. The latter
collect actual `invoke` and nested `relay` HIR before solver execution, preserve
shared formal identities, directly assert nested result/argument incidence,
and exercise late provider/result/effect replay and real contradictions.
Both code reviewers passed with the same minor assertion gap, now repaired.
The affected tests were rerun after the remote HIR change through `90629b2`;
the ordinary owning package check passed. A separate compatibility-only
allocator annotation follow-up at `489875759ef547f89ff8e29fde6ce78822c4ab7d`
keeps atomic behavior/compiler compatibility and passes that check without
the newly observed Rust 1.99 deprecation warnings.

This removes separately supplied replay/path-certificate constructors and
immediate formal/provider resolution from the bounded storage operation.
PATH does not decide semantic satisfiability. The test adapter's immutable
residual tokens/documentary references are not complete source certificates.
Full Function/WholeArg decomposition, original CallMem/C0, general JOINT_DEC,
Generalize/public/fresh-use correspondence and cutover stay open; the canonical
DAG is unchanged. Basic collection still has no registry-q4 prerequisite.

### Reviewed finite value/effect graph construction (2026-10-10)

The [RAW-EXTRACT / RAW-FRESH construction](../notes/theory/2026-10-10-simple-sub-kind-qualified-graph-construction.md)
and [independent proof/implementation review](../notes/progress/2026-10-10-kind-qualified-graph-review.md)
are pushed at `01bf7312360afe94ed40d4363208cf323baa8f1e`. The concrete constructor
retains every active value/effect row, all four ordered bound lists, actual
component/root references, all admitted typed-pair keys and every Function
child. One kind-qualified map preserves both polarities and row cycles; a
separate nominal term-record map gives an exact immutable-record inverse.
It does not clone the whole operational session or require complete raw capture
as a prerequisite for the actual rooted candidate exporter.

Both proof reviewers passed without findings. Both code reviewers passed; the
minor executed-scope comment was clarified. Four discriminating tests passed
under `shadow-f5` and under `shadow-apply-candidate`. Two multi-codegen-unit link
attempts failed with undefined hidden Rust symbols; the latter feature check
passed with a separate target, incremental disabled and one codegen unit.
No build policy changed. The actual F5 unbounded-negative-effect witness and
four-port provider effect replay were executed, with full raw-record round-trip
checks. The optional REALIZE/PARTIAL/residual recipes remain proof-only.

### Source-generated candidate Call graph and repeated use (2026-10-10)

The [actual constructor theorem](../notes/theory/2026-10-10-candidate-graph-call-correspondence.md)
and [review/execution record](../notes/progress/2026-10-10-candidate-graph-call-review.md)
connect the `280d399e` collector to its real SCC capture and incoming-use route.
SOURCE-LOCAL derives the current empty-import source envelope's local rows;
CAPTURE constructs its least rooted four-port/bound closure; FRESH-ROUTE
constructs one typed fresh map and actual retained-bound/root submission;
REPLAY and TERMINATION prove logical substitution factorization and finite
constructor/propagation behavior. Neither a supplied completed graph nor an
immediately solved Function/provider/effect is a premise.

The two actual `CandidateInference::solve` fixtures pass: `invoke f = f 1`
followed by two Name uses, and `id x = x; invoke f = f 1` followed by two
`invoke id` applications. Tests inspect the actual source Name/use ownership,
unknown formal demand, absence of premature positive Function/Empty bounds,
shared symbolic invocation/body effect, all-local classification, disjoint
Value/Effect fresh maps and Int propagation to both receiving result roots.
Both mathematical/specification proof reviews and both code reviews passed;
the terminal-precedence clarification and two minor assertion-coverage gaps
were repaired. The two affected tests passed again after repair.

Before publication, concurrent `334fd35` changed candidate bounds to directional
ownership and selected-side restoration. The full remote delta was preserved;
all 13 new focused tests passed on the rebased tree without assertion changes.
This revalidates runtime behavior, while the earlier theorem stays pinned to
`280d399e`. The [directional source theorem](../notes/theory/2026-10-10-candidate-directional-source-correspondence.md)
now derives the changed owner/restoration rules directly; its independent
mathematical and specification reviews passed with no findings.

This supplies new construction and execution evidence for the existing
nonshipping candidate graph path, not ordinary certified source acceptance or
a closed public scheme. Full CallMem/C0, JOINT_DEC, source-Generalize/public
correspondence, general lexical levels/polarity-copy extrusion, complete effect/
protection/provider/world/admission/future evidence and F5 cutover remain open.
The canonical DAG is unchanged. The original complete residual contract is not
replaced by the scalar spine; no unsupported generic source-use supplier is
promoted as a theorem. Implementation authority remains the current research
branch and existing candidate path.

### Successor polarity-copy bound owner (2026-10-10)

The [polarity-copy implementation record](../notes/progress/2026-10-10-successor-polarity-copy-extrusion.md)
now replaces in-place aging only in the private graph path. Kind-qualified
polarized representatives retain original levels, selected lower/upper bounds
and one-sided source links. Function argument ports reverse polarity; result
ports preserve it. Iterative reconstruction defers bound traversal until each
structural memo entry completes. Graph comparison uses directional receiving
owners and opposite-bound replay; schemes retain their owner side through fresh
use. Existing diagnostic and route journals retain their responsibilities.

M2 semantic/resource reviews found no BLOCKING/major finding. Candidate/default
owning builds passed without warnings on the frozen dependency set; no tests,
execution probes or measurements ran. Per-operation memoization does not imply
aggregate linearity: opposite-polarity copies can cross P*N memberships and
lower/upper replay crosses L*U bounds. Successful logical samples do not certify
failed-attempt peaks or allocator/RSS storage.

The source carrier for generic sequential local declarations is a disjoint HIR
slice under review, excluded from the solver checkpoint. Its parameter ownership,
trailing separator handling and lexical lookup cost have concrete review concerns
to adjudicate and repair. Then connect actual initializer levels and sequential
solve/freeze/install/use scheduling; current admitted source levels remain one.
General anchor closure, complete Call, public extraction and target-branch F5
replacement remain open. The full objective stays active.

### Generic local source formation checkpoint (2026-10-10)

The [HIR carrier record](../notes/progress/2026-10-10-generic-local-source-hir.md)
retains root-owned generic local declarations, actual local/formal source
identities, flat block order and nearest lexical captures in an explicit
nonshipping entrypoint. One batched repair closed three major findings and one
minor finding: local parameter ownership, valid trailing separators, quadratic
lexical lookup and late root-parameter rejection. Fresh semantic/resource delta
reviews passed. Frozen HIR and candidate solver Cargo checks passed without
warnings; no tests, execution probes or measurements ran.

This completes source formation only. `CandidateInference` still consumes the
legacy tree and admits level-one source rows. Next consume the sidecar with
raised initializer levels and sequential solve/freeze/install/use scheduling,
retaining outer captures and top-definition dependencies. Simple-sub's uniform
App rule and ordinary let freshening do not need a new semantic choice; keep
ordinary-value q1 withdrawn and registry q4 off the basic inference path.
Complete Call, general anchor closure, public extraction and target-branch F5
replacement remain open. Pending question directories stay excluded from Git.

### Reviewed directional source membership construction (2026-10-10)

The [new theorem and review](../notes/progress/2026-10-10-candidate-directional-source-review.md)
close the actual level-one constructor correspondence at `334fd35`. Source
locality and identity extrusion follow from real startup/admission/use owners.
Active membership closedness starts with actual empty lists and memo; rooted
capture retains a closed subset through every owner membership and all four
Function children. Fresh restoration explicitly inserts each source slot on
its recorded side using one typed map. Its induced memberships stay within the
renamed closed set, so the final pre-receiver logical set is exactly `M(C)`.
The subsequent receiving-root active solve preserves the invariant for the next
actual dependency-ordered capture. No supplied saturation or completed graph
is assumed, and no immediate provider/effect solution is required.

Both independent reviewers passed the full frozen proof with no findings.
Current invocation flow is `e.upper re`, not old paired `re.lower e`; possible
omission of the pure Name predecessor is explicit. The proof does not assume
idle restoration visits every opposite slot despite its changing index boundary.
It establishes membership-set equality and seed insertion, not physical slot,
comparison-cache, terminal-diagnostic or complete source evidence equivalence.
The 13 targeted tests passed on the directional implementation without assertion
changes. Later HIR-only `801e16e` leaves all four solver owners unchanged; its new
local carrier entrypoint remains outside these ordinary candidate source tests.
All 13 focused tests also passed after that HIR merge, with no assertion changes
or warnings; the new local-source entrypoint itself remains unexecuted here.

This removes the changed constructor/replay assumptions at the bounded seam.
General unequal-level source inference, original complete Call/C0 and JOINT,
source-Generalize/public scheme correspondence and F5 cutover remain open.
No canonical DAG status or language/public-contract choice changed. The full
production inference objective remains active; no stronger all-active snapshot
or arbitrary abstract-predicate decision theorem is imposed as a prerequisite.
The later live-let correction is binding: this theorem's finite worklist
closure is not completed initializer solving and creates no mandatory immutable
local-scheme barrier. Its scope is the pinned module-graph implementation.

### Source-level execution and complete Call next packet (2026-10-10)

An implementer owns only the four solver paths for the source-directed
execution schedule: immutable recipes with actual lexical levels; sequential
initializer processing, boundary handling and local scheme installation; action-time
module/local fresh uses; and direct/structural anchor closure. This live slice
is incomplete and build-unverified. Its writes stopped after the user's
correction: requiring completed initializer solving/freezing before continuation
solving was false. Levels and extrusion handle later cross-boundary constraints.
The boundary/live-scheme adapter is under read-only reassessment; preserve the
partial patch, and do not integrate it as a completed inference path. Default/public/cutover
behavior remains outside this private implementation lease.

A separate read-only owner audit produced the [complete Call source-spine
packet](../notes/progress/2026-10-10-complete-call-source-spine-next-packet.md).
Existing formation can retain shared formal roots, local complete demands and
specific unsolved obligations without a known provider or early role change.
After the source-level lease freezes, retain these at their owning construction
points. Authentic annotation/seed provenance and complete consuming suppliers
remain material requirements; scalar success cannot stand in for them.
No new choice question or complete Call closure follows from this packet.

### User correction: live let schemes and extrusion (2026-10-10)

The [correction record](../notes/progress/2026-10-10-live-let-level-extrusion-correction.md)
withdraws mandatory initializer saturation and immutable local publication.
The paused implementer resumed the same four-file lease with local schemes
holding actual live roots and enclosing boundaries. Fresh use captures the
current graph as temporary input, copies eligible rows and shares older anchors.
Reference-style source traversal installs intrinsic RHS relations using the
existing immediate constraint operation, while later constraints through older
extrusion coordinates remain legitimate. No new semantic choice or test ran.
The incomplete patch is not yet frozen/reviewed/built or integrated.

### Successor source levels and live local schemes (2026-10-10)

The [implementation record](../notes/progress/2026-10-10-successor-live-local-schemes.md)
connects the generic HIR carrier to actual lexical levels, live local root/boundary
handles and use-time graph freshening. Formal references alias actual rows;
older anchors stay live/shared; initializer effects contribute once to block
computation. Dependency-first source actions route actual module/local uses and
reuse the existing transactional bound/diagnostic/observer rollback. No immutable
local snapshot or completed-initializer barrier is introduced.

Independent M2 semantic/resource reviews found no blocking/major finding. The
minor O(U²) all-use observation lookup cost is documented. Frozen candidate/default
owning Cargo checks passed without warnings; no tests, runtime probes or
measurements ran. No generic-local execution claim is made.

Next retain complete Call source-spine inputs at actual source construction,
using existing plain-header provenance from LocalSource rather than inventing
an annotation-absence field. Specific unsolved obligations keep their original
inputs; scalar success cannot stand in for a complete consumer. Complete Call,
structured effects, general source/public correspondence, principality and
replacement on yulang3 remain open. Pending questions remain excluded from Git.

### Ordinary inference replacement owners (2026-10-10)

The [cutover entrypoint map](../notes/progress/2026-10-10-ordinary-inference-cutover-map.md)
locates the actual library default path, F5 SCC/export/use assumptions and
public result seams. There are no existing CLI/LSP/backend inference callers
in this workspace; this finding does not add those implementations to the
inference replacement scope. Target yulang3 remains at 32f0a063, rechecked
against the remote. The opening checkpoint counts are now explicitly pinned.

A producer owns candidate_call.rs (new), candidate_source.rs, shadow_apply.rs
and lib.rs for actual source inputs connected to generated native demand and
invocation rows, plus a validating pending compiler-construction consumer.
Complete original registration/exposure/Gen-Call-0 and carrier/result/future
suppliers are not fabricated or treated as scalar residuals. This slice is
in progress and not yet frozen/reviewed/built. F5 target replacement remains open.

### User-selected intrusion implementation (2026-10-10)

The user explicitly defined intrusion as retaining extrusion-copy parents and
making a copy equal to its parent when both enter the same SCC, then instructed
implementation. The [decision](../notes/design/2026-10-10-parent-copy-scc-intrusion.md)
is direct current authority; no new question-board choice is needed for it.
Bounded architecture mapping now targets actual row equality, parent provenance,
variable/SCC detection, recursive internal-use integration, propagation and
rollback. Parent metadata without working equality/SCC admission is insufficient.

The separate source-Call artifact has completed both M2 initial reviews; its
sole accepted major was missing State::Clone. A fresh producer repaired that
one derive; focused feature build and fresh semantic delta are running. Minor
observer-depth and source-planning peak exclusions remain disclosed limitations.
Keep this coherent checkpoint separate from the intrusion implementation.

### Source Call input checkpoint complete (2026-10-10)

The [source input record](../notes/progress/2026-10-10-call-source-inputs.md)
retains actual formal registrations/Names/Apply operands and connects them to
native demand/invocation rows. Borrowed observations validate actual ownership,
route and native interface before exposing typed pending construction. Original
semantic suppliers remain missing, not replaced by native fields or residuals.

One accepted compilation major (State::Clone) was repaired by a fresh producer
and closed by fresh semantic delta. Both initial M2 reviews otherwise passed;
observer-depth and source-planning peak exclusions are documented. Repaired
candidate and default owning builds passed without warnings. No tests, runtime
probes or measurements ran. Next implement the user-selected parent-copy SCC
intrusion; complete Call/public cutover remain open.


### Parent-copy SCC intrusion checkpoint complete (2026-10-10)

The directly authorized [intrusion operation](../notes/design/2026-10-10-parent-copy-scc-intrusion.md)
is implemented in the private successor. Actual extrusion parents are retained;
qualifying same-SCC copies/parents share canonical row identity, merged bounds,
minimum level and non-generic state. Quiescent propagation handles equality and
rollback. Recursive definition components register open roots first, route
internal uses with actual occurrences, execute every member schedule, and only
then capture member graphs.

[Implementation and review evidence](../notes/progress/2026-10-10-parent-copy-intrusion-implementation.md)
records initial M2 semantic/resource review and three bounded repair bundles.
All accepted majors are closed: current live-root recapture preserves later
bounds; exact per-use graphs preserve row-map correspondence; borrowed same-state
canonical source identity preserves existing assertions; hash diagnostic dedup,
first-write undo and cached capacity reporting avoid the reported multiplication;
SCC scratch stays charged through merge propagation. Final owning candidate and
default builds passed without warnings; diff checks passed. No runtime tests,
probes or measurements ran. Pending questions remain uncommitted.

This completes the user-selected intrusion implementation checkpoint on
research/simple-sub-intrusion, not the full inference goal. Next integrate
complete Call construction and public/default inference extraction for the
successor, then verify the concrete recursive/generalization behavior before
replacing F5 on yulang3. Runtime behavior, general source/public correspondence,
structured effects/protection, soundness and principality remain uncertified.


### Annotation effect hygiene: policy/proof integration (2026-10-10)

The user selected contravariant `[E]` as function-local subtraction permission
at its effect position and covariant `[E]` as concrete allowance, ignoring type
variables as concrete atoms. The user then requested reuse of older hygiene
proofs and integration, with explicit policy recording as the fallback.

The [selected policy and integration map](../notes/design/2026-10-10-annotation-effect-hygiene-integration.md)
now reuses reviewed conditional transport/lifetime, owner preservation and
exact-interface results without restarting them. It preserves source-variable
flow, checks on later concrete lowers, original annotation ownership and
existing attachment/support distinctions. Pure injective renaming is not a
proof of canonical row identification. One scoped M1 conformance review found
no issue; reference/diff checks passed; no compiler builds/tests/probes or
measurements ran. See the [delivery record](../notes/progress/2026-10-10-annotation-effect-hygiene-integration.md).

Compiler integration remains open because HIR does not retain resolved effect
annotations and the solver alphabet lacks concrete effects and executable
boundary filters. Next couple that annotation constructor with concrete effect
comparison/filter propagation, capture/freshening/extrusion and equality/rollback
preservation. Do not replace it with an unused grant bit, erase variable flow,
or create a full Call registry/arbitrary-view proof prerequisite. The broader
inference/F5 replacement objective remains active.

### Active withdrawal of Simple-sub bypasses (2026-10-10)

The user's [explicit withdrawal policy](../notes/design/2026-10-10-simple-sub-legacy-withdrawal.md)
requires actual removal of obsolete mechanisms and proof dependencies. The first
bounded implementation removes the exact captured-local fixture prerequisite
from successor preflight and graph collection; generic lexical LocalSource is
the actual owner. Historical F5 observer clients remain migration work.

The active proof DAG removes CTX_FINITE and its three edges and stops reusing
SD-NPB as a closed general solver lemma. Retirement is explicitly recorded,
not theorem closure. JOINT_DEC retains complete solving/residual, semantic
preservation/reflection and termination requirements. Complete Call, effect
hygiene, soundness and principality remain required. The
[delivery record](../notes/progress/2026-10-10-simple-sub-legacy-withdrawal.md)
records focused runtime checks, independent review and exact residual routes.

Next migrate actual effect annotation formation/propagation and complete Call
construction, then ordinary public inference/scheme use to the successor so
the historical pure observer, F5 closed-effect restriction, old extrusion and
generalizer can be deleted coherently. No active local SAT/freeze requirement
or complete registry runtime gate before basic constraint generation was found.
Anonymous lambda expressions remain outside the current generic LocalSource
formation envelope. The full inference goal stays active; this checkpoint is
not complete legacy withdrawal or production cutover.

### Actual intrusion runtime evidence (2026-10-10)

[Five owning regression tests](../notes/progress/2026-10-10-intrusion-runtime-regressions.md)
now pass for real extrusion parent provenance, same-SCC equality versus its
non-SCC control, merged metadata/later bounds, failed-route rollback and natural
recursive/captured-local behavior. Fresh repair strengthened late-result
reachability and exact older-anchor sharing assertions. This closes the missing
runtime evidence for those bounded operations, not general semantic correctness.
Concrete effect/co-annotation construction is the next active implementation;
full source subtraction still requires authentic contribution attachment.

### Withdrawal authority routing synchronized (2026-10-10)

`rules/design-authority.md` now routes the user's explicit legacy-withdrawal
decision into ordinary authority resolution: adding a parallel Simple-sub path
does not satisfy retirement, replaced implementation dependencies need actual
removal and focused regression evidence, and obsolete proof prerequisites leave
the active graph with a reason rather than a fictitious proof closure. Complete
Call, hygiene, soundness and principality retain their genuine requirements.
The design index and intrusion decision now link the bounded runtime evidence
at `a4ba1729b`; older no-runtime statements are historical checkpoint records.
This is M0 record/policy synchronization, with scoped reference/diff inspection
only, zero reviewers and zero measurement processes/samples. No compiler test
rerun is needed. The concrete annotation implementation remains in progress
under its separate lease; the full inference goal remains active.

### Authentic effect operation source next gate (2026-10-10)

The [constructor and parser packet](../notes/progress/2026-10-10-authentic-operation-source-next-gate.md)
locates actual Act-owned operation signatures and qualified `tick::next()`.
The exact reduced source parses with no diagnostics or recoveries. Frozen Oracle
owners establish primitive Unit for empty expression/type groups and empty-call
arguments; the earlier provisional zero-element tuple recommendation is withdrawn.
Next extend ordinary Unit constructors/comparison and actual Act operation
formation/resolution through compositional Apply, after the moving concrete/co
annotation lease freezes and is integrated. Public enum extensions require a
pre-write conformance gate. This source lookup does not supply complete Call
request execution, attachment hygiene or production cutover evidence.

### Concrete/co annotation initial review and active repair (2026-10-10)

The [frozen review record](../notes/progress/2026-10-10-concrete-effect-initial-review.md)
records three passing owning kernel tests and an owning build failure caused by
three syntax-only-dev-dependency references. The complete M3 review barrier found
one semantic and three resource majors: unrelated old conflict replay, quadratic
annotation recovery scans/unbounded type depth, repeated view copies and missing
extrusion scratch coexistence on nested/failing paths. Exact-conformance review
otherwise passed. A fresh implementer exclusively repairs the same twelve source
paths; code is uncommitted and has no final verification claim. The architect
confirmed HIR provenance reexport, depth measurement, shared view reconstruction
and scratch ownership. Next freeze that repair, run owning build/integration and
kernel checks, and close the findings through independent delta review. This
stage supplies no actual source operation/subtraction or public cutover evidence.

The architect also confirmed the [next closed-lifecycle retirement gate](../notes/progress/2026-10-10-candidate-closed-lifecycle-retirement-next-gate.md):
give private candidate results their own typed owner and skip unused F5 finalizer
startup/finish, while preserving ordinary/historical closed observers. This removes
an actual old runtime prerequisite; it is not a transformed public scheme. Shared
solver writes wait for the annotation repair's integration. Genuine transformed
scheme extraction/independent use remains a subsequent design and implementation
gate under the approved public-root policy.

### Concrete/co annotation checkpoint verified (2026-10-10)

The [implementation delivery](../notes/progress/2026-10-10-concrete-effect-annotation-implementation.md)
connects actual nullary declaration identity and whole-binding annotations to
paired negative checking/positive publication, immutable concrete support and
allowance with symbolic future checks, actual scheme/extrusion/SCC transport and
transactional diagnostics/accounting. All accepted M3 findings and later runtime
compilation causes are closed by fresh delta review. The focused matrix passes
43 tests; candidate all-target and feature-free owning checks pass without warnings.
No benchmark or full semantic proof was performed. Deep HIR fixture tests use
dedicated 16 MiB workers; an isolated 2 MiB probe localizes a separate 128-group
overflow inside `yu_syntax::parse_file`, before HIR can guard its parsed artifact.
That parser owner remains explicit and is not claimed fixed by larger test stacks.

The private candidate closed-lifecycle retirement gate is implemented and
verified in the checkpoint below. Next implement authentic Unit/operation
formation with the actual declaration-result
consumer. Source Apply alone constructs an inert operation request carrier in
frozen Oracle; forcing/execution is a distinct later owner, so family contribution
must not be injected merely from callee shape. Genuine contravariant attachments,
complete Call, public transformed schemes, soundness/principality and default
F5 replacement on `yulang3` remain open. Pending questions stay excluded from Git.

### Candidate closed-lifecycle dependency withdrawn (2026-10-10)

The [delivery record](../notes/progress/2026-10-10-candidate-closed-lifecycle-retirement.md)
records a genuine private candidate result owner, shared actual inference data,
candidate startup/finish without closed finalization, and Call observation
borrowing its real inputs. Legacy public closed results retain their real arena;
no empty closed payload substitutes for missing public schemes. M2 semantic and
regression reviews plus fresh delta review close the one accepted compilation
finding. Seven lifecycle guards, the 43-test annotation/intrusion/local matrix
and two focused historical closed controls pass (52 tests total). Candidate
all-target and default owning checks pass without warnings. Measurement budget
consumed: zero. No new semantic theorem is claimed proved or retired by this
runtime ownership removal.

Unit primitive adapters are integrated and verified in the checkpoint below.
Next implement actual operation
declaration/carrier and justified result-consumer formation. The isolated
`/tmp/yulang-unit-types-production-candidate/` delta supplied the production
types input; the integrated verification is recorded below. Complete Call, contravariant effect
attachments, hygiene correspondence, public transformed schemes,
soundness/principality and target `yulang3` cutover remain active.

### Oracle Unit primitive integrated (2026-10-10)

The [Unit delivery](../notes/progress/2026-10-10-unit-primitive-integration.md)
integrates the actual production types delta with HIR explicit/implicit Unit,
annotation Unit, solver comparisons, capture/freshening/extrusion/rollback,
boxed/flat/normalized/replayed closed storage and primitive result projection.
M2 semantic/regression reviews, batched repairs and fresh delta reviews close
the accepted findings. Unit-free diagnostic domains retain their old budget;
Unit-bearing domains now have consistent checked sizing and indexing. 129
distinct focused tests and all-feature owning/workspace checks pass without
warnings. No benchmark or broad semantic proof ran. Historical assertions and
discriminators are preserved; pending questions remain excluded from Git.

Next: retain authentic Act operation declarations, qualified operation identity,
declared signatures and inert carrier formation without another registry
admission prerequisite. The architect confirms current authority permits this
producer slice. Actual declared-result elimination must have an executable
owner and survive aliases/scheme use; source callee shape cannot justify Force.
Complete Call, contravariant attachments, hygiene, independent transformed
public schemes, soundness/principality and target `yulang3` replacement remain
required. A separate Unit closed incoming-use replay and source diagnostic-span
coverage remain unverified by this primitive slice.

### Authentic operation producer integrated (2026-10-10)

The [producer delivery](../notes/progress/2026-10-10-operation-producer-integration.md)
retains actual nullary Act members and qualified operation occurrences, resolves
visibility/ambiguity, and builds fresh declared signatures through the shared
structural constructor. Only the outer return-effect interface receives the
owning family; original members and symbolic tail remain. Lookup is exact-pure,
and typed operation provenance is preserved by existing view transport. No
registry admission, early satisfiability condition or shape-derived Force was
introduced. M2 semantic/conformance reviews and fresh repair deltas are closed;
66 distinct focused tests plus all-target/all-feature owning and workspace
checks pass without warnings. Zero measurement processes or samples ran.

The old empty-Act unsupported fixture premise was replaced by positive family
coverage after pre-write conformance adjudication: actual Oracle body lowering
has no minimum-member requirement. Genuine unsupported/private/duplicate and
recovery boundaries remain. This is producer compatibility expansion, not
closure of complete Call or source effect hygiene.

Next safe legacy withdrawal: candidate startup still reserves unused F5 draft
scratch in `InferenceSession::try_new`; all real DraftScheme consumers belong
to the legacy SCC branch. Guard that reservation by its existing legacy owner
and verify candidate success under an injected Drafts failure with a legacy
failure control. Actual execution consumers/contravariant attachments,
independent public schemes, soundness/principality and target `yulang3`
replacement remain active. Operation-specific full capture/intrusion execution,
backend execution and complete semantic proofs remain unverified here.

### Candidate unused F5 draft dependency withdrawn (2026-10-10)

The [resource withdrawal](../notes/progress/2026-10-10-candidate-unused-draft-withdrawal.md)
guards legacy `DraftScheme` startup capacity/reservation by its existing legacy
owner. Graph inference stages captured graphs and has no draft consumers;
candidate startup no longer fails on this unused F5 lane. Two new regressions
verify real exports/fresh uses/Calls under an armed Drafts failure, ordinary
legacy consumption/atomic release/retry, and zero physically sampled candidate
draft capacity/bytes. M1 independent regression review found no issue. Ten
focused tests, default check and all-target/all-feature owning check pass
without warnings. Measurement budget consumed: zero.

This closes the exact safe withdrawal identified above. Next: construct the
authentic execution/consumer supplier and contravariant effect attachment at
their actual owners, then migrate independent public schemes/default entrypoint.
Complete Call, hygiene, soundness/principality and target `yulang3` cutover
remain required; no proof node is declared closed by this resource removal.
Historical public observer/default F5 owners remain real migration targets.

### Bare Value entry admission withdrawal (2026-10-10)

The [bounded source-owner repair](../notes/progress/2026-10-10-value-entry-effect-integration.md)
replaces the candidate lambda's closed-empty argument-effect admission port with
formal-level entry/invocation rows and ordinary `entry <= invocation`,
`bodyE <= invocation` constraints. Unused, identity, alias, local, recursive and
higher-order effectful argument uses are accepted; source lookup/construction
stay pure, and independent invocation/result fibers and rollback are checked.
M2 semantic/regression review and repaired test deltas are clean; historical
graph observer pre-write and closure reviews pass. 62 distinct focused tests,
default/owning all-target all-feature and workspace checks pass without warnings. This is a runtime
constraint dependency withdrawal, not a closed semantic theorem or native
execution certification.

Next: retain source-owned entry roles through whole-binding annotations and
scheme transport; construct actual negative formal annotation and function-local
Value/effect filter boundaries, then independent public scheme publication and
default migration. Full Call, hygiene, soundness/principality and `yulang3` cutover
remain required. Formal-filter research checkpoint `9d7967c3a` has an accepted
source-correspondence defect: Oracle consumes/registers filters at row bound
insertion. A disjoint research-only repair is active; do not adopt its old
retained-filter transition or treat bounded checker agreement as hygiene proof.

### Formal filter insertion correspondence repaired (2026-10-10)

The conditional [transition model](../notes/progress/2026-10-10-formal-filter-transition-contract.md)
now registers/checks row filters at both insertion orientations and erases their
left filter before retaining bounds. Later Function replay preserves the pop
word without moving the consumed filter into latent ports. Independent delta
review closes the accepted source mismatch within the finite model; primary
checker passes 341 words, 3,087 replay inputs, 68 event orders and seven mutations,
with maxima 11 facts/four pending tasks. One checker process, zero timing samples
or benchmark processes. Earlier `9d7967c3a` insertion correspondence is superseded.

This is no hygiene theorem or production cutover: source construction, authentic
attachment lifetime/ID freshening, support projection, weighted-cycle termination
and actual SCC/rollback remain required. An architect is resolving the smallest
coupled production cut; a read-only Oracle map follows actual generalized
subtraction IDs and frame/output lifetime. No new source restriction or registry
adoption prerequisite is inferred.

### Unused observer Call inventory withdrawn (2026-10-10)

The [preflight retirement](../notes/progress/2026-10-10-unused-observer-call-inventory-retirement.md)
removes the candidate's discarded historical Call-vector construction and its
allocation failure prerequisite. Validation-only preflight keeps depth/scope/
error checks; historical observer inventory and real LocalSource inputs remain.
M1 independent review, pre-write fixture adjudication and fresh narrow delta
review close; 24 distinct owning regressions and coherent phase checks pass.
No genuine Call or semantic proof requirement was retired.

The separate primitive annotated-formal artifact is frozen and its focused
checks/reviews pass; integrated and pushed as `a49f0f1e9`. The
full negative Function formal remains a coupled source-owned interface,
contextual propagation and terminal incidence consumer gate. Independent public
schemes, complete semantic requirements and target `yulang3` cutover remain open.

### Primitive formal source annotations integrated (2026-10-10)

Withdrawal policy also records per-mechanism completion evidence in the
[current authority](../notes/design/2026-10-10-simple-sub-legacy-withdrawal.md#mechanism-by-mechanism-completion-evidence).
Adding a parallel route alone is insufficient; remaining consumers and genuine
semantic requirements stay explicit. Policy-only clarification uses M0 with no
new compiler checks or reviewers.

The [primitive delivery](../notes/progress/2026-10-10-annotated-primitive-formal-integration.md)
connects actual grouped Int/Unit formal annotations to ordinary positive body
information and negative argument checks before body synthesis. Top/local,
ignored/multiple formals, annotation-only inferred results without actuals,
fresh aliases, effectful arguments and transaction rollback are verified.
M2 semantic/source conformance review and fresh repaired test delta close.
Nine distinct new owning regressions and 83 distinct focused phase tests pass;
owning all-target/all-feature, workspace and default checks pass without warnings.

Next critical cut: paired source-owned Function formal interface and executable
head/residual/filter transport. Always exposing the annotation-negative domain
is a private construction candidate replacing the old calledness/observed-
wildcard decisions; retain body shared-row closure and prevent direct actual
provider flow into the raw body formal. Omitted effect ports, attachment lifetime/
freshening, latent returned values, equality/replay/rollback and surviving
independent same-family incidences remain real requirements. Source evidence
is available, but neither this candidate nor finite model consistency certifies
full hygiene/principality. Independently owned public schemes, default migration,
complete Call and target `yulang3` cutover remain active.

### Paired Function formal implementation verified (2026-10-10)

The [constructor gate](../notes/progress/2026-10-10-paired-function-formal-construction-gate.md)
has independent pre-write semantic/source conformance review. Separating the
negative interface with positive-bottom omitted ports loses actual callback
effects; shared per-Function argument/result rows replace that rejected route.
Named variables retain binding scope across formals and the top whole-binding
annotation. Ordinary row unions remain valid; no rigid annotation mode is added.
Only Function/named-variable temporary unsupported fixtures may move to positive
coverage under recorded pre-write adjudication.

The source/test leases are frozen and complete. M2 independent runtime reviews
and fresh store/resource/test deltas close, including the final default feature
guard. Paired callback effects and scoped ordinary annotation variables now use
actual constraint flow. The stronger failure witness exposed and repaired the
store's single-admission rollback assumption: all new keys and consumed receipts
are removed, with duplicates and serial reuse covered. No calledness, early SAT,
registry or second semantic memo is added.

The [delivery record](../notes/progress/2026-10-10-paired-function-formal-integration.md)
records 93 distinct focused tests (nine new owning regressions), all-target/all-
feature owning and workspace checks, final default owning check and store test,
no warnings, zero timing samples/benchmark processes. Primary alone owns Cargo
and Git. Broad runtime/parity/backend checks and full proofs were not run.

Next: authentic explicit effect attachment/context/filter construction and
consumer integration, then independently owned public export/import and actual
ordinary solver publication/query migration. Both read-only production maps are
complete; do not repeat mapping as progress. Wildcards, complete Call, hygiene,
soundness/principality and target `yulang3` cutover remain active. The pending
question bundles remain excluded from staging.

### Question-board cleanup at user request (2026-10-10)

The user explicitly requested deletion of unnecessary q & a and commits for
needed material. All 22 tracked decision bundles have question/current draft/
approved answer/receipt files and remain as decision provenance. The three
untracked directories contain no finalized approved answer: ordinary-value q1
has a withdrawn premise and unapproved d1/d2/d3 drafts; registry q1 is superseded
by integrated q2/q3; registry q4 is unadopted research removed from the inference
critical path. Their eight files are deleted; dispositions remain in the
[cleanup record](../notes/progress/2026-10-10-question-board-cleanup.md), and live
links/index wording are repaired. Earlier pending/preservation statements above
are historical checkpoint descriptions, superseded by this cleanup.

No answer was adopted by housekeeping. Approved committed bundles are unchanged;
complete Call, effect hygiene, soundness/principality and inference/public/default
migration remain active. M1 independent read-only reference/disposition review
has no blocking findings; narrow file/link/diff checks pass. Zero compiler
builds/tests or performance samples/processes for this record-only cleanup.


### Explicit effect attachment: callback example and cycle-source audit (2026-10-10)

The user mentioned this source example:

```yulang
my f(cb: (int -> [io] 'c)): 'c = run_io: cb 1
```

The user initially gave the scheme
`(int -> ['b, io] 'c) -> int -> ['b] 'c`, then corrected it as a mistake on
2026-10-10. Do not treat that scheme as an expected result, a hygiene
obligation, or evidence about handler residual behavior. The intended
correction has not yet been supplied, so this example establishes no particular
source/result contract. Existing conditional hygiene results do not prove an
end-to-end derivation for this example. The current candidate supports
singleton variable-only formal effect tails as ordinary rows, but still
rejects concrete `[E]` attachments; the corrected example remains unresolved.

The conditional finite attachment model checkpoint `b54e03d97` passes 72
valuations, 85 polarity paths and seven named shortcut checks. Frozen Oracle
source supplies a relevant cycle pattern test and distinct owners: same-TypeVar
contextual self-constraints are discarded; nonself variable bounds use
support-based admission subsumption while exact replay weights are retained.
This corrects the extrapolated finite model's unrestricted-cycle diagnosis; it
does not prove all-machine termination or successor correspondence. The
[cycle audit](../notes/progress/2026-10-10-explicit-effect-termination-source-map.md)
records exact anchors and remaining obligations.

The successor's existing same-endpoint shortcut applies only to context-free
identity constraints. Independent source inspection found no contextual
subtraction carried by its task, bound, extrusion, or intrusion representations;
therefore the Oracle self-edge rule cannot be copied as a termination fix. This
is a real source-construction gap, not evidence for an arbitrary work cap or a
new semantic choice. The exact contextual skip premise is that every local
check, residual/output consequence, latent Function consequence, and provenance
obligation remains owned and live after equality, freshening, and rollback.

The `ColonApplicationTail` source carrier now reaches `LocalSourceForm::Apply`
as one inline argument, retaining the nested `cb 1` application and source
identity. Focused HIR regressions cover this spelling, ordinary ML/Call tails,
recovery/layout rejection, and outer sequence ownership. This is syntax/HIR
transport only: it does not establish `run_io` semantics, typed effect-port
flow, subtraction, or the user's target scheme. See the
[source bridge checkpoint](../notes/progress/2026-10-10-colon-application-source-bridge.md).

Follow-up audits found that count-presence admission cannot stand alone: `POP_i`
and `POP_i²` have the same presence signature but differ when replayed against
`PUSH_i`. A separate source audit found an existing recursive back route from
published result effect through recursive invocation, application and body
back to the returned effect. Thus a future POP-bearing `R <: W` edge would
close a contextual cycle. The direct `loop f` / `f 1` shape keeps its POP on
the public wrapper, but a tuple-annotated nested Function supplies a distinct
pre-body route: its POP wraps skeleton outputs, then a returned-Function
comparison yields `P <: Z` under right POP. Adding the real tuple pattern
`\(f, _)` forces the anonymous input to a tuple and invokes the nested
callback: its annotated `PUSH_i` cancels the incoming right `POP_i`, and its
output-value wrapper leaves right `POP_i²`. The callback result is discarded,
so no return to that same Function comparison is traced. This is an Oracle
source-construction trace; it does not yet show replay returning to the same
eligible bound slot or unbounded debt. The current successor still rejects
concrete formal attachments and does not model this tuple route. See the updated
[cycle audit](../notes/progress/2026-10-10-explicit-effect-termination-source-map.md)
and [source trace](../notes/progress/2026-10-10-contextual-effect-source-correspondence.md).

Applying `(f 1) 2` with callback result `'c` creates a right-`POP_i²` Function
demand on `'c`, but no positive Function lower. Refining the annotation result
to `(int -> [_] 'c)` supplies a real nested positive Function: it is compared
to that demand under right `POP_i²`, and its inner return-effect lower reaches
the second call effect with both POPs intact. This is a distinct nested
constructor; the cycle does not return to the original callback Function
comparison. A separate recursive effect path does revisit the same `h <: E`
Effect bound slot: right `POP_i²` followed by left `POP_i` produces right
`POP_i³`, then higher counts. Oracle's alias guard suppresses these variants
using endpoint identity and right attachment-ID presence. This establishes
source-cycle existence, not guard soundness or a successor admission rule.
The exact next gate is an independently reviewed successor contextual
bound-admission simulation through level-selected orientation, current/future
opposite replay, Function children, residual/output projection, provenance,
extrusion, freshening, intrusion and rollback. A fixed-witness source audit
shows its existing `PUSH_i` belongs to outer owner `t` and is consumed at the
outer callback call; the fixed witness alone does not provide the
`PUSH_i²` continuation that distinguishes `POP_i²` from `POP_i³` at the mapped
`h <: E` suffix. The paired row-tail witness has two distinct HIR owners: its
original annotated callback is a field of `x`, while local annotations `a` and
`b` refer to the anonymous tuple parameter field `f`. The recursive use
`(loop x) x` reconnects these owners through application and tuple projection,
so owner distinction alone does not show the relation is absent. In the
observed path, however, the original `PUSH_i` meets right `POP_i` and becomes
identity at `Pos6/TV6 -> Neg33/TV20`; the subsequent inner comparison carries
right `POP_i²`. The four-edge `t→e→h` table is therefore conditional, not the
observed trace. See the
[bridge correction](../notes/progress/2026-10-10-paired-annotation-push-bridge-correction.md)
and [conditional construction](../notes/progress/2026-10-10-paired-annotation-push-bridge.md).

The pinned instrumented harness parsed and lowered the symbolic-tail variant
without errors; it did not execute the program. The original wildcard source
parses but fails lowering with `WildcardEffectRowInTypePosition`. The ordered
trace finds left POP1 at Pos33/TV20 → Neg69/TV50 before left POP2, which the
earlier POP1 bound subsumes; it does not show POP2 suppressing POP1. At
Pos4/TV5 → Neg69/TV50, right POP2 is inserted and later right POP3/POP4 are
subsumed. The trace lacks the source-origin/freshening map needed to identify
TV50 as the named source `E`, and records no admitted mixed PUSH/POP context.
Do not use it as an `e/E` versus `h/E` proof. The callback scheme previously
called the user's exact target was later corrected by the user as a mistake;
neither that scheme nor the earlier no-extra-arrow transcription is a verified
result. The intended scheme remains unspecified. Positive covariant annotations
already have a private source/propagation implementation. Full hygiene,
complete Call, soundness/principality and public/default F5 cutover remain open.

### Contextual effect cyclic algebra: exact partial solution (2026-10-10)

The direct mathematical task started at remote `b69bb905` and incorporated
upstream `2a7cc93c`'s inline colon source bridge. The
[integrated result](../notes/progress/2026-10-10-contextual-effect-saturation-results.md)
records a proved cyclic-algebra subsystem, not closure of the complete
contravariant source attachment. Its result note preserves two historical
scheme transcriptions; the user later corrected the claimed target scheme as a
mistake. Neither is a verified result, and the intended scheme remains
unspecified.

The independently reviewed
[theorem](../notes/progress/2026-10-10-contextual-effect-path-theorem.md)
establishes exact finite normal-form languages for one attachment ID on any
finite one-sided PUSH/POP graph, including arbitrary cycle powers. Balanced
reachability plus a two-phase automaton preserves every exact POP count. A
second theorem uses exact predecessor thresholds and Dickson's lemma to decide
simultaneous upward active/filter observations for all initial count vectors,
including future lower seeds. No numeric count bound, iteration cap, early
callee resolution, complete registry, SAT prerequisite or new source rule is
used. The POP-only self-loop omission theorem preserves only its specified
side-effect-free active observations, not full residual-context identity.

The [counterexample checkpoint](../notes/progress/2026-10-10-contextual-effect-counterexamples.md)
is published at `dd6b02ad`. It proves that unrestricted support keys are not
future-replay congruences, unbounded POP powers have infinitely many
continuation-distinguishable classes, and actual normalized directed replay is
nonassociative. These are algebraic witnesses with explicit source-reachability
limits, not claimed source bugs in Oracle. Actual source formation confirms
that shared rows can retain different attachment IDs.

Research implementations pass 256 cyclic word graphs, 15,182 bounded actual
walks, 3,304 decoded exact normal-form witnesses and 12,348 complete finite-DAG
observer queries, plus large-count/correlation/late-lower/iterator controls.
Independent code review exposed exhausted-iterator edge loss and guarded-input
bypass; the repair and new regressions passed fresh delta review. The algebra
checker passes 729 literal/count comparisons and 528 pair distinguishers. None
of these counts substitutes for the general proofs. No Cargo/Oracle execution,
runtime subtraction, production intrusion/freshening/rollback or full source
test is claimed; no production solver was added or modified.

The concrete remaining correctness boundary is the
[source/consumer audit](../notes/progress/2026-10-10-contextual-effect-source-correspondence.md):
Function swap/mixed replay needs its actual bracketing; row residuals change
family payloads; compact projection observes pending POP entries even at zero
active depth. The current finite upward observer is not a proof for those
operations. Follow-up research sharpens the next cut. Under a conditional
grammar cycle, `both_from_right` can double right debt and generate powers of
two; ordinary finite-automaton or pushdown output-language representations
cannot capture every exact residual. Componentwise upward-antichain predecessor
closure also fails for full three-coordinate replay. These are conditional
method obstructions, not undecidability or source-reachability results; see the
[unreviewed proof-method report](../notes/progress/2026-10-10-bracketed-replay-decision-obstructions.md).
A separate bounded model shows correlated tree observers can distinguish inputs
with the same sign/active/presence summaries after residual-head consumption
and compact projection, while a restricted nested family admits a closed-form
observer. See its [conditional discriminator and checker](../notes/progress/2026-10-10-correlated-mixed-replay-discriminator.md).

The source-level hinge is now precise: determine whether the actual
`both_from_right` Function port and replay ownership can return recursively to
the same eligible bound slot, and whether the correlated tree observer's
shared-derivation premise can arise. Preserve exact replay trees and current
source guards while deriving that endpoint/port invariant. If the cycle is
source-reachable, derive an exact observer for it; if not, prove the reducing
invariant against output residuals, pending-POP projection, extrusion and SCC
merges. The source-owned constructor/transport/journal and callback result
remain open.

The existing conditional hygiene/owner/lifetime/transport theorems retain their
original premises. No canonical proof-DAG status or prerequisite was changed;
whole termination, source soundness/completeness, principality, public owned
schemes and `yulang3` cutover remain OPEN. No new question-board decision was
created or consumed.

### Mixed cyclic debt: exact finite observation completed (2026-10-10)

The user's “OK．やってください” continued the direct termination/meaning task
from latest remote `e2f29d0a`; concurrent source-owner audits through
`3bb355b56` were inspected and preserved. Mathematical checkpoint
`3b32ed3afa49c7d4105da46ba7783524c9fdb35b` is published. The
[new theorem](../notes/progress/2026-10-10-mixed-replay-observer-construction.md)
now decides arbitrary finite **debt-only cyclic grammars**, including binary
directed replay, swap, both-from-right and shared choices, observed by any fixed
finite PUSH-bearing mixed continuation. It preserves exact active count and
pending/left/right presence at every node, with the specified fixed-family
filter/terminal/compact corollaries. The actual query PUSH mass B yields a
finite image with `(B+2)^2` states per nonterminal; the original exact grammar
is retained for future queries. This is a proved query abstraction, not a
semantic POP cap, permanently erased count, or finite-test completeness claim.

The [source callback circuit](../notes/progress/2026-10-10-mixed-replay-source-cycle.md)
uses shared argument/result `'c` and feeds `f f` back into the tuple callback.
Its primitive `F --L1--> C --R2--> R --R1--> F` circuit returns a concrete
Function lower under debts `1+4k` to the same callback comparison. Var-only
support suppression does not apply to these concrete lower consequences.
Independent source review corrected a genuine constructor error: absent
argument-effect annotation is `NegRow([],Top)`, not `NegBot`. Both argument
ports therefore swap; this source supplies no copying Effect child. Source
constructor/replay correspondence is reviewed, while parsing, successful
lowering/generalization, Oracle execution and acceptance remain unclaimed.

The [integrated report](../notes/progress/2026-10-10-mixed-debt-observer-results.md)
records the complete proof boundary, counterexamples, independent mathematical
review, fresh source/code repair closure and the executable
[`research_mixed_debt_observer.py`](../tools/research_mixed_debt_observer.py).
The final bounded check passes 147 assertions, 440 literal observer evaluations
and 11 exact finite-DAG values. The independent code reviewer also checked 216
terminal combinations and 400 shared-hole continuations at all nodes on the
reviewed snapshot. Count/entry erasure on empty family or filter failure was
repaired; the last minor reference-only repair distinguishes same-name binding
occurrences. These are research checks, not compiler regression counts.

The next single mathematical bottleneck is a contextual recursive component
into which PUSH-bearing input can return. Either decide that component exactly
or derive its source-owned separation into debt recursion and finite consumers.
The latter is not assumed for all source programs. Before final integration,
remote advanced through `92f07a06`; its paired symbolic annotation bridge was
inspected and preserved. It connects `t → e → h` with same-ID PUSH evidence,
while actual first-survivor admission at `e/E` and `h/E` remains open. This
constrains the next source witness without changing the debt theorem.
Exact residual-key gamma,
source filter registration, authority-preserving extrusion/SCC intrusion,
freshening and journal rollback remain implementation/semantic obligations.
No production source-owned attachment or second solver was enabled; the scheme
previously called the unexecuted source target has been retracted by the user
as a mistake, and the intended source target remains unspecified.
No canonical DAG node was closed, no new semantic question was opened, and
`yulang3` was not changed.

### Formal-effect admission reduction and Function-only debt circuit (2026-10-10)

The merged [source recursion audit](../notes/progress/2026-10-10-recursive-push-source-invariant.md)
finds two admitted paired-`as` source schemas that construct recursive
left-only PUSH components, including one actual full `(POP^p PUSH^n)` lower.
Its complete pre-generalization owner classification received independent
source review. This falsifies a universal debt-only source invariant for those
schemas. The [exact recursive full-pair observer](../notes/progress/2026-10-10-recursive-push-observer-construction.md)
reduces one-ID left-only recursive grammars followed by fixed finite mixed
continuations to PVASS reachability; its mathematics remains unreviewed. The
[subcase checker and algebra attack](../notes/progress/2026-10-10-recursive-push-algebra-attack.md)
cover exact linear and nonlinear families with bounded deterministic checks,
also pending independent review. None of these is Oracle parser/compiler
execution, a general recursively mixed observer, or production permission.
The paired-`as` source route is distinct from the callback source example and
does not resolve same-row contextual self admission.

Two research-only checkpoints were pushed after the earlier correction that
restored the returned `int ->` layer in the transcription. The user later
retracted that claimed result as a mistake, so it is not the current target:
[`4d5991b37`](../notes/progress/2026-10-10-formal-effect-admission-construct.md)
isolates an exact identity-context bound for the currently admitted
effect-free formal subset and gives a conditional joint finite observer for
debt-only recursive grammars with a fixed finite mixed continuation. It does
not certify the next effect-row constructor's recursive components.

[`bda9ee399`](../notes/progress/2026-10-10-formal-effect-admission-falsify.md)
records the Function-only source shape
`my knot (f: 'c -> [io] 'c) = f (f f)`. Under the pinned annotation/application
constructors and retained concrete-lower replay, it generates the prospective
debt circuit `F -> C -> R -> C`, with a left POP on `C -> R` and unbounded
natural debt counts. It uses no Tuple or provider backflow. The certificate is
reviewed by one independent compiler referee with no findings in its declared
conditional scope; see the [review record](../notes/progress/2026-10-10-formal-effect-admission-falsify-review.md).
It is not parsed/accepted execution and does not establish a returning PUSH
cycle. A later bounded implementation accepts singleton variable-only effect
tails on formal Function annotations as ordinary shared rows; concrete formal
effect rows and closed `[]` remain unsupported. See the
[implementation record](../notes/progress/2026-10-10-symbolic-formal-effect-tail-integration.md).

The next frozen artifact,
[`2026-10-10-contextual-self-discharge-falsifier.md`](../notes/progress/2026-10-10-contextual-self-discharge-falsifier.md),
constructs a three-formal source-shaped route where `accept g` registers an
Empty filter on the same symbolic Effect tail whose annotation owner is an
otherwise-unused `f`. If the dropped self candidate is counterfactually
retained as a positive lower `(T+, PUSH_i[{io}])`, that filter rejects it;
dropping the lower leaves this local check vacuous while preserving the
original registration. Its [independent compiler-referee review](../notes/progress/2026-10-10-contextual-self-discharge-falsifier-review.md)
confirms the source ownership, filter check, and exact premise. This remains a
conditional discriminator, not an admitted or executed witness: Oracle drops
the candidate, and the current equal-level successor route selects an upper
row, not the positive lower required by the fixture. Current successor still
rejects concrete formal effect rows; singleton symbolic-only tails do not carry
the contextual attachment needed by this discriminator. The local result does
not settle whether
upper retention is observable after extrusion and later scheme replay;
contextual self-discharge, full Effect hygiene, complete Call, generalization,
public cutover, and F5 replacement remain open.

The follow-up [upper self-filter owner trace](../notes/progress/2026-10-10-upper-self-filter-observer.md)
and its [independent review](../notes/progress/2026-10-10-upper-self-filter-observer-review.md)
confirm that the prior Empty-filter discriminator does not observe upper-only
retention in its local no-lower trace. Negative extrusion separately creates a
positive parent-to-copy lower and copies selected uppers without replay;
parent metadata alone is not an SCC edge. A later scheme may observe the
context if it reaches original T plus an anchored copy. The independently
reviewed [source-root bridge](../notes/progress/2026-10-10-upper-self-source-root-bridge.md)
now derives a real omitted-row route where the later scheme reaches original T
and anchored copy C through the retained formal domain and captured lower.
Conditionally, a separate symbolic-only formal routes Empty to fresh T' and
distinguishes retaining versus dropping the contextual PUSH upper. This is not
an admitted explicit-formal witness: construction, contextual payload
transport, replay/filter behavior and full SCC handling remain premises. See
the [bridge review](../notes/progress/2026-10-10-upper-self-source-root-bridge-review.md)
for the bounded independent result and exact omissions.

The [symbolic formal-effect tail slice](../notes/progress/2026-10-10-symbolic-formal-effect-tail-integration.md)
now shares named effect rows across formal ports and the whole-definition
annotation. Its compiler-referee delta review and focused regressions close only
that ordinary-flow case, including a late concrete lower and rollback. It does
not implement concrete `[E]` subtraction, contextual payload transport or
filter/replay semantics.

The authentic explicit-formal constructor and contextual payload transport
remain the next implementation slice. The [contextual residual-owner design](../design/2026-10-10-contextual-residual-owner-design.md)
now covers annotation identity, filters, contextual task/memo/bound/replay
identity, both residual directions, all Function-port transforms,
level-selected extrusion, capture/freshening, same-SCC parent-copy intrusion,
and rollback. Independent semantic and spec reviews closed their findings at
the recorded hash. The user's approved q1/a1 choice now selects constructor
lineage in the [narrow authoritative decision](../design/2026-10-10-contextual-residual-lineage-selection.md).
This closes only the residual-identity choice; contextual construction,
fan-out, reverse feedback, exact admission and dependent explicit-concrete-
formal implementation remain open. The integrated question receipt records
the approval and design freshness validation.

The [contextual attachment/admission design](../design/2026-10-10-contextual-attachment-admission-design.md)
is authoritative for the private contextual carrier and exact acceleration of
the two reviewed paired-ascription cycle shapes. The approved q1/a1 scope
requires preserving exact unbounded contexts, late-edge certificate
invalidation, dependent-result withdrawal, private deferral, and atomic
rollback. It does not enable arbitrary concrete formal rows or claim the
general mixed-component procedure. The finalized answer bundle is integrated
at `7a6490172`; its validation receipt and authoritative design-status
synchronization are recorded. Independent source mapping confirms the exact
callback remains unavailable in the candidate: concrete formal `[io]` is
rejected, `LocalSourceForm` has no `Catch` carrier, and `run_io` is an ordinary
name rather than a handler intrinsic. Complete Call, the generic handler/source
route, public/default inference, and F5 cutover remain open.

The reviewed evidence does not establish a source-reachable independent gamma
ingress, and does not prove that no such source exists. It must not become a
source restriction. The unbounded paired-`as` left-PUSH family also rules out a
raw finite context-entry cap as the entire admission argument. No numeric
resource threshold, diagnostic, or source rejection is selected. With lineage
identity and the reviewed contextual gate now selected, implement and verify
the bounded carrier/circuit gate; then continue the full explicit-attachment
and public-cutover work. Concrete annotation construction, filters/use,
generalization/freshening/rollback, public inference, full Call, hygiene and F5
cutover remain open.

### Catch source bridge audit (2026-10-10)

The current syntax tree has Catch expression/arm nodes, but the Pattern parser
does not admit the qualified operation-call arm shape needed by the proposed
handler source, and LocalSource has no arm-owned binder/scope representation.
Adding only a Catch carrier would preserve syntax without enabling inference.
The read-only audit therefore made no syntax-only edit. A useful bridge must
retain resolved operation patterns, resumption/payload binders and branch
bodies, then connect them to the selected contextual effect consumer. See the
[source bridge audit](../notes/progress/2026-10-10-catch-source-bridge-audit.md).
The pending contextual-admission choice remains separate; this finding does
not redefine or waive complete Call, public/default inference, or F5 cutover.

### Newly integrated mixed-context research (2026-10-10)

Four upstream research artifacts were integrated at `9610f0c3e` through
`c2674ba5a`, followed by the independent-replay interface characterization at
`de5c400d6` and constructive raw identity-self factoring at `65557b27`.
Their individual independent reviews are now complete within the stated
scopes; the [current review record](../notes/progress/2026-10-10-complete-mixed-self-edge-results.md)
records frozen hashes and two primary-only minor prose corrections. Historical
producer handoff headers are not the current review status. None changes
source semantics or production code.

- The two-ID shared-child construction proves undecidability for an unguarded
  abstract mixed-weight grammar support query. Its bridge to authentic source
  programs and a required compiler consumer is explicitly absent, so it does
  not prove source-level impossibility or authorize restricting source input.
- The nonpositive-displacement result gives an exact finite observer for its
  stated grammar class and arbitrary finite future contexts. The invariant is
  not established for actual source suppliers; positive-displacement recursive
  suppliers remain outside that result.
- The self-edge theorem proves that actual identity I is the only universal
  constant replay unit on mix-normal inputs, in either orientation. A raw
  nonidentity context whose isolated mix is I is insufficient. On raw inputs,
  even actual I performs mix and cannot simply be deleted. Checks and filter
  events remain separately owned; the source bridge remains conditional on
  the missing explicit contextual constructor and transport.
- The constructive normalizer removes bare I/mix self productions on arbitrary
  raw recursive suppliers by retaining every other incoming E and adding
  mix(E). A finite-derivation translation proves exact languages at every
  original vertex, without a stored-normality or debt bound. Future additions
  and supplied SCC quotients refactor original producers; plain self aliases
  are independently removed. Remaining arbitrary recursion is not decided.
- The independent-replay characterization shows that primitive bound replay
  chooses lower and upper records independently, while `both` duplicates one
  selected input atomically. Therefore the shared-child PCP reduction does not
  transfer to that primitive interface, and replacing atomic `both` by two
  independent children is unsound. The exact recursive decision question for
  this interface remains open.

These results reinforce the need to keep residual identity, source admission,
and generic algebra decidability as separate obligations. They do not resolve
the residual-lineage proposal or justify a finite entry cap. The independent
mathematical work proceeds under the existing annotation policy; this phase
selected no residual-lineage policy and created no new question. Authentic
source admission and the coupled constructor/consumer lifecycle remain
necessary before enabling the concrete formal-row path.

### Returning recursive PUSH: direct source instance solved (2026-10-10)

The user's follow-up explicitly required solving recursive PUSH or deriving a
source separation into debt recursion. Starting at latest remote `e3ddf9f1`,
this phase produced a direct solution, with independent mathematical, source
and executable reviews. Incoming documentation updates through `566310fa`
were inspected and preserved; no compiler or rule dependency changed. See the
[complete integration record](../notes/progress/2026-10-10-recursive-push-results.md).

The [main theorem](../notes/progress/2026-10-10-recursive-push-observer-construction.md)
at `c78346a8` decides exact finite mixed observations of arbitrary finite
left-only recursive grammars with independent binary replay. Both leading
POP and active PUSH counts may be simultaneously positive and unbounded.
A global-minimum certificate retains the exact pair in a finite PVASS;
the published general PVASS decision theorem supplies termination. The proof
does not cap recursive PUSH mass or assume the residual set semilinear.
It does not cover recursively shared children, right debt or mixed swap/both.

The [source construction](../notes/progress/2026-10-10-recursive-push-source-invariant.md)
at `e941268b` supplies authentic consecutive `as` annotations on one actual
provider lambda, with an eager real Act-operation Row seed. It gives the
distinct-owner `r --PUSH_i--> e --identity--> r` recurrence. A nested variant
adds `h --POP_i--> e --identity--> h` and admits every exact `(p,n)` at `e`.
Concrete Row lowers bypass Var-only self omission, support suppression and
frontier skipping. All incoming Function ports of these exact programs were
audited: their entire pre-generalization recursively reachable component is
left-only, one-ID/fixed-family, hence within the main theorem. This refutes a
universal debt-only source invariant and signed-depth collapse. Neither new
source was compiled; public acceptance/generalized future uses are unclaimed.

The [additional algebra theorem](../notes/progress/2026-10-10-recursive-push-algebra-attack.md)
at `7b4f3e68` directly accelerates a recurring PUSH/right-POP cancellation
context, full-pair affine growth and explicitly shared active doubling.
The [research observer](../tools/research_recursive_push_observer.py) at
`79e02343` decides finite DNF count queries for these supplying families and
the source push ray/all-left-pair sets. It uses exact finite signed-carry
automata, preserves every raw observer node and correlated hole choice, and
has no numeric unfolding cutoff. It is not a general PVASS implementation or
a second production solver. Producer runs passed 8,685 and 4,939 assertions;
an independent literal/kernel/trace probe passed 80,478 assertions. The final
code SHA and exact verification envelopes are in the integration record.

All three independent reviews had no blocking/major defect. Two source-only
minor inventory/arithmetic wording corrections were applied and checked by
the primary. Source/compiler tests, the user's corrected result and weighted
successor lifecycle remain unexecuted; that result is now retracted as a
mistake. This environment had no Cargo/Rust or
retained Oracle harness. No production source-owned attachment was enabled,
no canonical proof-DAG status changed, and no `yulang3` cutover occurred.

**Next single mathematical bottleneck:** an exact observer closed under right
debt, swap/both and correlated recursive copying returning into the same
PUSH-bearing Effect component. The solved source instances and arbitrary
left-word theorem are a real direct advance; they do not certify that every
source reduces to that class. Preserve the existing source filter/orientation,
authority, residual-key, intrusion/freshening/rollback and full hygiene gates.

### Complete mixed cycles and exact raw self-edge factoring (2026-10-10)

The latest user request asks for complete mixed Effect cycle decision and the
correct contextual self-edge omission condition. Starting at actual remote
`f75c8d2f` after `4958aa8d`, this wave closes a concrete part of that request:
**raw identity-self factoring is a finite exact transformation**, including
unbounded recursive PUSH suppliers. Complete authentic mixed decision remains
open. See the [proof/implementation/review record](../notes/progress/2026-10-10-complete-mixed-self-edge-results.md)
for full claims, counterexamples, hashes and publication history.

The [self-normalization theorem](../notes/progress/2026-10-10-contextual-self-edge-normalizer.md)
at `65557b27` removes only whole bare replay(X,I), replay(I,X), mix(X) self
productions and plain reflexive aliases. Each remaining original producer E
at a marked owner yields both E and mix(E). Every finite original derivation
compresses its initial unit chain to zero or one mix; the inverse inserts one
original self step. Exact raw languages and lexical child correlation are
preserved at every original vertex. New producers, quotient-created self
edges and newly merged producers must be handled from the original grammar.
Fresh injective naming commutes; saved original/derived pairs restore the
reference observations. The compiler filter journal is not implemented here.

The [constant-unit theorem](../notes/progress/2026-10-10-contextual-self-edge-erasure.md)
is maximal over all mix-normal inputs: only actual I is a universal unit, in
either orientation. Raw inputs admit no universal constant unit. Also finite
boolean active-presence continuations separate all distinct raw triples, so
permanent support-only identification cannot preserve arbitrary future mixed
observations. Exact state-dependent self redundancy is transfer-closure of
the dropped least solution; it is not presented as a general inclusion test.

The [finite mixed congruence](../notes/progress/2026-10-10-complete-mixed-effect-obstruction.md)
at `98d21e1b` solves arbitrary recursive mixed/copy grammars whose constant
left displacement and fixed-prefix displacement are nonpositive. This is a
mathematical class, not a source restriction. With d=p-n>=0 and derived active
bound N, retain (min(d,K),n,min(r,K)) for K>N. The operations form an exact
finite congruence, giving at most |V|(K+1)^2(N+1) tuple insertions. Each
finite future observer derives its own sufficient K from its fixed PUSH mass,
hole multiplicity, node count and queried debt thresholds. Exact original
syntax remains available for later observers; no POP count is permanently
capped. The [reference implementation](../tools/research_nonpositive_mixed_observer.py)
is published at `c2674ba5`.

The [unguarded PCP theorem](../notes/progress/2026-10-10-complete-mixed-effect-construction.md)
at `9610f0c3` proves undecidability of existential empty directed support for
the broader two-ID grammar with repeated shared recursive child selections.
The [source-rule audit](../notes/progress/2026-10-10-mixed-independent-grammar-bridge.md)
at `de5c400d` shows why that theorem does not establish Yulang impossibility:
ordinary bound replay selects independent lower/upper records, and an actual
joint-support consumer is not derived. Atomic both cannot be replaced by two
independent suppliers, and unfinished cancellation cannot be exported to a
later swap; exact small counterexamples are provided for both shortcuts.

All scoped independent reviews have no blocking/major finding. The two minor
corrections concern Oracle POP/PUSH arithmetic wording and the normalizer
validator's complexity; neither changes code or the exact-language/observer claims.
The self reference passed 4,534 assertions and 99 exact finite fixtures;
the finite observer passed 72 assertions and 495 literal evaluations, with
263 further independent code checks. These are bounded executable evidence,
not general proofs or compiler regressions. No production constructor/filter
consumer, source expected type, Rust transition, canonical proof-DAG CLOSED
status or `yulang3` cutover was changed. The previously claimed callback result
was retracted by the user as a mistake; its intended replacement remains
unspecified. Actual source-owned attachment/fresh-use/rollback tests remain
unrun.

**Next single mathematical bottleneck:** exact required observation of a
positive-displacement mixed recursive component with independent binary replay
and atomic both, preserving maximal cancellation at every raw interface before
later swap. A finite compositional construction or a genuine reduction for
precisely that interface is still missing. Parameterized residual gamma owners
and the complete source constructor/consumer bridge remain subsequent work;
none is assumed away to certify the new results.

### Whole-local primitive annotations (2026-10-10)

The live candidate path now accepts whole-local `Int`/`Unit` annotations,
checks the whole synthesized initializer, and installs a distinct positive
annotation root at the child level. One-shot initializer effects and pure
lookups remain intact. The shared local installer now journals slot
publication so failed route transactions restore newly installed schemes while
preserving prior ones. Focused HIR, solver, rollback/retry and solver package
checks passed; see the [implementation record](../notes/progress/2026-10-10-whole-local-primitive-annotations.md).
The accepted rollback repair and its resource accounting passed independent
delta review. Other local annotation forms, complete Call, effect hygiene,
public/default inference and F5 cutover remain open. At this local-annotation
checkpoint the residual-owner question was pending; its later approved answer
selects constructor lineage in the
[authoritative selection](../design/2026-10-10-contextual-residual-lineage-selection.md).
The separate contextual lifecycle/admission obligations still gate formal-row
work.

### Whole-local ground Function annotations (2026-10-10)

The candidate path now also admits pure whole-local Function trees over
`Int`/`Unit` leaves. It uses the paired annotation constructor for whole-value
checking and positive-root exposure, while preserving one-shot initializer
effects and pure lookups. Nested effect rows (including explicit empty rows),
variables, and unfinished formal forms remain unsupported. The updated 15-test
source target and all-target/all-feature solver check pass; independent semantic
review found no issue. See the [implementation record](../notes/progress/2026-10-10-whole-local-ground-functions.md).
The default/public entrypoint still selects F5, so this does not complete the
required production migration.

### Whole-local named annotations (2026-10-10)

The candidate now admits named value variables in whole-local annotations,
shares their scope with annotations on that binding's formals, isolates equal
names across distinct local identities, and freshens function schemes at each
use. It still rejects effect rows (including `[]`) and unfinished formal
annotations. Initializer evaluation remains one-shot and local lookups pure.
Focused tests pass; the independent compiler review's minor effect-evidence
finding was closed with a focused graph assertion. See the
[implementation record](../notes/progress/2026-10-10-whole-local-named-annotations.md).

This is a bounded local-annotation slice only. The `run_io` example, concrete
effect-row transport/hygiene, complete Call, public/default inference,
soundness/principality and F5 cutover remain open. The contextual residual-owner
identity has since been selected; its exact lifecycle and admission obligations
remain open for dependent formal-row work.

### Whole-local covariant effect annotation gate (2026-10-10)

At this checkpoint, the explicit refusals for local effect rows were temporary
limits of the private candidate route, not language-level rejections. The
authoritative annotation policy permits concrete effects at composed covariant
positions, and the existing paired local constructor carried support,
allowances, symbolic tails and lifecycle state. The bounded slice extended
local admission only to that supported covariant domain, including closed
empty rows; root computation rows and composed negative concrete rows stayed
unavailable at that time. The subsequent root-computation gate below supersedes
that temporary root-row limitation.
Contextual subtraction and explicit concrete formal rows remain blocked on the
pending residual-owner decision. The covariant local admission, support through
fresh use, symbolic-tail flow, independent use freshening, initializer edge,
rollback and solver all-target checks now pass. The pre-write spec audit and
post-write semantic review closed within M2; see the
[implementation record](../notes/progress/2026-10-10-local-covariant-effect-annotations.md).
This gate is not effect-hygiene completion: no concrete subtraction,
source-operation execution, complete Call, public/default cutover, soundness/
principality or F5 replacement is claimed.

### Root computation effect annotations (2026-10-10)

Whole-definition and whole-local annotations now check an explicit root row
against the actual initializer computation effect under the selected covariant
`[E]` allowance policy. Both action owners carry the actual effect endpoint and
use the annotation's shared variable/view maps. The allowance creates no
contribution; evaluation still flows once and local schemes remain value-only.
Closed listed, unlisted and empty rows, boundary provenance, pure computation,
and transaction rollback/retry are covered. A variable-only root row now uses
its shared scoped effect variable directly, retaining dependencies for future
lowers through local capture/extrusion/freshening. A later actual-argument
lower now reaches the nested Function port; concrete-plus-tail rows keep listed
members local. A source test also distinguishes the evaluation effect of a
Function-valued initializer from the returned Function's own effect port.
Focused source and rollback tests pass, and independent reviews found no issue.
See the [implementation record](../notes/progress/2026-10-10-root-computation-effect-annotations.md).

This closes only root covariant row checking and the tested variable-only
future-lower path and the tested Function-valued initializer shape in the
private candidate. Broader rows with both concrete members and symbolic tails,
contravariant subtraction, full hygiene and Call, public/default inference,
soundness/principality and F5 cutover remain open.

### Mixed covariant allowance capture through extrusion (2026-10-10)

The live candidate now preserves incoming bounds for a covariant effect row
combining a concrete allowance and symbolic tail across capture, positive
extrusion, freshening, intrusion bucket splicing, later concrete lowers and
rollback. Listed effects stay local while unmatched effects reach the tail.
Independent semantic and performance delta reviews found no blocking, major or
minor findings. Focused source/kernel tests and the solver all-target/all-
feature check passed. See the [implementation checkpoint](../notes/progress/2026-10-10-mixed-covariant-allowance-capture.md).

The kernel sequence is copy → capture → freshen → lower; the source regression
covers the later actual-argument lower before capture of the resulting
component. These complementary tests do not assert the same operation order.
This closes only the mixed covariant allowance lifecycle gap. The corrected
`run_io` callback result, contravariant subtraction, full effect hygiene, Call,
soundness/principality, public/default migration and F5 replacement remain
open.

### Recursive-definition external instantiation regression (2026-10-10)

The live candidate now has source regressions for a self-recursive definition
used externally at both integer and Function shapes, and a mutual `even`/`odd`
cycle with external uses at those distinct shapes. The self-recursive test
checks that both actual module-reference occurrences retain nonempty
generalized row images and that the two fresh-use images are disjoint under
canonical row identity. The mutual test confirms conflict-free external use
and nonempty generic images, without claiming cross-member fresh-image
disjointness. This is evidence for independent instantiation in the first
fixture and shape acceptance in the second; it does not prove internal SCC
monomorphism, mutual recursion soundness, or public/F5 publication. The focused
tests pass and independent compiler review found no blocking or major finding;
minor naming findings were narrowed and reverified. See the
[regression record](../notes/progress/2026-10-10-recursive-definition-external-instantiation.md).

The approved q1/a1 local-recursion decision now has a narrow authoritative
record in [local self-recursive binding](../design/2026-10-10-local-self-recursive-binding.md).
The single local binding must use one open monomorphic initializer root, then
publish through ordinary sequential visibility; the proposed direct-link seam
passed semantic and conformance review. The parameterized local-function slice
is now implemented in HIR and the private candidate route: recursive
occurrences, including nested-helper references, link to the same open root;
ordinary installation and later capture/freshening remain in place. The
conformance review's same-root test gap was repaired and delta-reviewed. Focused
HIR, solver, rollback, capture, independent-use and module-recursion checks pass;
the `yu-hir`/`yu-solver` all-target/all-feature check passes. See the
[implementation checkpoint](../notes/progress/2026-10-10-local-self-recursive-binding-implementation.md).
This does not change default/public inference or close broader recursion,
soundness or principality. Local mutual groups and polymorphic recursion remain
out of scope. Contextual residual identity is selected, but concrete negative
formal rows remain gated on source admission and full residual lifecycle
obligations. Authentic operation execution/Force, complete Call, effect hygiene,
public/default cutover and F5 replacement remain open.

### Ordinary HIR successor carrier proposal (2026-10-10)

The ordinary route still omits the source carrier required by successor
collection. A read-only HIR authority audit found that directly setting the
existing `local_source` switch would change ordinary header admission,
diagnostics, availability failures, and occurrence ordinals. A reviewed
proposal now specifies a supplementary per-admitted-root carrier formed after
ordinary HIR construction, with source-ordered outcomes and staged provenance
publication. It preserves existing HIR errors/recovery and does not expand
header admission. The spec audit and independent compiler review found no
remaining proposal findings after two minor precision repairs. This is a new
internal architecture decision; the proposal remains non-authoritative pending
user approval. No implementation, tests, or builds ran for this proposal.

Next: obtain the scoped carrier decision, then implement and verify the
behavior-preserving HIR bridge before connecting ordinary collection and the
public successor result. The full ordinary/public/F5 migration, exact callback
effect hygiene, complete Call, soundness and principality remain open.


### Paired formal composed-covariance integration (2026-10-10)

Continued from remote `3b263e110074cb17a04cae0b1eb529d879595e0f`, including
local self-recursion and the corrected historical callback trace. The private
formal constructor now composes variance from a negative formal root through
all four Function ports. Explicit concrete/empty rows at positive positions
use the existing annotation-owned Support/Allowance pair and scoped tail.
For example, `consume:(int -> [io, 'e] ()) -> ()` has a covariant inner row;
its historical Oracle paired PUSH construction is not the selected successor
meaning. Direct `cb:int -> [io] ()` remains contravariant and unavailable.

One source row occurrence yields one view shared by its paired interfaces.
Ordinary reciprocal formal replay gives the view two distinct incoming
Allowance source relations. The new tests preserve both through capture and
two independent fresh uses, and verify publication failure rollback plus retry.
Two source positions remain distinct even with a shared symbolic tail. No
contribution or subtraction authority is inferred from an allowance.

Two independent M2 reviews covered selected source/semantics and lifecycle/
resource ownership. The accepted formal-storage sampling defect was repaired;
source-derived incidence assertions corrected the new test's one-record
assumption without changing production ownership or pre-existing expectations.
Root verification passed 66 distinct focused tests (73 executions with seven
overlaps): formal kernel, effect-owner kernel, six new source cases, existing
formal/effect source regressions and incoming local-recursion regressions.
See the [proof and implementation record](../notes/progress/2026-10-10-selected-formal-contextual-integration.md)
for definitions, proofs, reviewed scope, exact code hashes and test commands.

The inspected nullary source has no Effect-to-Value propagation. Recursive
Value contexts in a constructor-faithful negative extension remain debt-only;
positive Effect recursion still needs phase-aware replay and indexed residual
feedback. The corrected direct negative provider uses an actual named inner
function's io operation. It parses/forms LocalSource; its symbolic control
solves, while the negative fixture still reports Unsupported. Historical
weighted gamma family mismatch is an owner-level falsifier, not an executed
source counterexample or language undecidability result.

The main user task remains incomplete. The single remaining construction seam
is an exact finite representation/consumer for the source-generated mixed
Effect component and its count-indexed residual lineages, retaining both
feedback directions and all current/future lowers. Contextual self checks,
filters, scope, freshening, qualifying parent/copy intrusion and rollback must
be preserved there. No old theorem is promoted to CLOSED; the previously
claimed callback scheme has been retracted by the user as a mistake, and the
intended result remains unspecified. Real run_io behavior, full negative
subtraction/hygiene, principality, complete Call and public/default F5 remain
unverified. This patch adds no certificate/deferral implementation or new
question. The incoming approved private carrier/two-cycle gate is preserved;
it does not establish general negative-formal admission.

Toolchain note: Rust 1.99.0 reports the pre-existing `AtomicU64::fetch_update`
deprecation at `candidate_effect::State::initialize`. The new name would change
older-compiler compatibility, while the workspace has no selected minimum
compiler-version change. This patch retains the existing implementation and
records that exact compatibility blocker; no warning-free build is claimed.


### Local-recursive contextual source/scheduling checkpoint (2026-10-10)

The [reviewed source witness](../notes/progress/2026-10-10-local-recursive-contextual-source-witness.md)
uses local self recursion and an outer unknown sink to force a genuine
level-2 formal Effect row's negative copy at level 1. Its stored lower-copy
link defeats the earlier premise that a weighted upper self could never meet
a Var lower. The exact source and symbolic-formal control parse and form
LocalSource; the control solves with no conflicts and one source call. The
negative source remains Unsupported. These two public inventory probes add
no negative execution or test-suite pass to the existing 66-test checkpoint.

An independent source review and a focused delta review closed the record's
claim boundaries. Primary inspection found the accepted major scheduling
distinction: extrusion's direct bound insertion does not enqueue replay with
pre-existing uppers. No later activation of this initial pair was established
in the exact fixture. Complete reference saturation under the required
weighted constructors yields all PUSH_i^k consumer histories, but the current
worklist is not shown to execute or diverge on them. Distinct histories do not
prove distinct allocated gamma recipes. No complete negative theorem is CLOSED.

The minimum unresolved consumer is the Var-to-Allowance relation carrying that
unbounded PUSH family: retain authentic attachment and constructor-lineage
identity, activate the copied lower, and deliver current/future lowers through
each residual's two feedback directions using an exact finite representation.
The approved private carrier/two-circuit gate remains selected; generic
negative-formal admission, mixed residual completion, exact run_io callback,
full hygiene/principality/Call and public/default F5 remain open. No production
change or additional broad test was made for this record.


### Contextual identity relation foundation (2026-10-10)

The approved contextual attachment gate now has a private identity-context
relation foundation. Typed canonical relations retain occurrence origins,
bound identities, ordered lower/upper replay dependencies, and transport
provenance. Semantic conflict replay uses this relation graph as its single
adjacency authority; transport alone does not make a fresh-use conflict flow
back into a generic template. Extrusion and qualifying intrusion preserve
multiple origins. Route rollback and retained-capacity accounting are covered.

Focused solver tests pass: contextual relation 8, candidate effect 25,
candidate intrusion 5, annotated function formals 10, annotated primitive
formals 21, and Simple-sub local source 7. The exact commands and limits are
recorded in [the progress checkpoint](../notes/progress/2026-10-10-contextual-identity-relation-foundation.md).
Independent compiler and performance delta reviews found no remaining concrete
issue. No timing measurement or speedup claim was made.

This is an incomplete implementation checkpoint. The relation store currently
admits identity contexts only; source-owned attachment operations, filters,
residual recipes, the approved two-cycle acceleration and late-edge
invalidation remain the next implementation gate. Concrete/closed-empty
formal effect rows remain unsupported. Complete Call, full effect hygiene,
soundness, principality, ordinary/default publication and F5 retirement remain
open. The separate ordinary-HIR carrier question has a local q1/a1 answer, but
its approved-answer text differs from the draft by `unstaged and uncommitted`
versus `unstaged/uncommitted`. At the user's explicit request, the questioning
primary committed the question bundle as an archival record, while the receipt
preserves the failed exact-content validation. The answer remains unconsumed,
and the ordinary carrier architecture remains unapproved.

Next: implement contextual attachment/context operations and the two-cycle
certificate lifecycle on this single relation authority, preserving the exact
formal-row refusal and source admission. Keep ordinary carrier approval and
the later default/public cutover as separate gates.

### Exact context-expression DAG foundation (2026-10-10)

The private relation store now interns exact structural operation nodes for
prefix/suffix, Function transforms, ordered replay and filter erasure. Child
sharing/order, opaque weight identity and source-owned `both` certificate
identity survive keying; node creation rolls back and retained capacity is
accounted. The focused 12-test context suite passes, and independent exact
conformance review found no finding. Production relation constructors remain
identity-only, so this foundation does not yet propagate annotations or effects.
See [the progress record](../notes/progress/2026-10-10-exact-context-expression-dag.md).

The annotation-member grouping decision is now integrated: members of one
exact annotation occurrence share an attachment identity while retaining
member ordinals and resolved operands; distinct occurrences and fresh local
instances remain distinct. See the durable §3.1 selection in the
[contextual attachment design](../notes/design/2026-10-10-contextual-attachment-admission-design.md).
The user also asked that the work stay anchored in Simple-sub; this decision
changes only attachment identity grouping.

Next: construct authentic source-owned weight/filter payloads and carry
contextual relation identity through worklist scheduling, bound insertion/replay,
extrusion, capture/freshening and intrusion. The certified-cycle invalidation
and rollback/retry gate remains required before admitting those recursive
contexts. Complete Call, effect hygiene, ordinary/default/public migration,
soundness/principality and F5 retirement remain open.

### Native registered formal root for pending Call construction (2026-10-10)

An independent Call lane added retention of each formal registration's actual
positive native Value root. Initialization checks the registration's parameter
ID against its authentic source recipe position and retains that root once;
borrowed observations validate its kind/polarity and expose it across direct,
wrapped and nested captured uses. Each source Call keeps its own callee, demand
and occurrence. A conflicting Call does not erase the registered input. The
source-input delta review found no conformance finding; the focused source-call
filter passed 3 tests. Exact evidence and limitations are in the
[Call input record](../notes/progress/2026-10-10-call-source-inputs.md).

This is retained construction input only. It supplies no original typing,
formal introduction, checking/seed evidence, complete Gen-Call-0, argument
carrier, receiver dispatch, or complete result/future interface, and it changes
neither Call admission/solving nor `UNRESOLVED`. No measurements or broad tests
ran. Next, continue a bounded Call supplier under the existing original
formation definitions; independently, implement contextual attachment
construction under the newly integrated member-grouping decision. Full effect
hygiene, ordinary/default/public migration, soundness/principality and F5
replacement remain open.

### Contextual closed-Allowance replay checkpoint (2026-10-10)

The candidate worklist now retains exact contextual relation identity. Closed
covariant source Allowance checks execute before endpoint memoization/self
omission and remain registered on the true receiver for later lowers. An
already registered Allowance now links each newly admitted relation to the
existing bound before discharge, so stored conflicts replay at that relation's
source occurrence; rollback/retry is covered. The candidate work-item layout
contract accounts for the new relation handle while preserving the default
layout assertion. The focused 15-test contextual suite and both default and
candidate focused layout tests pass. See the
[checkpoint record](../notes/progress/2026-10-10-contextual-closed-allowance-replay.md).

This is a partial contextual gate only. General operation transport, residual
lineage, two-cycle invalidation, full effect hygiene, complete Call,
public/default inference, soundness/principality and F5 retirement remain open.
Continue through the same Simple-sub relation authority; do not infer any
callback result scheme from the user-retracted example.

### Contextual bound fibers and replay scheduling (2026-10-10)

The private contextual store now retains multiple exact relation fibers per
bound and captures/transports all fibers. Opposite replay keeps ordered lower
and upper parents, schedules the corresponding context relation, and advances
incrementally for ordinary propagation. Scheme restoration deliberately
replays the complete applicable fiber product for each incoming use so errors
retain that use's occurrence and cause. Temporary replay output is charged
through publication and rollback. SCC representative changes migrate
third-owner incoming fibers to canonical keys, and later restoration through a
stale copy canonicalizes both sides before replay.

The initial independent review found an incoming-fiber loss and replay scratch
and duplicate-work issues. One batched repair closed them; a fresh delta exposed
stale-key restoration and per-use diagnostic loss, also repaired. Fresh
compiler-referee, spec-auditor and performance-auditor reviews then passed.
Focused checks passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` (22).
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests --offline --jobs=1 -- --test-threads=1` (27).
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests --offline --jobs=1 -- --test-threads=1` (5).
- `git diff --check` passed.

No benchmark or broad suite ran.

This is a partial gate checkpoint. General operation evaluation, source
operation payloads, operation-payload freshening, certified-cycle invalidation,
arbitrary formal-row admission, complete Call, full effect hygiene,
soundness/principality and production/F5 cutover remain open. The ordinary-HIR
carrier answer bundle remains rejected for exact-content mismatch in its
uncommitted receipt; its implementation remains independently gated.

Next: add source-owned operation payload construction and execute the approved
directed transforms through relations, bounds, extrusion, capture/freshening
and intrusion. Then complete the exact two-cycle certificate invalidation and
rollback/retry gate before admitting those recursive contexts. Keep ordinary
HIR approval and public/default/F5 migration as separate gates.

### Closed annotation filter payload checkpoint (2026-10-10)

The former special `ClosedAllowance` context now uses an immutable, source-owned
zero-word `LocalWeight` payload for closed covariant annotation views. The
payload keeps its allowed members and boundary/owner/position identity, while
the negative-wrapper path still installs or replays the actual allowance
before discharge and memoization. The follow-up source-record slice also
retains metadata for admitted covariant mixed-tail views while keeping them
outside closed-filter execution; operation views receive no source payload.
Copying creates independent local payload identities; payload storage and
member capacity participate in rollback/accounting. No concrete
contravariant row, nonempty operation, recursive context, or source admission
was enabled.

The frozen three-file delta passed independent compiler-referee, spec-auditor,
and performance-auditor review. Focused checks passed:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests --offline --jobs=1 -- --test-threads=1` (23).
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests --offline --jobs=1 -- --test-threads=1` (27).
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests --offline --jobs=1 -- --test-threads=1` (5).
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation --offline --jobs=1 -- --test-threads=1` (17).
- `git diff --check` passed.

No benchmarks or broad suites ran. Static performance review found O(k) extra
member-handle construction/storage per closed view with a constant-factor
increase on copied views; no timing decision depends on this slice. See the
[payload checkpoint](../notes/progress/2026-10-10-closed-annotation-filter-payload.md).

This remains a partial contextual gate. Written closed and admitted covariant
mixed-tail annotations retain source sets; negative written `[]` rows now also
retain inert source bundles while producing their existing leaves and no
executable views. The bundle transport indexes close the initial global-scan
cost finding. See the [source-set checkpoint](../notes/progress/2026-10-10-annotation-source-set-records.md)
and [negative-empty provenance checkpoint](../notes/progress/2026-10-10-negative-empty-attachment-provenance.md).

Next: implement the private finite operation evaluator while keeping nonempty
contexts disconnected from source-derived tasks. Then integrate source
construction, relation-sensitive completion, transport/freshening, and the
approved two-cycle certificate invalidation, withdrawal, rollback, and retry
gate before any recursive nonempty context can be admitted. The separate
ordinary-HIR carrier answer bundle remains rejected for exact-content mismatch
in its uncommitted receipt. Complete Call, full effect hygiene,
soundness/principality and production/default/F5 cutover remain open.

The first evaluator sub-slice now adds a detached iterative structural fold over
the retained context DAG. It preserves exact node/weight/certificate tokens,
replay order and bracketing, evaluates shared children once, and rejects
malformed handles through the existing internal availability result. It has no
source-task, weight-execution, certificate-authorization, relation-admission,
or `candidate_context_execute` call path. The M1 compiler-referee review passed;
three focused fold tests and scoped `git diff --check` passed. The immediately
following detached numeric evaluator now implements exact unbounded natural
counts and the finite resolved atom-set fragment with `All` only in filters.
It covers prefix/suffix, swap, both, filter clearing, ordered replay and
directed mix while preserving construction traces; it does not authorize
certificates, discharge filters, admit relations or connect to source tasks.
The initial compiler-referee review found and the batched repair closed an
unsupported `All` PUSH family; fresh delta review passed. Seven focused detached
tests and scoped `git diff --check` pass. Allocation-failure injection, broad
suites, and non-test builds remain unrun. These two preparatory checkpoints are
recorded in the [structural fold](../notes/progress/2026-10-10-context-structural-fold.md)
and [numeric evaluator](../notes/progress/2026-10-10-context-numeric-evaluator.md)
progress records. Numeric operation payload construction, relation-sensitive
completion, freshening, source integration, and two-cycle invalidation remain
the next gates before recursive nonempty context admission. One following
source-preparation slice now attaches a dormant unit-PUSH marker to admitted
written covariant sets with nonempty concrete members and materializes it only
through the detached evaluator. Existing source identity/freshening is reused;
no live dispatch or zero-word filter behavior changed. M1 compiler-referee
review passed, with 3 source-seed and 8 detached focused tests passing. See the
[source PUSH seed checkpoint](../notes/progress/2026-10-10-context-source-push-seed.md).
Relation-sensitive candidate completion is now keyed by the admitted exact
`RelationId` plus the existing SCC generation, while diagnostic memo ownership
remains on endpoint pairs. Distinct contexts on one pair no longer suppress
each other; raw aliases cannot mark their canonical semantic relation complete
before canonical replay. A focused regression covers a preexisting canonical
memo, actual parent/copy SCC invalidation, raw-alias retry, rollback, and
supported retry. The initial M2 compiler-referee review found the raw-alias
premature-completion defect; its repair passed fresh regression-auditor delta
review. Focused context (45), intrusion (7), and effect (27) tests passed, as
did the owning-package candidate-feature check and scoped diff check. One
production check exposed an unused identity-relation helper after completion
moved to RelationId; it is now test-only, and the repeated package check is
warning-free. No source PUSH execution, changed filter discharge, or formal-row
admission was added. See the [relation-completion checkpoint](../notes/progress/2026-10-10-context-relation-completion.md).

A detached context-DAG renamer now validates every cached suggestion against
the exact postorder-renamed constructor and all reachable explicit weight and
certificate substitutions. Malformed cached children fail through `Err`; the
helper rolls back its context insertions and map additions and releases charged
scratch. The initial compiler-referee review found a cache-bypass defect; the
repair passed fresh compiler-referee delta review. Focused context tests passed
(50), with scoped diff checks. This remains detached preparation with no live
freshening or transport consumer. See the
[context DAG renamer checkpoint](../notes/progress/2026-10-10-context-dag-renamer.md).

The contravariant effect lane now has three reviewed research artifacts: a
conditional derivation for composed Function polarity and exact attached
contribution subtraction; minimized conditional witnesses against support-wide
deletion, variable-as-empty/future-check bypass, and nearest-port polarity; and
a source-to-proof audit mapping retained premises to the still-missing negative
annotation constructor, consumer, and lifecycle correspondence. The
constructive derivation assumes source attachments, typed correspondences,
owner/profile witnesses and a consumer that checks current/future lowers; it
does not prove those inputs are currently source-generated. The falsifiers are
detached algebraic cases, not source counterexamples. The audit confirms the
existing covariant source-set work and RelationId completion while keeping
concrete negative rows rejected. Independent compiler-referee review passed
each artifact. See the [conditional derivation](../notes/progress/2026-10-10-contravariant-effect-conditional-proof.md),
[falsifiers](../notes/progress/2026-10-10-contravariant-effect-falsifiers.md),
and [source bridge audit](../notes/progress/2026-10-10-contravariant-source-bridge-audit.md).
These close no source-hygiene, soundness, principality, or production gate.
They ran no Cargo/Oracle execution or measurements. The bridge producer's
workflow minor is explicitly recorded in its §7: read-only Git queries violated
the packet's no-Git rule and are not counted as compliant verification. The
conditional proof handoff now explicitly retains the negative-row admission
guard and reserves enabling for the approved lifecycle/source bridge gate; its
delta review passed.

Contextual fresh-use capture and transport is now integrated across relation
DAGs and per-use payload/view identities. Context-only views and generic tails
are captured; shared context inputs are renamed once per use; copied attachment
bundles follow the actual renamed child relation. The existing `post_check_context`
discharge rule and equality/zero-use path remain separate. Focused context (53)
and effect (27) tests passed. M2 compiler-referee and regression-auditor review
passed after a resource-ledger repair for simultaneous context-map/traversal
capacity. A 130-node shared-DAG regression covers rollback, retry, peak
accounting, and capacity release. No broad checks, allocator-failure injection,
or measurements ran. Certificate-bearing `BothFromRight` remains unavailable
without an authentic owner, and source operation execution remains disconnected.
See the [context freshening checkpoint](../notes/progress/2026-10-10-context-freshening.md).

The follow-up source audit mapped the remaining approved two-cycle gate to
explicit missing owners: authentic inferred-entry evidence at
`admit_lambda_fact`; exact PUSH and POP/PUSH circuit recognition separate from
parent-copy SCC generation; dependency-indexed withdrawal of memos,
observations, and publication; private deferral that retains an unsupported
late edge; and atomic rollback/retry for the whole certificate dependency
state. Conditional one-memo, one-publication, and stale-edge witnesses show
why each lifecycle part matters; they do not claim current source reachability
or a compiler bug. The frozen Function-port projection falsifier adds a
conditional two-effect-edge witness: Swap and Preserve incidences can project
to the same endpoint adjacency, although the retained raw port records keep
their labels. It rules out the adjacency-only shortcut, not the richer retained
graph or an existing production recognizer. See the
[cycle certificate gap map](../notes/progress/2026-10-10-context-cycle-certificate-gap-map.md)
and the [Function-port projection falsifier](../notes/progress/2026-10-10-entry-circuit-source-falsifier.md).

The first inert-evidence implementation sub-slice now retains borrowed circuit
inputs rooted at RelationIds, validates Support views and exact replay/transport
incidences, and preserves explicit incompleteness where references or lifecycle
authentication are unavailable. Its independent compiler-referee delta review
passed; 71 focused context tests passed. This does not complete Packet 1:
readiness production and complete lifecycle-authenticated inputs remain open.
See [the retained-evidence checkpoint](../notes/progress/2026-10-10-retained-circuit-evidence-boundary.md).

Two additional independent research results are frozen: the [ordered replay
projection model](../notes/progress/2026-10-10-replay-input-projection-model.md)
finds a minimal order-sensitive filter witness in its supplied finite algebra,
and the [conditional Function-port origin derivation](../notes/progress/2026-10-10-function-port-origin-closure-proof.md)
separates Lambda entry/return rows from negative Function ports under explicit
source and transport premises. The first is unreviewed model evidence; the
second passed independent compiler-referee review as a conditional derivation,
with source polarity and transported-flow qualification premises still open.
Neither establishes universal source reachability or a production defect.

Next: close the exact Packet 1 retained-input/readiness obligations, then
recognize the two approved complete components and implement transactional
withdrawal, private deferral, and rollback before connecting operation
execution. Concrete contravariant rows remain rejected until their source
constructor, current/future consumer checks, and lifecycle correspondence are
proved. Complete Call, full effect hygiene, soundness/principality,
ordinary/default/public inference, and F5 retirement remain open.

The private HIR source carrier now retains expression ascriptions with their
exact annotation tail, occurrence, range, and lexical scope. Candidate source
construction evaluates the child first, aliases the ascription's canonical
component mapping to that child, and emits both annotation value directions on
the child's actual Value endpoint plus the annotation computation-effect check
on its actual Effect endpoint. Expression-ascription provenance uses distinct
45/46/47 slots so it can coexist with a binding annotation at the same HIR
occurrence; its empty-source bundle anchor is 46. Local annotation scope and
formal-name Call registration survive the adapter. This is a source-to-solver
construction bridge only: no cycle recognition, lifecycle certification,
recursive nonempty-context admission, complete Call semantics, or ordinary
inference enablement follows. The focused HIR (5) and solver (8) tests passed;
independent semantic and spec delta reviews passed. See the
[expression-ascription source bridge](../notes/progress/2026-10-10-expression-ascription-source-bridge.md).

The next source-owned sub-slice now retains inert inferred-entry origin
evidence exactly where `admit_lambda_fact` creates the fresh entry-to-return
Effect constraint at slot 3. Each record binds the source Lambda occurrence,
fresh entry/return rows, constraint occurrence, and cause; written Function
annotation construction creates no such record. The origin state participates
in capacity accounting and route checkpoint/rollback/retry. M3 semantic and
conformance reviews passed, as did two new origin tests and the existing
first-edge rollback/retry test. The record is not an `EntryCertificateId`,
cannot mint `BothFromRight`, and does not certify a recursive circuit or its
lifecycle.
See the [inferred-entry origin checkpoint](../notes/progress/2026-10-10-inferred-entry-origin.md).

Function decomposition now retains inert, field-specific operation incidence
with the exact parent and admitted child relations: argument Value/Effect record
Swap; result Value/Effect record Preserve. Lambda slot-3 entry provenance is
bound by passing the exact retained origin ID from its source owner, while all
other seeds use the no-handle path. This avoids endpoint reconstruction and
keeps current child-local context execution unchanged. The first M2 review
found a quadratic miss scan for unrelated slot-3 sources; direct ID plumbing
closed it. Focused solver tests passed (3 inferred-entry, 2 Function-port),
and fresh semantic and performance delta reviews passed. No context operation
is executed or authorized by these records. See the
[Function-port incidence checkpoint](../notes/progress/2026-10-10-function-port-incidence.md).

The follow-up source-owned Function-port construction now derives each child
from the exact processing parent’s post-check context: arguments Swap, results
Preserve, and a child-local positive prefix remains outside that transform.
Identity simplification retains provenance; unsupported context execution
remains unavailable. The focused candidate-context suite passed 77/77.
Independent spec review found no conformance finding; compiler-referee review
accepted the conditional proof after a minor locator correction. See the
[Function-port context operations checkpoint](../notes/progress/2026-10-10-function-port-context-operations.md).

Next: implement and verify live nonidentity context consumption through bound
insertion/replay, extrusion, capture/freshening and intrusion, then close the
exact two-cycle certificate invalidation, deferral and rollback gate before
admitting recursive nonempty contexts. Contravariant concrete effect
attachments remain rejected until their source constructor and current/future
consumer checks are implemented and tied to the conditional hygiene proof.
Complete Call, ordinary/default/public inference, soundness/principality and
F5 retirement remain open.

### Zero-word filter consumer and proof bridge (2026-10-10)

The live consumer now validates finite `Identity` / closed zero-word
`PrefixLeft` / ordered `Replay` contexts, registers every distinct boundary on
the same canonical receiver, retains the complete relation derivation, and
discharges only after checks are recorded. It skips ordinary endpoint
propagation only when the exact task upper is one of those authenticated
Allowances; unequal endpoints still follow the normal solver path. Validation
scratch is synchronous, capacity-accounted, and restored on nested Result
failures. Focused candidate-context tests pass 75/75, and a fresh
compiler-referee delta review found no BLOCKING, major, or minor findings.
Expected diagnostics were not changed. Static cost is one DAG traversal plus
boundary registration/authentication, `O(N+E+B)` expected work and `O(N+B)`
temporary storage, excluding ordinary bound checks/replay; no timing
measurements or broad tests ran.

The conditional zero-word discharge derivation has an independent spec-auditor
PASS under its explicit closed-view, same-receiver, retained-check, provenance
and atomic-lifetime hypotheses. A real custom `prover` child also produced a
source-to-consumer bridge characterization: source-authentic composed-negative
concrete formal rows cannot reach this candidate consumer because preflight
and paired/signature construction independently reject them. A negative
`Allowance` endpoint from an admitted composed-positive annotation is a
different case and does not prove local subtraction. Independent review found
no BLOCKING or major theorem finding; its minor handoff wording was repaired.
The prover worker exceeded its no-Git assignment by running read-only Git
queries; this is recorded as workflow nonconformance, not counted as
verification. The reviewed conditional contravariant subtraction theorem and
this bounded unreachability characterization do not enable negative rows or
close source formation, exact attachment, residual, lifecycle, full hygiene,
soundness, principality or production gates. Keep negative-concrete admission
guards in place until the later contextual-admission §§5–6 gate and any
required approval.

### Nested Function effect variance and hygiene bridge (2026-10-10)

A real custom `prover` child derived the finite-path variance rule and exact
Function-port operation order. Counting only Argument Effect edges is
insufficient for nested signatures: Argument Value edges also reverse
annotation variance and introduce Swap. The correct sign count uses all
Argument Value and Argument Effect descents; result ports preserve. The exact
operation word retains each Swap in source order without assuming involution or
moving it across a child prefix. Its contribution-local hygiene conclusion
remains conditional on the existing source-formation, exact-attachment,
transport, receiver and current/future-consumer hypotheses.

The candidate constructor applies Swap to the exact parent's post-check context
before a supported child prefix. Its live consumer still rejects nonidentity
Swap and nested prefixes; PUSH/POP words remain empty, and composed-negative
concrete rows remain preflight-disabled. Identity Swap is retained as field
incidence when its structural node is elided. Thus the inverse-position
derivation is reviewed, while source attachment construction and executable
effect hygiene remain open. A separate bounded falsifier found no violation of
the conditional order theorem and exhibited a one-PUSH witness against the
reverse-order mutation. See the [nested variance proof](../notes/progress/2026-10-10-nested-function-effect-variance-bridge-proof.md),
[source bridge audit](../notes/progress/2026-10-10-argument-effect-source-bridge-audit.md),
and [minimal order witness](../notes/progress/2026-10-10-effect-variance-counterexample-audit.md).

### Current-component certificate lifecycle (2026-10-10)

Architecture review interprets Authoritative §5 as allowing certification of
the complete current generated SCC before all source schedules finish, provided
every later premise-changing event invalidates the generation and withdraws
dependents before reuse. A schedule-completion token is not required by itself
and cannot replace snapshot completeness or mutation coverage. A conditional
prover theorem now states the guarded reuse, invalidation and full rollback
obligations. Independent compiler-referee and spec-auditor reviews passed
after separating the H1–H4 core induction from the H5 route extension. This is
not evidence that the candidate implements those transitions.

Source mapping found relation/dependency insertion alone cannot own the
generation: a repeated seed appends a new exact Origin to an existing relation
without a new relation or dependency ID. Other mutation sites include bundle
incidence, bound fibers, view/attachment data, discharge, replay cursors,
representative forests, memos, diagnostics and graph publication. Existing
intrusion generation tracks equality merges; there is no circuit-certificate
generation, complete dependent-observation index or dirty-before-reuse path.
The earlier Packet 1 control-flow result remains valid: first capture may
occur inside `Action::Local` before its root schedule finishes; member-staging
capture follows all member schedules, but establishes neither full readiness
nor complete query/observation coverage. `retained_input` still has no
production caller. Member graph publication and active-frontier changes also
lack located route-journal undo. See the [Packet 1 readiness proof](../notes/progress/2026-10-10-packet1-source-readiness-proof.md),
[conditional lifecycle proof](../notes/progress/2026-10-10-certificate-generation-conditional-proof.md)
and [origin mutation falsifier](../notes/progress/2026-10-10-certificate-generation-falsifier.md).

The independently reviewed [bound-fiber audit](../notes/progress/2026-10-10-canonical-bound-fiber-prover-audit.md)
derives conditional storage coverage: successful bound insertion attaches its
context fiber before publishing the physical bound, and SCC canonicalization
transports retained fibers. Its proposed missing-fiber trace was rejected: the
first nested comparison itself inserts the allegedly absent mixed key. The
remaining question is whether a restore-loop iteration can omit any incoming-
use obligation after a nested SCC drain changes the opposite-bound vector. A
complementary static [reachability audit](../notes/progress/2026-10-10-canonical-bound-fiber-reachability-audit.md)
finds that the exact two-parent Value setup is API-injected rather than
reconstructed by the normal Value capture path; it leaves Effect and alternate
source constructions open. Neither note establishes a compiler defect or
source counterexample. No code/test/build result follows from these static
characterizations.

The new [restoration snapshot proof](../notes/progress/2026-10-10-canonical-bound-fiber-restoration-proof.md)
proves the literal incoming-use Cartesian snapshot and its fixed-frontier
corollary under explicit stability hypotheses. Independent compiler review
found no mismatch in those bounded claims. Its source/operational coverage R
remains open: nested canonicalization may grow a third-owner fiber that the
outer loop still addresses by a historical key, while ordinary merge replay
and Value/Effect diagnostic reachability provide possible rescue paths whose
universal coverage is unproved. The complementary [Effect incidence audit](../notes/progress/2026-10-10-canonical-bound-fiber-source-witness.md)
identifies a source producer route to a shared owner and excludes pre-use
frontiers as its direct explanation, but finds no authentic within-use
counterexample; independent review accepted these bounded claims. Neither
artifact establishes an implementation defect or closes R. No tests/builds ran.

The reviewed [mixed-annotation use trace](../notes/progress/2026-10-10-canonical-bound-fiber-within-use-trace.md)
follows the authored `left` fixture through HIR actions, levels, capture,
freshening, and restoration. All six captured rows remain level 1 and freshen
per use; the only restore callback is `BottomEffect <: Allowance(v_use)`, which
adds no bound. Equal-level extrusion produces no copies or parent records, so
this fixture cannot realize the shared-owner/nested-merge condition. The
compiler-referee delta review found no mismatch in this bounded derivation.
Parser/HIR success and runtime behavior remain unverified; R remains open.
The note is checkpointed as `dfeb75cca`.

The reviewed [negative-row preflight proof](../notes/progress/2026-10-10-negative-effect-preflight-invariant-proof.md)
establishes the current successor entrypoint's rejection-safety invariant: the
recursive whole/formal preflights reject explicit concrete rows at every
composed-negative annotation occurrence, and the row constructor repeats that
guard before allocation, view lookup, bound insertion, or live-term return.
The independent compiler-referee review found no finding; the primary also
matched every listed dependency hash to baseline `26b89d7b4`. This was a
prover-equivalent generic fallback because the current collaboration schema
does not expose `prover`; requested Sol/high, observed runtime settings unknown.
It does not prove effect hygiene/subtraction, nor authorize retaining the
rejection after the enabling gate. No tests/builds ran. Checkpoint: `f92b5119e`.

The reviewed [shared-Allowance restoration trace](../notes/progress/2026-10-10-shared-allowance-restoration-trace.md)
confirms that the existing mixed-root fixture realizes a shared incoming
Allowance owner `C1` with real parent provenance at its local boundary. Its
three incidence keys restore before positive template bounds, but `C1` has no
positive lower then, so its restore has zero opposite count and cannot cause
the required within-loop drain. Later callbacks may drain the solver but add
neither a positive `C1` lower nor a qualifying `C1/I3` SCC. The independent
compiler-referee review found no mismatch; the primary matched all eleven
dependencies against baseline `26b89d7b4`. This is a bounded exclusion for that
lookup, not a source counterexample or closure of R. The producer's one
read-only `git rev-parse HEAD` violated its no-Git packet; it is explicitly
recorded, and the producer reported no Git mutations. No tests/builds ran.
Checkpoint: `87ad21a03`.

### Positive-lower restoration source bridge (2026-10-10)

The bounded [fixture search](../notes/progress/2026-10-10-positive-lower-incidence-fixture-search.md)
covered 20 solver test files and found no qualifying authored fixture. An
independent regression-auditor review reproduced its inventory and found no
blocking or major issue. Its dependency hashes were checked against baseline
`ddbb588d2`; the artifact is checkpointed at `155780d75`.

The actual direct-operation fixture at
`candidate_effect_annotation.rs:345` does create real positive bounds, including
on its original negative root Allowance port. That port, Function ports, and
symbolic tail are level 1 and generic at the top-level boundary 0, so capture
freshens them before restoring the incidence Allowance; the original lower is
not present on the fresh owner's pre-restore snapshot. This is a bounded
exclusion for that fixture, not a universal reachability claim. Its source
tracer issued two read-only Git commands despite a no-Git packet; no mutation
occurred, and the violation was returned explicitly.

An independent [positive-lower insertion derivation](../notes/progress/2026-10-10-positive-lower-bound-insertion-proof.md)
now characterizes when `candidate_apply_effect` physically pushes a positive
lower onto its canonical upper row: after canonicalization, the upper is a row
and the lower is either non-row or an older row. It distinguishes direct bound
vectors from contextual-fiber deduplication and worklist memo suppression.
The actual `prover` role ran through `tools/codex-prover.sh` as
`/root/proof_bridge`; requested Sol/high, observed model/effort unknown. An
independent compiler-referee review found no major issue and one minor level
wording defect, fixed to name canonical rows. Exact source provenance, timely
admission and survival on the same owner remain an unproved premise. The note
is checkpointed at `8eaceb287`; no tests/builds/probes ran.

The alternate positive-tail-extrusion seam can copy a positive lower to an
incoming owner before inserting its remapped negative Allowance. The bounded
fixture audit found only separate ingredients: a mixed covariant formal row
whose owner remains level 2 and freshens at bridge uses; a local symbolic
annotation whose checking owner is freshened before incidence restoration; and
the maker fixture whose shared-owner provider arrives too late. No inspected
authored schedule composes positive input bounds, positive extrusion to a lower
annotated boundary, and later nongeneric capture/use on the same canonical
owner. This is an exclusion over the inspected paths, not proof of impossibility.

### Successor source and lifecycle bridges (2026-10-10)

The frozen [ordinary-HIR composition search](../notes/progress/2026-10-10-ordinary-hir-successor-composition-search.md)
derives a level obstruction for a fresh incoming owner and its scoped tail
copied together by positive extrusion. It does not establish a source witness
or universal exclusion. The [prover-equivalent conditional bridge](../notes/progress/2026-10-10-positive-tail-source-composition-proof.md)
shows that a qualifying owner-only parent/copy merge can leave the tail generic
and restore an Allowance on the unchanged owner. The missing source premise is
an actual HIR path `C -> ... -> S` that closes the owner pair without closing
the tail pair. A later witness must also show a mutation inside the saved
restore loop that omits a required fiber pair and survives ordinary replay and
Value/Effect diagnostic rescue. The Allowance view ID remains stable through
row canonicalization, so this seam does not establish the historical-key
failure route. An independent compiler-referee review found no blocking or
major issue and one minor imprecision: ordinary admission via
`candidate_apply_effect` replays opposites, while direct physical insertion
does not; both notes now state this distinction. No tests, builds or probes
ran. The custom `prover` spawn was unavailable in this
session; a generic prover-equivalent Sol/high-requested leaf ran with observed
runtime settings unknown. The earlier actual prover run recorded above remains
separate evidence.

The frozen [finite-operation source bridge](../notes/progress/2026-10-10-finite-context-operation-source-bridge.md)
traces the supported closed-filter path and the missing source-to-live
operation owners. `SourceUnitPush` currently prepares only detached algebra;
nonidentity Swap/nested-prefix/Both/Suffix contexts fail live validation;
inferred-entry incidence has no authorization consumer; residual construction
does not yet retain lineage and both feedback directions. Existing composed-
negative concrete admission remains guarded at preflight and construction.
This artifact is bounded source characterization, not proof of complete
hygiene or authority to widen inputs.

The first finite live-operation slice is now present in
`candidate_context.rs`: payload-free Swap, WithoutLeftFilter and ordered Replay
contexts execute for Value and Effect tasks while preserving the exact retained
context. Authenticated zero-word Effect filters can discharge before a
payload-free operation residual, while replay-only filter fragments retain
their existing receiver checks. Filters buried under Swap/WithoutLeftFilter,
nested prefixes under Replay, and Value-filter execution remain unavailable.
The stale Function result-port expectation was updated only for the
authenticated Result/ResultEffect case under design §4. Spec review passed and
the focused `function_port_context_uses_exact_post_check_parent_and_child_local_order`
test passed (1/1). Weighted operation consumption, exact weighted post-check
context, source reachability and full hygiene remain open.

The registered `prover` role ran through `tools/codex-prover.sh` as
`/root/function_port_path_proof` (requested Sol/high; effective settings
unknown). Its [finite Function-port path derivation](../notes/progress/2026-10-10-function-port-context-composition-proof.md)
extends the one-edge algebra by induction while keeping the exact nested
operation order, shared input and attachment identities. A fresh
compiler-referee review found no findings. This remains a conditional algebraic
claim: child-wrapper scheduling, discharge/reset absence, source reachability,
and complete execution are not established.

The [ordinary HIR owner-return search](../notes/progress/2026-10-10-hir-owner-scc-return-path.md)
found no selective source path from copied owner C back to S while keeping the
tail pair outside the SCC. Its conditional graph derivation shows that a
tail-based return can close both recorded pairs. The nested Function audit
adds a polarity-specific obstruction: direct structural exposure of a fresh
negative checking port uses a different polarity map from its positive
incoming-incidence copy. It leaves open a positive exposed port that later
receives an Allowance through admitted replay; no source schedule was proved.
The [custom prover's inherited-lower derivation](../notes/progress/2026-10-10-source-hir-selective-scc-proof.md)
also gives a conditional return through an older positive lower and its live
Allowance bounds, so positive exposure of C is not universally necessary.
Neither route has an authentic source witness. Both remain open before the
selective SCC tests, and an SCC witness would still need a named missed fiber
and failure of every replay/diagnostic rescue. No global impossibility was
proved.

The authentic [source/HIR selective-SCC search](../notes/progress/2026-10-10-source-hir-selective-scc-witness.md)
now executes three valid focused parsed/lowered programs through their normal
root schedules. It realizes the first three inherited-lower keys and `C + R`,
but none produces the required `X -> S` return: the owner pair does not qualify
and the tail pair remains outside at the same snapshot. The final repeated-call
variant adds real continuation edges without changing that result. The note
also inventories 38 actual restore calls / 19 literal Cartesian products and
does not identify a lost obligation or rescue failure. This is a strong
near-witness, not a counterexample or impossibility result. The independently
reviewed [nested Function polarity search](../notes/progress/2026-10-10-function-port-source-return-search.md)
narrows direct structural exposure of a fresh negative checking port to
different positive/negative copy keys; later Allowance registration on an
already-positive exposed port remains open. Checkpoint commits are
`09ea300c3` and `3bda4d9d8`.

The separate [positive Function-port source search](../notes/progress/2026-10-10-positive-port-source-route-search.md)
ran eight more valid source roots against the same frozen binary/source set.
It found two concrete route failures: a symbolic positive port can receive its
own-tail Allowance, but its owner and tail parent pairs are identical; a
deeper distinct-tail checking port is negatively extruded to a copy before
replay, leaving the original positive callback result bare. No final snapshot
contains a returning positive Effect parent/copy pair. These eleven source
roots and the constructor-level polarity/level facts do not quantify over all
ordinary source schedules or intermediate snapshots, so source impossibility
and R remain open. Checkpoint `8697c8dfa`.

The [constructor audit](../notes/progress/2026-10-10-source-selective-scc-impossibility-audit.md)
enumerates the current source owners and finds no permanent polarity barrier:
replayed Support and Allowance can retain younger tails on reused older
computation rows via ordinary Group/Install Effect links. Its proposed delayed
Lambda/two-tail route remains unexecuted because its root effect ascription is
rejected by the parser at byte 176; three bounded GDB observations of that one
input show no lowering or actions. This is a localized residual, not an
impossibility proof. A single follow-up replaces that spelling with an
ordinary local computation annotation and preserves the intended schedule.
The separate [restoration-product derivation](../notes/progress/2026-10-10-restore-product-rescue-proof.md)
proves literal-head snapshot enumeration, fixed-frontier coverage, and
ordinary/merged-owner replay coverage. Its Function mutation sketch is not an
admitted capture state. Universal rescue remains open at displaced old exact
entries, third-owner/key/fiber transport without owner replay, and diagnostic
accessibility for suppressed dependencies. Neither note closes R. Checkpoints
are `7984bd084` and `bed730d1b`.

The valid [local-annotation source probe](../notes/progress/2026-10-10-local-annotation-selective-route-probe.md)
now executes the delayed-Lambda route normally. It realizes original
`X28 -> S26` through callback checking and the positive owner/tail parents
`(C73,S26)` and `(T'72,T24)`, but both positive pairs remain outside an SCC;
the exact distinct-tail `R31 - Allowance(X28)` key is absent. Negative
extrusion creates `X61` with `X61 -> S26` absent, so the original X return
cannot be substituted for the copied X return. The annotation's same-spelled
`'x` is independently scoped row54. This is the closest authentic source
state so far, not R. Checkpoint `56a7e48dd`.

The [whole Function result-row probe](../notes/progress/2026-10-10-bridge-result-type-route.md)
uses an explicit Lambda Function annotation and verifies actual sharing of
bridge tail X27. At the same first physical snapshot, owner pair `(C62,S25)` is
outside one SCC while tail pair `(T'61,T23)` is inside; `R30-Allowance(X27)` is
still absent. The source schedule then reaches a debug assertion at
`candidate_context.rs:1846`. The follow-up [endpoint assertion audit](../notes/progress/2026-10-10-endpoint-assertion-route-audit.md)
observes RelationId270 and its raw task both retain `(27,58)` after the actual
negative parent/copy merge `58 -> 44`; current representatives canonicalize
both to `(27,44)`. Thus the task/relation association agrees, but the queued
relation key is stale across the merge and aborts ordinary LocalAnnotation.
The exact relation producer/enqueue chronology is still inaccessible. Normal
root completion, full AST inventory and restoration/rescue were not observed.
This exposes a source-reachable endpoint-lifecycle failure, not an R witness,
global impossibility proof or completed root-cause repair. Checkpoints are
`88eee6ef4` and `c2f7851d8`.

After the queued-relation transport repair, the [symbolic whole-argument
source attempt](../notes/progress/2026-10-10-source-owner-construction-search.md)
ran one fresh parsed/lowered root to completion with zero solver errors. It
reused formal result X, omitted the repeated `[E,'t]` argument tail and retained
actual positive pairs `(C62,S25)` and `(T'61,T23)`. Both pairs stayed outside
same-SCC qualification at the same physical snapshot; C62 reaches T'61 but not
S25. This is a bounded failed source construction. The separate constructor
review finds no current history-preserved invariant that proves the owner-only
state impossible, so that universal source question remains open, as do
unchanged-owner restoration, the omitted fiber, and full replay/diagnostic
rescue.

The [identity-context transport derivation](../notes/progress/2026-10-10-identity-context-stale-relation-lemma.md)
shows that identity means no local filter work, but is not by itself proof that
the stale relation's origins/replay/diagnostic ancestry reaches the canonical
relation. Changed attached bounds already add that bridge during bound
canonicalization; arbitrary queued relations lack an established equivalent.
The conditional gap is `r=(P,I)`, `P != Q=rep(P)`, with no changed-bound
incidence/path: admission may intern/select `c=(Q,I)` without adding `r -> c`.
This is not yet shown to be RelationId270's actual parent history. The note is
unreviewed and does not close the R obligation. Checkpoint `63ac38a7a`.

The [current-component lifecycle inventory](../notes/progress/2026-10-10-current-component-generation-bridge.md)
has an independent spec-auditor review with no conformance findings. Every
successful current `retained_input` is marked Incomplete and has no production
caller. SCC equality generation is not a certificate mutation generation;
dependent withdrawal, private deferral and publication rollback have no
current owner. This is a reviewed source inventory only, not a certificate
proof or implementation closure. Its checkpoint is `ad1d048e5`.

The queued-relation ancestry bridge is implemented: task transport retains the
exact post-check context on canonical `c` and records `Derived(r,c)` before
execution. Its focused retry test passed 1/1; the recorded direct source root
also completes after the repair. Do not repeat this code change. The separate
Value diagnostic-parent issue remains conditional: `pair_is_current` can skip
the raw alias diagnostic edge when its canonical processing relation is
already current, but eleven bounded ordinary roots, including the known R
witness, produced no Value merge or retained-child replay. No source witness or
source impossibility proof exists for that diagnostic history.

The distinct-tail Allowance route is now constructively reachable from ordinary
parsed source: one pre-merge snapshot has a positive owner/copy SCC and an
unclosed copied-tail/original-tail pair. Independent compiler-referee review
conditionally passed its graph interpretation. The later same-source bridge
use was traced through 52 restores and the tail merge, but its captured graph
contains neither R43 nor the target S49/R43 bound; all observed relation
contexts are identity. This does not identify a missing ordered restore fiber
or prove all rescue paths. See the [constructive source witness](../notes/progress/2026-10-11-distinct-tail-source-constructor-search.md#ordinary-source-constructive-witness-primary-diagnostic-2026-10-11)
and [later restore trace](../notes/progress/2026-10-11-distinct-tail-restore-source-trace.md).

Immediate implementation gate: assign explicit mutation-generation,
dependent-observation withdrawal, private deferral, member-publication and
rollback ownership under contextual-admission §§4–6. The current-component
inventory shows no production certificate caller and no undo owner for these
dependent/publication states. Keep nonempty recursive-context admission and
concrete negative formal rows disabled until that lifecycle and exact recognizer
gate is implemented. The separate restored-fiber proof and Call/Catch/public
scheme source audits can continue against the frozen baseline. Full Oracle
hygiene transfer, ordinary Simple-sub inference, general residuals, complete
Call/Catch, soundness/principality and F5 cutover remain open.

The nested synchronous caller gap now has an approved private continuation-stack
contract at [private candidate suspension](../notes/design/2026-10-11-private-candidate-suspension-contract.md).
It preserves freshening, bound/replay cursors, typed child drains, source/SCC
progress, invalidation recomputation, rollback and group publication without a
public pending API or semantic change. The user approved the reviewed contract
on 2026-10-11; lifecycle code remains unimplemented and is the immediate
implementation gate.

The [FunctionPort lifecycle mutation bridge](../notes/progress/2026-10-11-functionport-lifecycle-mutation.md)
identifies a mutation class that an allocation/equality-generation hook alone
misses: a new FunctionPort dependency can change retained recognizer evidence
while reusing existing identity relations and leaving intrusion generation
unchanged. Relation-mask growth has an extra premise and is not established on
an ordinary source route; actual Function dispatch may already retain a
connecting Derived edge. Existing route rollback does undo the dependency
append, but future certificate-dependent observations and publication still
lack owners. The `current-component-generation-bridge` note's earlier claim
that all nonidentity Swap contexts are unexecutable is stale: payload-free
Swap/WithoutLeftFilter fragments are now accepted by the zero-word executor.
The [inert bound-evidence retention slice](../notes/progress/2026-10-11-bound-evidence-retention-slice.md)
now records admissions, emissions, replay recipes, snapshots, reverse
construction links, and fiber transforms with rollback/accounting. Its focused
regressions cover the actual reservation-error branch, mid-import failure,
two-fiber ambiguous-origin transport, and named Function-port polarity; 7
focused tests passed. The conformance delta review passed. This supplies
producer evidence only: it has no circuit-authorization consumer, and the
reviewed invalidation/private-deferral/publication lifecycle remains
unimplemented.

That exact pre-existing-relation case now has a focused regression covering
dependency-only evidence mutation, unchanged relation/context counts and
intrusion generation, rollback, retry and duplicate admission. It passed 1/1;
a fresh compiler-referee review found no findings. The no-witness transport
wrapper is now test-only. Three remaining unused evidence groups
(`RetainedInput` fields, `CircuitEvidence.parents`, and `owned_bytes`) are
required by the future certificate consumer and remain assigned to the
lifecycle implementation gate; they were not removed or blanket-suppressed.

The [boundary-zero source restoration probe](../notes/progress/2026-10-11-boundary-zero-source-restoration.md)
remains a reviewed capture/fresh-use control. A later
[Function-ascription source route](../notes/progress/2026-10-11-selected-owner-restore-callback-coverage.md)
now constructs the selected unchanged owner S53 with distinct old positive
lower R47, captures its incoming Allowance bound at boundary1, and restores it
without freshening S53. The exact saved opposite vector has six slots and three
unique ordered pairs; all six children emit and dequeue. A callback appends a
duplicate Allowance upper but leaves the old opposite vector and fibers stable,
so this source does not omit a required pair. Independent compiler-referee
review passed the source bridge and callback-local enumeration. A separate
[successful-drain closure proof](../notes/progress/2026-10-11-q113-successful-drain-closure-proof.md)
uses append-only bound writers, immutable view tails, propagated merge errors,
checked intrusion generation and the six successful `Ok(0)` drains to extend
the q113 outgoing-closure result to every intermediate state within those six
callbacks. A fresh compiler-referee review passed that argument. This excludes
an intra-drain q113-to-R45/R47 physical path in this exact interval, but it
still constructs no missing ordered fiber and says nothing about later
restores or diagnostics.

This closes the missing source-construction premise for an unchanged-owner
Allowance restore with an old distinct lower. It does not construct an absent
child or prove universal rescue/impossibility. Alternative A and Alternative B
remain open. The next decisive evidence is a source-owned callback mutation
that displaces a required old ordered pair from the saved-index loop without
another actual replay covering it; otherwise an all-source constructor proof
must rule that event out. Complete diagnostic discharge and rollback/retry
remain unproved.

The follow-up [source displacement search](../notes/progress/2026-10-11-source-displacement-search.md)
did not find such an execution. It narrows the direct-append route: ordinary
Effect callbacks on the reviewed level-1 S53 cannot append a row lower by
level orientation, and lifting S to level2 still does not construct the needed
row-to-row callback task absent SCC reconstruction. A concrete transport route
remains conditional: R47 is a negative copy of R45, so merging them could
transport S53's fiber without replay; the exact missing source edge is
`q113 ->* R45`. This static route analysis ran no source execution and proves
neither its reachability nor global impossibility. Alternative A and B remain
open. A configured prover child was launched through `tools/codex-prover.sh`
as `/root/source_transport_proof`; its session JSONL authenticates
`agent_role=prover`, `model=gpt-6.1-sol`, and `effort=high`. Its conditional
direct-edge level lemma passed independent compiler-referee review. See [the
prover callback-return result](../notes/progress/2026-10-11-prover-callback-return-obstruction.md).
The lemma excludes only direct ordinary row-comparison edges from supplying
an upward `q113 -> R45` path while levels and representatives stay fixed. The
independently reviewed [q113 observer](../notes/progress/2026-10-11-q113-outgoing-closure-observation.md)
found the closed two-node outgoing graph `E113 -> Allowance9 -> E113` at all
26 sampled restore boundaries, with no path to R45 or R47 and no
representative changes. Callback0 adds only the incoming `R47 -> Allowance9 ->
q113` path. This is evidence for this one source interval; transient states
inside drains, later replay/diagnostics, alternate schedules, and full
provenance remain unobserved. Alternative A/B and diagnostic rescue remain
open.

The same-scope source variation subsequently constructed and captured a real
`q95 -> X33` return, but restored it only after the selected S53 product. Its
independently reviewed suffix audit found a later E112-owned re-emission of
S53/Allowance9, no S53-owned product revisit or R47/R45 merge, and a final
uninstantiated boundary0 recipe containing the relevant fibers. This still
does not establish semantic discharge or a failing source state; diagnostic
consumer evidence and future-use replay remain absent. See the [later
schedule audit](../notes/progress/2026-10-11-q113-later-schedule-audit.md)
and its frozen [trace artifact](/tmp/yulang-source-q113-later-schedule-20261011.md).

An authenticated `prover` child then applied the reviewed successful-drain
lemma to the original q113 run. Independent compiler-referee review passed:
through every state in the six successful callbacks, the proposed
q113→R45 return is absent, so the specific R47/R45 equality-transport route
cannot displace the S53/R47 fiber in this interval. This is a fixed-source
route exclusion, not global Alternative B; other source constructors,
diagnostic discharge, and the source-level A/B decision remain open. See the
[third-owner route proof record](../notes/progress/2026-10-11-q113-third-owner-route-exclusion.md).

A separate view/tail construction attempt also produced no qualified source
candidate. Independent compiler-referee review confirmed that descriptor
remapping only copies the supplied tail; captured physical bounds restore
separately, and annotation tails come from scoped names rather than inferred
expression endpoints. This blocks that specific proposed supplier, not all
source constructors. See the [view-constructor obstruction](../notes/progress/2026-10-11-q113-view-constructor-obstruction.md).

The distinct earlier third-owner `X/+q` route now has a reviewed capture-
identity obstruction. Capture emits q's incidence before q's direct upper
bounds, so finding q earlier does not move its own return ahead of the selected
Allowance restore. An earlier X restore would replay `q_U <: Y_U`; capture
freshens generic Y with q and X, so it does not reach original R45 without an
independently sourced sharing or transport edge. The authentic historical
capture has boundary1, local q95 at level2, shared S53/R47 at level1, use level1,
and no R45 in the captured row map; R45 is level3. The level-only sharing
condition `3 <= boundary < 2` is unsatisfiable for that fixed capture. This
rejects that candidate mapping, not all source constructions. No compile or
source execution was warranted because no grammar-valid candidate preserved
the old R45 identity and a source/use-rooted omega. See the [old-parent capture
obstruction](../notes/progress/2026-10-11-q113-old-parent-capture-obstruction.md).
Alternative A/B, required-omega absence, and diagnostic rescue remain open.

The [bounded source-state decision](../notes/progress/2026-10-11-q113-source-state-decision.md)
adds a reviewed all-false `non_generic` production invariant and a reviewed
prover derivation: a native Lambda's body capture precedes that Lambda's own
native Effect ports, while local helper capture is live at later Name use.
Neither result constructs the exact old-parent Function field and both
`q <: X` / `X <: Y` tasks in the necessary order, nor excludes every other
source constructor. The historical q113 execution emits all six selected
products and is not a failing-state witness. No changed source was compiled
or run. The source-level A/B decision remains OPEN; the next evidence must
construct the original-Y Function field and unrescued omega, or prove an
exhaustive owner invariant ruling that route out.

The [high-root route adjudication](../notes/progress/2026-10-11-q113-high-root-route-adjudication.md)
adds independent reviewed obstructions for the paired-formal route, helper
W/V ancestry merge, and selected Allowance-tail supplier. A completed-Lambda
escape construction also fails to supply the original-Y lineage before the
later published fresh use. The [ordered omega consumer map](/tmp/yulang-q113-omega-consumer-map-20261011.md)
maps downstream consumers but does not prove universal discharge or
non-discharge. These are route-local results: no authentic source reaches the
full target and no all-source Alternative B theorem exists. A/B remains OPEN.
The exact remaining join is a source prefix with original-Y/old-lower
identities, qualifying restored-fiber mutation and omega, followed by either
an uncovered mutation or a universal coverage proof and terminal consumer
closure. No candidate met source prerequisites for parsing or execution.
