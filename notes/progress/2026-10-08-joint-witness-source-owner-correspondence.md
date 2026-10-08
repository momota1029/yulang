# Native id joint witnesses: source owners and effective representation cut

Date: 2026-10-08
Baseline: `2e2adc88e93d3aadd8079e764d58e25af786019b`
Branch: `research/simple-sub-intrusion`
Status: reviewed conditional source/implementation correspondence; research only
Gate/method: JOINT_DEC; one native-id source chain, scoped witness-owner audit
Exclusive lease: this file only; frozen on submission
Implementation/API/semantic authority: none; JOINT_DEC remains OPEN-PROOF

## Objective, dependencies and accepted premises

Locate the actual construction owners of the complete J/carrier/context and
strategy witnesses used by the selected native `my id x=x` image law. Trace
whether their exact records or effective classification/replay operations have
counterparts in the current HIR -> collection -> inference -> solved-result
entrypoints. The subject is simultaneous original witnesses, rather than a
generic SourceBuild field inventory or another finite-model attack.

The following abbreviations refer to exact governing sections:

- **U**: [uniform inlet](../theory/2026-10-08-uniform-value-entry-constructor.md)
  §§4.1–4.3 (Parameter/schema/gamma/Delta), §4 Lemma S, §§5.1–5.2
  (fixed raw registration and witness sum), §6 Uniform-ID/Joint-ID.
- **P**: [phase constructor](../theory/2026-10-08-id-public-phase-constructor.md)
  §§2.1,3 (independent V/W/Car and challenge/history records), §§4.1–4.4
  (exhaustive VP/Echo observations), §5 Lemma B (source transitions).
  U supplies the generic inlet; P's earlier fixed-inlet equality is not reused
  as an equality between GenericValueInlet and a frame's I_q[A;Delta].
- **N**: [native certificate constructors](../theory/2026-10-08-native-projection-certificate-constructors.md)
  §2.1 (full evidence), §3 (L registry), §§4.1–4.5 (local action certificates),
  §5 (source owners), §6 CE (all retained proof fields and raw aliases).
- **G**: [source Generalize proof](../theory/2026-10-08-source-generalize-definition-and-proof.md)
  §2 L1–L5, §§3.1–3.4 (rules, checks, ownership and one strategy), §4
  (source rule-choice nodes), §§5.1–5.2 (fixed closure and allocation).
- **O**: [reviewed image owner cut](2026-10-08-id-inlet-whole-output-image-owner-cut.md),
  “Exact source predicate and original telescope”, “Constructed local law and
  conditional prefix lift”, “Effective decision cut”.
- **E**: [JOINT-DEC attempt](2026-10-08-joint-dec-constructive-attempt.md)
  §1 EPR clauses 1–4 and ER, §2 conditional induction/extraction, §3.1 repaired
  classifier gap. EPR and ER are candidate premises, not source rules.
- [Selected native projection](../design/2026-10-08-native-projection-public-export-definition.md)
  §§2–4 selects U/N and VP+Echo before Build; it does not authorize production.
- [Canonical JOINT-DEC](../theory/successor-proof-obligations.md#joint-dec)
  requires effective joint preservation/reflection and simultaneous original
  witnesses. Its current record says required-before-cutover and OPEN-PROOF.

Accepted background: the original local proofs and telescopes remain honest;
the id input-image action is conditional on complete independent input evidence
and one coherent joint strategy; EPR does not imply ER; current production
has no selected public-root producer/checker. The
[q1 receipt](../../questions/2026-10-08-l4-initial-jointwf-owner/receipt.md)
selects the caller as the authentic initial JointWF evidence owner. This audit
uses that decision as a supplied premise; it neither reopens the owner nor
selects its API, validation, representation or lifecycle.

## One source chain and inspected Rust seam

The chain is Parameter Desc/schema -> Lambda raw U_g/IF0 -> independently typed
argument J/gamma and current challenge -> PackGeneric -> receipt/Force ->
Bind/Read/PureReturn/InvocationReturn -> same-provider future restrictions,
all inside one original scoped strategy. Build and Generalize retain that
chain and its rule choices; they do not originate the missing argument or
context validity.

Narrow Rust anchors used below:

| Anchor | Inspected code and actual retained information |
| --- | --- |
| H0 | `crates/yu-hir/src/module.rs:106,867`: SemanticImports is an opaque unit input with only empty construction; lower_module accepts identity, parsed source and that import input. No JointWF/context evidence parameter. |
| H1 | `module.rs:378,461,1289,1338`: HirParameter has id/name/range; the ResolvedExpr::Lambda variant has occurrence/parameter/body/range; lower_plan mints the parameter and wraps the body. NameResolution::Parameter retains lexical identity. |
| H2 | `module.rs:631`: evaluation_class assigns FetchValue to this Lambda/Name form. That is an evaluation classification, not a Car, world or invocation certificate. |
| S0 | `crates/yu-solver/src/lib.rs:697,796,855,1717`: LambdaRecipe and ConstraintBatch retain source occurrence/parameter/component positions and structural fact ordering. For the same-parameter body, emit_lambda sets body_value_component=None and retains body effect positions. |
| S1 | `lib.rs:9755,10790`: startup allocates the parameter value row; admit_lambda_fact uses its negative argument and positive result endpoints, then emits positive_function_term(argument, empty, body_effect, result) below the root. This preserves a type-row link, not a decorated provider/world/proof tuple. |
| S2 | `lib.rs:3023,10685`: AdmissionReceipt brands a store transaction and records constraint occurrence, cause, fact and Accepted/Duplicate. It is not the source receiver receipt or independently admitted argument record. |
| S3 | `lib.rs:7419,9969,15740,16027`: InferenceSession owns live structural rows/bounds and executes SCC solving; solve accepts only ConstraintBatch. finish transfers schemes, closed arena, projections, provenance, errors and store into SolvedModule (`lib.rs:7333`). |

These are inspected local representations, not a repository-wide absence
search. Source origin/position evidence is useful and retained. No identity
test on those fields provides the semantic record laws below.

## Field-by-field witness correspondence

Classification follows `rules/compiler-engineering.md`, “Natural compiler
behavior and proof-obligation economy”: **A** safety/correctness; **B** natural
inference; **C** stronger characterization; **D** reconstruction debt. A/D in
the table means an A obligation with a D retention opportunity *if* the genuine
fact is already constructed. It does not assert that current Rust possessed
and discarded the semantic certificate. An absent supplier cannot be repaired
by retaining an invented field.

| Witness / coordinate | Selected owner and exact clauses | Retained record / evidence | Current compiler counterpart | Missing representation or decision operation; classification |
| --- | --- | --- | --- | --- |
| Original xi=(nu,K,D), scope, registry/authority/incidence | Caller initial JointWF (q1); G §2 L4, §3.3; P §§2.1,3 | Authentic initial world and scope tree; later current-event evidence, exact shared operands | H0 has module/source identities; H1/S0 have lexical and component IDs | No input or transfer of complete JointWF in these entrypoints. Module/artifact IDs do not classify lawful worlds. **A**; source owner already selected. |
| Pre-challenge A/Delta | Parameter, U §4.1; G §3.3 Desc and Description; G §5.2 new | Desc(C,q,ValueEndpoint,sigma,Delta_a); one schema before challenges, repeated payload endpoints share a | H1 parameter identity; S1 parameter row and argument/result row link | Typed Desc telescope and complete Delta are absent; type-row uniformity is only part of the ordinary inference correspondence. **A/B**, not erased semantic proof evidence. |
| Fixed raw U_g and IF0 | Lambda, U §5.1; selected projection §2.2 | One actual closure/provider, fixed GenericValueInlet, intrinsic receipt/formal/return registration and scope/lifetime | H1 Lambda syntax; H2 FetchValue; S0 recipe | No raw provider, actual registration or fixed inlet record. Syntax/row identity does not invert the semantic Act constructor. **A**. |
| Complete J | Independently typed argument, U §4.2 clause 1; G §2 L1/L2/L4 | Whole contract at original root: inlet/port, licence, effects/guarantees/profile, operation/response/raw/future/lifetime/dependencies, including production-only alternatives | S0/S1 expose argument type endpoint; no J record | Supply/encode the argument's independently formed complete contract, without choosing it from tested id safety. No exhaustive J candidate/reflection law. **A**. |
| kappa_J | Argument's authentic formation, U §4.2 clause 1; N §2.1 | Original formation/provenance/scope evidence for that same J/root | H1/S0 occurrence and cause provenance | No interpretation from occurrence/cause provenance to authentic contract formation. **A**; retaining genuine formation records would be D prevention after formation correspondence exists. |
| carrier_J and t/provider | Independent inert carrier introduction, P §2.1; U §4.2 clause 1, Lemma S | Inert formation, restriction at every independently compatible designated demand, universal execution/continuation certificate for the same carrier | S1 structural Function term; H2 FetchValue | No Car record or complete-demand eliminator. Cannot reconstruct complete Car from a payload row or actual successful Force run. **A**, semantic supplier obligation. |
| Current W/context/other values/authority/lifetime | Independent challenge assembly, P §3 initial fields 1–4; U §4.2 clause 4 | Typed punctured context with declared holes, installed values and full live guards; no tested callable membership or executed receipt | H0/H1 lexical namespace; S3 solver context | No admitted context tuple or current-world certificate. The caller's initial evidence alone is not every later compatible context. **A**. |
| Response/raw Resume/Future challenges | Independent history constructors, P §3; VP-Develop/VP-Future in §4.2 | Exposed operation/handle or returned provider, declared demand/response port, current compatible world, scope/lifetime and original history incidence | No semantic history in H1/S0–S3 | Need encodings and effective replay for every independently legal challenge, retaining earlier fields. Finite grammar does not bound histories or classify them. **A** (ER). |
| mu_result | Original argument-result checking, U §4.2 clause 2; G §3.2; N §3 | Finite same-decorated-value local proof, hereditary result action, all intermediate/auxiliary proofs and genuine local laws | S1 constrains structural endpoints; S2 records fact provenance | No matching same-provider inclusion proof term/action. At an authentic source check this term is known and should be retained; endpoint success cannot recreate it. **A/D**, conditional D seam. |
| original_port_map | Checked argument/formal registration, U §4.2 clause 3; P §2.1 IF | Whole carrier/Force/receipt/formal/result and future port incidences, repeated operands and intrinsic fields | H1 lexical parameter/body; S0 component/root positions | No full semantic port map or justified frame action. Retain authentic registration rather than recover it from coincident endpoint IDs. **A/D**, conditional D seam. |
| delta_static | Original entry constraints at their existing static/initial telescope, U §4.3 | Complete original Delta conjunct proofs with their original static dependencies | S0 facts/effect endpoints and S1 bounds | No Delta-specific proof record/telescope or independent leaf law. Existing structural facts cannot assert unrelated guarantees. **A/D** for genuine source-produced proofs. |
| delta_check | Original Call/argument check, U §4.3, especially whole union coverage and current-event congruence | Finite whole-image proof on every J alternative, including production extras and all response/raw/future subtrees; original proof choices kept | S1 structural pair solving, S2 transaction receipt | No complete image proof with all operand telescopes. Bare id's projection schema is selected, but an arbitrary constrained J must supply its genuine derivation. Certificate checking does not decide cell inhabitance. **A/D** locally; effective reflection remains **A**. |
| PackGeneric(kappa,gamma) | Sum introduction, U §5.2 and Forget-Value-Inlet | Exact prechosen schema and gamma, same actual carrier/current world/IF0 guards | No counterpart in S0–S3 | Missing submitted-witness encoding/injection/elimination. Introduction is a syntax-directed local action once inputs exist; it does not enumerate or decide admissible witnesses. **A**; no new inferred Desc under h. |
| Receipt and current invocation occurrence | Lambda Value entry and Strict IF action, P §2.1, §§4.1–4.2; U Uniform-ID | Receipt absent at Start; actual token/current occurrence after receipt; borrow-or-fresh reentry uses current world | S2 AdmissionReceipt certifies constraint-store admission only | No source receipt/frame record or replay action. Substituting S2's identically named receipt would change the proposition. **A**. |
| BindCert / installed binding | Parameter/rebind, N §§4.1,5; P VP-Entry | Actual completed Force Return, same value/provider, extended W, retained binding/hereditary evidence and all checking terms | H1 parameter/Name resolution; S1 shared row | No actual Return/world extension certificate. The selected install law is known; preservation of a genuine constructed record can remove later reconstruction. **A/D** conditionally. |
| ReadCert | Immutable Name, N §§4.2,5 | Projection of that world's one retained binding, restriction at current event, original programs/intermediates and final V evidence | H1 NameResolution::Parameter; S0 body_value_component=None | Lexical identity is retained. No installed-world projection/hereditary proof record follows from that identity. **A/D** for the authentic Name operation; not a new world selection. |
| PureReturnCert and unfinished prefixes | Pure source Result, N §§4.3,5; P VP-Body/BodyReturn/Restrict | Same raw result/provider/world and exact result port; no fabricated completed value in prefixes; all L choices retained | S0 body/lambda effect rows; S1 result endpoint | No complete/pending T certificate or proof tuple. Empty body effect is not whole-input purity or future safety. **A/D** for known genuine Return evidence. |
| InvocationReturnCert | Complete invocation return, N §4.4; P VP-InvocationReturn | Exit only current own occurrence, projected live W and same outward provider/future certificate, all proof fields | S1 Function result port; S3 closed Function scheme | No current-occurrence removal/world-projection action. An arrow result does not identify body and outward incidences. **A/D** for supplied genuine frame-action evidence. |
| L and all proof alternatives/intermediates | Independent registry, N §3 and §4.5; G §3.2 and §4 rule choices | Full typed input/output telescopes and independent laws; Identity versus Compose/union/structural/registered choices remain distinct | S2 causes/facts; S3 structural pair/worklist and schemes | No complete L term representation or corresponding choice graph. Finite grammar gives recognition by its local laws, not all-true-inclusion completeness or a finite candidate bound. **A/D** for proofs selected at source checks; arbitrary semantic inclusion characterization is **C** outside this audit. |
| Shared/ViewLogic/Check/EventField/EventProof | Their owning source rules, G §3.3; allocation G §5.2; N §5 | One Shared witness; one pre-challenge ViewLogic per frame; runtime event operands shared, EventProof remains per-description under that same event; intermediates at original scopes | H1 lexical binding; S3 levels/non_generic and scheme freshening | No explicit original dependent proof/choice tree. Levels/freshened rows are not a strategy preserving these distinctions. **A/D** for scoped owner data, plus **B** for natural independent new/alias behavior. |
| Joint strategy, aliases/new and active W | G §3.4 joint legality and strategy definition; U Joint-ID; N CE; G §5.2 | One strategy over the whole original tree; aliases reuse a frame, new allocates a frame; shared event/world/proof operands and arbitrary active client clauses remain joined | S3 SCC solve, use routes and closed schemes | No encoded original prefix, classifier, challenge replay, or simultaneous proof-witness strategy. Joining separately successful structural comparisons cannot construct this strategy. **A** (EPR/ER); not solely D. |

The table identifies selected local owners, rather than delegating everything
to Generalize. Complete J/Car/context and authentic local leaf evidence are
inputs to those owners. Their full-domain validity is not a fact shown to have
been discarded by the current compiler. Source registration, source check
choices and exact lexical/alias incidence are useful retention seams once
their genuine constructor correspondence is established.

## Conditional derivation and the exact effective gap

**Claim class: bounded static characterization plus a conditional derivation.**
No new unconditional semantic theorem or production conformance result is
claimed. Assume:

1. The selected native U/P/N source meanings and genuine L1–L5 laws, including
   caller-supplied authentic initial JointWF and independently legal later
   world/context actions.
2. One lawful original assignment and scoped joint strategy s satisfying all
   prior choices and active client W. Every A/Delta and ViewLogic choice has
   its original pre-challenge placement; no late choice repairs a prefix.
3. At each admitted challenge, that same carrier's independently formed
   complete J, kappa_J, carrier_J and gamma, including full delta_check and
   mu_result choices and all hereditary/context subtrees.

Under these hypotheses the following source transformation is derivable:

```text
original prefix a with supplied s and checked gamma
  -> same a with PackGeneric(kappa,gamma)
  -> receipt / current-world Force observation from carrier_J
  -> delta_check elimination on that SAME J observation/development
  -> Bind / Read / Return / InvocationReturn certificates at their owners
  -> original same-provider future restriction and unfinished-suffix extension.
```

PackGeneric is U's sum introduction. Lemma S obtains the same Force observation
from carrier_J, applies the whole-image proof at its current tuple and uses
mu_result only at a completed Return. N's local records then introduce or
project exact binding/world/Return certificates. At a Request, the original
raw handle acts at C_current and only the unfinished suffix remains; receipt,
static descriptions and earlier witnesses are not replayed. P's independently
legal history constructors and hereditary eliminators justify each later
extension. Finite-history induction supplies this local action for every
legal finite extension, not just histories below a sampled depth. Joint-ID
applies these actions to all frames using the already supplied same s. CE
preserves its nondefinitional proof choices and substitutes only forced raw
aliases. Thus the source transformation preserves original prefix incidence
and choices under the hypotheses.

This derivation constructs an action on **supplied** certificates. It does
not prove that any arbitrary remaining residual has such certificates or s.
In particular it cannot fulfill the following EPR/ER requests merely by naming
the owning source constructors:

| Effective request | Source contribution | Exact unsupplied premise |
| --- | --- | --- |
| EPR.1 finite effective residual presentation | Finite inlet/VP/local-proof/source grammar schemas | Terminating construction of a finite layered residual presentation and a certified semantic map for every legal original prefix. This alone does not require every auxiliary state to represent an inhabited tuple. |
| EPR.2 forward extension | Above conditional same-prefix action; P's legal history domains | A map q_n preserving every active predicate under a proposed abstraction, including all original choices. No such abstraction is selected here. |
| EPR.3 prefix-local backward extension | PackGeneric and native action extend the supplied original prefix | Every listed abstract child must have a legal lift at **each fixed concrete prefix** in its fiber. Native transfer of an already coherent witness does not supply a witness in an empty or incompatible fiber. |
| EPR.4 exact terminal labels/evidence | delta_check/L eliminators derive their conclusions from genuine premises | Effective joint cell decision/reflection for all actual retained predicates, not only recognition of a submitted proof or structural payload witness. |
| ER encoding/classification/replay | Four independent history constructors; finite proof syntax and local event actions | Whole-prefix/challenge codes with independent interpretations, total terminating classifiers for every legal encoded prefix, and replay/lift closure preserving that exact prefix for every legal challenge. |

ER is a separate demand from EPR's semantic q_n. An effective local proof
constructor supplied with complete field codes could implement the displayed
record action. That conditional fact supplies no classifier for arbitrary
semantic challenges, nor a code for every compatible world or external input.
External symbolic parameters need an independent interpretation/classification
contract; a call to a supplied q_n oracle would assume the missing premise.

The decisive classification is **A**, a known semantic/correctness owner
obligation for the selected complete residual route: authentic argument/context
formation must supply its evidence, and an effective joint route must prove
cell reflection and same-prefix classification/replay. The selected source
rules do not assign an effective residual classifier algorithm. Their absence
does not establish a new language decision. D can remove reconstruction of
genuinely known owner records; it cannot show a complete J cell inhabited or
compute a strategy that the constructor assumes. JOINT_DEC remains open.

## Independence, coverage and process report

This is a source-grounded derivation and scoped Rust representation inspection,
not an executable experiment. It reuses O's reviewed conditional image action
and E's repaired premises, without independently reviewing them or repeating
the Record-chain/noncomputable-classifier attacks. There is no reference oracle,
random seed, enumeration range, mutation run, proof search or performance data.
Independence here means the local laws/challenge domains are defined before
tested callable realization and query success. This report itself has not
received independent review. A checker interpreting the same supplied rules
would validate internal consistency and submitted terms; it would not prove
the genuine source rules, complete witness range, or EPR/ER reflection.

Failure conditions: incomplete J alternatives; absent/false carrier/context/L
law; static Delta hoisted under a challenge or event proof hoisted above it;
proof choices/intermediates erased despite active W; new world/provider chosen
to join frames; historical receipt replay; raw resumption using a saved world;
unencodable legal challenge; classifier assuming a semantic oracle; replay
changing an earlier witness; abstract inhabited-cell lifting valid only at
another prefix. Any of these invalidates the claimed local correspondence or
effective route at the relevant seam. None is excused by successful structural
solving.

Commands/results: required rules and exact sources read with cat, rg -n and
bounded sed; source SHA-256 capture; narrow Rust owner reads; leased-note static
integrity and final dependency recheck. Initial combined captures included
truncation; subsequent exact source slices supplied the cited clauses. The
large solver file was inspected only at the listed owners and their immediate
data flow, not in full. No repository-wide absence or completed search is
claimed. No tests, builds, network, benchmarks, formatting or Git mutations.

Process deviation: baseline verification used read-only `git rev-parse HEAD`,
`git status --short` and dependency-only `git diff --name-only BASE -- paths`,
despite the assignment's stricter no-Git-operations wording. HEAD matched the
pinned SHA, initial status was clean and the inspected dependencies had no
baseline differences. This was disclosed to the primary. Subsequent checks
use filesystem reads and SHA-256 only; no index/ref was mutated.

Independent compiler-referee review at the pre-repair artifact SHA-256
`ad46e0959ef97e85427a423ec74a70ed0c303eed177210e1d3504ab38844feaf` found no
blocking or major issue and one minor precision issue: EPR.1 should describe
finite presentation construction and the map for legal prefixes, while
inhabitance/reflection belongs to EPR.3–4. The primary corrected that wording
and the HIR Lambda source locator (`443` -> `461`) without changing the
conditional claim or gate status.

Resources: lightweight read commands and one leased note write; no compute
probe/build/test processes or generated output paths. Independent reads were
batched, with at most three shell reads concurrently; no heavyweight work.
No numeric CPU/RAM/wall-time budget was supplied. Aggregate CPU, peak RSS and
wall time were not instrumented and are unknown. Work stops after this one
native-id chain. Unverified scope includes foreign/State/general recursive
inputs, arbitrary catalogues or true extensional inclusions, whole-language
solver completeness/principality, public-root production and cutover.

**One recommended next action:** lease a source-grounded effective witness
interface derivation for one exact complete native J/current-context family,
requiring independent code interpretation, same-prefix challenge replay and
joint inhabited-cell reflection (EPR.3–4 plus ER). Keep authentic L/gamma and
all original proof scopes explicit. Treat the current native transfer action
as a consumer of those inputs, not a substitute for those missing laws.

## Dependency snapshot and commit packet

Direct semantic/implementation dependencies at baseline:

```text
b9a6f724fc574a580d14ac31dcaca41fcc5347b50b6ecccf7976f15a102050e5  notes/progress/2026-10-08-id-inlet-whole-output-image-owner-cut.md
dbf98d3a6dbbd55c79289f5bb43dd3edf2fea76287f1203c83a4876d5a820977  notes/progress/2026-10-08-joint-dec-constructive-attempt.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b  notes/theory/2026-10-08-id-public-phase-constructor.md
04c5699dfaaf5f98ee9db54df5bd124f25e7131abb6bc3104e1675a5490f74a8  notes/theory/2026-10-08-native-projection-certificate-constructors.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919  notes/design/2026-10-08-native-projection-public-export-definition.md
59442db205d0bc381de74a373f1d58a753e3366ae0ba845e8c9c877465e738fc  notes/theory/successor-proof-obligations.md
3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363  crates/yu-hir/src/module.rs
236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2  crates/yu-solver/src/lib.rs
3e7e520a29818c105bca09f8c46c44e6d1cc2562c5d973580491bbc552e99da2  questions/2026-10-08-l4-initial-jointwf-owner/approved-answer.md
c9c832d9c28261a7df9c67247bb14045070cf901b8e04aad36115c0e653bf7f6  questions/2026-10-08-l4-initial-jointwf-owner/receipt.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442  rules/compiler-engineering.md
32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716  rules/orchestration-budget.md
```

- Exact leased/changed path:
  `notes/progress/2026-10-08-joint-witness-source-owner-correspondence.md`.
- Baseline SHA: `2e2adc88e93d3aadd8079e764d58e25af786019b`.
- Dependency changes: none in the direct source snapshot. Filesystem HEAD
  advanced during work to `9a286b72d1659a558165832434943f814a17fa70`; all eleven
  semantic/implementation hashes still matched the original snapshot. The
  final seventeen-entry snapshot also records the accepted receipt and rules.
  q1's accepted answer hash matches its receipt; committed-bundle integration
  provenance is the supplied receipt. The pinned research baseline is retained.
- Claim/review status: unreviewed bounded characterization and conditional
  source derivation, research only. No independent certification by producer;
  frozen on submission. JOINT_DEC and all other gate statuses unchanged.
- Checks already run: exact source/owner reads, initial read-only Git baseline
  comparison (process deviation above), SHA-256 snapshot/recheck, leased-path
  Markdown links and whitespace/final-newline integrity. No tests or builds.
- Proposed one-line research checkpoint commit message:
  `research: trace native id joint witness owners and effective replay gaps`.
- Shared-record deltas intentionally left for primary/curator: optionally link
  this note under JOINT_DEC and record the distinction between retained local
  certificates and missing EPR.3–4/ER witness laws. Preserve OPEN-PROOF and
  caller initial-world selection. No task/index/authority/theory-map/manifests/
  lockfiles/question bundles were edited.
