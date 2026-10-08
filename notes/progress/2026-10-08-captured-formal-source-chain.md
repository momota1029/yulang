# Captured formal f: conditional source constructor dependency chain

Date: 2026-10-08
Status: unreviewed conditional source-only dependency map; frozen on submission
Baseline: `dfab5f781f6d6640034b0857969ad4cd4c65baf2`
Branch/worktree: `research/simple-sub-intrusion`, `/home/momota1029/rust/yulang`
Exclusive lease: this new note only
Implementation, source-meaning selection, independent certification and gate closure: none

## 1. Objective, method and governing clauses

Trace the exact captured formal in

```text
my apply f = { my step x = f x; step }
```

from an original semantic context to the Call owner's input and its dependent
Gen-Call-0 output. Method: one constructive rule-premise/dependency pass;
no compiler inspection, model, executable experiment or search. This does
not repeat the existing production owner audits or prove their absence claims.

Abbreviations and exact governing locations:

| Reference | Clauses used |
| --- | --- |
| SG-D: `notes/design/2026-10-08-source-generalize-definition.md` | §§2–4 select native source rules, retain L1–L5 and separate production. |
| SG: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | §2 L1–L5; §3 opening; §3.1 Parameter/Lambda/Name/Bind/Result/Call; §3.2 genuine local checks; §3.3 original owning records and telescopes. |
| UV: `notes/theory/2026-10-08-uniform-value-entry-constructor.md` | §§4.1–4.3 Parameter/schema/complete argument witnesses and Lemma S; §§5.1–5.2 raw generic inlet and injection; §§6,7.2,8 body theorem limitations. |
| IR: `notes/theory/2026-10-08-call-semantic-input-realization.md` | §2 original `xi`/live events and independent challenge assembly; §4.1 hereditary environment and Lemma W. |
| CG: `notes/progress/2026-10-06-source-call-generation-construction.md` | §3 exact formal/Name roots; §§4.2,4.4 Gen-Call-0 and scope/capture; §5 complete Call clause. |
| NB: `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | §§1–3 exact selected block/capture/core meaning. |

NB fixes `u_f -> d_f`, `u_x -> d_x`, sequential local binding and return of
the same `step` without invocation. The original shared `xi=(nu,K,D)`, actual
source role/entry and annotated-boundary meanings remain fixed. This note
selects no owner family, initial-world API, or new meaning. The pending
`l4-initial-jointwf-owner/q1` and `flat-application-owner-family/q1` questions
were read only as premises/blocked-scope records; no answer was consumed.

## 2. Claim classes and precise hypotheses

**Established selected constructors reused:** SG owning records; UV finite
Parameter schema and raw generic inlet constructor at its authentic source
formation seam; IR Lemma W; CG's bounded Gen-Call-0 schema. Recorded review of
these inputs is not independent review of this note. CG supplies a conditional
interpreted construction, not an Authoritative implementation adoption.

**Conditional derivation here:** if the following original inputs and local
constructor premises are supplied at their own scopes, the same outer formal
certificate reaches `Gamma(d_f)=Value(A_f)` in the captured Call environment;
the Call schema can introduce unsolved complete dependent `F_c` at `R_f`.
This is a construction implication, not existence of its premises or a
satisfying assignment.

**Bounded characterization:** none of the inspected source arrows constructs
initial JointWF from this syntax or empty captures. The cited production audits
report missing interpreted descriptor/environment input and then complete
`F_c`; those remain their bounded audits, not a new repository-wide result.

**Candidate assumptions:** none adopted. Applicability/realization premises
are explicitly conditional below; they are not new definitions or successful
typing facts. In particular no candidate empty-world, fresh captured type,
Function-shape implication, or new effectful-body law is inserted.

The exact local-law inventory is retained:

| Premise | Required input here; no strengthening or discharge |
| --- | --- |
| L1, SG §2 | Any authentic primitive used by a supplied argument/context has its independently fixed relation, full operands, guards, effects, provider/future/admission laws and permitted rule schema. No opaque `LegalSource`/query leaf. |
| L2, SG §2 | Original Return/Request/Bind/Call/closure/delay/elimination laws; selected native constructors only in their stated cases. Foreign constructors require original identification. |
| L3, SG §2 and §3.2 | Genuine finite local whole-interface inclusion/checking or actual conversion proof. UV `mu_result` and `delta_check` require these laws; admission alone supplies neither. |
| L4, SG §2 and §3 opening | Genuine original initial JointWF registry/scope/authority/incidence world, actual event and original introduction/annotation/profile evidence needed by the derivation. No separate-member worlds or Empty bootstrap. This exact chain adds no general recursion law. |
| L5, SG §2; IR §§2,4.1 | Original independently compatible current/future contexts, history extensions and actual lifetimes. Every Option 2 W/Z arm retains its full law/hard envelope. Mutable State compatibility is not inferred from immutable references. |

Additionally fix the resolved graph and original binder tree, one original
static assignment `eta0`, actual registrations/incidences and one jointly
scoped witness strategy. The current world changes at actual events; `eta0`
does not freeze it. Actual Value-entry argument certificates, receipt/rebind
guards and any body/checking premises are genuine inputs when used. A bare
source string is not an independently typed carrier or environment.

## 3. Original telescopes and identities

Distinguish the source component `C_src` from live configurations `C_e`.
Write `v_f,p_f,r_f` for the actual returned decorated value, provider and
registered value incidence of f. `R_f` is CG's inferred-contract root at
`(C_src,d_f,A_f,sigma)`; it is not asserted equal to `p_f`, `r_f`, the outer
raw provider `U_apply`, or a structural solver row.

The dependency order is schematic notation for the **existing** binder tree:

```text
original xi / context / registrations / Shared dependencies
  sigma_f: Desc(C_src,d_f,ValueEndpoint,sigma_f,Delta_f): A_f
  formed entry schema and description/checking operands at original scopes
    h_apply: independent whole-carrier/context challenge
      actual receipt / Force developments
        completed Return: v_f,p_f,r_f,C_return,w_return, hereditary V(A_f)
        actual f rebind and dependency-closed capture at step formation
          sigma_x: Desc(C_step,d_x,ValueEndpoint,sigma_x,Delta_x): A_x
          step's own description/checking operands
            h_step: independent challenge / actual receipt / Force
              completed x rebind / current captured f restriction
                c = Apply(u_f,u_x), original Call telescope
                dependent F_c and Call evidence at their permitted scopes
```

`sigma_f` precedes `h_apply`; `A_f` cannot depend on f's later argument
witness. `sigma_x` precedes `h_step` but may be inside the enclosing actual
apply event if its authentic source owning rule places it there. This diagram
does not hoist it or prescribe a new quantifier order. `F_c`/evidence stay
inside every original rigid binder they depend on. `Desc` dependencies are
already introduced operands; no extra unconstrained effect/profile/interface
binder is added. SG §3.3 keeps Shared once, ViewLogic at its description
scope, actual EventField under its event, and EventProof under the same
actual operands. Distinct proof choices are retained, not erased.

## 4. Forward arrows with supplier classification

`O` means selected source constructor output given its original premises;
`P` means genuine semantic premise; `M` means absent production correspondence
on the previously inspected path, reported here only by citation.

| Arrow | Premise consumed and exact output | Class / correspondence boundary |
| --- | --- | --- |
| Context to source formation | Original actual event and `JointWF(C_init,w_init)` with registry, authority, scope, incidence and lifetime; resolved definition/formal registrations. | P: SG §2 L4, §3 opening; IR §4.1. No source rule here concludes initial world from syntax. M: prior L4 trace/owner question does not assign a production supplier. |
| Parameter f | Authentic unannotated Value formal and already introduced original operands. Introduce `Desc(C_src,d_f,ValueEndpoint,sigma_f,Delta_f):A_f`, Intrinsic source slots/mode and `I_f=I_qf[A_f;Delta_f]`, retaining Description edges and constraints. | O: SG §§3.1,3.3; UV §4.1. Not Function membership and not a per-use endpoint. Production retention is unproved. |
| Lambda registration/raw entry | Authentic raw registration, actual role, formal qf, body operation, immutable capture references, original receipt/consumer/lifetime fields. At UV's generic source-owning formation case construct one `U_apply`, `IF0_apply`, fixed `GenericValueInlet(qf,IF0_apply)` and separate Internal entry/body/result description. | O conditional on that constructor's formation premises: UV §5.1. Raw operations include actual receipt, designated one-layer Force, Return/rebind, body and invocation return. Their typing/complete body law is P, not a raw-registration conclusion. |
| Checked challenge to actual entry | Prechosen original `A_f/Delta_f` and complete independently typed argument witness `gamma_f=(J,kappa_J,carrier_J,mu_result,original_port_map,delta_static,delta_check,current_guards)`; original compatible context. Inject the same witness with `PackGeneric`, then follow the actual receipt/Force. A completed Force supplies the same `v_f,p_f,r_f` and hereditary V(A_f) at its current world. | P for full gamma/context/guards; O for injection and Lemma S elimination: UV §§4.2–5.2; IR §2. No body safety, receipt execution or VIncl follows from admission alone. |
| Return to formal rebind | Actual completed Force Return, its V/W and original typed rebind path. ValueBind/ResultBind append exactly that decorated value/certificate; old bindings restrict to that same compatible event. | O given P: IR §4.1 Lemma W; SG §3.1 Lambda/Bind. Pending or divergent entry supplies no rebound f and no downstream completed body. |
| f rebind to step capture | Dependency-closed original free-binding subgraph, including f's whole certificate and all dependent fields. Capture restricts the existing projection; `Mono(h,Contract_h)`/Established and alias edges retain the exact installed contract. | O given P: IR §4.1; SG §3.3. No new provider, root, inference declaration or instantiation. Relative to step, free outer dependencies remain those of its actual capture; this is not a claim about global Generalize eligibility. |
| step formation and return | Actual local Lambda registration/qx/entry/body/consumer, same retained f projection and local world. Local Bind installs the actual returned step; final Name/Result yields it without invoking it. Step's Parameter is introduced before its own challenge. | O for owning records/operations: SG §§3.1,3.3; NB §2. Original formation/body certificates remain P. Formation does not execute `f x`, establish step membership, or replace f by a convenient provider. |
| Future step use to captured Name | Independently compatible live event, x's whole argument certificate/completed rebind and old f certificate's hereditary restriction to that same event. `Name(d_f)` projects exactly retained `v_f,p_f,r_f,A_f` and the complete dependent evidence. Result forms `J_f=ReturnImage(Name(d_f),original environment)`. Similarly form `J_x`. | O given P: SG §3.1 Name/Result; IR §4.1; CG §3. Original lifetime/authority guards are evaluated at this event; maker authority is not blindly retained as live. M: cited F5 crosswalk reports these complete images absent. |
| Captured environment to Call owner | Restrict the installed joint certificate at exact lexical `d_f`: `Gamma(d_f)=Value(A_f)`; `Gamma(d_x)=Value(A_x)`, same original xi/scopes and resolved c. | O as environment projection; P as the Call input package: CG §3. Endpoint, original root/provider/world and whole dependent telescope accompany the tag. M: production audits report missing interpreted source descriptor/environment relation before row-to-A_f interpretation. |
| Call input to Gen-Call-0 | The exact resolved singleton Call and that interpreted input produce `R_f`, one dependent complete Function variable `F_c` at R_f, `beta=(d_f,R_f)`, p0/pout and ElimOrigin incidence. | O: CG §4.2, with coherent scope/capture action in §4.4. F_c is unsolved; static formation is neither WF_Dec proof, actual provider decomposition, emitted complete membership clause nor solver inclusion. M: cited audits report no complete production F_c supplier. |

UV §5.1 says generic entry has no actual payload-type/dictionary consultation;
description-dependent one-shot entry/code/dictionary fields remain fixed.
This is a formation premise, not permission to erase arbitrary such fields.
This note assigns no Pure role to apply or step. UV §§6,8 prove the id/pick
projection body cases, and explicitly omit general effectful/State bodies.
Their theorem cannot establish apply/step body typing. Here Lambda's actual
entry/body operation and required complete invocation are retained from SG's
selected rule; any full body/checking derivation remains a genuine premise.
The map stops at constraint formation so it need not assume its own successful
Call check in order to emit the unsolved F_c.

## 5. What the last arrow has not proved

CG §5 keeps the complete conjuncts separately active:

```text
exists_sigma(F_c,e).
  WF_Dec(F_c;xi)
  & VIncl(A_f,F_c;xi,e_value)
  & WholeArgCompatible(J_x,CarrierContract(F_c);xi,e_arg)
  & CIncl(ExecuteCallableImage(J_f,Delay(J_x),F_c,e;xi),
          Comp(E_c,A_c);xi,e_result)
  & TypedCallCert_Dec(c,F_c,e;xi)
  & Role_0 and canonical Gen-Call-0 records
```

The source generator can introduce a dependent variable and emit these
constraints without satisfying them. The complete variable is not merely
body/result arrow ports: its descriptor domain retains whole-carrier,
entry/consumer, independent admission/observation, response/raw/future,
profile, scope and joint dependency fields. Formation does not prove their
well-formed realization. Role_0 is an internal singleton role refinement;
it does not assign the actual captured value's introduction role.

Neither hereditary `V(A_f)` of one actual f nor registration of R_f proves
the universal same-decorated-value `VIncl(A_f,F_c)`. `J_x` is the exact Name
Return image; its printed `Comp(empty,A_x)` is not an exact returning image
and does not replace step's external entry carrier. Complete invocation
includes entry, body and designated consumers; its effect is not a bare
body row. TypedCallCert retains supplied decorated profile/receipt/operation/
observation/correspondence evidence beyond static ElimOrigin. No relative
RT.2 comparison action, all-argument compatibility, execution containment,
principality, solver completeness, production F5 preservation or cutover
follows from this chain.

## 6. First missing supplier and falsifiable next question

First source premise: authentic initial JointWF/world/registration evidence,
before Lambda or any rebind. IR Lemma W's Empty uses **the joint world's empty
environment**. Empty captures, immutable IDs, raw registration and an opaque
validity flag cannot supply that world. The pending initial-owner question
chooses neither an answer nor an API in this note.

First missing production supplier reported by the existing bounded audits:
an interpreted original descriptor/environment relation with shared xi and
original scopes. The symbolic captured-binder registration is structural.
Conditional on the authentic source input, complete dependent F_c at R_f is
the next reported absent Call-produced object. This note does not reinspect
production or extend that audit's search coverage.

Recommended next action: after the primary resolves the initial-context owner,
trace that owner's retained output through the exact Parameter/rebind/capture/
Name path to the pre-admission Call constructor. Falsifiable question: **does
one named producer retain the complete original `Gamma(d_f)=Value(A_f)`
certificate, same provider/root/xi/scopes and dependencies, then construct
complete dependent F_c at R_f before structural solver admission?** A positive
answer identifies the producer, fields and transfer path; an ID-only record,
four-port term, successful constraint/query or newly selected world fails it.

Premise-removal discriminator (documentary, not an executed counterexample):
keep source/resolutions and A_f fixed, remove the independently typed outer
carrier's Return certificate. The resolved capture still exists syntactically,
but IR rebind has no V/W input and cannot derive a semantic f environment.
Restore that certificate and compatible world evidence to recover the
conditional arrow. This separates lexical capture from semantic supply;
it claims no legal Yulang rejection or alternate language model.

## 7. Verification, coverage and freeze

No executable oracle is used. This derivation shares the selected source
constructors and L1–L5; it does not independently validate those laws against
Oracle, legacy runtime or current compiler. A checker assuming their
transitions would establish conditional consistency, not prove source rules.
There are no executable seeds, ranges, mutation counts or model coverage.
No proof/model variants or repeated toy probes were run.

Checks: bounded cat/sed/rg section reads; read-only HEAD/branch/status; Python
SHA-256 and byte comparison of the 14 dependencies below to
`git show dfab5f781f6d6640034b0857969ad4cd4c65baf2:path`; note newline,
whitespace/fence/local-file-link checks. All tracked dependency bytes match
baseline. Initial batched output was truncated; operative clauses were
subsequently read in bounded chunks. Pending question premise files were
hashed separately and remain non-authoritative untracked inputs.

Resource budget consumed: documentary I/O and integrity checks only; zero
builds, tests, semantic probes, measurements or child agents. Read batches
used at most three lightweight read commands concurrently; no heavyweight
process. CPU time, peak RSS and aggregate LLM wall time were not instrumented.
No computation timeout or incomplete enumeration exists; production search
was intentionally omitted. Whole-language inhabitance, foreign/State laws,
effectful body proofs, complete capture-summary construction, runtime oracle,
source/production correspondence and every downstream gate remain unverified.

Only this leased note was written. No shared record, question file, production
code, test, manifest, lockfile or Git state was mutated. Writing stops at
submission; the artifact is frozen and producer-inspected, not independently
reviewed. Repairs require renewed scope.

### Baseline dependency SHA-256 snapshot

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
32174c0eb14314df334499586b43db3074de4662fdc908da60eb1a24e1dc3716  rules/orchestration-budget.md
8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0  rules/question-board.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5  notes/theory/2026-10-08-uniform-value-entry-constructor.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
7fea7293e8506e481ebcbff591e043617b58144e24cc071208249285860505d9  notes/progress/2026-10-08-f5-apply-preadmission-owner-cut.md
61cc5a1b39b04b1c52fd564aef30334eea5eee4f693fb7e90d0700361cb89de3  notes/progress/2026-10-08-f5-apply-source-field-crosswalk.md
f9b6d30855f26d9e87cd9f64aa23c46957c74ff042c2a9d0bbddb48f98a501f5  notes/progress/2026-10-08-l4-id-anchor-source-constructor-trace.md
```

Untracked premise-only snapshots, not consumed answers:

```text
f0f29397637524928830ba98b58b92c708c4b8a903b82ab91190b171aef16aba  questions/2026-10-08-l4-initial-jointwf-owner/question.md
90e1f4912ff0bdd113b9557e41404c773ef4b76747b43bf5645084b0eaad4cd3  questions/2026-10-08-flat-application-owner-family/question.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-captured-formal-source-chain.md`.
- Baseline SHA: `dfab5f781f6d6640034b0857969ad4cd4c65baf2`.
- Dependency hashes changed from baseline: none; pending questions are premise-only snapshots, with no approval consumption.
- Claim/review status: conditional source-only dependency map, frozen/unreviewed; no independent certification, authority or gate promotion.
- Checks already run: bounded source reads, read-only branch/status, dependency byte/hash checks and note integrity; no compiler tests/builds/probes/measurements.
- Proposed checkpoint message: `research: trace captured formal source dependencies to Gen-Call-0`.
- Shared-record deltas left to primary/curator: link this exact conditional chain in `tasks/current.md` and any relevant theory navigation after adjudication; retain L4/initial-owner and interpreted-environment supplier gates, complete F_c correspondence and all Call/RT.2/principality/F5 residuals. No shared-record edit or status promotion by this producer.
