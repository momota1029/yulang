# ReadInvoke initial/lookup evidence: constructive map audit

Date: 2026-10-08
Status: non-authoritative bounded construction derivation and exact remaining premise; frozen on submission
Baseline: `85d59a99389647d8eb9f4e4cf16e5897bc57df7e`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Independent review, export selection, semantic extension and production authority: none

## 1. Objective, authority and result

Audit the forward/back evidence maps left open by [prefix projection](2026-10-08-pure-read-prefix-projection-audit.md) §§4–6 for the original source formation retained in [ReadInvoke](../design/2026-10-08-pure-read-call-result-constructor.md) §3. The method is elimination and reassembly of the actual selected source constructors, followed by an inventory of their original evidence consumers. It does not repeat the preceding conditional proof-sensitive countermodel or a transition experiment.

The selected sources support a **lossless construction-time record map** for the fixed local source `call(result(name f),result(name x))`. They also support projection of early evidence to the recorded binding, phase, dependent interface and guard fields. They do not supply a complete elimination/reintroduction law for the original retained-formation field after its constructor evidence is discarded. The exact missing law is stated in §5. No genuine separating source pair is established; no impossibility theorem follows.

The [approved root-policy q1/a1](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md), decision items 1–5, selects a displayable transformed scheme with only necessary use-time information. A lossless encoding of q does not meet that goal by renaming q, and is not an acceptable transformed public export merely because its fields are finite. The record below is a diagnostic control for distinguishing reconstruction from actual evidence abstraction. Its necessity, size and suitability for an export are not established.

Exact governing scope:

- [Function-call views](../design/2026-10-05-inferred-function-call-views.md) §§1–5: shared source-generated contract, original slot/path/incidence and correlated `nu,K,D`; source annotations, public scheme and internal evidence remain distinct.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2–3,5.3: independently interpreted constructor images; separate `M_E` and `DescMem`; finite source derivations, complete original alternatives and independently certified whole actions. Its general interpretation/query contracts remain conditional, not selected concrete semantics.
- ReadInvoke §3: retain original formation in initial/lookup prefixes, same-root binding obligation, Bind interface, paths, guards and suspended suffix; no actual Delay/challenge/receipt/entry early.
- [Selected source-interface definition](../design/2026-10-08-call-source-interface-definition.md) §§2–4 and [construction](2026-10-08-call-source-interface-construction.md) §§3.1–3.3,4–5: explicit complete field retention and contextual projections, with original source derivations inserted at callee/argument slots.
- [Selected closure constructors](../design/2026-10-08-captured-closure-constructor-definition.md) §4 and [closure proof](2026-10-08-captured-call-closure-introduction.md) §§4.1–4.3: original finite Name/Result/Bind/Call prefix cases.
- [Source-input construction](2026-10-07-call-input-construction-proof.md) §§3.1,3.4,4: the exhibited finite certificate payload and syntactic whole-substitution law. No unselected semantic clauses from its §5 are used.

The integrated [receipt](../../questions/2026-10-08-successor-generalize-root-policy/receipt.md) fixes the accepted decision's scope. Dirty coordination files are not premises. All direct inputs were read at the pinned revision and matched live bytes at verification.

## 2. Original index and explicit hypotheses

Fix the original joint index j, binder tree, typed environment E, source/use/operator incidences, assignment `xi=(nu,K,D)`, and the one actual finite source formation q. The captured f keeps its outer declaration/root; x is the actual post-entry/rebind Value binding. No captured coordinate is freshened by this construction. The early tuple `(e,O,w)` is before the inner callee Return. An actual callee-result provider, carrier, checked challenge or receiver observation is therefore absent.

For the construction-time statement, assume:

1. q is an introduction derivation of exactly the displayed Data-Name, Code-Result, Carrier-Delay and Code-Call cases, with their exhibited constructor payload. Any additional opaque formation evidence must also be retained; the argument below does not erase it.
2. Every binding certificate, original Name use-to-binding evidence field, origin witness and dependent port is available at its original index. Their validity comes from the original source construction, rather than endpoint equality or a successful comparison.
3. Repeated occurrences retain their original sharing. In particular the carrier uses the same argument derivation; Check_c uses the same callee/argument/carrier derivations; IF placements use those same original source occurrences.
4. A supplied legal whole substitution acts on all source/binder operands and origins together as in source-input §4. Arbitrary semantic maps and later-event evidence actions require their independently supplied laws.

No world inhabitance, satisfying assignment, VIncl truth, WholeArgCompatible truth, receiver acceptance, source-base membership of the whole Call, Q success or descriptor typing is a formation hypothesis. Semantic use of the early fact projection additionally retains the original valid environment, live guards and independent complete interface/action inputs. None is generated by record reassembly.

## 3. Actual construction-time forward/back maps

Expand the fixed original formation using the displayed constructor rules:

```text
n_f = Data-Name(b_f,edge_f)
q_f = Code-Result(n_f,o_f)
n_x = Data-Name(b_x,edge_x)
q_x = Code-Result(n_x,o_x)
t   = Carrier-Delay(q_x,o_arg)
q   = Code-Call(q_f,q_x,t,Check_c,o_c,suffix_ports)
```

Here `edge_f` and `edge_x` are the **original use-to-binding evidence outputs** of Name resolution, not merely its endpoint. Source-input §3 constructs them by induction on actual resolution. It does not say that the entire resolution proof tree is part of the Data-Name payload, and this audit imposes no such requirement. `o_arg` contains the actual ReifyOrigin root, scope and incidences. Check_c is the original bundle described in source-input §3.4: actual Application origin, independently formed checked descriptors, emitted VIncl/WholeArgCompatible origins, complete result interface, original resolved roots/scopes/incidences and dependent suffix. Its repeated `q_f,q_x,t` references are the same objects above. No component is replaced by the truth of an emitted constraint.

Define L(q) by removing the displayed constructor nesting and duplicate references while retaining:

```text
(j,E;
 b_f,edge_f,o_f; b_x,edge_x,o_x;
 actual Application origin, o_arg;
 original F_c,R_f and complete Comp(E_c,A_c), o_c;
 actual VIncl-origin, WholeArgCompatible-origin;
 original roots/scopes/incidences and suffix ports;
 original sharing/reference coordinates).
```

L retains all original proof payloads, not a set of their conclusions. Other original dependent decorations stay unchanged outside this local record. In particular, the binding leaf may contain a dependency-closed imported certificate; no size bound or abstraction of that leaf is proved here.

The inverse A takes precisely these operands, applies Data-Name and Code-Result twice, applies Carrier-Delay to the same q_x, rebuilds Check_c from the original fields and shared references, then applies Code-Call at the original Application origin. This constructs no new source root or program occurrence. Direct substitution of the displayed terms yields

```text
A(L(q)) = q
L(A(l)) = l                 for l in the image of L.
```

These equalities concern the exhibited constructor expression and its retained payload, not pointer identity of a proof allocation or equality of an unspecified opaque evidence family. They use neither proof irrelevance nor uniqueness of arbitrary source formation. Each leaf witness is copied unchanged. The second equality is restricted to the image: an arbitrary same-shaped record need not possess genuine origin evidence or the required sharing.

By the source-input §4 whole-substitution induction,

```text
L(theta q) = theta L(q)
A(theta l) = theta A(l).
```

This is a bounded syntactic naturality derivation for supplied lawful source substitutions. Event restriction on hereditary world evidence or opaque primitive evidence is not proved by this equation. IF construction §3.3 gives corresponding forward/back projections for a *retained contextual slot*: injection retains the complete operand/evidence fields and projection recovers those same fields. It does not recover an operand discarded from that slot.

This is the genuine lossless control: formation information suffices to rebuild its local introduction. Replacing q with L(q) and rebuilding q at use still retains its full local formation content. It does not discharge the approved transformed-export objective or the semantic Early factor law.

## 4. Selected early evidence predicates and consumers

The selected documents expose the following consumers; none explicitly exposes a readout of allocation identity or a proof-irrelevance rule.

| Original field/consumer | Actual selected clause and supported action | Missing abstraction action |
| --- | --- | --- |
| Name formation | Source-input §3.1: Data-Name takes `(b,edge)` from the actual Name resolution; closure proof §4.1 uses original read edge and current binding projection | The sources do not identify the original edge evidence family/actions with a record containing only the composed substitution and typed path conclusions; a resolved endpoint alone is insufficient |
| Return/prefix witness | Closure proof §4.1: ME-Result takes the data-constructor witness and raw Return/prefix rule; early prefixes retain code/capture/world incidence | The rule constructs evidence from the retained source witness; it supplies no elimination of that witness from the evidence family |
| Ordered suspended suffix | Closure proof §4.2: Bind retains first/second source derivations and actual dependent result/rebind; initial prefixes retain actual phase and unreached dependent suffix | Replacing a suspended source derivation by only its interface requires its original evidence interpretation/action law |
| Pre-Return Call witness | Closure proof §4.3: stored Call formation and unassembled suffix; IF construction §4 inserts original source derivations at callee/argument slots | IF slot projection recovers the retained operand, not a new source derivation from an output telescope |
| Same-root read obligation | ReadInvoke §3 and contextual membership definition §3 retain original binding/capture certificates; actual world restriction uses the same joint certificate | Abstracting certificate internals requires a lawful binding-evidence map at all compatible later events |
| Checked descriptor/guards | ReadInvoke §§3–5: complete original constraints, paths, guard schemas, fixed D_c and suspended obligations | Shapes, incidence and record reconstruction establish no semantic truth or primitive evidence action |
| Constrained-source judgment | Source-contracts §2.2 keeps `M_E` independent of `DescMem`; §3.5 translates finite source-base derivations under its typing/transport hypotheses | No clause identifies raw source proof evidence with the fact certificate, or manufactures `M_E` from `DescMem` |
| Query evidence | Source-contracts §5.3 requires original identifiers, operands/scope and fixed non-child source paths; constructor congruence preserves those operands | The conditional calculus has no rule deleting formation evidence by shape equality or successful comparison |

Thus the forward field map is explicit: read the current phase/world/binding projections, the contextual IF/Bind fields, the suspended interfaces and original guard evidence from the retained source/early witness. On constructor-introduced evidence this is the factual map already enumerated by prefix projection §4. Its typed leaf/origin component can be L(q) if lossless retention is allowed. It does not assert a backward map from the smaller b_pre.

If q is retained as an external parameter, one can reinsert that same q and reuse the original introductions. This is a **q-dependent reintroduction**, not source-free use. If L(q) is retained, A supplies the same exhibited constructor payload; this remains lossless reconstruction. Neither route is the missing semantic abstraction.

## 5. Exact missing law and omission frontier

Let Early(q,e,O,w) name the selected initial/lookup evidence family, and b denote the preceding audit's fact projection. A useful source-free map must supply an actual evidence family K(b,e,O,w) and lawful maps

```text
F_q : Early(q,e,O,w) -> K(pi_fact(q),e,O,w)
B_q : K(pi_fact(q),e,O,w) -> Early(q,e,O,w)
```

whose implementation uses only the exported certificate and current independent inputs. B_q must not retrieve q from the original definition, retain it under an opaque atom, or choose another convenient M_E/source witness. The maps preserve every original evidence projection demanded by later consumers, and commute with supplied whole actions and compatible-event restrictions. Any proposed round-trip equality must state which original evidence equality is meant; none is inferred from mere proposition equivalence. This is a candidate theorem obligation, not a new definition of Early or M_E.

The selected ReadInvoke §3 requirement to retain original formation is explicit. Its **evidence elimination signature, introduction law from reduced operands, equality law and restriction action on that field are not specified completely**. The consumer inventory exposes uses of stored formation; it does not show that all its possible required evidence actions reduce to b_pre. This is the precise blocker. A complete selected elimination law would permit a proof; the absence of that law is not proof that abstraction is impossible.

Concrete omissions to test at the owning construction:

1. **Original Name edge evidence.** Preserve actual binding/root, typed use/path, composed substitution, capture/dependency sharing and source tag. If those fields are exactly the original `(b,edge)` payload with its actions, no reconstruction premise remains for this leaf. If they retain only its conclusions, prove the original Data-Name/ME evidence and restrictions are recoverable through them. The table for b_pre does not specify that evidence equality. No omission of an entire resolution proof tree is inferred: that tree is not explicitly a Data-Name payload field.
2. **Duplicate q_f/q_x/t references and local constructor nesting.** L already removes redundant nesting syntactically while retaining all original leaves. Further elimination of those leaf formation witnesses requires the retained-formation consumer law; reconstruction from L alone provides no information-necessity result.
3. **Application/Reify/Result/checking origin proof interiors.** Retain the real origins, licenses, complete result/checked interfaces, emitted constraints and source incidences. A metadata ID or semantic truth cannot replace their proof inputs without the owning origin-evidence action law. Source-interface §2 explicitly leaves semantic validity independent.
4. **Suspended-source evidence behind interface fields.** Preserve complete dependent Bind/receiver/result/future schemas and their original maps, guards and alternatives. Omit the stored source derivation only if its future evidence uses factor through those schemas. Interface allocation alone proves no such law.

These are evidence omission candidates, not demonstrated differences between two fully specified record types, and not permission to delete original paths, scopes, root identity, licenses, constraints, provider correlations or any independent W/Z evidence. Necessity of retaining proof interiors has not been demonstrated. No source pair distinguishes them under the selected consumer semantics. Conversely the existing lossless map does not justify omitting them. If b_pre is interpreted as retaining every original payload and action listed in L, local reconstruction may already apply; that interpretation would establish lossless retention, rather than prove a smaller sufficient export.

## 6. Coverage, independence, resources and next action

Claim class: bounded constructor-record derivation, supported factual projection and an exact unresolved semantic premise. The full evidence equivalence, transformed export, generalization/instantiation, principality and production conformance remain unproved. Only the fixed two-Name structural early branch is audited. Effectful/computed callees, whole-Call W/Z observations, arbitrary formation evidence, recursion, independent transitive leaf presentation and later receiver/carrier/result cases receive no closure. Original alternatives remain complete and separate; no challenge-domain restriction or language meaning is selected.

Oracle independence: none. The derivation uses the selected constructor grammar and independent interface/action contracts; it is a source correspondence argument, not independent operational validation. A checker encoding A and L would establish constructor consistency under that same grammar and would not prove the retained-formation consumer law. No executable experiment, seed/range enumeration or mutation was run. No third toy probe was attempted: the untouched premise is the actual evidence elimination/reintroduction law.

Failure conditions: any missing original leaf/origin payload or changed sharing defeats A; extra opaque proof decoration needs its own retained field; absence of a lawful semantic/event action prevents promoting syntactic naturality to semantic naturality. Invalid live guards, bindings, carrier admission or primitive alternatives cannot be repaired by q reconstruction.

Checks: pinned `git show` reads, SHA-256 and live-byte equality for every direct dependency, scoped whitespace and local Markdown-link integrity checks. These are documentary checks; no compiler tests/builds or Git mutation ran. Some initial combined captures were truncated; the relevant constructor and governing sections were reread narrowly. No exhaustive repository-wide consumer inventory is claimed. Only sequential lightweight processes were used. CPU/RSS and numerical wall-time were not measured; the assignment supplied no numerical budget. There were no heavyweight processes or additional outputs.

Recommended next action: specify or locate the existing retained-formation field's complete elimination/reintroduction and lawful event-action signature, starting with original Name use-to-binding evidence versus its composed binding map. Then derive the semantic maps from that exact signature. Review this frozen note independently before promoting any result; another prefix transition experiment will not establish that premise.

## 7. Dependency snapshot and commit packet

All direct semantic inputs below matched pinned baseline bytes at capture and final verification. No dependency hash changed. Historical baselines/hashes embedded in those inputs are not substituted for this snapshot.

| Input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-08-pure-read-prefix-projection-audit.md` | `a629637bbae12a15e8d363d9f09f37cba05e7f2b290683aa782975f9b0d88ba9` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-08-readinvoke-early-evidence-maps.md` only.
- Baseline SHA: `85d59a99389647d8eb9f4e4cf16e5897bc57df7e`.
- Changed dependency hashes: none; final frozen artifact SHA-256 supplied in the handoff.
- Review status: producer-only research derivation; no independent review, semantic projection closure, representation adoption or production authority.
- Checks already run: pinned dependency/live-byte SHA-256 verification; scoped whitespace and relative-link checks. No tests/builds, executable probe or Git mutation.
- Proposed one-line research-checkpoint message: `research: derive ReadInvoke early formation record maps`.
- Shared-record deltas left to primary/curator: record the lossless local constructor control and exact unresolved retained-formation consumer/action law; do not close the public-export/H-factor gate or select the record as export. Task/index/authority/theory-map/question files remain untouched.

The producer stops writing before submitting this artifact for frozen review.
