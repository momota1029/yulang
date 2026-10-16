# First Apply: source elimination stops before native Function predicates

Date: 2026-10-16. Author: `/root/astra_first_apply`; no coauthors or descendants.
Status: UNREVIEWED source/native owner audit and exact proof obstruction.
No parent theorem proved or refuted; no production authority.

Sprint `first-apply-owner-elimination-20261016`, revision 2:
`tasks/agent-loop/sprints/first-apply-owner-elimination-20261016-amendment-1.json`,
SHA-256 `8ff567e9584bc51fc4b06da3e806fe3541000b119aba24ab062766db9e226a20`.
Original revision 1 SHA-256:
`9b5fe6ab1bf847bcc4b93d1b43c013b9e2b337e4894022992597b1c3b5eebb5b`.
Baseline supplied by Luna: `eeb7826a238848d219058f4f14e0948c115ae6ac`.
Luna acknowledged the three additional direct dependency pins before this write.

## 1. Parent and precise outcome

FIRST-RESULT-ADEQUACY keeps the original source:

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

For every original `xi=(nu,K,D)` and every complete first-Call return witness
`z`, retain the same provider, captures, scopes/binders, whole Unit carrier,
entry/current configuration, pending Bind/future obligations and both tagged
images `M_W* W_z union_tagged M_res* F_R,z`. The required implication starts
with the original source obligations at those coordinates, not with native
constraints or successful comparison. Fresh implementation storage cannot
change any of those original coordinates.

**Outcome:** none of the inspected governing source owners supplies an
independently selected elimination from that original coupled obligation to
all four actual native contextual predicates. This is a bounded authority and
source audit, not a global nonexistence theorem. The exact missing input is the
interpretation/elimination of the original Apply/Check obligation as a selected
abstract constraint judgment, with the original source-to-native coordinate
map and the native parent-context actions below. The semantic membership
eliminator does exist, but its conclusion is acceptance and complete observation
safety of the same provider; it is not the four-child native judgment.

Applied to the parent, the previously reviewed source prefix still constructs
the same first result and its two tagged packet images. The induction still
stops at first Apply. This audit rules out treating the currently inspected
membership, CallMem, IF, callback-B or typed-core containment clauses as an
already supplied native elimination. It does not reduce the original quantifiers
or claim that this repeated premise has become a new conditional theorem.

## 2. Source-owner elimination audit

| Exact source owner | Available elimination/consequence | Missing conclusion |
| --- | --- | --- |
| Original Call formation §§3–4, OSig-Demand / OC-CallEff | Original complete invocation root and typed occurrence at the retained dependent tuple | Native predicates or complete execution/admission evidence |
| Contextual Function membership §2 | Given the independently admitted checked challenge and same actual decomposition, actual-provider acceptance; every complete/pending observation and admitted future satisfies the descriptor contract | Compilation/reflection into native component predicates and their contexts |
| Complete Call contribution §2, CallMem | Exact original whole-operation witness at the same fiber; structural and independent W/Z alternatives retain their own contracts | C0 or native Function-child satisfaction |
| Source Call interface §§2–4, IF-Insert / IF-Use | Actual declaration/reference placements and full static interface graph on its constructor envelope | Operator typing, witness actions, dispatch/phase validity, contextual world binding |
| Typed computation core §6 Apply | Computation(E_call,A_call), original callee/whole-carrier constraints, complete invocation relation, source entry/result-consumer skeleton | A four-port abstract constraint rule with contextual predicate interpretation |
| Typed computation core §7 Check | VIncl/CIncl semantic inclusion under one assignment; proof-label erasure retains those premises | Effective sound/principal inclusion presentation, explicitly still open there |
| Typed computation core §9 ExecuteCallable / joint containment | Complete actual entry/body/designated-consumer image; sufficient joint domain/observation containment | Converse structural completeness or native child elimination |
| Callback context delivery §§2–2.1, B | Independently synthesize literal endpoints; generate one completed-interface inequality | Port rule: §2 expressly leaves it an obligation rather than defining one |

The typed-core document is Draft, with reviewed conditional constructions and
selected source premises. The membership authority explicitly declines to adopt
its open checking/descriptor/implementation choices wholesale. Reading that
Draft does not select a new solver semantics. Callback delivery is Authoritative
within its bounded source case, with no compiler implementation authority; the
existing-value case preserves actual introduction and entry. It cannot replace
the original arbitrary provider by a new callback literal.

The inference principles §1.1 do select ordinary source-generated constraints
and subsequent Simple-sub propagation/extrusion/intrusion. They do not state the
missing contextual Function elimination. This result is no reason to delay
generation until execution, comparison success, or concrete solution discovery.

## 3. Actual native construction and retained context

The inspected code establishes emitted objects and control flow, not semantic
satisfaction of the original source relation:

1. `candidate_source.rs:980` handles the actual `LocalSourceForm::Apply`.
   At lines 1011 and 1040 it retains `CandidateRelation::Apply` and
   `ApplySourceInput`: source owner/expression, callee and argument identities,
   level, effect/result coordinates, checking occurrence and cause, formal-name
   registration and optional receiver attachment. This is a source input, not
   a complete Call certificate.
2. `shadow_apply::admit_candidate_fact` at lines 1560–1660 validates the recipe
   against that input. In the graph-effects route it allocates an invocation
   effect row at the application row's level and constructs
   `D1- = Fun-(u+,d+,i-,r-)`. It records `NativeInterface` before admitting the
   constraint. Its later effect edges retain both callee-to-application and
   invocation-to-application dependencies (lines 1696 onward).
3. `InferenceSession::dispatch_live_item`, `lib.rs:12644`, reads actual positive
   and negative Function children and selects exactly the four pairs below.
   `candidate_step_function_dispatch` (`lib.rs:12796`) calls
   `candidate_function_port_admit` before enqueueing each child.
4. `candidate_context::candidate_function_port_admit` (line 3001) retains the
   processing parent, field, operation, source set and scoped flow. It uses
   `post_check_context(parent)` (line 2799): an already discharged parent uses
   its retained discharge residual, otherwise the original context. It does
   not assume discharge. A nonidentity child-local PrefixLeft wraps the
   inherited context in source order. When scoped demand is present, it
   checks that the original upper is that demand's actual root, clears the
   child's demand, and applies the field-specific scope transformer.
5. `candidate_call::observe` (line 437) checks source ownership, incidence,
   scopes, native demand fields/polarities and registration consistency. It
   reads a retained artifact; it does not prove original Call satisfaction.

Write `H=post_check_context(parent)`, and `L` for the permitted child-local
prefix. The following table gives construction facts. It asserts no semantic
equivalence between a row pair and the complete contextual predicate.

| Field | Native pair for the first annotated Call | Inherited context | Scoped-demand action, when present |
| --- | --- | --- | --- |
| Argument | `u+ <: Unit-` | `L(Swap(H))`, with identity handled by code | clear demand; transformer 0 |
| ArgumentEffect | `d+ <: e_A-` | `L(Swap(H))` | `stamp_input(demand.input)` |
| ResultEffect | `e_R+ <: i-` | `L(H)` | `protect_body(demand.output_scope,demand.input)` |
| Result | `a+ <: r-` | `L(H)` | clear demand; transformer 0 |

The table is conditional on this actual positive annotated Function and its
actual first demand reaching Function dispatch. It does not assert that every
source witness reaches that code branch, nor success of a child. Without scoped
demand the existing scoped flow is retained instead of inventing these actions.
Argument/ArgumentEffect swap the inherited context; ResultEffect/Result preserve
it. Neither operation permits replacing the context by identity or identifying
residual, provider and witness lineages. This identifies a stronger concrete
proof target than the uncontextualized four inequalities alone.

## 4. Apply each available source consequence to each child

**Argument.** Source literal/Name construction and original whole-carrier
admission supply the same Unit carrier at the same receiver. At the erased
value endpoints, Unit inclusion is unproblematic. The original membership
eliminator supplies actual receiver acceptance for the independently admitted
challenge. Neither fact derives the full child under `L(Swap(H))`, its original
incidence and scoped flow. The source checking interpretation must supply that
bridge; a bare Unit reflexivity calculation cannot remove the parent context.

**ArgumentEffect.** The original Unit carrier has the source empty evaluation
effect. The erased empty-support inclusion cannot establish a contextual
native predicate with the actual swapped residual and input stamping. Empty
support does not prove a receipt, live boundary, provider acceptance or the
pending continuation contract. Those remain the original joint conditions.

**ResultEffect.** ExecuteCallable includes actual entry, body and designated
result consumer, including an operation's post-native-return request execution.
Membership bounds those complete observations. A bound on observed execution
is not automatically the native annotation-port-to-invocation-port predicate
under `protect_body` and `L(H)`. The first result `E1` and original predicates
are fixed; choosing `i=e_R` to make a row inequality reflexive is not a universal
translation at those coordinates. The callee/application effect edges likewise
remain distinct and are not an ordered-Bind theorem.

**Result.** The original source construction retains the endpoint obligation
relating the first result `A1` to the original annotation `alpha`; it also
retains the exact returned provider and both tagged images. That obligation
cannot be silently identified with `a+ <: r-` under `L(H)` before its
interpretation is supplied. Giving the original returned value membership
in both interfaces is weaker than inclusion of every value represented by
the positive annotation port. Rebinding/name identity preserves the witness;
it does not manufacture the missing inclusion.

A simple logical separator explains why the semantic route alone cannot fill
this last step: `O={v}`, `A={v,w}`, `R={v}` satisfies `O subset A` and
`O subset R`, but not `A subset R`. Here `O` represents observations of one
actual provider and `A,R` are possible bounds. This is only a countermodel to
the attempted inference from observation membership to bound inclusion. It is
**not** a source-qualified counterexample: no claim is made that these sets
satisfy the original alpha/A1 constraint, K/D, admission, z or native context.
Thus it rejects a proof method without refuting FIRST-RESULT-ADEQUACY.

Two routes have now left the same premise intact: semantic elimination gives
acceptance/observation containment; constructor inspection gives native pairs
and contexts. Their missing connection cannot be supplied by repeating either
route or by defining each child to mean the whole original premise.

## 5. Reuse, exclusions and next owner

Reuse the reviewed first-result source-judgment prefix at its pinned hash:
annotation target exposure, Name identity, Unit formation, original complete
first-return packet construction, Bind and same-g transport. Reuse the prior
core/source-attack native direction trace as static evidence. The local View
construction remains conditional on its original decorated-kernel premises;
it supplies no first-Apply predicate interpretation and no opaque continuation
application law. No earlier proof is broadened or independently recertified.

Rejected routes: adding native children to the original antecedent; assuming
comparison success; convenient reassignment of original r/i coordinates;
replacing complete Call by closure body or operation native return; replacing
joint observation contracts by independent rows; importing a stronger allocation
certificate; restoring withdrawn generation-time admission or source-shape
bypasses. No tested assumed transition is used as constructor evidence.

**TODO FA-ELIM-OWNER-1, Luna / original Apply-Check authority owner.** Supply the
independently governing selected abstract judgment and its interpretation for
this original Apply obligation, or adjudicate that it is not currently supplied.
Required inputs: the original source derivation and complete obligation,
fixed xi/z/provider/whole Unit carrier, source-to-native coordinate map and
all four actual contextual children in §3. Required output: an independently
reviewable elimination at those indices covering retained source constraints,
contexts and scope actions, without adding child satisfaction as a premise.
Falsifier: one original admitted xi/z satisfying the original obligations,
with the same two packet images and parent context, for which an identified
actual child predicate fails. The schematic separator above does not meet it.
New semantic selection or a newly introduced dependency returns to Luna.

**TODO FA-NATIVE-1, Luna implementation owner, contingent on FA-ELIM-OWNER-1.**
Use the existing retained `ApplySourceInput` / `NativeInterface` /
`FunctionPort` owner chain to check any supplied rule. No new metadata or
production edit is justified by this audit. If a subsequent implementation
packet is needed, its minimal falsifier must compare the rule's four predicates
against the actual pair/context/scoped-flow outputs for that same source
occurrence, including nonidentity residual and scoped-demand cases. A test of
manually assumed transitions is insufficient. This TODO grants no write lease.

The remaining same-provider source-result interpretation, complete W/Z arms,
response/pending cases and opaque foreign continuation contracts remain visible.
F1-FULL, FK1-FOREIGN, FIRST-RESULT-ADEQUACY in both required directions,
IMPLEMENTATION-E2E and production cutover remain OPEN. The next step changes
input/owner to FA-ELIM-OWNER-1; another identical conditional lemma is not planned.
The exact-missing-premise stop condition is reached.

## 6. Frozen inputs, resources and writer receipt

All 17 direct dependency hashes are the exact manifest in the frozen revision-2
contract above; every value was checked by SHA-256 against current bytes. The
14 revision-1 dependency pins and three added pins match. The contract's own
hash and its base hash were also checked. These are snapshot checks, not tests
of semantics. No dependency was changed by this worker.

Direct source additions explicitly authorized by Luna:

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |

Four substantive stages: source authority/eliminator audit; native construction
and context audit; per-field implication attempt and logical separator; parent
application and frozen handoff. Budget: at most 900 active seconds / 6 stages;
zero heavy processes and zero lightweight probes. Only static text/hash reads
and the two leased artifact writes. No tests/builds, Git, network, compiler or
shared-record edits, nested CLI or delegation. CPU/RAM and exact active time
are uninstrumented; handoff records a conservative elapsed accounting bound.

Requested role/model/effort: astra_prover / gpt-6-astra / medium. Observed
model/effort: UNKNOWN; role request is not runtime metadata. Worker identity:
`/root/astra_first_apply`; current session identifier UNKNOWN. The delivered
NEW_TASK and this work are the active receipt. Author is this worker alone.

All new paths: this note and
`tasks/agent-loop/inbox/20261016-first-apply-owner-elimination.md`.
No scratch paths. Artifact bytes freeze at handoff; writes stop after creating
that one handoff. No descendants or unresolved descendant leases. Fresh
independent review and Luna adjudication remain pending; the author certifies
neither theorem nor production readiness.
