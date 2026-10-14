# Source Call interface elaboration: bounded native construction packet

- Date: 2026-10-15
- Status: independently reviewed non-authoritative representation proposal; no compiler implementation authority
- Parent: original admitted shallow-Catch callback protection and residual-effect goal
- Baseline: `cb216f7e8e60b3839ac6756308acd021bbd146c8`
- Review budget: M2, one `compiler_referee` and one `spec_auditor`
- Implementation / default-route / source-acceptance / cutover authority: none

## 1. Purpose and exact boundary

H1-G's independently reviewed correspondence pair localizes the first missing
edge: an authentic HIR `Apply` plus its jointly constructed native Function4
demand does not produce an authentic complete original `Gen-Call-0`,
`FrameCall`, or `Q_e` interpretation. The source Call semantics is already
selected by `OC-CallEff`, `J_call`/`ExecuteCallable`, `FrameCall`,
`C-Inv`/`C-Call`, `InvMem` and `CallMem`. This packet does not choose those
semantics again.

The proposed construction starts at actual source declaration/operator
elaboration and ends at one source-owned Apply record linked to those complete
interfaces and to the existing native constraint fields. It supplies static
source correspondence only. It does not prove source admission, complete C0,
constraint satisfiability, execution, typed Receive/Observe, expiry, hygiene,
soundness, principality or production cutover.

The proposed implementation owner is the existing source elaboration and
constraint collection boundary (`candidate_source` plus the owning
registration/operator constructors), before solving. It reuses the reviewed
finite dependent-interface graph direction in
`2026-10-10-practical-complete-call-production-gate.md`; it does not introduce
a parallel semantic engine or recover complete contracts after solving.

## 2. Proposed retained graph

Retain one unpublished, source-component graph with three distinct node kinds:

1. **Contract node.** An original source declaration/operator reference, its
   complete declared dependent telescope, original alternatives, source
   binders and scope. A formal registration owns one shared contract root;
   source Name/capture occurrences point to that root through separate scoped
   use edges. Equal solved endpoints do not merge declarations or uses.
2. **Call node.** One actual Apply occurrence, its callee and whole argument
   source children, their independently generated type/effect variables, the
   referenced callee contract, and the complete original Call index and frame
   edges. The Call node retains an open whole-carrier slot; it does not replace
   that slot with the source argument's diagonal.
3. **Native-field map.** A typed map from that same Call node to the exact
   existing native recipe and Function4 fields, invocation row and application
   effect. This map records source correspondence; equality of terms or
   `RelationId`s alone is not the correspondence proof.

All dependent fields, references, alternatives, scope inclusions and native
field links are interpreted by one component assignment `sigma`. Fresh type
variables may remain symbolic while this graph is built. A lawful substitution
acts on the whole graph and its edges in one operation; the implementation may
not choose separate witnesses for argument, invocation, result, receiver or
future fields.

### 2.1 Original index and producer map

The complete source index remains the one selected in the source formation
definition:

```text
Idx(e) = (B, X, xi, Delta_e;
          d_f, A_f, R_f, u_f, u_x, c, u, U_e, beta, p0, p_out(c), ElimOrigin)
xi = (nu, K, D)                  beta = (d_f, R_f)
```

The table identifies the construction obligation for each group of fields.
“Present prefix” describes existing retained facts, not a completed original
semantic interpretation.

| Original field(s) | Present source/native owner | Proposed graph construction |
|---|---|---|
| `B`, `X`, `xi=(nu,K,D)` | HIR artifact/occurrence identities and private solver batch/session | Keep a source-component key and one joint assignment/scope object. The bridge from that object to the complete original environment, world and evidence indices remains an explicit proof obligation. |
| `Delta_e` | `LocalSourceExpr.scope`, binding/formal scopes and generation levels | Retain the actual binder telescope and scope inclusions on the graph edges; a numeric level alone is not the original dependent context. |
| `d_f`, `A_f` | Resolved `Parameter(HirParameterId)`, `FormalRegistrationInput`, parameter recipe and native Value root | Attach the actual declaration and typed root to one Contract node. Do not infer its declaration interface from the Value row. |
| `R_f`, `beta=(d_f,R_f)` | Candidate registration/root identity only | Retain an original inferred-contract-root reference and its typed interpretation at registration. No current native producer supplies this reference. |
| `u_f`, `u_x`, `c` | Actual LocalSource child indices, source occurrences, resolved Name/capture route | Retain separate lexical use, callee/argument child and Call occurrence edges, each with its owning scope and typed derivation. Arguments may be arbitrary expressions. |
| `u` | `ApplySourceInput.checking` and `cause` | Preserve this authentic constraint provenance while separately constructing the original checking exposure/seed derivation. |
| `U_e=F_c`, `demand` | Native negative Function4 demand from `shadow_apply` | Link all four actual native fields together to the Call node. Establish their original complete descriptor interpretation separately; the native demand is not that interpretation by itself. |
| `p0` | No original producer in this path | Construct from the authentic registration/demand root with the selected dependent interpretation, or keep the graph incomplete and stop. |
| `p_out(c)`, `ElimOrigin` | Native invocation ResultEffect and application effect rows | Retain distinct typed invocation-output address and elimination-origin edge. Do not identify either with an effect row or a raw continuation suffix. |
| Frame callee | Actual callee subtree, native callee Value and evaluation effect | Retain the whole callee computation/result/provider telescope and its interface reference. |
| Frame argument | Actual whole argument subtree, native argument Value and evaluation effect | Retain original Reify/Delay/capture interface plus the independently fillable whole-carrier hole. |
| Frame receiver | Native Function demand only | Retain the callee-result-dependent actual provider, current configuration, entry role, receipt/Force/rebind/body/consumer sequence, and both pending-suffix cases under the same `sigma`. These are not supplied by the current native demand. |
| Frame return/future | Native result Value term | Retain actual result/current state, dependent latent/future interfaces and alternative-provider contracts. A result term is not the future interface. |
| Frame arms/source diagram, `Q_e` | Source syntax and operation declaration identities | Retain authentic declaration insertion/reference-use edges and the complete original operation reference. Do not assert clause membership, C0, or a complete joint witness until independently constructed. |

## 3. Construction order and invariants

1. Source registration constructs the actual declaration Contract node before
   uses are consumed. Each Name/capture occurrence adds a scoped use edge to
   that node; it does not copy the interface into unrelated scalar endpoints.
2. Source operators and Apply collection construct their child source nodes,
   fresh type variables, levels, scope edges and constraint provenance before
   solving. Conditional branches contribute their constraints without
   evaluating conditions first. No constant-folding, branch selection or
   whole-type solving is a prerequisite for this graph.
3. Reify/capture construction retains the whole argument contract and an
   independently fillable carrier hole. It does not assert that the only
   carrier is the source expression's own value.
4. Apply collection creates one Call node and links it to the existing native
   recipe. Function4's Argument, ArgumentEffect, ResultEffect and Result fields
   remain their actual native fields with their actual variance. The
   invocation row, callee evaluation row and application effect remain
   separate coordinates with their existing inclusion constraints.
5. Propagation, extrusion, copying and fresh use must transport the whole
   graph under the already authorized scoped assignment. This packet defines
   no new extrusion/intrusion behavior and claims no preservation theorem;
   H2 remains its own gate.
6. A later execution/evidence owner may connect this static graph to an actual
   receiving Call, immutable historical receiver, matching typed path,
   Receive/Observe, current roots and expiry. No HIR ID, Function4 port,
   `RelationId`, shared pointer or candidate context is an execution receipt.

The first prototype should stop at the first absent original field and expose
it as an internal incomplete-construction result. It must not turn that
missing supplier into a user source error, a guessed semantic witness, or a
partial public export. Existing accepted paths continue to use their current
behavior until a separate cutover gate authorizes otherwise.

## 4. Relation to existing authority and prior proposal

This proposal instantiates a compiler-side correspondence seam for the
reviewed source constructors and finite dependent-interface graph. Its source
meaning is supplied only by the indexed Authoritative definitions in
`notes/design/INDEX.md`, including:

- Original Call formation: `notes/design/2026-10-07-original-call-formation-definition.md`
  §§2–4.
- Complete Call contributions: `notes/design/2026-10-07-complete-call-contribution-definition.md`
  §§2–4.
- Complete source interfaces and Theorem IF:
  `notes/design/2026-10-08-call-source-interface-definition.md` §§2–4 and
  `notes/theory/2026-10-08-call-source-interface-construction.md` §§2–5.
- Joint inference ordering and abnormal-path requirements:
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1,
  1.1, 3–4.

The practical Call graph proposal from 2026-10-10 is a reviewed, conditional,
non-authoritative representation proposal. This packet narrows its first
construction seam to original source registration/operator formation and one
Apply record. Neither document authorizes implementation or production
behavior. Any mismatch with an Authoritative definition returns to review; it
does not change that definition.

## 5. Deliberate exclusions and failure checks

- No source behavior, Call rule, callback role, effect position, receiver
  transition or lifecycle policy is reopened or newly selected.
- No complete Call, C0, `Q_e` membership, source admission, provider execution,
  typed receipt, event observation, current-root or expiry conclusion is
  certified by merely constructing the graph.
- No full H1/H2/U theorem, soundness, principality, generic rigid opening,
  public API or F5/production cutover is closed.
- Do not reconstruct the record from solved endpoints, an `Apply`/Lambda ID,
  a row key, or the C_in/C_cb pair. C_in (receiving the provider) and C_cb
  (calling the formal) retain distinct source Call nodes.
- Do not collapse actual provider-dependent output/future fields, the
  callee-pending and post-receipt receiver-pending suffixes, or original
  alternatives into scalar effects or a single chosen witness.
- Do not let a static `ContextExpr` or assumed typed-evidence adapter masquerade
  as the later operational consumer.

The smallest falsifier is an original admitted complete Call tuple under one
`sigma` for which a proposed graph image changes, loses, or independently
chooses a dependent field, scope edge, carrier hole, original alternative,
provider, ordered suffix, or typed evidence edge. No such source-qualified
counterexample is claimed in this packet.

## 6. Approval and next gate

The immediate question after independent review is whether to use this bounded
graph-construction owner as the basis for a reversible playground prototype.
The proposed first implementation would retain and inspect the source-side
Call node only; it would not switch production inference or claim complete
Call construction. If approved, the first code lease must separately name the
owned Rust files, one focused source-to-field invariant, failure behavior,
smallest verification, and rollback boundary. New durable graph representation
or production routing still requires its own approval and proof gates.

Alternatives for the primary decision:

1. Approve the bounded source-registration/operator-to-Apply graph slice for
   a private playground prototype under the exclusions above.
2. Keep the existing reviewed graph proposal as reference and choose a
   different construction owner; name that owner and the behavior-preserving
   source evidence it must retain.
3. Defer this representation decision; H1/H2/U remain open and no dependent
   implementation starts.

Regardless of choice, H1/H2/U remain OPEN and H3/P remain disabled until their
separate source, consumer, proof and review obligations close.

## 7. Evidence and review status

Source/consumer evidence is limited to the independently reviewed H1-G pair:
`notes/theory/2026-10-15-call-native-correspondence-construction.md` and
`notes/progress/2026-10-15-call-native-correspondence-falsifier.md`. The
read-only `architect` owner map additionally located the first missing
interface at `FormalRegistrationInput` and at non-formal source/operator
interface formation. A fresh M2 `compiler_referee` reviewed dependent graph
structure, source correspondence and lifecycle boundaries; it found no
blocking, major or minor findings. A fresh M2 `spec_auditor` reviewed the
selected-contract scope and approval boundary; it also found no blocking,
major or minor findings. Neither review certifies implementation correctness,
source admission, execution, transport, lifecycle, complete Call or cutover.
No tests, builds, probes or measurements were run.
