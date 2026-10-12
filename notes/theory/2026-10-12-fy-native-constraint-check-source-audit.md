# Application c: native constraints and finite-checking evidence audit

Date: 2026-10-12
Status: frozen, unreviewed bounded source/implementation characterization
Baseline: `d61a66ed02c22aaa454d8b864dc68a4db7eb6aac`, branch `research/simple-sub-intrusion`
Producer: leaf `/root/fy_native_constraint_check_source_audit`
Exclusive lease: this file only
Budget: one static read/derivation pass, at most 25 minutes; no measurements,
tests, builds, inference runs, implementation writes or delegation
Parent L3-at-c, L4, complete Call and inference gates: OPEN

## 1. Objective, authority and hypotheses

Trace the exact carrier Apply 13, `f y`, from the established
[two-use source bridge](2026-10-12-two-use-exact-source-bridge.md) §§3–5 into
native constraint production, retained metadata and immediate consumers.
Classify which outputs can supply the original finite checking tree and
where the first missing source/semantic premise remains. This complements
the constructive checking proof; it does not repeat parser/binder derivation
or construct another recursive coalgebra.

The source bridge supplies the unchanged 116-byte source, its original
resolved graph, and Apply slots 13/8/6/4 at levels 3/3/3/2. Slot 13 has
callee 14, recursive local f/0; argument 15, parameter y/1; owner Q; and
scope E(7). Slot 12 is a distinct Group facade, used as the argument of
Apply 8. Those facts are inputs here. They are not inferred from a printed
type or a new successful query.

Governing sources are the selected [Source Generalize definition](../design/2026-10-08-source-generalize-definition.md)
§§2–3 and [construction](2026-10-08-source-generalize-definition-and-proof.md)
§§2,3.1–3.3,4–5; [contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md)
§§2–3; [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [Application c obligation](2026-10-12-application-c-finite-check-proof.md)
§§1–6; and [postfixedness obstruction](2026-10-12-nested-recursive-f-postfixedness-proof.md)
§6. No selected meaning is changed.

**Claim class:** bounded static source/implementation characterization and
conditional native constructor derivation. Hypotheses: the supplied carrier
and feature route are the bridge's authentic artifacts; native collection
and each named admission action complete with normal finite identity and
allocation availability. A conditional Function decomposition additionally
requires that the actual work item reaches a positive/negative Function
pair. No hypothesis assumes source admission, f membership, D, P or L4.

Keep the original semantic problem unchanged: original A_f and actual
`Act(v_f,U_f,r_f)`; actual entry interface I_x; independently selected
complete demand F_c; whole Name-y carrier J_y; original `xi`, worlds,
incidences, scopes and event e. The required tree k_c concludes

```text
D: d in D_F_c(e) -> the same complete d in D_A_f(e)
P: o in P_A_f[S](d) -> the same decorated o in P_F_c[S](d).
```

D is independent of S. P needs its genuine children at S. Every independently
admitted checked challenge and retained actual decomposition remains covered,
including open carriers, zero-step/pending observations and compatible finite
future developments. The entry receipt/path/context guards and hard envelope
remain required. J_y, y's native value row, A_y and I_x are distinct objects.

## 2. Exact native producer derivation

Use `V_i`/`E_i` for the value/effect component of source slot i and `Y` for
y's parameter recipe row. Superscripts +/− denote native polarized terms,
not semantic membership certificates. Native row ordinals can canonicalize
or be copied; these names identify constructor operands before that transport.

1. `candidate_source.rs:168–246` allocates expression components, parameter
   recipes and lexical formal registrations. Parameter Name 15's endpoint
   is `Parameter(y)`; its expression component is not substituted for Y.
   Name 14's endpoint is its own component V_14.
2. `candidate_source.rs:300–305,373–389` resolves active recursive f to its
   still-forming initializer endpoint V_2. Name 14 emits `Action::Link`;
   `execute_candidate_action` at 665–669 calls
   `candidate_scheme.rs:1337–1343::admit_candidate_value_link`, with local
   constraint slot 30. Thus the actual native constraint is `V_2+ <: V_14−`.
   Each Name also emits its own evaluation-effect bottom/empty constraints
   (source lines 373–375). Name y has no value-link action: it already uses Y.
3. Finishing Apply 13 at `candidate_source.rs:394–411` retains an Apply recipe
   with callee V_14, callee effect E_14, argument Y, argument effect E_15,
   result V_13 and application effect E_13. It creates source Call input 0,
   `checking=(occurrence_13,0)`, its occurrence-derived cause, level 3 and
   the original source indices. `formal_name=None`: this callee is local f,
   not a formal, even though its argument is formal y. Planning retains
   operands; it does not admit this constraint.
4. `shadow_apply.rs:1299–1404::admit_candidate_fact` checks recipe/input
   correspondence, obtains the polarized operands, allocates an invocation
   effect row T_c at E_13's current level, and constructs

   ```text
   N_c = NegativeFunction(Y+, E_15+, T_c−, V_13−)
   occurrence_13 slot 0: V_14+ <: N_c
   occurrence_13 slot 1: E_14+ <: E_13−
   occurrence_13 slot 2: T_c+  <: E_13−
   ```

   The last two constraints are independently admitted effect edges
   (`shadow_apply.rs:1424–1473`). E_15 is placed in the Function argument
   effect port. It is not directly added to E_13 by this Apply constructor.
   `NativeInterface` records the exact callee, argument, all effects, result,
   demand, invocation row and application effect before propagation.
5. Each of those admitted facts records provenance and calls the actual typed
   solver drain. Value slot 0 calls `constrain_live_value`; effect slots 1/2
   call `constrain_live_effect`. This is real propagation, rather than only
   storing a request. `lib.rs:11906–11958` routes the candidate through
   `run_candidate_typed_drain`; dispatch at 12323 onward handles canonical
   pairs, variable/structural bounds, extrusion and Function decomposition.
   `candidate_extrusion.rs:808–837` is the candidate row-bound consumer:
   canonicalize, choose owner/polarity from endpoints and levels, insert the
   bound, then replay it. No transition count is interpreted as semantic proof.

Source Finish visits children before the enclosing Lambda. At planning time
the recursive Link and Apply 13 action precede f's Lambda action. The source
owner therefore does not need an already published f scheme or eager solution
of the recursive call to generate N_c. Subsequent publication, copies,
canonicalization and replay can change which native Function terms meet it;
their exact runtime sequence is not established by this static pass.

## 3. Native Function children: available evidence and conditional scope

f's Lambda recipe retains x's parameter, body slot 3's result/effect and its
initializer root V_2 (`candidate_source.rs:446–459`). At successful native
admission, `lib.rs:11233–11365` forms the positive Function

```text
L_f = PositiveFunction(X−, Entry_f−, Return_f+, V_3+)
Entry_f+ <: Return_f−       (Lambda slot 3)
E_3+     <: Return_f−       (Lambda slot 4)
L_f      <: V_2            (Lambda slot 2)
```

The bare parameter has no written formal-domain annotation in this source.
The general producer can instead use a retained formal annotation domain;
that branch is not selected for x. Entry and return effect rows are fresh
at x's parameter level. The Lambda owner retains an inferred-entry origin
for its slot 3 edge, before canonicalization. This is a concrete native
entry-effect construction; it has no complete semantic I_x/receiver object.

If a dispatch sees L_f and N_c without an intervening transported copy, the
four children in `lib.rs:12490–12529` are precisely

| Native field | Child task |
| --- | --- |
| Argument | `Y+ <: X−` |
| ArgumentEffect | `E_15+ <: Entry_f−` |
| ResultEffect | `Return_f+ <: T_c−` |
| Result | `V_3+ <: V_13−` |

For transported Functions the same dispatch rule uses their actual retained
children, not these original names. The rule is contravariant in both
argument ports and covariant in both result ports. This conditional four-child
derivation follows directly from the native source code. It does not assert
that an unexecuted particular pair was reached or that a copy is semantically
equal to its parent.

`candidate_step_function_dispatch` (`lib.rs:12642–12672`) calls the context
owner for each child and enqueues it. `candidate_context.rs:2557–2607`
retains `Dependency::FunctionPort { parent, child, field, operation }`, using
Swap for argument fields and Preserve for result fields, with actual inherited
and child-local context. Native source origins retain occurrence and optional
Lambda inferred-entry handle (2496–2535). This supplies construction incidence
and context operands beyond a flat cause log.

## 4. Which outputs are proof constructors?

| Retained output | Exact status for the selected grammar |
| --- | --- |
| ApplySourceInput, source scopes/indices, recipe and checking cause | Authentic native construction operands and origins. They identify where a local proof would belong. They are not the complete original Gen-Call-0 record or k_c. |
| Negative N_c and polarized four-port NativeInterface | Native demand constructor and port incidence. Mapping it to original complete F_c, including its independent challenge domain, is an unproved semantic bridge. |
| Native Argument/ArgumentEffect children | Actual constraint obligations for this native demand's y/value and effect ports. They may be inputs to a translation proof; they are not a derivation admitting every F_c whole carrier into actual I_x. |
| Native Result/ResultEffect children | Actual result constraints. No tree of whole decorated observations at S, equation pairing or nonpositive child evidence is stored here. |
| ProvenanceEdge / SemanticFact | Cause→fact and lower/upper native terms (`lib.rs:3144–3170`). No semantic proof-constructor tag, full operand telescope or complete D/P child is represented by these records. |
| AdmissionReceipt | Authentication of a constraint-store transaction and its cause/fact (`lib.rs:3119–3142,3536–3549`). It is unrelated to actual U_f's runtime receipt of a whole carrier. |
| FunctionPort dependencies and context relations | Retained native parent/child field and context incidence; not source Generalize Check/ViewLogic/EventProof or a semantic action certificate. |

This last boundary has an explicit consumer rather than merely an absence
claim: `candidate_context.rs:965–969` classifies FunctionPort evidence as
`InertOperation`. `retained_input` ends at 1005–1016 with
`InputCompleteness::Incomplete`, unconditionally including
FilterObligationsUnavailable, ProducerReadinessUnavailable and
DependentObservationsUnavailable. It can additionally report reference and
transport gaps. This is the context-circuit owner's readiness judgment,
not itself proof that no original finite k_c exists. In particular a relation
ID or Swap/Preserve incidence must not be promoted into a proof tree.
This borrowed evidence reader is marked as a later certificate-input consumer
(`candidate_context.rs:866`); no production invocation or observed readiness
result is claimed by this static audit.

`candidate_call.rs:282–376::observe` authenticates the original source
occurrences/scopes, the negative Function's exact four children and native
port kinds. Its pending consumer at 224–245 always returns
OriginalGenCall0, ArgumentReifyAndWholeCarrier and
ReceiverDispatchAndCompleteResultFutureInterfaces for this call. All 16
OriginalGenCall0Input coordinates remain required (90–129). The three
formal-callee suppliers are absent because this callee is not a formal;
their absence supplies no semantic admission law. `source_call` merely
borrows these authentic operands. It does not discharge the pending suppliers.

## 5. First missing D and P evidence; economy audit

The first native-to-original gap is at creation of N_c and the corresponding
f Lambda interface: no inspected output constructs their original complete
F_c/A_f/actual-I_x interpretation and challenge/guard operands. The first
semantic D child remains the original map

```text
d in D_F_c(e)
  -> Acc(I_x; d.wholeCarrier,C_e,w_e,eta0,xi)
     + actual receipt/path/context preconditions
     + original A_f complete-challenge formation at those same indices.
```

The constraints give useful exact native inputs: y's parameter row, its
evaluation effect, x's domain row and entry effect. They do not identify
J_y with a row or I_x with X. Even an established semantic operand check
`WholeArgCompatible(J_y,CarrierContract(F_c))` concerns the source argument,
not the independently admitted F_c-to-I_x domain map. No Function shape,
row inclusion, constraint-store receipt or successful solve supplies that
missing direction and scope by itself.

P has a separate gap: neither flat facts nor FunctionPort dependencies carry
a finite proof whose genuine children transport whole decorated observations
at the candidate S. Constructor congruence/result weakening/equation pairing
in Source Generalize §3.2(4) still needs its actual original premises,
including nonpositive equalities/domain proofs. Native four-port covariance
does not establish those semantic laws. Ordinary V* inclusion cannot be
applied to unproved S.V membership. L4's simultaneous source member/world
introduction remains an independent parent obligation after D/P.

Under `rules/compiler-engineering.md`'s economy classification:

- **A/B:** complete actual-receiver admission and intended natural recursive
  checking remain necessary. This audit does not downgrade them to C.
- **D:** reconstructing source indices, native port incidence, inferred-entry
  identity or Function child direction from endpoint shapes would repeat facts
  already known by these constructors. Their existing retained records can
  serve that constructional part of the bridge.
- **A/B remaining semantic premise:** actual whole-carrier/guard meaning and
  S-indexed observation action are not shown to be facts the native producer
  already knows. Adding a certificate tag cannot establish them. They need
  a genuine constructor interpretation and finite checking derivation.
- **C:** no additional all-view or arbitrary converse theorem is proposed.

No finite original k_c or source-qualified falsifier was constructed. This
is a localized source-constructor/consumer obstruction, not impossibility,
source rejection, or evidence for changing the source domain. The new evidence
is the exact native edge/child inventory and the explicit retained-input
incompleteness consumer. Another toy checker assuming D/P would leave the
same premise untouched.

**One recommended next action:** assign the Application/Lambda interpretation
owner a constructor proof for these exact native operands to the original
F_c, A_f and I_x carrier/guard formation, producing the D child with all
independent challenges retained. Then the constructive lane can consume that
same original local tree for its still-separate S-indexed P obligation.

## 6. Checks, independence, omissions and frozen hashes

Checks performed: bounded `cat`, `sed`, `rg` source/rule reads and direct
constructor substitution; SHA-256 dependency snapshots; final leased-note
whitespace, fences and local Markdown-link checks. No tests/builds, executable
inference, Scala/Oracle runs, search samples, mutations or measurements.
Seeds/ranges are inapplicable: coverage is one exact source Apply producer,
its native Lambda operands, admission and immediate dispatch/context consumers.
The conditional dispatch law covers its four fields; this is not a history
enumeration or compiler-wide absence proof. Some initial broad captures
truncated; decisive producer, grammar and consumer sections were read in
bounded windows.

Evidence independence: actual Rust record fields and producer/consumer code
are distinct evidence from the selected semantic rule grammar. They do not
independently validate that grammar's interpretation in Rust. The prior source
bridge and this audit share its exact carrier/feature-route hypothesis. No
checker is used as a semantic oracle, and this producer cannot independently
review its own artifact.

One initial read-only Git command queried HEAD/branch/status contrary to the
packet's no-Git restriction; it confirmed the supplied baseline and branch,
and was reported to the primary. No Git mutation or further Git command was
performed. Baseline blob equality and integration remain primary-owned.
No dependency was written. Dependency hashes were unchanged at handoff:

```text
d2689d6e0ee7581926916454481be9b384b54e04c3e73c874b9bd43a0cc3902f notes/theory/2026-10-12-two-use-exact-source-bridge.md
2f84356158426711bf81f099ca99748fa320d2bbc52876a08a73fcdaabc25d2c notes/theory/2026-10-12-application-c-finite-check-proof.md
73810fef85c264e02a179b8630d4c392fdc0f5369123cb1a4cbe7cfecb2eccb2 notes/theory/2026-10-12-nested-recursive-f-postfixedness-proof.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49 crates/yu-solver/src/candidate_source.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987 crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1 crates/yu-solver/src/candidate_scheme.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
```

Resource use: one reasoning lane; at most four batched lightweight read
processes; zero heavy processes, solver runs or measurement samples. CPU/RSS
and exact elapsed wall time were not instrumented. Requested worker role:
complementary source audit, leaf only. Observed identity is the producer above;
effective runtime model/effort metadata are unknown. No child or model-policy
change occurred. The yulang-proofs skill was applied within this leaf lease.

Unverified: complete original semantic record emission/interpretation, D,
P at S, L4 and background embedding, source/runtime admission, all actual
copy/extrusion/equality/frame transport and replay histories, effects/hygiene,
generalization, soundness, required principality and production cutover. No
code, test, rule, config, shared record or question file changed.

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-fy-native-constraint-check-source-audit.md`.
- Baseline SHA: `d61a66ed02c22aaa454d8b864dc68a4db7eb6aac`.
- Changed dependency hashes: none between initial/final snapshots; baseline
  blob comparison remains primary-owned.
- Review status: frozen unreviewed research characterization; no theorem or
  parent-gate promotion and no independent review claimed.
- Checks already run: static constructor/consumer derivation, dependency
  hashes, whitespace/fence/local-link integrity; no compiler checks.
- Proposed checkpoint message: `research: trace f-y native checking constraints and evidence gaps`.
- Shared-record deltas left to primary/curator: attach this exact native
  edge/port/context inventory to L3-at-c's construction owner; record the
  retained-input incompleteness consumer; keep D, P, L4, complete Call and
  inference OPEN. Shared task/index/theory and question bundles untouched.

Writes stop at handoff; review and integration remain primary-owned.
