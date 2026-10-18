# FieldBound prefix inputs and the missing exported-root incidence

Status: frozen candidate source/native construction audit, revision 1; independent review NOT_RUN. Parent theorem and production authority remain OPEN.
Author: `/root/r19_freshuse_proof`, sole author; no descendants.
Assignment/handoff: `r20-fieldbound-prefix-and-use-construction`, revision 1.
Sprint contract: `operation-v1-fieldbound-prefix-authentic-use-consumer-20261018-r20`, revision 1, SHA-256 `6445b5965db5eaa0019937e80e0793dafd0f74fd4e05684eeaa64f1572c09a2e`.
Supplied baseline: `8e1ad99fd`, exact contract pins; no Git inspection.
Requested model/effort: Sol/high. Observed effective model/effort: UNKNOWN/UNKNOWN. R20 active-work acknowledgement was sent before writing.

## Parent application and actual result

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN, original conditions closed 0 -> 0**. Preserve the original paired negative formal and ordinary formal edges, complete dependent source signature and joint witness, and the same original contribution through `f() -> R1 -> Install(g) -> Capture/FreshUse(u) -> g()/J2`. Providers, observations, worlds, assignments, contexts, occurrences, positions, scopes, guards, continuations, interactions, Call demands and futures retain their original quantifiers. J1/J2 and F1/FK1 stay independent. The operation-v1 specimen is a bounded application, not the parent source domain.

R19 established actual capture order and generic drain ownership. R20 changes method: backward-slice the concrete field constructor's inputs and follow the source's *exported value roots*, rather than assume that an earlier field record is enough. This gives a v1-only prefix where the existing native ingredients and initializer-check actions are available. It also identifies the next missing operand more precisely: a source-derived incidence connecting the actual callback member/q/m0 to the annotated response's exported root, its exact use at `k response`, and the returned Catch root installed as g. The current rules/code inspected here do not construct that typed incidence. Simply moving FieldBound before capture does not discharge it.

No full prefix/use invariant, accepted local-g run, semantic counterexample or original universal condition is proved. The result supplies an owner-bound constructor TODO, not another transport theorem assuming a field incidence.

## 1. Actual early prefixes, with their premises

Use the exact R6 source form: a direct `signal::ping()` Catch scrutinee; matching resolved arm/binder k; an annotated local `response: int -> [outer] int = \x -> outer::next()` inside that arm; and the unique resolved `k response` Apply. For an unannotated local g initialized by that Catch, consider a later ordinary g Name use. This is the versioned v1 source shape. Every statement about reaching a prefix is conditional on unchanged source admission and completion of preceding actions; no program was executed here.

`operation_v1_catch_source` (`candidate_source.rs:651–753`) constructs h_arg during collection from exact same-source child/resolution edges. It retains c=u_ping, declaration, catch/arm, continuation binder, actual Apply/argument occurrence, response definition/annotation, typed field positions and distinct callback operation/Apply c_outer. This is early linkage, not a complete successful candidate typing.

The existing stack traversal gives the following concrete sequence:

| Reached prefix | Actual construction and remaining limitation |
| --- | --- |
| CatchOperation completed | `candidate_effect.rs:962–995` creates q_view, the special negative row n_q, slot249 `n_q <: Allowance(v_q)`, and PreparedFieldV1 carrying the original h_arg. This precedes arm-body traversal (`candidate_source.rs:1056–1090`). |
| Callback Operation action completed | `candidate_operation:902–924` constructs the actual callback signature. For the fixed `outer::next: () -> int`, `candidate_signature_effect:1884–1893` creates its operation-provenance view v_body, no tail, allowed member outer, and a Support lower on its result-effect port. Thus `AnnotationMember(v_body,0)` is a real native operand with this source operation provenance. |
| Callback Apply and Lambda completed | The Apply recipe checks the exact callee/argument/result/effect operands (`shadow_apply.rs:1763–1930`). `admit_lambda_fact` (`lib.rs:11328–11505`) connects actual body effects to the Lambda return-effect row and constructs its positive Function. A source body occurrence is not substituted for a native member ID. |
| LocalAnnotation(response) completed | `construct_candidate_local_annotation` (`candidate_effect.rs:1551–1606`) executes the whole initializer comparison and builds the annotation pair/exposed root. In the staged source driver this precedes PublishLocal(response). An executed comparison can still record conflicts; successful full-candidate publication remains a later obligation. |
| Response Name, k response, Catch finish, Install(g) | The published response Name takes its own authentic capture/FreshUse; the actual k Apply is checked; Catch arm outputs flow to the Catch result; Install stores that exact root/boundary. Subsequent g Names take their own capture/FreshUse. |
| Deferred FieldBound action | Only after ordinary traversal/local-use actions, `candidate_source.rs:1448` appends the action that actually creates q/m0/FieldBound (`candidate_effect.rs:1075–1096`). |

The two native inputs used by the field constructor can therefore be ready before the response annotation and before Install(g): the exact PreparedFieldV1 and the original callback view. This is a stronger location result than R19's final-action timing. It does **not** prove that invoking the constructor at that earlier instant has already established complete m0 typing. Callback Apply/Lambda/annotation checks and final conflict-free publication still matter. The completed response LocalAnnotation is a concrete later prefix where those local check actions have run, still before the selected g capture. Neither prefix currently emits FieldBound.

Other source shapes need their own ordering. In particular, a response defined outside the arm, recursive initializer Link, multiple requests sharing a callback, another schedule, or a foreign continuation is not covered by this local ordering calculation. They remain original open cases, not new source restrictions.

Identity checks constrain any future prefix hook: `same_handler_argument_v1` (`candidate_effect.rs:211–230`) includes pointer identity of the retained response annotation and callback declaration. Re-running the source matcher to rebuild equal-looking h_arg allocates different evidence and does not meet that check. Carry the actual retained h_arg clone. Slot250 must stay collision-free against the complete ordinary source/recipe slots and other field producers; a successful check against an earlier provenance prefix alone does not prove later uniqueness. This packet makes no scheduling or slot-policy change.

## 2. The exported-root calculation

Let L be the actual response Lambda value endpoint, A-/A+ its annotation's paired negative/positive Functions, R_response the new exposed annotation root, R_ping the actual Catch scrutinee value endpoint, R_k the result of the particular `k response`, and R_catch the Catch value root. All are schematic names for existing native owner operands; their runtime numeric IDs are UNKNOWN.

The response annotation constructor emits:

```text
L <: A-                         initializer check, source slot40
A+ <: R_response                exposed annotation root, source slot41
Install(response) = R_response  source PublishLocal
```

It does not install L. The negative and positive annotation constructions share the existing annotation variable/view environment, but their ordinary comparison does not itself emit a q/m0-bearing incidence from the initializer/body member to R_response. This is a missing proof/evidence output; it is not a claim that annotation checking fails, that its ordinary bounds disappear or that no generic context can reach a related endpoint.

At `k response`, `candidate_catch_operation_inner:997–1027` has already constructed the resumption interfaces:

```text
k+ = Fun+(negative_response, entry-, returned+, R_ping+)
k- = Fun-(positive_response, entry+, returned-, R_ping-)
k+ <: P_k <: k-
```

The real Apply demand with argument S = FreshUse(response)'s actual value decomposes through these interfaces. On the positive Function/demand comparison its ordinary argument check is `S <: negative_response` and its value result check is `R_ping+ <: R_k-`. It does not generate an equality between S and R_ping. Neither source spelling nor equal Function types supplies one. The positive response signature and modified negative q-bearing response are constructed as different typed operands, not cast into each other.

Catch finishing (`candidate_source.rs:1148–1168`) then emits each actual arm body's value constraint into R_catch, and Install(g) publishes that actual Catch root. Initializer effects are separately joined once to the enclosing block. Therefore the native value-root path is real, but the typed same-field incidence has distinct seams:

```text
actual v_body/member + q/n_q/h_arg
  -> [missing source-owned annotation incidence] -> R_response
  -> actual response FreshUse -> S
  -> [missing evidence for actual resumption-result association] -> R_ping/R_k
  -> actual arm/Catch value constraints -> R_catch -> Install(g).
```

The brackets name required evidence, not assumed transitions. For the direct v1 scrutinee, an owner-derived source argument/return association may be justifiable using its exact h_arg and direct raw suffix; this packet does not silently extend that fact to arbitrary continuation contexts. The existing static constructor does not retain such a root/field result. R18's one execution returning the response closure cannot prove every original foreign-continuation case.

**Earliest actual source-emission gap** is the absence of a prefix FieldBound action at the owner-ready prefix. **The first additional root operand needed before a transport proof** is the initializer-to-exposed-annotation-root field incidence at `construct_candidate_local_annotation`, followed by the actual k-response/result incidence at `admit_candidate_fact` plus Catch construction. A completed end-of-solve field receipt alone supplies neither. These are more precise owners/operands than “transport the field earlier.”

## 3. Authentic mapping and native consumption

The existing local route reads the installed scheme's exact local ID/root/boundary/capture region, captures at that Name occurrence, and immediately prepares its FreshUse (`candidate_scheme.rs:1954–2044`). Each successful `begin_use` increments a checked counter (`candidate_context.rs:2997`); two uses have distinct context_use even when older non-generic row anchors are shared. Ordinary level-based freshening is preserved.

For a field that truly belongs to this rooted presentation, its actual lower, upper, negative row and Function coordinates would need the following existing map evidence. Their presence is a missing premise here, not assumed:

| Coordinate | Existing mapping owner and required evidence |
| --- | --- |
| Value/effect rows | `prepare_candidate_fresh_use:1543–1611`: canonical row map; fresh only above boundary and generic, otherwise the actual shared anchor. No forced freshening or row-to-witness identification. |
| Lower member / upper allowance | `:1638–1664`: node-indexed effect_operands uses the actual view/tail map and preserves AnnotationMember/Allowance kinds and member ordinal. A new view ID is related by that map, not equal to the original ID. |
| Native field endpoints absent from structural traversal | They need a justified rooted field incidence and captured node coordinates; neither source-family lookup nor capturing all global records authenticates membership in this root. |
| Context/bundle/evidence | `:1612–1632,1665–1843`: actual bundle remap, weight/context rename and imported immutable captured snapshots. `captured_snapshot_was_imported` never samples later evidence heads. |
| Scope/input/demand/root | Existing scoped branch remaps owned scopes and inputs, actual negative roots/all Function ports and use IDs. `solve_operation_v1_research` calls `solve_mode(false,true)` (`shadow_apply.rs:274`), so its scope remap is the default map. Do not claim the scoped experiment ran or infer complete original scope correspondence from it. |

The local `view_remap` is temporary; retained FreshUse stores `effect_operands` keyed by captured node index, not an arbitrary global-view map. Its typed field cannot be recovered merely by scanning for a copied operation provenance after capture. If n_q is an older shared anchor, use its ordinary identity map; do not force-copy it to simplify the field proof. Source owner c, declaration/field/license positions and h_arg remain source identities; c_outer, body/native view/member and mapped receiver/use coordinates remain distinct. Provider, witness and residual lineages cannot collapse when rows share.

The authentic generic consumer is already established in R19 and remains applicable to actual captured bounds: `begin_candidate_fresh_bound:1846` names this imported antecedent/source BoundKey/use_origin/mapped relation; `candidate_begin_bound_restoration` appends and reads back the exact physical row fiber; restoration runs its opposite-bound children; `candidate_context_step_replay_child` binds operation/index/destination/occurrence/cause to the real typed drain; terminal acknowledgements and the matching return precede Local cursor advancement. Zero opposite children may legitimately complete the physical restoration without a new comparison drain. Generic coverage gaps are not erased.

FieldBound's current separate task is an atom-to-atom `AnnotationMember(v_body,0) <: Allowance(v_q)` at callback slot250. `candidate_apply_effect` (`candidate_extrusion.rs:944–966`) sends that pair to membership checking without a row-bound append. `constrain_live_effect` really completes its typed drain before consumed, but its initial item has no FreshUse replay acknowledgement. A generic physical restoration or later global consumed flag cannot certify that *this field*, under *this map*, reached the target use's own J2 drain.

## 4. Owner-bound handoff and falsifier

**R20-FIELD-EXPORTED-ROOT-1**, unchanged parent: Luna assigns source/annotation owners `candidate_source::Work::Install` and `candidate_effect::construct_candidate_local_annotation` the actual prefix input tuple `(retained h_arg,c,declaration/field position,n_q,v_q,v_body/member,L,A-/A+,R_response)` with the completed local check actions. Required output is an approved source-derived initializer/field-to-exposed-root incidence, including exact conflict/publication conditions and which source constructor retains it. Then `shadow_apply::admit_candidate_fact` and Catch source owner must supply its exact argument/resumption-result/Catch-root extension. This is not permission to add a new source meaning or equate the argument/result types. If a bridge rule is missing, Luna must select/review/adopt it before dependent implementation. A repeated proof starting from an assumed exported-root incidence is not progress.

**R20-FIELD-OWN-USE-1**, dependent on that actual output: capture the justified rooted field coordinates before each g FreshUse, apply its actual maps and join the mapped endpoint task to the physical use and exact drain/ack. Require distinct field-use instances, while keeping source proof and shared anchors intact. A minimal provisional implementation TODO is owner instrumentation/retained phase output at those existing constructors and consumers, not a global receipt copy. Code/test/schema selection remains Luna's design/lease decision.

Concrete falsifier: in one same-HIR accepted source, invoke the installed g at two distinct resolved Name occurrences u1/u2. A field-consumption claim for u2 must reject u1's route/context_use, mapped member/allowance/scope, physical emission or ReplayChildAck, even when the source c/h_arg/family and old anchors coincide. Additionally, replacing the initializer with another compatible callback must not inherit the original m0 solely through the same annotation-positive type. These are specified checks, not executed counterexamples. Source acceptance is prerequisite, and the separate runtime HIR lane owns its first refusal.

Apply the useful result back to the parent now: early input readiness removes the need to guess when q/native operands could first be retained, but original whole-presentation transport remains blocked on a specific source/annotation/resumption-root incidence. No NPAIR negative-formal, complete Call/effect, source-Generalize, soundness, principality, termination, FIRST-RESULT, F1/FK1, F5 or production gate closes. Preserve ordinary Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying Value-SCC intrusion and generalization.

## 5. Reuse, checks and freeze

R19 reviewed proof/source characterizations are reused only for action/capture order, real generic map/consumer ownership and their explicit missing field join. This author constructed the R19 proof and remains ineligible to certify either combined result. The complementary R19 source audit author is `/root/r19_freshuse_falsification`; its result was not a source-qualified sibling counterexample. R6 design fixes c versus c_outer and exact h_arg; no broader source bridge is inferred. The original receive contract fixes the unchanged claim; its historical source hashes/refusal are not current native behavior. R18/R19 runtime milestones/failures are used only as the R20 contract states, never as proof of field transport. Green checks of assumed transitions would not supply these constructors.

All 19 R20 pins matched before reliance. The direct frozen dependency manifest below identifies the exact relied-upon bytes. Baseline runtime fixture text was read only while its pin matched; concurrent runtime HIR-gate changes are not inputs to this construction audit. No new external dependency or write path was added.

Checks: read/search/hash and manual source/constraint/backward-slice audit only. No source/production edit, test, executable probe, build, Cargo, Git, network, nested CLI or descendant. Initial combined reads were truncated; decisive source equations/constructors were reread in focused excerpts. Budget720s/Astra0; elapsed active time, CPU/RAM and token usage UNKNOWN; conservatively charge full grant, no renewal. Requested Sol/high; observed UNKNOWN/UNKNOWN.

Only new/written paths: this note and `tasks/agent-loop/inbox/20261018-fieldbound-prefix-and-use-construction.md`; no scratch paths. Author STOPPED at frozen handoff; no descendants/unresolved leases. Pending fresh independent review and Luna intake. Next work belongs to the annotation/resumption source owners above, not a background continuation of this writer.

### Direct dependency hashes

```text
98b00634966c692f5c8f7ab0b3312b168688ce5a46694efee117a77854c07d8e tasks/agent-loop/sprints/receive-negative-pair-construction-20261017.json
276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54 notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md
1d63c2c9740bdc47e4c5e3671c8e4fb524a14edeaa600baa91af0e1cf282ed73 notes/theory/2026-10-18-fieldbound-capture-order-and-consumer.md
d2952e5bba7fbae3da0c89ef37de89a8773111610bdc2c5b6aa42cdb743144c2 notes/theory/2026-10-18-fieldbound-freshuse-source-falsifier.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd crates/yu-solver/src/candidate_scheme.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a crates/yu-solver/tests/candidate_operation_catch.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca crates/yu-solver/src/candidate_context.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479 crates/yu-solver/src/candidate_call.rs
7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c crates/yu-solver/src/candidate_intrusion.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d crates/yu-solver/src/candidate_extrusion.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee crates/yu-solver/src/lib.rs
```

Contract/design/closeout approval provenance remains with Luna; historical code authors/effective models beyond their frozen receipts are UNKNOWN. This leaf is the sole author of the two new leased outputs. Hashes freeze evidence; they confer no review or production authority.
