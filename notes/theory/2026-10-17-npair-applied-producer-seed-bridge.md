# Applied NPAIR producer and descriptor-to-seed frontier

Status: frozen candidate mathematics and static source/native evidence; fresh independent review pending. No reviewed theorem or production authority.
Author: `/root/npair_applied_producer_seed_bridge`, sole author, no descendants.
Assignment: `NPAIR-APPLIED-PRODUCER-SEED-BRIDGE-20261017`, revision 1.
Sprint: `npair-applied-producer-and-seed-bridge-20261017`, contract revision 3,
SHA-256 `4e4f0c9797044b8395305775d7c45192a10300ee9b9bceb7a7d0a15ddae1f883`.
Baseline: `24be694c5bd3c024faa20bea0efb19e38f73b0c5`, verified by reading HEAD and its loose ref, without Git commands.
Requested model/effort: `gpt-6.1-sol` / `high`; observed model/effort: UNKNOWN / UNKNOWN. Current-session active receipt acknowledged the two exact output leases before substantive work.

## 1. Parent application and actual advance

Parent **CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017 remains OPEN**. The adopted negative-pair source interface is the proposal §§2–4 under its adoption receipt. Preserve its original providers, observations, assignments, worlds, typed positions, source occurrences, scopes, guards, continuations, interactions, Call demands and futures. F1 and FK1 remain independent. No local structural action discharges a foreign-continuation quantifier.

The applied internal constructor now fills the former concrete-only native pair hole: a successful invocation constructs both polar terms over one fresh row and separate inert Permission, then admits both formal links. This is a constructor correspondence result under successful internal invocation, not a source-reachability theorem. Source preflight still rejects this concrete negative row before source collection.

A further useful result is that Permission does not need a separately stored row merely to recover its construction incidence. The complete negative root in `formal_domains[parameter]` and the Permission's typed path recover the exact effect child and generated row. This removes the previously suspected missing row-to-descriptor association from the bounded, unchanged-construction snapshot. The recovery uses the constructed Function tree, not a family or arbitrary row equality.

Existing Operation seed identity plus live emission/admission records and checked FunctionPort/ordered Replay premises can then furnish a native derivation skeleton ending at that recovered row. This is not yet adopted `At(D,w,delta)`: it has neither an admitted negative-concrete source construction nor the original dependent semantic witness `w`. No current reader of `formal_permissions` constructs or validates that association. The first missing events and their exact owners are in §5. No information-loss lower bound requiring a new event ID is established.

## 2. Successful internal producer correspondence

Scope of the claim: a bounded, well-formed annotation and parameter supplied to `candidate_formal_annotation`, with live branch-owned terms, successful allocation/admission/resource checks and successful enclosing route completion. All nested rows must pass the actual internal guards; concrete negative rows here are nonempty and have zero symbolic variables. This is the approved bounded slice, not a restriction of the original source domain. The formal's root computation annotation remains a separate FormalEntry operation.

At `candidate_effect.rs:1157`, the internal negative guard now accepts exactly singleton-symbolic/no-concrete or nonempty-concrete/no-symbol rows; omitted rows bypass the written-row guard. Mixed, multiple-symbolic and explicit-empty negative forms are refused in this slice. Positive branches retain their existing behavior.

At :1215–1267, the nonempty concrete negative branch calls `fresh_effect_at_level(level)` once. It copies the current child path, exact source row position, complete native concrete-ID vector, parameter, occurrence, source owner and annotation scope into a temporary FormalPermission. It returns the positive and negative live effect terms of that same port. No atom is inserted into that port by this branch, and no upper cap, empty-row equation, residual, provider or arrival is constructed. Freshness is allocation freshness at this construction; later canonicalization/intrusion may identify rows without identifying descriptors or contributions.

At :1185–1212, Function construction runs argument value, result value, argument effect, result effect in that order. Each operation pushes its own Argument/Result step, performs the operation, restores the caller's path and only then propagates error. Argument recursion reverses variance; result recursion preserves it. The final terms are exactly:

```text
Fun+(argument−, argumentEffect−, resultEffect+, result+)
Fun−(argument+, argumentEffect+, resultEffect−, result−)
```

Induction over this recursive construction establishes the typed path invariant: each Permission path names the annotation child whose effect port created that record. Nonterminal steps traverse the corresponding Function value child; the last step selects its parent's argument-effect or result-effect child. In particular, receive's inner concrete row has path `[Result, Result]`, not the outer Function's effect row. Argument-side paths remain covered by the variance induction.

At :1294–1369, complete pair construction precedes either formal edge. The constructor reserves publication capacity, then calls `admit_candidate_value_link(occurrence,43,positive,P−)` and `admit_candidate_value_link(occurrence,44,P+,negative)`. That owner (`candidate_scheme.rs:1528`) records the exact ConstraintOccurrence and invokes ordinary live value constraints. Only after both calls return successfully does it append Permission records and store `formal_domains[parameter]=negative`. Thus every retained record from a successful completed route belongs to a complete pair with both admitted links. This does not assert that both edges already existed while link 44 was being processed: Permission publication occurs after that synchronous work, so any eventual association consumer must inspect already present lowers as well as later lowers.

The temporary path/concrete backing becomes retained state before the post-publication sample; outer temporary-vector capacity remains scratch until drop. Checkpoints store Permission length and backing bytes; rollback truncates and restores those values (:274–285). Domain insertion is journaled. These are static owner/lifetime facts. Successful route completion is essential; a bare error after publication is not a proof that partial state is publishable. Runtime resource behavior is unverified here.

Applying this to the original recursive calculation now gives:

```text
Q+ = live+(q)                 Q− = live−(q), q fresh at formal level
Inner+ = Fun+(B−, Z−, Q+, C+)
Inner− = Fun−(B+, Z+, Q−, C−)
Outer+ = Fun+(A−, X−, Y+, Inner+)
Outer− = Fun−(A+, X+, Y−, Inner−)
Outer+ <: P_f                P_f <: Outer−       slots 43 / 44
Permission D at [Result,Result], separate from q's unknown inflow
```

This discharges the bounded *internal construction* premise formerly left as an assumed Q. It does not say the receive source executed this constructor. The adopted source signature and preflight acceptance remain different gates.

## 3. Recover the descriptor's exact construction port

Take a live retained Permission D produced in a successfully completed route, and the same construction snapshot. Let `n=formal_domains[D.parameter]`. Read n through the actual branch `TermView::NegativeFunction`/`PositiveFunction` children (`lib.rs:14180–14225`). Follow all but the last path step through the corresponding value child. At the last step read the corresponding effect child. Check the appropriate Function tag at every step, composed polarity, and its branch-owned LiveVariable effect view; failure is a failed certificate, not a fallback row. Read the raw view ordinal to recover the allocated q. If an endpoint API is used, note that `effect_endpoint` (`lib.rs:11541`) immediately canonicalizes through `effect_rep`; retain the raw construction occurrence separately and validate its current representative against the same snapshot. A representative alone cannot recover which construction occurrence was selected.

For the concrete negative branch the stored effect term is `live−(q)` on the negative-root traversal; its endpoint may be the current representative of q. Its positive mate comes from the same single allocation by §2. At an Argument step the stored Function changes polarity exactly as the source recursion does; the path's source variance and term polarity therefore agree by induction. For the displayed receive path, negative Outer.result is negative Inner and Inner.result_effect is `live−(q)`.

D's source row, owner, occurrence, scope and concrete vector are the values copied by this same constructor. Validate them against the actual formal source annotation/action where source authentication is requested; the descriptor itself is not independent evidence that preflight admitted that action. Match the recorded links at D.occurrence slots 43/44 and their parameter/root endpoints, and preserve their source occurrences. The duplicate-domain guard prevents a second successful domain construction for that parameter in this state. Rollback removes this invocation's domain and Permission together.

Consequently the map

```text
(D, live formal_domains, branch term arena, same construction snapshot)
    -> (exact negative Function occurrence, effect child, generated q)
```

is a deterministic constructor inverse on these produced records. Different paths remain distinct even when later row representatives coincide. No row registry, Permission ID, or processing-event ID follows as necessary. Do not extrapolate to copied/generalized presentations, stale arenas, row reuse, rollback-truncated vectors or arbitrary canonicalized snapshots: those require their actual lifecycle/transport evidence. The retained domain is also used as Lambda's actual argument term (`lib.rs:11326`), so this is part of the existing constructor presentation, not an invented second semantics.

## 4. Combine the complete native seed and processing evidence

The prior authentic-seed proof's Operation case survives the applied source delta. Rechecked current owners are `candidate_operation` (:844), `candidate_signature_value` (:1661–1697) and `candidate_signature_effect` (:1716–1724). A positive resolved Operation signature's omitted result row gets a fresh s with physical lower Support(v). The view retains OperationOrigin, declaration, owner, occurrence, signature position and concrete members. This is a source-owned native interface member, not generally Contribution(u32), and not the full semantic provider/observation tuple.

`candidate_extrusion::candidate_insert_bound_with_evidence` (:442–601) admits a bound before physical append and then retains BoundEmission pointing to that exact admission, bound, owner/lane/index. In a live snapshot check emission/admission bound equality, canonical physical owner, lane, slot and operand still present. Resolve Support(v) and a member m in range; verify Operation provenance and declaration identity. `shadow_apply.rs:377–389` already exposes this exact OperationInterfaceMember identity. Do not require a fabricated ordinary Contribution producer.

A bounded candidate native incidence certificate can use all of the following together:

1. The produced D, its formal root and port recovered by §3, and the actual links 43/44 with their occurrences.
2. A live physical source seed emission and its admission, source-owned view and exact member as above.
3. A finite checked derivation tree over actual retained relation records: FunctionPort edges must match the actual parent Function endpoints, field, Swap/Preserve operation and child endpoints; Replay nodes must check both ordered inputs and their BoundKeys. Derived edges cannot silently replace an unknown semantic rule. Keep all needed leaves; graph reachability alone is insufficient.
4. A live lower emission at D's recovered negative port, with its admission relation and OwnerEmission.processing connected by that checked tree to the seed. For example, the unchanged-row/ordinary-level case compares a positive Function result s to q, records s's upper q, and replays its existing Support(v) lower to q; both insertion orders are replay owners, not assumed transitions.

The real producers of this skeleton are `lib.rs:12643–12711` (all four Function children), `candidate_step_function_dispatch` (:12797), `candidate_context::candidate_function_port_admit` (:3001–3065), typed processing assignment (:12355), and ordered replay generation (:3401–3470). Bound admission retains its own relation as well as optional processing; validate both using `candidate_context_bound_for` (:3299). No equality of family names or bare row numbers substitutes for this chain.

This construction is a specification of a partial static evidence validator, not implemented consumer code or an exhibited accepted receive run. It supplies a native structural association only when those records exist and checks succeed. Failure to find them is not proof of semantic ineligibility. Initial Operation seed construction may have processing=None; provenance plus physical emission authenticates that native seed, while the checked later Function/replay records supply its arrival skeleton.

Multiple Origins can share one interned RelationKey, and Derived self-edges can occur. Traverse with cycle guards, preserve alternative proof premises and do not choose the first Origin. Checking a finite native proof tree avoids pretending a unique historical Origin selector exists; it does not prove existential native alternatives sufficient for the original provider-indexed delta. The earlier projection ambiguity is retained only within that projection. It proves neither identical complete source runs nor impossibility of reconstructing a sufficient derivation from the entire store.

## 5. Exact remaining events, owners and mutual TODOs

**First source event missing:** `candidate_source::preflight` (:423–426) calls `preflight_formal_value(...,false)`; nested `preflight_formal` (:457) requires a negative written row to have no concrete atoms and exactly one symbol. Receive's concrete-only row fails. Thus ordinary collection does not emit its Action::FormalAnnotation (:749) or execute it (:1350). The applied constructor is internally available but remains unreachable for this source form on the approved current route. This is the earliest exact missing source event, not an inference that the original language forbids the source.

**Association event missing:** a repository-wide symbol search shows no native arrival reader of `formal_permissions`; references are its producer, accounting, checkpoint and rollback. No owner emits/validates an N-Ingress association connecting this exact D to the original `w` and actual derivation. Existing BoundAdmission coverage expressly includes OrdinarySeedAuthenticationUnavailable, ProcessingAntecedentsUnavailable and MissingAntecedent for OwnerEmission (`candidate_context.rs:684–702`). These flags are conservative evidence gaps; their presence alone does not prove all relevant raw fields absent. Sections 3–4 show retained raw evidence can already recover more than those labels imply.

The missing output is not established to be a new stored selector or ID. It is an authenticated N-Ingress judgment/event with original dependent inputs. Its representation, whether validated from existing evidence or retained at the producer, needs Luna's subsequent contract. No new source field is authorized here.

- **NPAIR-DESCRIPTOR-INCIDENCE:** formal owner `candidate_formal_annotation` plus native evidence consumer owner. Input: exact D, domain term, path, links 43/44 and live source/arena snapshot. Required output: checked construction port using §3. Falsifiers: accepting row/family equality without Function incidence, using a parent path, accepting stale/reused state, or treating record allocation as source admission. This portion is now a candidate constructor lemma ready for independent review; a new row field is not a proven prerequisite.
- **NPAIR-NATIVE-INGRESS-VALIDATION:** Function/effect emission and context consumer owners. Inputs: §4's complete certificate, actual source construction status and original dependent witness w. Required output: establish exactly which native identity/derivation fields realize each original w/delta coordinate, then validate or retain the N-Ingress event at the real reached port. Falsifiers: interface member relabeled as full w, fabricated view, wrong declaration/member, stale slot, missing ordered replay premise, arbitrary Origin choice, or merged same-family providers/residual lineages. Preserve already existing lowers because Permission publishes after both drains, and later lowers because ingress remains live. This is a provisional implementation TODO only; no compiler lease or semantic choice is granted.
- **NPAIR-SOURCE-ADMISSION:** candidate_source preflight/collection owner and Luna. Inputs: approved producer correspondence plus independent source/native review and the original source contract. Required output: a separately authorized admission contract for the exact negative source form, preserving ordinary constraint construction. Falsifier: deleting a refusal and calling that source adequacy, expanding symbolic/empty coverage without its original C_sym evidence, or converting an internal API trace into an accepted source run. No source execution is requested here.
- **NPAIR-LOCAL-CONSUMER-20261017:** install/capture/FreshUse and actual receive-demand owners. The first Call still yields Y <: J1 and Inner+ <: R1; only authentic whole-presentation transport can yield rho_u(Q+) <: J2 at the second Call. J1 and J2 remain separate. No map retention test proves that actual source constructors emitted the missing association. Extrusion, qualifying Value-SCC intrusion, propagation, levels and generalization retain all original obligations.

These TODOs reduce the frontier by the applied Q construction and recoverable D incidence. They do not close N-Transport, native rho_u, all existing/future ingress, subtraction consumer, full operands/C_sym, source-Generalize, FIRST-RESULT, soundness, principality, F1/FK1, F5 or production. Receive contains no Catch; Permission alone determines no subtraction result. The uncalled f0 supplies no provider witness.

## 6. Reuse, resources, checks and frozen dependencies

Reuse the prior authentic-seed author `/root/npair_authentic_seed_antecedent` for the source-owned Operation seed and bounded Function/Replay reconstruction, after rechecking its unchanged native owners. Reuse source-construction author `/root/receive_negative_pair_construction` for original parent calculation and historical earliest refusal. Its former internal pair-hole statement is historical for the old candidate_effect snapshot and is replaced only for the new bounded internal constructor by §2. Reuse approved producer design and Luna's application for the shared-row/separate-Permission representation. Existing source authors remain their recorded authors; no authorship/model history is inferred. Reject stronger claims from seed Origin projection ambiguity, assumed transitions, equal-family matching, or conditional pure renaming across identifying intrusion.

Six substantive stages: authority/pins; producer correspondence; descriptor inverse; complete native seed/processing audit; parent frontier and falsifiers; freeze. Conservatively charge the full 720-second reservation, zero remaining authority; no measured runtime claim. One initial `python` hashing command failed because unavailable; `python3` was used thereafter. Contract revision 1 had a malformed 62-hex historical pin; proof reliance paused, Luna issued revision 2 with the corrected pin, verified and acknowledged. Revision 3 was a formatting-only contract update, verified and acknowledged. No budget reset. Truncated combined reads were followed by decisive bounded excerpts.

Checks: static source/symbol inspection, byte hashing and artifact formatting only. No tests, builds, Cargo, probes, compiler/source execution, network, Git commands, nested CLI or descendants. Only this artifact and its exact inbox were created; no scratch paths. This producer cannot independently certify the result. Writer STOPPED at final freeze; fresh independent review and Luna adjudication remain pending.

All manifest pins below were verified. Supplemental native/authority pins are the already frozen direct dependencies in the two supplied prior artifacts, not a new external source domain.

| Dependency | SHA-256 |
| --- | --- |
| Sprint contract revision 3 | `4e4f0c9797044b8395305775d7c45192a10300ee9b9bceb7a7d0a15ddae1f883` |
| candidate_effect.rs | `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb` |
| candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| candidate_context.rs | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| candidate_scheme.rs | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| candidate_extrusion.rs | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| shadow_apply.rs | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| Native-port design | `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce` |
| Producer approval receipt | `cd81ea1385b1304da283ef8ee15cdd626b98d1759cf79aa372f672e53c5bab67` |
| Authentic-seed proof | `0121e51f0f41da70c16f301df8f3ddebcbffc37171029a37d604401d8caa0be3` |
| Authentic-seed handoff | `a9c68beb7f9ba77feb7096927b37b123cc49fdc657b2b6c1a4700f1ff70fa8a8` |
| Authenticated-seed readiness design | `5e9d7566cc7e367100ce5403e363d82473167ff30969f41ca698f8cdcec3e523` |
| Readiness handoff | `72025e4d7e06461af98c227e7d89cdfe50a4026ee9b492f3aaaaae1b3004009e` |
| Source-construction proof, corrected pin | `2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f` |
| Source-construction handoff | `c74308096bfd0be1be7a39a21dea0e91bba43f9e0273975bd33ad0c8a1c93a81` |
| Adopted negative-pair proposal | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| Source-formation adoption receipt | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Annotation hygiene integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Source Call interface definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
