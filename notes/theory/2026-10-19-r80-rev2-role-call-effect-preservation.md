# R80 rev2: selected role-call simulation and effect frontiers

Date: 2026-10-19. Assignment: `R80-REV2-PROOF`, handoff revision 1.
Author and sole writer: `/root/r80_rev2_proof`; no descendants or coauthors.
Status: **candidate conditional derivation and bounded source evidence**.
Independent review: pending Luna; this author cannot certify this result.
Contract: `tasks/agent-loop/sprints/effect-hygiene-role-call-20261019-r80-rev2.md`,
revision 2, SHA-256 `e7ff179d48156bf3aa897c4e8f186916936a6b0bbcea7bc0314cad3a7e7f110e`.
Read manifest: `tasks/agent-loop/sprints/r80-producer-manifest-20261019.md`,
SHA-256 `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`.
Contract baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`;
not independently observed through Git.

## 1. Parent application and precise remaining premise

The original Simple-sub/evaluator and A/B obligations remain **OPEN 0→0**;
R50 remains NOT_ADOPTED. The parent requires its original accepted source
domain and universal quantifiers, including independent F1/FK1 or foreign
continuation cases, rather than a theorem about one selected local handler.
R78 records the hygiene obligation with original provider, annotation position,
receiver, request, residual and witness lineages under one joint
`xi=(nu,K,D)`. This note preserves that formulation without claiming to
reconstruct the unmanifested governing hygiene proofs from their summaries.

The useful reduction is concrete: **once a source-owned selected member has
been materialized with its own formal annotations and lexical environment,
qualification can disappear into ordinary Apply without adding an evaluation
or handling rule**. Sections 2–4 derive this conditional result at one original
qualified-call occurrence. They identify which output the missing source
producer must emit and which existing consumers then preserve entry and
requests. They do not establish that today's constructors emit that output.

The first missing role-call premise is a validated, executable association
`(qualified occurrence, RoleId, receiver typing evidence) -> (ImplId, MemberId,
member root, lexical environment, original formal annotations, Apply provenance)`.
The actual pinned HIR exposes pending syntax occurrences, while the present
LocalSource qualified-path route constructs **operations**. No inspected owner
supplies executable role-member selection. Candidate/runtime admission also
only exempts registered Act declaration placeholders. Luna owns adoption and
the future source/admission implementation packet; this is not an inference
restriction or a new approved implementation authority.

The simulation applies to the parent by isolating that constructor-to-consumer
join. Even after this join is implemented and reviewed, ordinary Call formation,
source typing, joint native `K,D`, residual meaning, and the original complete
continuation obligations remain separate premises. No generation, accumulation,
propagation, levels, extrusion, qualifying intrusion or generalization step is
replaced, bypassed or weakened.

## 2. Source-owned occurrence data and hypotheses

Fix one original source occurrence `o` of the proposed `R::m e0 ... en`.
This notation and lookup meaning remain Draft. `e0` is the written receiver;
its **static source typing evidence**, not executing its code during lookup,
determines the proposed receiver type. Let `i,j` be the exact selected
`(ImplId, MemberId)`, `r` its executable root, `rho` its lexical environment,
and `p0 ... pn` its original curried implementation binders. These are indexed
by `o`; no spelling identifies two source members, and two executions of `o`
still allocate distinct invocation/event identities.

Use the following checkable output hypotheses, not assumed successful traces:

* **Hsel:** validation and unique resolution retain `o`, exact role and member
  declarations and `(i,j)`. Missing role/member/implementation or a duplicate
  same-key implementation cannot publish a target. This is a candidate source
  interface obligation, not a fact derived from a parser node.
* **Hroot:** `(i,j)` identifies one executable root `r` and its actual lexical
  binding/capture environment `rho`. Its body and parameter/Name resolutions
  are the ordinary source body's resolutions. Materialization does not move
  it to an empty/global environment or replace its `HirParameterId`s.
* **Hann:** every implementation binder retains its own original annotation
  owner, position and outer effects marker. Under charter §21, `p` or `p:A`
  is Value; `p:[E] A`, including `p:[_] A`, is Computation. Role-signature
  validation checks compatibility; it does not fabricate a binder annotation.
* **Hgraph:** ordinary expression construction supplies each entire `ek` once
  as an argument subtree and emits `A0=Apply(C(i,j,r,rho),E0)` and
  `Ak=Apply(A(k-1),Ek)` for `k>0`. Here `C` denotes the ordinary executable
  closure reference to the member, not a new machine instruction. Every edge
  retains a distinct source occurrence/provenance join to `o` and the written
  argument; no operand is run, duplicated, hoisted, dropped or reordered by
  selection. The member body subgraph is shared under its own identities.
* **Hadmit:** complete declaration/root metadata and these source occurrences
  pass source validation and candidate/runtime preflight before publication.
  Failure exposes no partially executable member table. This does not assume
  complete Call typing, a solver theorem, or a residual equality.

Hsel/Hroot/Hgraph/Hadmit are absent producer obligations for this role slice.
Hann is authoritative source policy, with an existing ordinary Lambda consumer
once the correct binder is retained. Neither `RoleId` nor `(ImplId,MemberId)`
is asserted to be a current production type. The candidate tuple specifies the
identity requirement for a future adopted representation.

## 3. Conditional simulation and proof

**Claim C(o).** Under Hsel/Hroot/Hann/Hgraph/Hadmit, the candidate selected call
has the ordinary execution of `An`. Its selection/materialization stage adds
no request, argument evaluation, receiving activation, handler installation or
continuation resumption. Relative to the same ordinary program and initial
state, each subsequent ordinary transition has the same source operand,
parameter binding, receiving role and outward request. This is a conditional
lowering simulation, not a new evaluation semantics for the Draft syntax.

For precision, the comparison target is the **same emitted ordinary graph**
with the qualification metadata erased. SourceSite values of that graph are
retained on both sides; it is not a separately parsed textual expansion with
invented source IDs. Runtime `(i,j)->r` binding remains an input obligation
because today's Instruction set has no selected-member instruction.

Define the relation at the handoff to ordinary evaluation by equality of the
root label, executable closure's parameter/role/schema/body/environment,
argument labels and source sites; and equality of the machine state, frames,
cells, receiving ledger, active invocations and counters. Qualifications and
the selection certificate are administrative data unused by ordinary Apply.
If independently constructed arenas use different indices, require a bijection
of those allocated handles preserving these fields; **source identities,
original receiver boundaries and event lineage are never renamed into one
another**. Taking the same emitted graph needs only equality, not that extra
representation lemma.

1. Hsel/Hroot select exactly the member closure to which ordinary evaluation
   transfers. Hgraph supplies exactly the curried argument labels. Thus the
   related ordinary configurations coincide initially. Hsel cannot be proved
   by running an operand to see which target works.
2. `machine.rs:648–657`, `Instruction::Apply`, pushes `Frame::Callee` with the
   argument label and **caller** environment, then evaluates the callee. The
   argument is not evaluated by this transition. Both configurations therefore
   retain the same whole argument and caller lexical references.
3. `Frame::Callee`, `:879–1009`, allocates one inert Delay with that argument
   code and caller environment. The returned closure retains its separately
   captured **member** environment (`Instruction::Lambda`, `:629–647`). The
   closure branch allocates a fresh invocation from call/provider sites and
   installs ReceiverReturn. This separates argument lookup from body lookup;
   a spelling-only body substitution is not enough to establish Hroot.
4. For Value, the branch installs ValueEntry and executes the whole Delay.
   ValueEntry (`:1084–1105`) binds the returned received value to the exact
   parameter in the member environment before entering the body. An unused
   formal still executes its operand; divergence or an outward request can
   stop entry. One forcing at this entry does not mean a captured continuation
   can never replay the corresponding source span.
5. For Computation, the branch binds the Delay under the exact parameter with
   Computation interface and enters the body without executing an argument
   prefix. Where RootCompSchema is available, genuine `Receiving::enter`
   constructs a new boundary and entry receipt for that fresh activation.
   An explicit outer annotation fixes the role even if its solved support is
   empty; a missing/unsupported ground schema does not change that role into
   Value or prove permission. `program.rs:414–433,488–509` obtains the role and
   parameter Name consumption from the implementation Lambda annotation.
6. Reapply 2–5 at each outer curried edge. This preserves the written order
   through actual callee evaluation, including effects of any intermediate
   member stage. For the simple `second self selected = selected`, evaluating
   the first stage produces the second closure; receiver Value entry precedes
   explicit-argument Value entry. For an arbitrary body, one must include its
   intermediate-stage effects rather than promise that both operands execute
   before all body code. Computation operands may remain unexecuted entirely.
7. Thereafter both sides use the same ordinary evaluator and state. Induction
   on any shared finite ordinary prefix preserves equality. This is transfer
   of existing behavior, including failure/unavailability, not proof that
   each ordinary continuation transition satisfies the hygiene theorem. In
   particular the induction does not certify uninspected template constructors
   or native consumers; those remain explicit in section 5. At an operation,
   `execute`, `:1929–1960`, creates the same fresh request event, resolved
   declaration, payload, source and observations. Qualification has installed
   no handler, so it cannot consume or erase that request. Shallow selection,
   saved suffix and outward results follow the same ordinary handler path.

This proves C(o) from output structure and actual ordinary entry consumers.
It does not prove Hsel/Hroot/Hgraph/Hadmit by assuming a runtime trace, and does
not certify an implementation which has not been written. Every result is
indexed by the fixed selected source occurrence; no finite example discharges
the parent's all-source or foreign-continuation quantifier.

**Immediate parent use.** A future correspondence handoff must exhibit those
five source outputs for each admitted role-call path. It can then reuse C(o)
to avoid a second method-specific receiving/effect rule. The remaining native
constraints and universal hygiene obligations keep their original owners.
No local grant, equal effect family, or same value endpoint identifies a
provider, residual contribution, receiving view or witness lineage.

## 4. Inspected producer/consumer joins and prior work

| Owner | Actual evidence and limit |
| --- | --- |
| `full_parse.rs:317–331`, `cursor.rs:85–98`, `root_statement.rs:145–231`, `statement.rs:259–344` | The previously unpinned root dispatcher is now inspected: it constructs Root and routes classified statements to Act, binding, role and impl parsers. This removes R79's **read-boundary obstruction**, not its whole literal-to-HIR premise. No execution or complete parser-combinator derivation of U/O/S was performed. |
| `shadow.rs:888–899`, `pending_role_impl_sources` | Retains RoleDeclaration/ImplDeclaration parser positions, expressly without semantic RoleId/implementation identities or a selection law. Pending syntax is not Hsel. |
| `local_source.rs:892–970,1088–1101` | Ordinary tails produce Apply; a `::` path produces Operation using effect/operation namespaces. There is no inspected selected-role-member output here. This is an exact producer seam, not a claim that the proposed syntax is already runnable. |
| `local_source.rs:595–623`, `source_annotation.rs:342–386` | Named formals retain their admitted binder source and own parsed annotation owner/position. `local_source.rs:1120–1188` pushes Catch arms in source child order, preserves resolved operation IDs and explicit Unit payload/continuation patterns. These structural producers support R78's required shapes conditional on the authentic CST; they do not complete every raw fixture derivation. |
| `candidate_source.rs:826–882,1000–1021` | Checks the actual owned LocalSource/occurrences; emits FormalRegistrationInput with implementation Lambda role, then distinct FormalEntry/FormalAnnotation actions. This is generation evidence, not proof that later native consumers preserve all `K,D` lineages. |
| `shadow_apply.rs:385–427`, `RuntimeProgram::from_hir`, `program.rs:249–321` | Declaration-placeholder exemption uses source_effect_declarations. Unsupported role/impl placeholders have no inspected validated-member admission. Runtime does not consume a CandidateInference proof merely because a test helper solved one first. Both admission seams need explicit extension after adoption. |
| `program.rs:488–566`, `machine.rs:629–657,879–1105` | Actual ordinary Lambda/Apply construction, original SourceSite retention, member closure environment and caller Delay environment, annotation-directed entry. These are the source-linked consumer facts used by C(o). |

R78 (author `/root/r78_proof`, frozen hash below) is reused only as its
**conditional** authentic-HIR runtime derivation for U/O/S and its explicitly
retained native/universal gaps. Its cited historical forwarding/primitive-root/
typed-boundary proofs are not newly inspected direct dependencies: their exact
governing files are outside this manifest. No independent new theorem from
those historical premises is asserted here. R79 (Luna draft/closeout and
reviewers credited by closeout) supplies the failed §21 inheritance claim and
missing-role example as defects to avoid; its parser-boundary failure is not
evidence of a parser defect. R78/R79 remain frozen.

Rejected shortcuts: role signature as impl annotation; accepted parser path as
executable role identity; tests as emitted-HIR evidence; family equality as
operation identity; permission as actual inflow; missing local grant as proven
nonprotection; runtime success as empty native residual; one local action as
F1/FK1 closure; discard as resumption; new source restrictions, withdrawn
bypasses or R50 adoption. No storage/fiber inventory was used.

## 5. Six effect-hygiene frontiers: status, not six proofs

| Frontier | Evidence at an exact owner | Established / conditional / OPEN |
| --- | --- | --- |
| 1. Direct matching and arm priority | `machine.rs:1550–1637` validates installed handler, scans original arm order, skips different resolved operation IDs and checks permission/declaration/payload before selection. R78 U/O: `signal::ping()` with Unit gives `1`; earlier `io::other` cannot preempt `io::tick 7`, whose matching arm gives `7`. `local_source.rs:1120–1188` retains arm order and Unit pattern. | Consumer facts inspected; U/O whole-source results remain conditional on their authentic complete source projection and admission. No general exhaustiveness/ambiguity theorem. Exact same-operation wildcard-first fixture is only a read assertion at `runtime_receiving.rs:159–166`, not a new execution receipt. |
| 2. Retained Computation versus Value | C(o), charter §21, `program.rs:414–433,488–509`, `machine.rs:879–1105`; `receiving.rs:22–43,131–166`. | Ordinary branch behavior inspected; role-method preservation conditional on Hroot/Hann/Hgraph. A draft `my run self (action:[_] int) = 0` must retain its own annotation even when the signature also writes Computation. No role inference from body or signature; unknown profile remains unknown. |
| 3. Wrong/sibling permission | `Receiving::local_grant`, `receiving.rs:230–326`, requires exact live invocation, original boundary, concrete resolved family, authenticated event/execution, genuine candidate-owner receipt of the same view/formal route, and ancestry reaching that boundary. Empty-row and nested-helper fixtures at `runtime_receiving.rs:128–139` assert missing HandlerEvidence. | Local positive predicate and fail-closed consumer inspected. A captured formal in a helper does not alone authenticate the helper's receiving boundary. **False grant is not proof of an unprotected request**: a matching arm without positive grant returns HandlerEvidence (`machine.rs:1580–1591`) rather than automatically forwarding. Protected sibling contribution/native residual preservation remains OPEN. |
| 4. Shallow unmatched outward requests | R78 S: selecting tick pops exact CatchReturn before arm code (`machine.rs:1635–1680`); its `io::other p` creates a distinct event with payload `7`, and cannot select the consumed handler's later other arm. `propagate_request`/`stop_unhandled_request`, `:1706–1775`, retain escaping source/operation/event/payload/suffix. | Conditional S result is UnhandledRequest(other,7); this is an arm-produced new request, not a second contribution erased from the original thunk. Independently unmatched/protected same-point contributions are not established by S. Runtime forwarding does not prove a native residual type. |
| 5. One continuation path and protected sibling | The concrete source occurrence is the pinned `operation_response_type_is_independent_of_the_final_boolean_computation_root`, `runtime_receiving.rs:324–328`: receive a `[signal] bool` computation containing `ping 7`, bind `k`, invoke `k 23`, then the thunk's body returns false. The assertion was read only. See bounded path below. | Capture and resumption call sites inspected; complete constructor/native correspondence OPEN. No protected sibling exists in this literal, so its preservation is **uncovered**, not vacuously a universal result. F1/FK1 remain independent and OPEN. |
| 6. One static-to-runtime operation | For that same `ping 7` occurrence: source_annotation.rs declarations create module+declaration SourceEffectId and SourceOperationId, preserving signature positions; LocalSource resolves the operation, candidate_source.rs:1210–1222 emits Action::Operation and :1692 calls candidate_operation. FormalEntry actions are separate at :1009/:1662. Runtime program clones the resolved declaration, machine's operation Apply builds/executes its request. | Source/action and runtime joins inspected. First unproved native edge is Action::Operation/FormalEntry -> actual candidate_operation/candidate_formal_entry_annotation native obligations and corresponding `K,D`/residual consumer. Those definitions were not found in the pinned candidate_source/lib files. candidate_effect/candidate_call are declared modules outside the manifest; their ownership of these definitions is a routing inference, not inspected evidence. Exact implementation owner and native consumer remain OPEN/uninspected. Solver success and an operation-expression evaluation-bottom constraint are not a proof of empty call/request residual. |

The bounded continuation path in frontier 5 is deliberately one path:

```yu
act signal:
    our ping: int -> int
my receive (input:[signal] bool) = catch input { signal::ping(p), k -> k 23 }
my forward (pending:[signal] bool) = receive pending
my main = forward { my ignored = signal::ping 7; false }
```

`propagate_request` (`machine.rs:1607–1631`) requires compatible primitive
response type before `capture_template`. `capture_template` (`:1309–1378`)
constructs Hole/Bind/View/Owner/ForwardHandler nodes from the actual saved
suffix, rejects global/cache-write frames, appends the containing owner and
publishes a TemplateHandle after validation. The selected arm binds a fresh
Continuation executable retaining that handle (`:1655–1677`); this is the
transport to the original Catch binder cell, not an arbitrary heap/fiber route.
Applying that cell uses ordinary Callee, creates an inert response argument,
and evaluates it (`:899–910`). ResumeArgument checks the operation declaration's
response type against `23`, then starts the recorded root with a fresh control
map (`:748–817`). `enter_template` (`:1380–1485`) reconstructs the listed frames,
borrows a still-active original owner or allocates an invocation for an inactive
one, reinstalls forwarded handlers under validated owners, and obtains a fresh
execution occurrence for an original receiving view/receipt. It does **not**
call Receiving::enter to mint a new permission boundary on this path. The
resumed suffix can then reach the body result false under its original source
bindings, conditional on source/template validity; the operation response Int
and final computation Bool are distinct source types.

The imported data-definition owner
`tools/inference-playground/src/runtime/continuation.rs`
(`ResumeTemplate`, `TemplateHandle`, `TemplateNode`, named by machine.rs:2) is
**outside the manifest and was not opened**. Thus the complete template
representation and its source/native correspondence are OPEN even though
these call sites are visible. This is the inspection boundary, not a defect
or source-qualified counterexample. No exhaustive capture/storage/fiber search
or arbitrary resumption proof follows. Permission on a reminted control owner
cannot be assumed from an old view; frontier 3's exact boundary checks still
apply, and protected-sibling correspondence requires its own evidence.

## 6. Minimal evidence requests and next action

| Stable request | Parent, first missing evidence, owner, output and falsifier |
| --- | --- |
| `R80-ROLE-MATERIALIZATION-1` | Original complete Call/evaluator parent. Luna first obtains adoption, then pins/leases the source-owned role/member validation and materialization owners: HIR declaration/local-source/source-identity, candidate_source/shadow_apply preflight, runtime program metadata. Required output is the exact Hsel/Hroot/Hann/Hgraph/Hadmit correspondence for the unique `SecondInt::second 1 2` plus named rejection paths. Minimal provisional/approved implementation TODO only; no code authorized by this note. Falsifier: qualified path remains Operation, another same-spelled member is selected, role/impl annotation ownership is lost, operand executes during lookup, caller/member environments collapse, or unsupported declaration publishes executable metadata. Bind C(o) to actual future bytes before review. |
| `R80-CONTINUATION-OWNER-1` | Original continuation/hygiene parent. Luna may issue a versioned manifest adding only runtime/continuation.rs and the exact native response/transport consumer needed for the one literal above. Required output: template-definition-to-capture/binder/ResumeArgument/enter_template correspondence, including what the old view and reminted control owner authorize. Falsifier: new permission is inferred merely from reminted control, original receiving identity is replaced, or one concrete path is offered as F1/FK1/general protected-sibling closure. No request here grants a new read or write lease. |
| `R80-NATIVE-OPERATION-1` | Original source/native hygiene parent. Luna identifies and pins the implementation owners of candidate_operation and candidate_formal_entry_annotation plus the actual residual consumer before inspection; candidate_effect/candidate_call are inferred routing candidates, not observed definition owners. Required input is the original operation/formal/annotation occurrence chain in frontier 6; required output is one source-derived constraint and actual mapped-admission/consumer derivation under joint `xi=(nu,K,D)`. Falsifier: permission becomes inflow, original endpoints replace a FreshUse copy, provider/witness/residual lineages merge, or an independent surviving contribution is deleted. No claim of full native ledger from runtime receiving records. |
| `R80-SOURCE-LITERALS-1` | R78/R79 source-to-LocalSource parent. The previously missing root dispatcher is now pinned and inspected, but the full literal-specific lexical/parser-combinator and annotation/Name/operation projection remains OPEN. Luna routes a bounded exact fixture proof if still critical. Required output joins original U/O/S literal occurrences to the retained IDs/patterns; falsifier is a mismatched emitted owner/annotation/arm/pattern or use of green tests as construction proof. Do not restart the old runtime-only conditional trace. |

Two distinct methods were used for the decisive role premise: direct forward
producer inspection (syntax positions/qualified-path LocalSource) and backward
consumer inspection (ordinary runtime closure/Apply/admission requirements).
Both locate the same missing executable selected-member association. A third
runtime-only proof would leave it untouched. The next high-value action is the
adoption-backed materialization correspondence in the first row, with focused
native operation evidence in parallel when pinned. It is not an open-ended
storage inventory. Stage 1 has no authorized code slice; actual inspected
blocked owners are LocalSource qualified-path formation and both admission
consumers, not an invented compiler failure.

Luna owns decision-package consistency, independent review, intake and any
source/lease/resource change. The author supplies this frozen derivation and
will need a separately leased actual-byte binding if Stage 2 is adopted.
There is no remaining active successor inside this Stage 1 leaf assignment.

## 7. Dependencies, checks and writer receipt

All 103 manifest entries were hash-checked against the current filesystem;
zero mismatches. The manifest and contract hashes matched the assignment.
This is byte-integrity evidence only. The `python` alias was unavailable;
the same read-only SHA-256 calculation succeeded with `python3`. No compiler,
test, probe, build, nested agent CLI, Git, network or production write ran.

Direct substantive dependencies (all in the frozen manifest):

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`, §21 | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/theory/2026-10-19-r78-receiving-selection-certificate.md` | `a6fcf5c95169f7b71932476a5fff915e1ac450b7859755c595bf6d73a30af31c` |
| `notes/design/2026-10-19-r79-first-executable-role-call.md` | `564d979d009eb2ec197731cf805ec89cd121cddb329c5f23da3b52da9ecaf6d9` |
| `notes/progress/2026-10-19-r79-closeout.md` | `0547575780500ccb8e089539cd3bafc8eb6777c38de24d6c3dbe7799db208272` |
| `crates/yu-syntax/src/full_parse.rs` | `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8` |
| `crates/yu-syntax/src/cursor.rs` | `f08aae49fcf048ad11890def7ef9cadab56825a63b8d87db44821a792fe9b142` |
| `crates/yu-syntax/src/root_statement.rs` | `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626` |
| `crates/yu-syntax/src/statement.rs` | `fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797` |
| `crates/yu-hir/src/shadow.rs` | `9bf3e046a55206607527d2df3dde42b32afa814bc8d8b82c814583923aefc856` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/shadow_apply.rs` | `b28193a5141b019afd6e10766dd77f86366f7a3c04e822b2a4fce784673b665b` |
| `crates/yu-solver/src/lib.rs` | `b90eeb2ce7ff78731ce418313fd9fb54b91283d90ae6462723186fde5c0045b0` |
| `tools/inference-playground/src/runtime/program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `tools/inference-playground/src/runtime/machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |

Additional inspected pinned context: HIR module/source identity and role/impl
parser headers; their hashes are the exact entries of the manifest above.
No unpinned production owner was opened. Historical hashes transitively listed
inside R78 are not current-source inspection receipts.

Requested routing: Sol/high. Effective observed model/effort: **UNKNOWN**;
no effective-model metadata was returned to this worker. Worker identity is
the actual assigned `/root/r80_rev2_proof`; no model-switch claim is made.
First clock receipt: `2026-10-19 01:44:24 UTC`; pre-receipt startup is UNKNOWN.
The parser/root-dispatch plus one continuation-path exploration was bounded
to the interval `01:44:46–01:45:57 UTC` (71 seconds charged conservatively for
that entire interval), below its 300-second subcap. Later writing uses those
already inspected facts; it does not continue that exploration.

Allocation: 1200 seconds total; full 1200 charged, no carryover/reservation or
budget expansion. Actual final clock observation is recorded in the frozen
handoff. Reviews and Luna's budget are outside this leaf allocation.
Only the theory artifact and `tasks/agent-loop/inbox/20261019-r80-rev2-proof.md`
were created; no scratch paths. On the submitted revision both paths are
frozen and **writes stopped**; descendants: none. Candidate mathematics,
source/native correspondence, reviewed theorem and production authority stay
distinct; neither parent closure nor review acceptance is asserted.
