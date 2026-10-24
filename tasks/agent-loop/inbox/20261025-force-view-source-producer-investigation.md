# Force/View source producer investigation — revision 1

Status: **FROZEN research characterization; SOURCE REALIZATION PREMISE OPEN**.
Independent review: NOT RUN. No semantic adoption, theorem closure, production
approval, or executable verification is claimed.

## Objective, baseline, and method

Investigate the source producer prerequisite of `call_step_erasure` (S) and
`call_raw_successor_coverage` (C), under
`tasks/agent-loop/sprints/force-view-source-owner-20261025-r1.md`.
Pinned baseline supplied by Luna: `57fbf68f79581349f994bf0db9cd9235d8edd298`.
No Git command was used to infer or change that baseline.

Method: bounded textual source/owner audit, following the operational paper,
the typed-boundary draft, their exact role-elaboration reference, the two
assigned Rust inspection targets, and the pinned Lean representation. This is
complementary source evidence, not the constructive prover lane. No descendants
were launched. Existing candidate edits were read without modification.

**Result:** the normative paper has a mathematical, syntax-directed producer
`d`; neither assigned Rust target realizes its Force evidence. The exact
missing artifact is a construction-directed executable realization of the
Force row of `d`, linked to its latent body graph and to the consumer's state
representation. Calling the selected Force meaning undefined would overstate
the finding. Calling the assumed Rust ports a realized producer would also
overstate it. No full producer-to-consumer derivation is established here.

## Authority and dependency snapshot

The accepted typed-value transport principle remains the user's 2026-10-02
decision: corresponding typed paths carry evidence through capture, storage,
return, and adaptation; unrelated latent paths acquire no grant; expiry ends
authority; raw resumption uses current state. The draft's exact realization is
unapproved. Inert argument receipt and complete Call extent are preserved.

The operational paper is used in the packet's assigned normative scope. Its
lines 2619–2645 distinguish its typed language/decoration from the compiler
translation and VM/native realization theorems. Its claimed paper theorems are
source statements, not independently proved results of this audit.

All eight packet input hashes matched their frozen values on initial read.
The additional role-elaboration file is an exact reference of the draft
(lines 654–662); its historical compiler locators describe revision
`a58eefc3`, not current executable Force evidence.

| Dependency | SHA-256 |
|---|---|
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| notes/design/2026-10-02-typed-boundary-realization-draft.md | 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb |
| tasks/agent-loop/sprints/lean-complete-call-20261025-force-view-interface-amendment.md | 8d7ad0d788d559d5efa3e7b75953221d8a7bd9586ffe09ac1f705fe6a3862406 |
| tasks/agent-loop/sprints/lean-complete-call-20261025-r9-outcome.md | 66d5f30ee3323b33b6943b5817ee48cdd69e20bfd793ea65b08df125567a7579 |
| notes/theory/lean/YulangClosure/CoreSyntax.lean | dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece |
| notes/theory/lean/YulangClosure/ControlSyntax.lean | 1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0 |
| crates/yu-core/src/shadow_typed_evidence.rs | dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95 |
| crates/yu-hir/src/shadow.rs | b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e |
| notes/design/2026-10-02-source-computation-role-elaboration.md | 9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb |
| tasks/agent-loop/sprints/force-view-source-owner-20261025-r1.md | ec9b434fc06b6b037590f7d1066fb62bb4722f54d34450ae6fb576352641d1af |

## Governing source and actual ownership

1. Operational paper, `sec:decoration`, lines 1186–1195: input is typed syntax
   with resolved declaration identities, type instances, annotation occurrences,
   lambda introductions and selected adapter code. It does not assume an
   inference algorithm that produces that input. Lines 1231–1252 define the
   decorator: stable labels are separate from dynamic identities; Delay saves
   code/captured views; Force installs `View(v,force.effect,M)` and a separate
   result transport. Lines 1255–1257 put captured-binding Receive at actual
   invocation, rather than at closure allocation.
2. `sec:refined-typing`, lines 1517–1559: Delay retains the body graph/free
   packets; Force re-observes in the current diagram and connects View entry,
   body, and leave. The typing judgment includes both the original typed
   derivation and `d`, not endpoint equality alone. Lines 1579–1581 permit
   views only through decoration, specified transport, receipt and substitution.
3. `sec:machine`, lines 303–307, 331–335, 458–494, 515–526, plus
   `sec:concrete-eligibility`, lines 535–613: raw constructor reduction,
   failures, view interpretation, current execution occurrences, typed flow,
   receipts and event-time observation have explicit source owners.
4. `sec:representation`, lines 1296–1322 and 1344–1358: concrete world includes
   execution/search/saved contexts and substitutions. Normal leave restores
   the saved outer ambient packet, not set subtraction; resumption adds saved
   inner Views to the resumer's current ambient packet. Abstract relations
   retain all consistent unknown candidates; those relations are not a
   concrete Force construction algorithm.
5. Typed-boundary draft, lines 388–460: `p_force` is the thunk's current effect
   position; demanded-force elaboration remains an input obligation. Lines
   667–775 describe typed path transport and removal of the result prefix;
   this supplies useful candidate correspondence detail, without upgrading
   the draft's exact realization to accepted compiler semantics.

The original semantic owner is therefore the paper's typed-syntax decorator
`d` and Force graph rule, together with its raw context machine. The upstream
construction owner is the resolved typed-syntax/source elaboration and
representation bridge feeding `d`. There is no established current production
function for that owner among the inspected targets.

### Why the two Rust targets are not producers

`crates/yu-core/src/shadow_typed_evidence.rs:1–5,24–34,92–146,151–210`:
`AssumedTypedEvidence::new` takes caller-owned typed ports, profiles, Flow,
Observe and Receive. It checks indices, context branding, duplicate ports and
nonzero witness storage, then constructs adjacency lists. It neither creates
a Delay body derivation nor derives Force ports, current observations or
lifecycles. `query_conditionally` computes reachability plus the supplied
activation filter and returns status `Assumed`. Witness addresses stand for
assumed identities; they are not an allocation/occurrence producer.

`crates/yu-hir/src/shadow.rs:2537–2647,2703–2802,3742–3761`:
`CapturedCallInput` retains lexical source topology. Its
`SourceViewPremiseLocator` explicitly constructs no invocation/profile,
receipt, receiver, typed evidence, Flow, SourceViewInst, or even evidence of
input existence. Its inventory leaves profiles, jointly scoped constraints,
typed invocation/whole-row resumption, callback paths, initial-world admission,
refined relation coverage and signature formation unresolved. `Form` contains
Lambda/Bind/literal/Use/Group/Apply, not a decorated Delay/Force plan.
`ClosureCorrespondence` is pending typed capture/provider/receiver discharge.
The demand-time/captured-binding/Delay marker is explicitly an unadopted
candidate, not a source judgment. Adding Apply nodes adds pending premises.

The draft's exact role-elaboration reference, §§6 and 9, separates historical
runtime `MakeThunk` retention and forcing from source invocation/typing. It
explicitly says those runtime carrier-building stages must not be identified
with source invocation entry without a representation mapping. Such a legacy
allocation path would not supply the missing evidence merely by allocating a
thunk. Its historical files were not chased as current producers.

## Small nested witness and trace with explicit hypotheses

Use the normative typed-plan schema, not a claimed parsed Yulang fixture:

```text
t0 = Viewχ(Delay(Ret(Delay(perform_o p))))
let t1 <- Force t0 in Force t1
```

Hypotheses H1–H4, not proved existence claims:

- H1: a resolved typed input derivation gives the outer thunk a type
  `U(E0,U(E1,Qo))`, the operation its actual declaration/instance and payload
  type, and all free packets the same joint assignment/substitution.
- H2: χ is licensed by source receipt/typed transport for this exact alias,
  including the indicated nested result path. The unrestricted projected
  View typing rule is insufficient to establish this hypothesis.
- H3: the execution starts in an admitted concrete world/current context with
  its actual live owners/handlers, typed environment and literal outer suffix.
- H4: a realized source decorator supplies the plan/graph and its correspondence
  to the consumer's concrete state. **This is the missing premise.**

The two levels make immediate effect versus returned latent effect visible.
Removing the second Force leaves the smaller obstruction
`Force(Viewχ(Delay(Ret ())))`: even that one exposure requires H4 in the
current executable representation. This is a minimized missing-input witness,
not a semantic or compiler counterexample and not an independent proof of H1–H3.

| Stage | Direct source fact / derived obligation | Unestablished executable construction |
|---|---|---|
| Delay t0 | Save outer body graph and captured packets. The inner Delay is latent until the outer body executes. Allocate no executing Force View at either construction. Source: 1244,1531. | Body code/graph/capture derivation packaged with a source-owned Force plan, beyond a structural HIR capture ID. |
| First Force | Observe underlying Delay through the licensed wrapper; re-observe its graph in the current world. Enter its `force.effect` delimiter, execute the retained `Ret(Delay(...))`. Source: 490–494,1245,1532. | Concrete projection from this wrapper's typed root/evidence to the current Force effect port; fresh dynamic occurrence and its relation to the source label. |
| First Ret | Pop precisely this executing Force delimiter and transport the returned thunk along the separate result correspondence. A structural result path loses its selected result prefix; the outer effect port does not become the inner effect port. Source: 485–488,1245,1352–1355; draft 762–775 gives the candidate path equation. Bind's following Force runs outside the completed first Force delimiter. | Realized pair and proof of that result-prefix correspondence. The paper's row is the mathematical owner; neither Rust target emits the pair. |
| Later Force t1 | Preserve the returned latent packet/body graph and re-observe it under this later current diagram, not Delay creation activity or the completed first delimiter. Enter a new dynamic Force occurrence. Source: 1531–1532; draft 403–415. | Source-derived second pair and current occurrence/context mapping. Equal result/effect endpoint types supply no such mapping. |
| Event/Req | `perform_o p` creates q with actual operation instance and typed payload/response. Record every executing View, including outer Call Views beyond handlers, at emission; bubbling creates no new event. Source: 320–321,515–526,560–570,589–595. | Actual world/context emitter supplying those Observe rows, rather than passed-in `AssumedObserve` records. |
| Req suspension/resume | Save exposure and remaining continuation; suspension is not normal leave. Crossed inner Views suspend, retain packet/port, and re-enter freshly under current resumer context. Views outside the selected capture boundary stay outside the raw saved continuation. Bound names freshen coherently; free live owners remain current. Source: 458–494,1352–1358; draft 441–460. | Reconstruction/renaming correspondence for the Force plan and typed suffix. A generic suspendView field does not establish it. |
| Resumed Ret | Operation response satisfies Qo, saved suffix continues under restored inner Force delimiter, and completion uses its result transport once. Source: continuation typing and expose/result rules above. | Same retained plan mapping across suspension and repeated resumptions; no executable realization inspected here establishes it. |
| Fail/Bad | Replace the inner body by a source failure to inspect Fail; an expose/other active frame propagates that same failure. Malformed raw `Force` with no underlying Delay is genuinely Bad; View wrapping does not repair the constructor. A child's Bad propagates as Bad. Source: 303–307,331–335. Typed exclusion requires H1 plus canonical-form premises. | Projection of the context reduction into the chosen Lean World/metadata fields. No arbitrary `failWorld` successor or result transport is licensed by failure propagation. |

For all rows the complete Call delimiter, if present, surrounds its own entire
argument/entry/body/result-consumer/adapter computation (1246). A Force delimiter
is only the forced body's computation. Static syntax labels never serve as
dynamic View or owner IDs. No receiver is allocated merely by Force or by an
alias. The trace uses context replacement beneath an unchanged symbolic typed
outer suffix; it does not prove arbitrary-suffix preservation in Lean.

## Exact obstruction, claim class, and semantic question

Claim class: **bounded source characterization and conditional trace**, with
H4 explicitly open. The normative paper specifies `d`; this audit does not
refute its mathematical definition or demand an inference implementation to
state it. The missing executable definition is a realized, source-indexed
Force-plan constructor consuming the typed wrapped thunk/body derivation and
current context and returning:

1. static source occurrence and retained body/capture/latent graph;
2. typed `force.effect` and separately typed result-prefix correspondence;
3. source-derived path/packet transport preserving χ, shared K/D and lineage;
4. fresh dynamic execution occurrence with actual current owner/world inputs;
5. consumer entry, Ret, Req/re-entry and failure projections preserving the
   literal typed suffix and exact source control boundaries.

This missing definition belongs to the `d`/source elaboration/representation
owner, not to the finite query module. At the Lean consumer,
`CoreSyntax.lean:208–235,251–284` has generic paths/adapterMap and an expose
pair but no source-derived Force plan. `ControlSyntax.lean:274–319` can enter
a supplied expose pair or an unexposed Delay body; it supplies no wrapped-thunk
Force producer. Lines 353–363 and 405–419 consume the result/effect pair on
Ret/Req; lines 457–466 require a generic `md.failWorld` premise on Fail.
Those are consumers/assumptions, not an independent realization proof.

**Smallest unresolved semantic question:** no new question about the selected
observable Force behavior is established by these reads. Ret, Req, Fail and
malformed Bad are distinguished by the accepted source. The smallest remaining
interface question is: which source-derived representation maps contextual
Force entry/leave/suspension/failure to this particular Lean World's fields?
The source's context removal and ambient restoration constrain that mapping;
the audit cannot equate them to an arbitrary Metadata relation. Whether a
particular World field changes is not an unanswered language choice until its
representation has been specified. If that specification exposes a genuinely
unfixed observable case, return only that case for adjudication. Do not reopen
the accepted lifecycle or adopt the draft merely to populate a field.

## Independence, coverage, and failure conditions

No oracle, executable model, search, mutation, random seed or numeric range was
used. There is consequently no measured search coverage. The audit is
independent of any checker that assumes transitions: it inspected constructor
and query signatures and their source-owner declarations directly. It shares
the packet's normative source and H1–H3 and does not establish source admission
or operational adequacy independently of them.

Coverage is the named files/sections and a two-level typed-plan trace with
Ret/Req and explicit Fail/Bad branch obligations. Not covered: arbitrary raw
source elaboration, unknown-shape instantiation, full source/native realization,
all wrapper chains, all metadata transitions, compiler execution, formal
proofs, or complete Call S/C. No negative whole-repository producer search is
claimed. A previously uninspected producer could change the characterization.

The independent falsifier is exactly an admitted wrapped thunk for which a
required port/occurrence/body/capture/lifecycle mapping has no source-derived
constructor. The minimized schema above exposes that conditional seam; it is
not promoted to an admitted-program counterexample. Conversely, an existing
executable constructor proving the five outputs above, with current-world and
saved-context correspondence, would defeat the missing-producer finding.
An arbitrary adapter map, equal types, passed-in observation table or abstract
all-candidate world relation would not.

## Commands, resources, cessation, and next action

Commands run: bounded `rg`/`rg --files`, `cat`, `sed`, `head`, `wc`, `pwd`,
`date -u`, `sha256sum`; `apply_patch` wrote this sole leased note. These are
text/hash inspections, not executable semantic checks. All eight initial
dependency comparisons matched. Final hash revalidation is reported with the
handoff's external digest, avoiding a self-referential hash in this file.

Not run: Git; compiler, Lean/Lake, Cargo, native program, builds, tests,
simulation, or formatting. No source, shared task/index/authority, manifests,
lockfiles, question bundles or other worker files were changed.

Worker: `/root/force_view_source_owner_r1`. Requested in packet: Sol/high
researcher; observed model/effort metadata: UNKNOWN. One worker, no descendants,
no background process or generated artifact. Cap: 600 seconds. Exact wall-time,
CPU and peak memory were not instrumented and remain UNKNOWN; no heavyweight
work was run. Last observed UTC before final note preparation:
`2026-10-24T23:50:59Z`.

Write-cessation receipt: revision 1 is the final authored byte snapshot. After
this write only read-only dependency/artifact hashing and the handoff will run.
No further edits or descendants are pending. The lease may be marked FROZEN
for independent review of the externally reported hash; this is cessation,
not approval or an independent review receipt.

Recommended next action: Luna should adjudicate a narrow source-to-record
Force realization interface against `d` and the concrete context machine,
before authorizing any exact representation work. Keep S/C and the complete
semantics/inference parent OPEN. This recommends an interface handoff, not
another assumed-port probe and not semantic adoption.

## Commit packet

- Exact sole leased/changed path:
  `tasks/agent-loop/inbox/20261025-force-view-source-producer-investigation.md`.
- Baseline SHA: `57fbf68f79581349f994bf0db9cd9235d8edd298` (primary supplied).
- Dependency changes: none observed; additional exact-reference hashes above.
- Review status: frozen revision 1, UNREVIEWED research-only characterization.
- Checks already run: textual source/owner inspection and SHA-256 comparisons;
  no executable or formal check.
- Proposed one-line research-checkpoint commit message:
  `research: locate Force View producer realization premise`.
- Shared-record deltas intentionally left to Luna/curator: record stopped writer
  and frozen note hash; adjudicate the realization-versus-semantics distinction;
  retain Force input, S/C, Call A/B and full parent OPEN; obtain fresh independent
  review and decide the next exact interface lease. No shared files were edited.
