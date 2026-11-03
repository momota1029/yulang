# R339 EI realization repair — exact producer obstruction

Assignment `R339-EI-REALIZATION` / handoff revision **1**. Selected contract:
`tasks/agent-loop/sprints/source-witness-integration-r339.md`, updated repair
revision SHA-256 `e2d2b87031854fd7e6ebf591aec3f9d28859df29992a7dd378338f125d924672`.
Baseline supplied in the contract: `790cbe408`; no Git command was run.

Sole author/runtime task: `/root/r339_ei_param`, resumed by NEW_TASK from
`/root`. Launch UUID/model/effort metadata are not exposed: requested and
observed model/effort UNKNOWN. No descendants, coauthors, production rights,
or reviewer appointment.

## Disposition

**BLOCKED at an absent original producer/interface bridge; no new theorem.**
The unchanged parent is universal EI-Intro/EI-All/EI-Result, applied through
R311/R330/R328/R293/R306 to unchanged R159. The repair does not reduce this
parent. It identifies the exact missing domain correspondence and independent
component-evidence transport. No source/semantic constructor was changed.

The independent review is correct: the earlier R339 `ResponseSchema` permits
an empty response type or `Develops := False`, so its universal theorem can be
vacuous. Its `restricted_callee_response` supplies changed-world `CalleeInputs`
and changed primitive inputs as fresh hypotheses rather than transporting
those proofs. The earlier frozen artifact's phrase “closes the typed universal
callee-request construction edge” must therefore be read only as **conditional
assembly over the supplied schema**. Any claim of an authenticated original
parent-edge reduction is withdrawn by this repair disposition. The earlier
Lean theorems remain valid under their printed premises; this does not change
those frozen bytes or their checked mathematical statement.

IF legitimately quantifies over independently typed original primitive
contracts. This obstruction does not require choosing concrete W/Z or proving
an opaque primitive from nothing. It requires exposing the actual original
contract and its correspondence/naturality in the formal owner interfaces.
The current source records and local guard interface do not expose that
contract. Renaming arbitrary predicates as “original” cannot supply it.

## Constructive owner attempts and exact failures

### 1. Original source event / admission owner

`OriginalSourceEvents.Response` (line 642) and `RawResume` (line 653) are DATA
constructors. They retain original invocation, other environment, request,
operation declaration, raw handle, continuation, suffix, response record and
joint fields. Neither constructor carries or produces a response typing,
request-specific admission, continuation development or semantic action law.
`sourceRecord` (line 798) chooses an actual source owner and checks runtime
binder kind, then decorates the record. It explicitly performs no original
admission/domain test. Thus its source ownership cannot certify the missing
semantic domain.

The actual admission consumer is:

```lean
OriginalSourceEnvironment.LocalAdmissions.response :
  Decoded s View → Binder → ResponseData s View → Prop
```

`ResponseData` (line 97) has only `observation` and `receipt`.
`DataAdmitted` (line 608), response case line 620, checks exactly binder kind
and this arbitrary local relation. `RuntimeReadout.event` (line 295) obtains
the actual history/configuration from `receipt.after`, and other semantic
fields from opaque readout functions; it produces no response typing or
continuation-development certificate.

`OriginalSourceEvents.RawRecord.runtime` (line 780) erases operation, request,
raw handle, continuation and suffix before that consumer. This information
loss is already certified by the existing theorem:

```lean
OriginalSourceEvents.different_operations_same_runtime
  (original : Invocation s View) (others : s.Context)
  (request : s.Observation) (handle continuation : s.Continuation)
  (suffix : s.Context) (responseData : ResponseData s View) :
  let first := RawRecord.response original others request 0 handle continuation suffix responseData
  let second := RawRecord.response original others request 1 handle continuation suffix responseData
  first.runtime = second.runtime ∧ first ≠ second
```

That existing result is reused as source evidence, not reproved under a new
name. A predicate factoring only through this runtime projection cannot
recover which operation-specific response type/continuation was intended.
It remains possible for a separately supplied `LocalAdmissions.response` to
encode external information, but no provided field/equation authenticates
such an encoding or its completeness.

The source generation owner `OriginalSourceGeneration.sourceRules` (line 84)
emits a primitive's exact `.primitiveDeclarationInstance` obligation; App
emits `.completeCallCertificate`/`.sourceCallIncidence` obligations. It does
not implement their response semantics. Its ordered `suffix` (line 48) uses
an `executionE` return/rebind binder whose domain is the independently supplied
kernel. This is an obligation site, not the required domain supplier.

### 2. Actual source declaration → formal TypedCall owner

`OriginalSourcePrimitiveBridgeR336.sourceRequest` (line 55) and
`source_request_exact` (line 102) authenticate the full actual source Key/use,
physical operation declaration and resulting `TypedCall.OperationInstance`.
`resolved_source_response_domain` (line 125) gives the genuine complete formal
response domain for that declaration. `formalResponseClause` (line 145) and
`source_bound_request_boundary` (line 182) construct and apply the corresponding
formal captured-continuation clause without assuming a completed EI body.
This is real reusable progress under its original premises.

The attempted next application fails at a concrete type/interface mismatch:
its response values are `TypedCall.Value`, typing is
`TypedCall.ValueTyped Original.emptyContext ... operation.responseType`,
continuations are `TypedCall.Comp`, and developments use
`Control.CallControlStep`/`Control.CallState`. R311/SourceEvents use opaque
`s.Observation`, `s.Continuation`, `Event s` and `LocalAdmissions.response`.
No constructor in this dependency route interprets the former into the latter
and proves both response-domain coverage and continuation-step correspondence.
R336's own module/consumer comments explicitly leave original Inputs, native
correspondence and R159 admission open. Replacing its domain by one native
sample or extending it to arbitrary opaque s by choice would be unsound.

### 3. Evidence restriction owner

The genuine existing hereditary laws are:

```lean
OriginalSourceInterpretation.value_restrict
  (inputs : Inputs s) (row : ValueRow s)
  (valid : Meaning inputs (.value row)) (later : Event s)
  (compatible : inputs.compatible row.event later) :
  Meaning inputs (.value (row.atEvent later))

OriginalSourceInterpretation.carrier_restrict
  (inputs : Inputs s) (row : CarrierRow s)
  (valid : Meaning inputs (.carrier row)) (later : Event s)
  (compatible : inputs.compatible row.event later) :
  Meaning inputs (.carrier (row.atEvent later))
```

They preserve the same value/carrier and vary its compatible event. They do
not transport arbitrary raw trace observations, source resolutions or primitive
declarations. `PhiT` (line 408) contains coherence, observation guards, world,
optional return and observation fields at one raw tuple, with no generic
restriction premise. `Inputs` (line 324) provides no naturality of those fields
under arbitrary `FieldMap`, nor a `Develops`/response signature to transport.
Thus there is no original theorem turning prior callee trace membership into
the changed callee trace membership required by R339 `CalleeInputs.member`.

`OriginalSourceChecking.GuardRegistry` (line 189) supplies only:

```lean
law : ∀ identifier entry, declaration identifier = some entry →
  entry.before.Holds inputs original → entry.after.Holds inputs original
```

It has no transformed-declaration lookup, signature naturality, guard
transport, or resolution transport field. R311 `PrimitiveLeaf` and `Resolution`
therefore cannot produce a changed primitive leaf/precondition from an old one
under the earlier `LawfulResponseMap`. That map contains response typing,
admission, raw projection/development and receipt laws only; none mentions
`Meaning`, registry/guard proofs, same-return checking or original primitive
resolution. Requiring a new changed-world `CalleeInputs` simply restates the
missing evidence. R328/R331 conservative embedding transports a separately
constructed extended interpretation; it is not arbitrary original whole
restriction and cannot discharge this gap.

## Missing equations, owners and falsifiers

The following are specifications of missing source evidence, **not new
assumptions silently installed as completed proofs**:

1. **`R339-REALIZE-DOMAIN` — original operation/source interpretation owner.**
   Construct a declaration-authenticated response/continuation interface before
   runtime erasure. For every original request, expose encoding/decoding of
   the same complete response/current-world tuple and prove an iff with the
   original independently typed/admitted response domain. Both directions are
   needed: soundness alone permits omission, and surjectivity onto raw records
   alone does not prove typing. Relate `ResponseSchema.Develops` iff the original
   saved continuation's zero/pending/finite development at the actual response
   current world, preserving handle, suffix, witness and all independent arms.
   Falsifiers: empty schema despite an original admitted response; operation or
   handle substitution surviving the runtime erasure; omitted divergent prefix;
   resumption at the old world. Target consumers: R311 `Phase.calleeRequest`,
   `.receiverRequest`, and their `.calleeResume`/`.receiverResume` goals.

2. **`R339-REALIZE-ACTION` — original primitive/operator contract owner.**
   Supply and prove component action equations for original trace/world/guard
   fields and transformed declaration/resolution lookup, at the same raw tuple
   and shared witness. Derive transported callee membership, same-return
   checking, original argument certificate and primitive before/after evidence;
   then construct changed `CalleeInputs` instead of assuming them. Inputs may
   be genuine independent primitive law components, but not phaseBody,
   target membership as an unexplained action law, or completed EI/child proof.
   Falsifier: lawful response-data map with a changed trace guard or missing
   transformed registry entry while all earlier ResponseMap laws still hold.
   Target consumers: R331 `callee_phase_from_original_operands` and R339
   `restricted_callee_response`, then R330/R306/R159.

3. **Native correspondence owner, only when that bridge is assigned.**
   The existing runtime owns the real data in `machine.rs::PendingRequest`
   (line 831), `SavedContinuation` (line 839), `propagate_request` (line 3456),
   and `Frame::ResumeArgument` in the return consumer (around line 1968).
   `continuation.rs::ResumeTemplate`/`TemplateNode::Hole` retain the captured
   continuation structure. These are source-evidence locators, not a request
   to edit production. Any future interpretation must relate the actual
   declaration signature check, exact template/handle, received value/view,
   current configuration and all developments to the above original contracts.
   Passing an emitted witness cannot prove this universal correspondence.

These two formal bridges are independent of selecting a concrete W/Z meaning.
Their construction needs an owner of the actual original primitive contracts;
current data-only source constructors cannot manufacture those contracts.

## Checks, resources and writes

Method: targeted original-source/type/constructor inspection, attempted
applications at the two existing producer routes, and exact premise accounting.
No new Lean declaration was useful after locating the absent producer. Luna
explicitly directed that redundant audits of existing theorems should be skipped.
Accordingly no checker, build, test or probe was run, and no new theorem/axiom
claim is made. The displayed existing types were read from their original source;
they are not reported as freshly checked in this repair. The earlier R339 audit
remains evidence only for its actual conditional statements.

No `.lean` file was created at the leased `OriginalSourceEIRealizationR339.lean`
path. No scratch directory/file was created. The sole new/write path is this
handoff. Earlier frozen artifacts remain byte-identical. No Git, compiler edits,
external contact, children, shared-state writes or dependency changes.

Bound: 1800 seconds, three substantive owner investigations and handoff. Active
wall time was not independently metered; conservatively charge 1800 seconds,
remaining 0. No checker slot was consumed. Stop condition reached: no genuine
producer in the assigned source/formalization route, and repeated wrappers would
leave the same original premise untouched.

## Frozen dependency evidence

Hashes are observed source bytes for this read-only investigation; native source
may have concurrent owners and is not frozen by this receipt. No native authority
or lease is inferred from its hash.

| Source | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/source-witness-integration-r339.md` | `e2d2b87031854fd7e6ebf591aec3f9d28859df29992a7dd378338f125d924672` |
| `notes/design/2026-10-24-computed-call-result-constructor.md` | `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/lean/YulangClosure/OriginalSourceEIConstructionR339.lean` | `2fd555ac67ccb12e5a770c4878013a29d36d691434a4613bfc21fa680effc08d` |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| `notes/theory/lean/YulangClosure/OriginalComputedCallInterpretationR311.lean` | `7d230579d98b9034e62192330f98b2578629635e9810e7a7ff9195a29c813de6` |
| `notes/theory/lean/YulangClosure/OriginalSourcePrimitiveBridgeR336.lean` | `3a55a01f37f1759ca7af8ef38ed9085f7e1827a7faa5226a64034b66d14ce749` |
| `notes/theory/lean/YulangClosure/OriginalSourceScopedInterpretationR335.lean` | `219eecf85e03aae12b71b773497a9506f229832e7a7c7e8c5bf944a84063cc10` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironmentTransportR331.lean` | `d21945af4a0230a70b1670682f818530fe21460649a3b3b66c787da52109a97c` |
| `tools/inference-playground/src/runtime/machine.rs` | `1832020d095134dd69637bb1eb8f9eea70499037124c0654417190d6dba78803` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |

**STOPPED / WRITES STOPPED after final handoff hash.** No checker subprocess,
descendant or unresolved writer lease. Parent unchanged/open. Next step belongs
to Luna: adjudicate the source-domain/contract interface construction; do not
promote the earlier conditional assembly to authenticated EI or R159 closure.
