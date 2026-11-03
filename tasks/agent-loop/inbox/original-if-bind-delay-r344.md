# R344 Bind/Delay owner handoff

Outcome: **BLOCKED at the original raw component producer**. No parent edge
closed. No new Lean declaration, countermodel, assumed operator contract or
replacement IF semantics was added. The primary explicitly redirected this
packet to this owner handoff if no positive raw-law construction was available,
and released checker use. Writes stopped after this handoff.

## Fixed claim and authority

Assigned baseline: `9c084ac4f`. Original unchanged target: IF formation for
`Bind(x,q1,q2)` and `Delay(q)` in
`notes/theory/2026-10-08-call-source-interface-construction.md` §§3.1–3.2,
§5 (Sequential Bind and Reify/Delay), §6, and §7 (Callee pending).
The selection is `notes/design/2026-10-08-call-source-interface-definition.md`
§§1–4. The original raw equations also appear in
`notes/design/2026-10-05-source-contracts-and-common-allowance.md` §3.2:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S = Request(q,C,(response,C'). k(response,C') >>= S)
```

The selected extension explicitly retains independent original operator typing,
witness actions, actual-provider dispatch/phase validity and contextual
hole/world binding. It does not derive these from slot names. IF §5 requires
the *original Bind relation* to supply the result-to-rebind equation.
No result/provider/current coordinate may be selected independently; pending
suffixes remain suspended, and Delay formation performs no Force/receipt.
Operation native `Return(MakeRequestThunk)` and its declaration-derived
consumer remain distinct, as required by IF §5 and the R343 carrier correction.

The task retains arbitrary original worlds, ordinary parameters, dependent
provider/future families, whole lawful substitutions, original licenses,
independent arms, and nonreturning/effectful prefixes. No case was removed to
obtain a proof. This handoff does not refute the selected IF construction.

## Exact existing interfaces and missing producer

* `OriginalFullIFArmInterpretationR343.Primitive.projections` emits
  `PrimitiveFields inputs (raw.atInterface (primitive.interface parameter))`
  for its **own** licensed primitive. `PrimitiveFields.returned` reads only
  `Inputs.traceForm`; it does not supply a provider, original ResultBind
  relation, source suffix instantiation or constructor result image.
  `PrimitiveAction` transports only those original primitive fields. It
  contains no source-derived Bind/Delay action instance.
* `OriginalSourceInterpretation.Inputs` has `traceForm`,
  `observationGuards`, `observationFields`, `carrierGuards`,
  `carrierCaptures`, `demand`, `force` and `forceIncidence`. It has no original
  Bind observation constructor, ResultBind relation, Request/resume equation,
  or Delay formation/capture producer tying those independent readouts to
  the resolved source constructor. `TraceForm.unfinished` does not identify
  a Request/raw continuation.
* `OriginalComputedCallInterpretationR311.BoundReturn` stores the raw callee,
  value and provider but establishes no relation among them.
  `OriginalSourceEIInterpretationR331.ReturnInputs` supplies those relations
  separately. Its `ArgumentInput.checked` is already
  `Meaning inputs (.carrier carrier)`, so using it to synthesize the requested
  Delay child would reintroduce the completed carrier conclusion.
* There is a genuine partial raw route:
  `OriginalCalleeArgumentHistoryR312.carrier_from_original_leaves` constructs
  Name-delay carrier Meaning from actual allocation/caller evidence. Its
  remaining `Surrounding`, `NativeRead` and `PrefixFields` inputs have **no
  concrete instances there**. They require all-Reach world/extension/stored
  capture/view laws; inert carrier guards and capture fields; and all-fuel
  actual native prefix coherence/world guards/observation guards/fields.
  This is a formal-Name route, not a producer for the full arbitrary translated
  argument and Bind syntax in this packet.
* `OriginalSourcePrimitiveBridgeR336.sourceRequest` authenticates the actual
  tick declaration and formal `TypedCall.OperationInstance`. Its formal
  response clause explicitly does not interpret that declaration as an
  original `Inputs` clause. It cannot supply the absent original raw Bind or
  Delay field equations.

The next source/model owner is **the primary's original source-to-Inputs
interpretation lane**, with the native history owner supplying concrete raw
leaves where that route is chosen. Required positive inputs are the actual
constructor-specific readouts/equations, established independently of target
Meaning: the original returned provider/current middle and ResultBind
instantiation; component observation/world/return-field laws for the resulting
ordered computation; the pending Request suffix equation at every admitted
response/current development; and inert formation/capture/demand/Force readouts
for the actual whole Delay. These must be tied to the source declaration and
its original lawful whole action. A callback returning the finished
`OperatorContract`, child, complete result fields, or semantic result would
not discharge this producer.

Relevant concrete Rust owners inspected read-only:
`tools/inference-playground/src/runtime/machine.rs`: `Frame::Callee` return
handling (~2160), `Frame::Local` result rebind (~2805), `begin_local` (~3963),
`execute_with_substitution` Delay case (~4014), `capture_template` (~3150), and
`TemplateNode::Bind` materialization (~3272).
`tools/inference-playground/src/runtime/receiving.rs`: `Receiving::delay`
(~261), preserving inherited image dependency. These supply concrete operations
to interpret; their code is not itself an original `Inputs` law or universal
runtime receipt. No Rust execution or compiler edit was performed.

## Unchanged parent application and precise first goal

`OriginalClauseCompilerR318.Local.compileDerivation` accepts an **actual**
original `Local.Table` and its finite `Local.Derivation`. `Local.Clause` covers
primitive/Union/Conj/Scope/Rename/Ref; it has no Bind/Delay image constructor.
Choosing a new arbitrary Conj/reference relation would not authenticate the
original Bind result, and requiring both executed children would lose the
pending-first case. An actual independently justified constructor-to-table
interpretation is still required before invoking this theorem.

At `ComputedCallPhaseDescriptorR306.source_contribution_registered`, the
first unsupplied producer output remains exactly:

```lean
childNode : SourceSignatureConstruction.Node (RawObservation s)
sameCatalogue : childNode.catalogue =
  ComputedCallUnionRealizationR293.branchCatalogue inputs state scope source
packet : SourceContributionConstruction.Packet
  (ComputedCallUnionRealizationR293.branchCatalogue inputs state scope source) raw
child : SourceContributionConstruction.DeclContribution graph old operators
  left raw childNode (sameCatalogue ▸ packet)
```

R306 already computes fresh Union registration once that original child and
catalogue are established. The absent Bind/Delay producer must construct these
outputs from the independently justified raw components above; neither a static
support slot nor the primitive's own trace catalogue supplies the equation.
`SourceAppAdmissionR159.app_source_iff` and `app_continuation_iff` therefore
retain their original admission, all actual local premises and same-environment
callee/argument source proofs. Before/after parent-edge status is unchanged.

## Execution and frozen evidence

Read root AGENTS, AGENTS.pre-sprint, goal-driven sprint rules, current state,
README, R343 contract, Lean skill/source/execution references, and focused
original source/definition/consumer files. No checker, Lake build, theorem
audit or cache-writing command was run. The primary requested no repeated
audit of unchanged theorems. No theorem type/axiom result is claimed.

Actual environment queries from `notes/theory/lean`:

```text
elan which lake
  exit 0: /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake
<resolved lake> --version
  exit 0: Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
<resolved lake> env lean --version
  exit 0: Lean 4.35.0, x86_64-unknown-linux-gnu,
          commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release
```

A batched read mistakenly used repo-relative paths from the Lean project cwd;
those reads failed with `No such file or directory`. They were repeated from
the repository root. No mathematical failure or checker result follows from
that path error. Elan emitted a failed-latest-query warning but resolved the
installed pinned native executable; nothing was installed or changed.

Only changed path: this handoff. The leased
`notes/theory/lean/YulangClosure/OriginalIFBindDelayR344.lean` was not created.
No scratch/cache/generated output was created in `/tmp/yulang-r344-bind`.
All work stayed below the assigned 3000-second bound; no concurrent heavy
verification, Git, compiler changes, children or shared status writes.

SHA-256 of inspected inputs:

```text
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
435d9c99e683590ee77c95c01467608f8d3644574f883c92d84f03f79e211a03  notes/theory/lean/YulangClosure/OriginalFullIFArmInterpretationR343.lean
2aec3d3381ce8e99925c164be2d14a1a0f12e9ac1f05dc34cacb3d49a9195a9d  notes/theory/lean/YulangClosure/OriginalSourceEIInterpretationR331.lean
7d230579d98b9034e62192330f98b2578629635e9810e7a7ff9195a29c813de6  notes/theory/lean/YulangClosure/OriginalComputedCallInterpretationR311.lean
feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef  notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean
15ac251eec2927cf32d2a5d32f7487f7de0e9f64b0d7b7032103bb3c2791ec6b  notes/theory/lean/YulangClosure/OriginalClauseCompilerR318.lean
77fa332ef53d272fe67a0c511fdebf9a3def7bf64baebfed84a3eec739ef203e  notes/theory/lean/YulangClosure/ComputedCallPhaseDescriptorR306.lean
```

Independent review and source/native correspondence were not established by
this packet. Production authority remains unchanged. **STOPPED; writes stopped.**
