# R221 independent falsifier — bounded carrier/readout audit

Verdict: **NO_ADMITTED_CARRIER_INTERPRETATION not refuted in the inspected dependency envelope.** The exact missing equation is confirmed below. Claim class: independent source/artifact evidence of an unconstructed interface, not a checked theorem, semantic underdetermination, impossibility result, or source-qualified counterexample. Parent-premise delta: **0**.

Owner: `/root/r221_falsifier`; no coauthors or descendants. Baseline supplied by primary: `yulang3/d39ec2532e424526d8808dc6fd4ba13b95113766`. Frozen producer input: `R221-ORIGINAL-LITERAL-READOUT/r1`. Exact exclusive output: this file. No source/model/authority change is proposed.

## Objective and method

Attempt to refute the producer's obstruction by finding an already admitted construction from the same satisfying regular graph/reference assignment to the actual original source row, including payload, original occurrence/context, root, event, scope, joint witness, and pure Return. Method: inspect the actual definitions and callers, then derive the definitional boundary. No copy of the producer's free-false-declaration parameter attack was executed or used as the falsifier.

Governing sections: R221 contract “Fixed semantics and exact first interface,” “Dependencies, resources and stop conditions”; Authoritative L1 “Adopted introduction” and “Proof and implementation boundary”; `rules/design-authority.md` authority order and natural compiler behavior; `rules/research-lab.pre-sprint.md` source-evidence and unproductive-loop boundaries; `rules/git-concurrency.md` exact leases and frozen dependencies. L1's eight complete raw payloads and original `(q,r,e₀,ξ,ω)` are accepted without reinterpretation. The original parent remains `Contracts.lean:128–130`, `SourceProblem.InferenceSoundness`, with the very same solved `a` in `sameScoped`.

## Derivation and exact first missing equation

Fix an original literal occurrence `q`, raw literal `l`, context, original coordinates `(r,e₀,ξ,ω)`, and one satisfying `(graph, refs)` for the actual generated solution. Also keep the original semantic `Sorts`, `Inputs`, declaration and assignment `A` fixed; none may be replaced to fit the result.

1. `AbstractGeneratorDenotationR220.lean:31–36,116–122` gives, **if the actual generated store has the specified fragment at its allocated coordinates**, only

   ```text
   graph.lookup .value (refs .value valueVar) = some (.atom (literalCode l))
   graph.lookup .effect (refs .effect effectVar) = some .bottom.
   ```

   The fragment's actual source-port allocation and inclusion in the original generated store are not supplied by the theorem. Its arguments contain no `Sorts`, `Inputs`, `SourceAssignment`, endpoint map, event, or shared witness.

2. Unfolding `OriginalSourceInterpretation.lean:830–850` gives precisely

   ```text
   (A.row q).descriptor = A.descriptor ⟨q, finalRoot⟩
   (A.row q).value      = A.value      ⟨q, finalRoot⟩
   (A.row q).root       = A.root       ⟨q, finalRoot⟩
   (A.row q).event      = A.event.
   ```

   These are definitional field equations, independently read from source, not new checker results. `Sorts:23–50` only declares original types; `Inputs:324–371` independently supplies `valueForm`, `ground`, and `traceForm`. None defines an interpretation of a regular graph node or payload into those types.

3. Thus the first absent construction is an admitted interpretation/allocation of **that same solution** whose finalRoot projection at the unannotated intrinsic literal edge equals the adopted original tuple:

   ```text
   A.row q = ⟨Value(τ(l)), v(l), r, e₀⟩,
   with A identified as the original readout of this very (graph, refs),
   and with original fiber/scope/witness ξ/ω retained.
   ```

   This display is L1's schematic original notation, not a well-typed new Lean equality: the existing abstract `s.Descriptor` and `s.Value` first need their admitted original embeddings. The missing connection must justify declaration, `valueForm = ground`, and groundness for this projection, rather than assume `LiteralAtom` or source `Satisfies`. For annotated cases, no blanket equality of the converted final descriptor with the intrinsic descriptor is asserted; the actual conversion must connect the distinct intrinsic and target rows to the row consumed by the source rule.

4. Return has a further genuine interpretation obligation. `TraceForm:308–310` contains `.pureReturn (value : ValueRow s)`; `return_observation_iff:680–689` **assumes** `inputs.traceForm returned = .pureReturn value` and retains world, event, guards, and observation fields. R220's effect `.bottom` does not construct a `TraceRow s`, its `Comp(empty,τ(l))` interface, or that traceForm equation. `generated_name_return:972–990` demonstrates the same explicit dependency for an existing consumer; it cannot supply a missing literal Return law.

No admitted endpoint/solution interpretation supplying step 3 or step 4 was found. The semantic/model construction owner remains Luna with the original generator/solution model owner. An assumed “readout law” of these conclusions would leave the original literal premise untouched.

## Candidate routes and attacks on shortcuts

- **Actual source generation:** `OriginalSourceGeneration.lean:35–43,85–89` retains the complete raw literal in `literalDeclaration`. The annotation boundary is synthesis → writtenTarget. `OriginalSourceSyntax.lean:359–368` declares synthesis, finalRoot and writtenTarget as distinct ports. No inspected equation identifies these ports or allocates R220's Nat variables. Port equality must not be inferred from equal solved types.
- **Existing decoder:** `SimpleSubRegularPublication.lean:12,14–47,65–86` decodes to graph indices, with variable references retained and atoms found by node equality. It has no original semantic codomain. `OriginalSourceEnvironment.lean:239–245,308–320` instead starts with a supplied `SourceAssignment`; logical/object/runtime updates at 346–380 install supplied data. `foldedLiteralKernel:963–970` still requires `LiteralAtom`; `folded_generated_literal_membership:981–1002` extracts the ground facts already inside that premise. This is not the missing independent graph readout.
- **Payload collision:** `.int 0` and `.int 1` both have code 2. This refutes the shortcut of decoding the payload from the code alone, but **does not refute the intended bridge**: R220 retains `l` as an input, and the original generator retains its full payload. A source-directed admitted interpretation could preserve both. The same observation applies to bool, floatBits, string, bytes, path and character; unit has no varying payload.
- **Duplicate atom indices:** R220 proves lookup-node equality, not identity of reference indices. The decoder's first matching index cannot silently replace `refs .value valueVar`. Conversely, duplicates alone do not refute a correctly defined interpretation that is invariant under equal-node readout. No such invariant is assumed here.
- **Root/event/shared witness:** `A.row` retains `A.event` exactly, so it does not itself create a fresh witness or scope. What remains missing is its identification with the event and original root of the same solved source occurrence. Neither a new assignment nor independent existential witnesses can discharge that requirement.
- **Carrier candidates:** the focused declaration search found the explicitly limited Bool `OriginalCheckingAdmission.Discriminator.sorts:643–674`, its `OriginalFunctionFuture` extension, and parameterized sort changes. The inspected discriminator expressly disclaims a complete Yulang semantic instance. It is not evidence of the all-payload original interpretation.

These are source inspections and shortcut delimitations, not repeated executable toy probes. No source-qualified counterexample is claimed and no new semantic decision is inferred from missing construction evidence.

## Input authentication

All following hashes were computed from current frozen bytes. Contract/source pins agree with the R221 contract and producer note; no dependency hash change was observed.

| Input | SHA-256 |
| --- | --- |
| R221 contract | `bdaa51efd7aecb2a0e291e256cec4749fc0ad78ca0623e4b1cc7b08bf8a49876` |
| R221 proof note | `1d4f46b9e9d2375d31284957c4157906df9fd00477fc976d43204262dedcb805` |
| R221 proof handoff | `3da0827d4c71ade065b33660ea3d8b2ba355374674b4bda537bcc02f10dcf25c` |
| OriginalSourceInterpretation.lean | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| OriginalSourceGeneration.lean | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| AbstractGeneratorDenotationR220.lean | `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254` |
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| SimpleSubRegularPublication.lean | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| OriginalSourceEnvironment.lean | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| PaperExecutionSyntax.lean | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Commands, coverage, resources, and next action

Read-only `cat`, `sed`, `rg`, `sha256sum`, `pwd`, and tool-clock calls succeeded. Searches for `AbstractGeneratorDenotationR220|literal_structural_readout|literalStructuralFragment` over `notes/theory/lean --glob '*.lean'` found only the R220 module itself. This textual dependency search cannot rule out unnamed or indirect equivalent constructions; direct field/type inspection is the substantive evidence. The focused Sorts/declaration search is not an exhaustive semantic search of the repository. Initial batched output was truncated; decisive source sections were reread in bounded outputs before this conclusion.

No Lean/Lake build, tests, executable experiment, Rust, Git command, network, new environment/cache, scratch file or child process ran. No theorem or axiom audit is newly delivered. No seeds, finite ranges, or mutation suite apply. Oracle independence: source definitions were inspected independently of the producer's narrative, but both lanes share the same frozen authoritative definitions and model boundary; this is not an independent semantic oracle or producer-output certification. No review of this falsifier's own output is claimed. CPU/RAM were not measured; only short read/hash processes ran. First sampled clock was 2026-11-01 21:24:34 UTC after startup reading; total assigned work remained below the 300-second limit. No process remains running.

Unverified scope: actual source-store allocation, admitted full original carrier instance, graph-to-source satisfaction, annotated conversion realization, pure Return construction, parent `sameScoped`, full effects, native/Rust correspondence. Recommended next action: Luna authenticate or construct the original carrier plus endpoint/solution interpretation at the actual owner, with the exact step-3 equation and Return projection, before dispatching another solver-reflection proof.

**WRITES_STOPPED**: this exact artifact is frozen; no further edits in this assignment.

## Commit packet

- Exact leased paths: `tasks/agent-loop/inbox/original-literal-readout-r221-falsifier.md` only.
- Baseline SHA: `d39ec2532e424526d8808dc6fd4ba13b95113766`.
- Changed dependency hashes: none observed; authenticated inputs listed above.
- Review status: independent complementary falsification/source audit of frozen producer input; no source counterexample; this output awaits primary adjudication and is not self-certified.
- Checks already run: focused source/caller searches and reads, SHA-256 authentication; no Lean build or tests.
- Proposed commit message: `research: delimit R221 original literal carrier readout obstruction`.
- Shared-record deltas left to primary/curator: record bounded independent confirmation, parent delta 0, exact carrier/readout construction owner and next evidence; no semantic-underdetermination, theorem-closure, production or global-impossibility status.
