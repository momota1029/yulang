# HIR-owned runtime entry correspondence for returned `step`

Date: 2026-10-17  
Status: **Frozen narrow source correspondence; experimental playground only**  
Author: `/root` (Luna primary)  
Sprint: `receive-inlet-admission-and-hir-entry-correspondence-20261017`, contract revision 3  
Contract SHA-256: `e7300e34dbf87ca0dab862acd340d25a0cae84d7226caf97ea370cc39233a45d`  
Source: `my apply f = { my step x = f x; step }`

## Claim and result

For this selected HIR source path, the runtime Value/Computation entry
classification and the binder identity used at Lambda entry are carried from
HIR directly. Lambda compilation stores the HIR parameter ID and derives the
role from that parameter's own effect annotation. Closure allocation copies
the same ID, role, body and lexical environment handle. Returning `step`
through its local binding stores and reads the same closure value under the
original `HirLocalId`. Calling it binds its argument under the same
`HirParameterId`; resolving `f` in the body still finds the outer parameter ID
in the captured environment chain. Saved ordinary frames and handler
boundaries retain their environment handles and frame fields when requests
capture and resume the suffix.

This proves a bounded, source-derived runtime entry correspondence for the
selected playground path without importing candidate fresh-use evidence. It
does **not** prove source typing, candidate-to-runtime plan validity, complete
runtime soundness, inference correctness, or semantic Pure/Handler role. The
original inlet/SAT comparison remains OPEN in both directions; the missing
F2 admission law is independent of this runtime result.

## Field trace

| Path stage | Identity/role carried | Source consequence |
|---|---|---|
| Named HIR binders | `local_source.rs:1285-1312` records each named parameter ID at its `IdentifierPattern` and maps it to the owning `HirLocalId`. `:651-690` wraps those named parameters in local `Lambda` forms and resolves their body names to `Parameter(id)`. | `step` has its original parameter ID `p_x`; the outer `apply` formal has its own ID `p_f`. The body reference to `f` remains `Name(Parameter(p_f))`. |
| Runtime code generation | `program.rs:382-395` emits `Instruction::Lambda { parameter: parameter.id.clone(), role, ... }`; role is `Computation` exactly when that formal's own annotation has an effect row, otherwise `Value`. The `Name` instruction retains source resolution; parameter names consult the role registry derived from those Lambda records (`:310-367`). | Role is owned by the Lambda/formal. For this unannotated `x`, entry is Value. No role is inferred from `Unit`, callable shape or candidate inference. |
| Closure creation and capture | `machine.rs:491-508` allocates `ExecutableValue::Closure` with the instruction's parameter ID, role, body and current environment handle. | The closure owns the same formal ID and captures the lexical environment by a stable runtime handle, preserving the cell chain containing `p_f`. |
| Local return and alias read | `machine.rs:850-895` stores the initializer's returned `ValueHandle` in its cell and extends the environment with `Binder::Local(bindings[next-1].id.clone())`; `:440-476` resolves a Local Name by exact `HirLocalId` and passes the retrieved `ReceivedValue` to `consume`. | `step` remains the same closure value under its source local ID. A local alias can refer to that value, but does not become a formal or rewrite the closure's formal ID. |
| Invocation and formal binding | `machine.rs:693-744` reads closure fields. Value entry pushes `Frame::ValueEntry {parameter,body,environment}`; Computation entry follows its separate receiving path and then binds the same parameter. `:819-835` binds `Binder::Parameter(parameter)` in that captured environment. `:1612-1634` performs parent-chain lookup by exact binder identity. | The argument binder uses `p_x`, and the body Name for `f` resolves by `p_f` through the captured parent chain. Entry enum role selects runtime protocol; it says nothing about semantic Pure/Handler. |
| Suspended/saved continuation | `machine.rs:1360-1418` moves the actual unwound suffix into the pending request. `:1020-1080` builds a template by cloning saved frames, preserving their fields; handler boundaries retain their environment handle. `:1120-1175` enters the template by restoring those frames and environments. | The saved `Callee`/`ValueEntry`/local/handler frames retain the source IDs and environment indices they carried before suspension. No candidate remap is consulted during this restoration. |

The execution entrypoint corroborates the separation: `lib.rs:143-153`
receives `(hir, _candidate)` from `prepare` and calls
`RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`. The candidate
object is not an input to the identity chain above. This establishes only the
runtime's HIR-owned construction rule on the selected bounded path; it does
not validate the inference result that `prepare` produced or show that
candidate transport is unnecessary for a different consumer.

## Correspondence argument and falsifier

1. HIR assigns one parameter ID to each named formal and records its owning
   source parameter node/local. The resolved body Name contains the same
   outer `p_f` ID.
2. Runtime code generation copies those IDs into Lambda instructions and
   resolves roles from each formal's own source annotation.
3. Evaluating a Lambda copies its instruction fields into the closure and
   captures the existing lexical environment handle. Local initialization
   stores that closure value; local lookup returns the same value.
4. Applying the returned closure transfers its captured environment and
   formal ID to the entry frame. Entry extends the captured environment with
   the same parameter ID. Name lookup compares exact IDs while traversing the
   persistent parent chain.
5. When a request suspends this path, saved frames are copied/restored with
   their environment handles and source-ID fields intact. No inference
   Candidate object participates in steps 2–5.

The narrow correspondence is falsified if a step changes the parameter or
local identity, if a closure copies a non-source binding under another ID, if
capture loses the parent environment containing `p_f`, or if saved-frame
restoration changes an identity/environment handle. A future code change to
these paths needs a source-owner-specific repair and review. This receipt
does not itself propose such a change.

## Limits and remaining owners

- Runtime Value/Computation is distinct from semantic Pure/Handler.
- No test, build, probe, compiler/runtime execution or expected-output change
  was made. The correspondence is a bounded source argument, not observed
  execution.
- Candidate inlet SAT2, complete RG2, original guard inventory and arbitrary
  lawful transport remain open. Original FORWARD-FIRST-CALL A/B, source T,
  anchored native MODEL, production/principality and cutover remain open.
- No code slice is authorized by this proof. This result only removes the
  supposed need for **candidate-inference evidence** in this selected
  annotation-derived runtime entry path. It does not supply the absent
  original F2 `I2/B_in` admission correspondence in the preceding handoff.

## Frozen source pins

| File | SHA-256 |
|---|---|
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/source_identity.rs` | `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| Admission-comparison artifact | `956b710546be0446ae6fd054a597196e467ce59202a08812d4c6ac349455a6e1` |
| Admission-comparison handoff | `e8e0052c6337b28f6c252e5761f882f30574c1e2cdefdca79408cef9523d8822` |

This is a frozen read-only source correspondence result awaiting independent
compiler, specification and architecture review. No parent gate is closed.
