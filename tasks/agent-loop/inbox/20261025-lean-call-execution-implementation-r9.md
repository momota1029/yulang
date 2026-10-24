# LEAN-COMPLETE-CALL-20261025/r9 implementation handoff

Sprint contract SHA-256: `6a2a2ce7cce845df7239b790709cdbfe24e15bbacc834d9d3027e9f697131811`
Assignment-ID / handoff revision: `20261025-lean-call-execution-implementation-r9 / 1`
Parent gate: checked Call execution adequacy prerequisite for unchanged Call A/B; original inference A/B and full parent remain OPEN. Contract locator: `tasks/agent-loop/sprints/lean-complete-call-20261025-r9.md`.
Baseline: checkpoint `4df64ba1581d9ffb4150c44f4548d7d9588dd8cb`; semantic baseline `8656445efaadb63bb7919e0ef0155e7630a9748f`.

## Role and resources

- Requested role/model/effort: `implementer`, `gpt-6-luna`, high.
- Actual worker: `/root/call_implementation_r9`; current worker-session and observed model/effort telemetry: UNKNOWN.
- Fresh implementation cap: 1,800 seconds. Exact active elapsed time: UNKNOWN; no verification budget used.
- Authors/descendants: this worker only; no descendants.
- State: STOPPED_WRITES after freezing this handoff. No Lean, Lake, test, Cargo/native, or Git command was run. Luna owns checks and integration.

## Outcome and parent application

Outcome class: candidate implementation plus exact source-input obstruction; not proof, source/native closure, or production authority.

Repaired the r8 declaration-order/elaboration structure by separating the `Value`/`Comp` syntax mutual group from the `ValueTyped`/`CompTyped` typing mutual group, and by defining `Function` before its `FunctionTyped` relation. Added an actual `CallControlStep` for `.force (.original (.delay body))` that enters the retained Original body state. These edits address the reported r8 declaration failures and one statically identified missing Call successor; they are unchecked bytes, so no elaboration or theorem claim is made.

The full raw Call relation and its S/C interfaces were not defined. A governing-source input required for the View-wrapped Force successor is absent from the current representation, so defining that relation or claiming complete typed-image coverage would require inventing a metadata mapping or operation policy.

## Exact source obstruction and TODO for Luna

The governing source requires Force to expose the thunk body under `force.effect` and to transport its result separately under `force.result` (`docs/yulang-operational-type-safety-ja.tex`, §12.45, line 1245; force graph discussion at line 1532). The complete Call View requirement is separately stated at §12.46, line 1246. A typed Call `Value.view` can wrap any value, including a thunk. The leased representation supplies only `TypedCall.ViewOccurrence { identity, path }`, with one path; `CallView` and `CallState` contain no Force-specific paired effect/result occurrences, mapping from the wrapped occurrence to those two paths, or source-owned Force enter/leave world operation. `Comp.expose` can store a pair, but no source constructor or derivation supplies the pair for forcing a wrapped thunk.

**TODO owner:** Luna, source/View metadata producer and Call representation owner. **First missing evidence:** the source-owned constructor/consumer contract for Force of a View-wrapped thunk, supplying distinct `force.effect` and `force.result` occurrence data, their mapping from the wrapped value's observation, and the specified event-time world operations. **Falsifier:** the actual source producer and consumer show those two occurrences and operations are derivable from existing fields by a unique stated rule; otherwise the obstruction remains. Do not assign S/C or claim the raw/typed seam is frozen until this input is resolved in an authorized contract/lease update.

This leaves the source domain unchanged and preserves original Call order, result consumers, Req/Fail intent, world parameters, and literal suffix fields. No cleanup or observation policy was added. The existing Call A/B quantifiers and parent claims remain unchanged and OPEN.

## Evidence reused and rejected

- Reused r8 outcome `tasks/agent-loop/sprints/lean-complete-call-20261025-r8-outcome.md` (SHA-256 `83961c24d5c87e49248475180287272ae21066671bbcf3164e0cdd68037f4a12`): exact first `CoreSyntax.lean` diagnostics and static embedded-Original/View-force successor omissions.
- Reused governing source rules: raw Force and malformed-operation Bad (`docs/yulang-operational-type-safety-ja.tex`, lines 303–333), Call order (`362–400`), failure/Bad distinction (`490–493`), and Force/View ports (`1245`, `1532`). These are semantic inputs, not a proof of source reachability.
- Rejected the r8 candidate as an accepted dependency: its first module check failed before any dependent module, proof, or review ran. No Simple-sub bypass or r8 unissued proof grant was reused.

## Artifact hashes

Changed leased artifacts:

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |

Direct pinned dependencies observed before these edits:

| Path | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | `9a48a5f2ef15eb947478757e0fa74457579183ccdb90abf2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Exact lease disposition:

| Leased path | Disposition |
|---|---|
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | changed; hash above |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | untouched; SHA-256 `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | untouched; SHA-256 `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | changed; hash above |
| `notes/theory/lean/YulangClosure/ControlTyping.lean` | untouched; SHA-256 `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `notes/theory/lean/YulangClosure/ControlComposition.lean` | untouched; SHA-256 `9a48a5f2ef15eb947478757e0fa74457579183ccdb90abf2518886590e33fc40` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | untouched; SHA-256 `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `notes/theory/lean/YulangClosure/CallExecution.lean` | not created; blocked by the exact source metadata obstruction above |
| `tasks/agent-loop/inbox/20261025-lean-call-execution-implementation-r9.md` | this frozen revision 1 handoff |

Checks: none run, as assigned. The r8 diagnostics remain historical evidence only; they do not verify this revision. Independent review: NOT RUN. S/C seam: NOT FROZEN.

Next in-scope step: Luna resolves the source metadata TODO or records it as an exact open premise, then decides whether a versioned authority/lease change is needed before any further implementation or proof dispatch.

Mutual TODO: Luna to provide the source-owned Force/View metadata evidence above. No proof worker TODOs are issued because no independent raw relation or typed/raw interface is frozen.

New paths: `tasks/agent-loop/inbox/20261025-lean-call-execution-implementation-r9.md` only. Disposable scratch: none. Commit-ready: no; pending source input, Luna checks, fresh review, and integration.

Write cessation receipt: immediately after hashing this revision 1 handoff, this worker stopped all writes. No descendant or scratch writer remains. S/C remain unissued under the frozen contract.
