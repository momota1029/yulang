# Independent review: allocation and retained-response execution

Review date: 2026-10-26 UTC. Reviewer: `/root/inference_frontier`, independent of this packet's author. Decision: **CLEAN for the declared component claim; no blocking, major, or minor findings.** The original parent safety/inference claims remain OPEN.

## Frozen inputs and review method

The following SHA-256 values were recomputed from the files read for this review and matched the assigned freeze:

| Input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/PaperAllocationExecution.lean` | `d5cd9f4499ec0c6e67e73a9444634671e43b507368c418b1d9ecec7fd57f0aa4` |
| `tasks/agent-loop/inbox/20261026-proof-advance-paper-allocation.md` | `5fd6a0ddb9698e09c995dcaeb4759c9c3c06a01c8bb4f500ebf4a95dc5918cf3` |
| isolated `complete-audit.log` | `06da09ea0af9ca80ee351bb3a9cfea1dd8c9969b7b9c6036665f89184221c9a0` |
| isolated `input-hashes.json` | `f1c4968769dffd28811b00fc0ea5bcbe46adc063c2e9336b6076f9a68a1362fb` |
| isolated `project/AuditPaperAllocation.lean` | `bf71818e43050d8679c86a41ea0a97cdb714b6b6122b634fc5b5f92b311089b1` |
| isolated `axioms.json` | `18e9346382ace1d552adb1a67c57a7768bcb61c5b7f2d9ef1b2bb477effc7878` |
| isolated `public-audit.log` | `9a9fa924bbe42c02d576c9e0a4887714cd2f0c98d807f7f1968226d9acdb493c` |
| isolated `final-build.log` | `5744d75ce15b3ec62787f7f20fb29ae022234aa2ac0b137e2df4e18df7cc18d2` |

The isolated evidence directory is `/workspace/scratch/f98087c7ac1a/paper-allocation/`. I recursively enumerated the actual local import closure from `PaperAllocationExecution`; it is exactly the 22 entries in the frozen input manifest, with no missing or extra local module. Every recorded input SHA matches both the repository file and its isolated project copy. I inspected the retained audit program, full theorem-block structure, theorem types relevant to the claims, all collected axiom results, warning/error summary, source correspondence, constructor definitions, and proof bodies. No Lean/Lake rerun was warranted by a concrete gap, and none was run. This is an independent source-and-retained-evidence review, not a second checker execution.

## Findings by critical obligation

### 1. The history does not contain the desired invariant as an assumption

`History` fixes one declaration table `d`, binder, type environment `e`, and initial graph/heap/state. Its `initial` constructor has the literal initial state and an empty saved list. `internal` requires an actual successful `PaperExtendedExecution.controlStep`. `allocation` requires a source-context `BlockTyped`, `TermSubstitutionTyped`, unique IDs, and freshness against the current graph and heap. Its result graph and heap are the actual `formals block ++ g` and `allocate block rho heap`, and its state and saved list are unchanged.

Neither final state typing, final heap typing, final saved typing, nor a preservation law is a `History` constructor premise. `history_preservation` derives these from the initial `StateTyped` and `HeapPayloadTyped`, independently typed table bodies, and the actual history. This discharges a real composition obligation rather than renaming a final typing premise.

### 2. Save and response cannot move an arbitrary current state to a packet

Both `save` and `response` require the previous history's actual state to be exactly `packet.state`. Saving leaves that state unchanged and records the same packet. A response uses the same packet's continuation and requires `PaperValueTyped d g e response packet.operation.responseType` at the current graph. The response equation unfolds to the unchanged executor's exposed-request interface.

`saved_request_components` inverts the actual request typing and eliminates the operation-instance equality. Its payload and continuation types are the fields of that same stored operation instance, not an unrelated newly chosen instance. The record stores only operation, payload, response binder and body: no save-time graph/heap/world or saved typing certificate is restored.

### 3. Existing heap values, bodies, and observations are preserved exactly

`HeapLookupPreserved` preserves each successful old lookup with the same literal payload. Allocation uses `FreshHeap.heap_old_success` and current-heap freshness; repeated histories compose this exact equality and establish that the final heap is a prefix extension of the initial heap. This is stronger than retaining merely the reference type or existence of a lookup.

The observation transport proofs cover all three actual observation constructors: successful graph read, type beta, and the type-application function context. `ObservationTrace` transport is induction over the supplied finite trace. The saved record itself is carried literally in all history constructors; graph weakening changes its typing derivation, not its body, payload, or operation.

`observedForce` requires a supplied observation on the current heap ending in the actual `.delay body`. Its preservation invokes the existing heap-observation bridge and real Force/Delay control equation. It is an auxiliary evidence constructor; it is not misrepresented as a successful partial-executor transition directly from the unobserved graph reference.

### 4. Allocation and body typing use the actual source-context premises

`allocation_body` consumes the existing `FreshHeap.finite_allocation`, the same `graphFormalReplacements` used for allocated RHSs, graph weakening, and the existing term-substitution typing theorem. Its inputs give body typing under the old graph with recursive formals prefixed to the source term environment and stack typing under the old graph. It derives both the public substitution function's successful result and the new graph's state typing, with unchanged declaration table, target term environment, stack and result type.

`allocated_body_history` feeds that derived allocated state/heap into history preservation. It does not take initial allocated-state typing, final state typing, or new-graph typing as independent hypotheses. The source-to-de-Bruijn ordering and original recursive constructor are still explicit missing bridges; the handoff accurately says so.

### 5. Retained replay is a real response interface, with an honest branching boundary

`saved_response_prefix` and `saved_response_history` recover a saved packet's typing from membership in the proved history invariant, use a current-graph typed response, and establish the actual `responseStep` equation. A later branch begins at `packet.resume response` with the current graph/heap. Its preservation retains all original packets as well as newly saved packets under the final graph.

The branch is a separate invocation of the retained request. The theorem does not assert a scheduler edge from an unrelated previous final state to that request. This boundary is explicit in the module and handoff and is appropriate for the supplied component claim; it would be a scope error to reinterpret the result as one continuous operational trajectory containing such a jump.

`fresh_response_replay` is non-vacuous: it constructs a save, fresh node 10 containing delayed true, a response using node 10, actual response substitution, another allocation of node 20 containing delayed false, and an observation/force of the unchanged old node. It then invokes the same saved packet with node 20 and proves the false result through a separate actual substitution/observation branch. The second invocation uses the first history's retained packet membership and the general replay theorem. `example_response_requires_extension` proves that node 20 cannot have its required type in the empty save-time graph but does have it in the current graph. No final typing, postulated observation, future step, or arbitrary result is an input to this example.

## Source authority and omitted cases

The following source hashes were independently recomputed and matched the handoff:

| Source | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md` | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| `notes/theory/2026-10-24-corrected-machine-simulation.md` | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| `docs/yulang-whole-proof-closure-ja.md` | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |

I compared the immutable heap clauses at operational lines 264–269; simultaneous source-rec allocation at 324–326 and 980–991; unchanged retained continuation at 458–464; and finite prefixes, fresh external nodes and repeated responses at 1140–1163. I also compared corrected core V1(d), V4, V5(2,6,8), V6 and corrected-machine section 4.2. The formal component matches the value-typing/preservation portion. It does not claim the manuscript's guarded graph judgment, progress, full control/world simulation, or whole-language safety.

## Retained checker/audit evidence

The audit enumerates every theorem constant whose originating module is `YulangClosure.PaperAllocationExecution`, including generated theorem constants, rejects project axioms in that module, checks all 24 required public roots, prints full types and axioms, and rejects collected axioms outside the standard whitelist. I checked all 50 BEGIN/END blocks: each contains its matching theorem type and axiom result, and all names agree with `axioms.json`.

There are 50 theorem constants: 24 public roots and 26 generated theorems. The log-derived counts exactly match the JSON: 40 use `[propext, Quot.sound]`, 3 use `[propext]`, and 7 use no axioms. No `Classical.choice`, project axiom, `sorryAx`, or native/trusted evaluation axiom occurs in those results. The retained final build log has no error and no warning from the new module; its 658 warnings are confined to the seven unchanged dependencies listed in the producer receipt. The review relies on the producer's retained successful checker execution and the matching frozen inputs; it does not claim an independently rerun kernel check.

## Parent integration and remaining obligations

The primary may integrate this frozen module and its audit roots after review. The root import/audit integration was outside this producer's and reviewer's leases, so the default root build does not yet by itself establish coverage of the new module. Parent validation must cover the integrated import surface without broadening the theorem claims.

The original obligations remain open: source-rec formation and source/formal ordering correspondence; represented recursive typing and execution; guarded heap construction and finite observation existence/termination; progress and Bad exclusion; nonempty-owner/seven-frame resumption and corrected current-world/lifetime/release evidence; remaining source constructors and native correspondence; and the original inference soundness, principality/coverage, naturalness, termination and effect-inclusion claims. `BodiesTyped`, initial heap/state typing, fresh source-directed allocations, actual successful executor steps, current-instance typed responses and supplied finite observations remain genuine premises of the general theorem. They are not hidden in an asserted final invariant.

## Review write lease and stop receipt

This review wrote only `tasks/agent-loop/inbox/20261026-proof-advance-paper-allocation-review.md`. It made no proof repair, Git operation, shared-record edit, arithmetic edit, checker/cache/configuration change, or descendant delegation. All review tools were read-only except creation of this receipt. No process was launched that remains running. Review writes stop after this file creation; its SHA-256 is returned to the primary separately.

Receipt completed at 2026-10-26 00:50:01 UTC.
