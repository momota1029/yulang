# R62 primary verification receipt — revision 1

Disposition: PRIMARY VERIFIED; fresh independent review pending. No semantic or process failure was found. The bounded conditional represented result is suitable for review; no integration or parent closure is claimed before that review and Luna adjudication.

Sprint `YULANG3-HEAP-EXECUTION-BRIDGE-20261026/r62`, contract SHA-256 `9de3e01ef995fef5bc00448e7c90cfdcc0bbd5461894af8bc94f546996832f0b`, baseline `408c1c6a8276ca74f0760cb3d71dd11e704826c0`, branch `yulang3`. Frozen worker handoff SHA-256 `6356133fa6473271c17e79a1d3b04dbe354b97c076af1ef37217c30b3f8af5b1`.

## Provenance and independent primary execution

After worker STOP, primary independently checked all 37 contract input pins: 0 mismatches. The exact candidate copies in `/tmp/yulang-r62-heap-execution/primary` match `PaperHeapObservation.lean` SHA-256 `19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f` and `PaperHeapExecution.lean` SHA-256 `46a9e8e76f5745cbaffc40b7bb95ff37064941a84532fa5edc07672ddad3d59f`. The worker's audit, checks, runner and manifest match the frozen hashes in the handoff. All five worker captures match their recorded lengths and hashes; all five process groups were independently observed absent. No worker process or writer remains.

Primary used detached baseline workspace `/tmp/yulang-r62-heap-execution/primary`. Resolved native Lake `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`; Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)`, Lean reports `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Primary used the explicit environment recorded in `/tmp/yulang-r62-heap-execution/primary/process-manifest.json` (manifest SHA-256 `043c68682a116350b6624a343dfd3704fa3ceec347e5d0923c14e2ca7908004a`), durable per-call STARTED/COMPLETE records and exclusive full stdout/stderr captures. Four calls, all exit 0, no timeout or signal:

1. `lake --version` — 0.069726972s; stdout 53 bytes, SHA-256 `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`; empty stderr.
2. `lake env lean --version` — 0.121120401s; stdout 106 bytes, SHA-256 `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`; empty stderr.
3. `lake --no-cache build +YulangClosure.PaperHeapObservation +YulangClosure.PaperHeapExecution` — 40.723034623s; stdout 456,098 bytes, SHA-256 `d431e9c9e7676282f5104e95b71b8f5165103036b0b247a143b0e2da90c3875e`; empty stderr.
4. `lake --no-cache env lean -j1 -M1024 --root=. .lake/R62Audit.lean` — 0.709687485s; stdout 61,986 bytes, SHA-256 `b89b6764d91d88849f94a68287e84f3770f39aefb597e9257fc889a2b530abea`; empty stderr.

The complete stdout/stderr and manifest remain at the primary scratch paths above. Primary checker time: 41.623569481s of 150s. No tests, Cargo, runtime probes, network or full default build ran.

## Independent audit and semantic checks

Applied the repository's unchanged bundled `validate_audit` to the complete primary call-04 capture with all 40 exact names. It passed. A separate static pass checked all 80 ordered BEGIN/END markers, 40 unique names, module totals 37 + 3, completion marker `40/40`, and all 13 public theorem names/kinds. Complete printed types and `#print axioms` reports are retained in call-04.stdout. Results: 18 declarations use no axioms, 3 use only `propext`, and 19 use `propext, Quot.sound`; all three new public theorems use only `propext, Quot.sound`. No `Classical.choice`, `sorryAx`, project axiom, `native_decide` or `debug.skipKernelTC` appears.

Primary recursively traversed the actual import cone from both modules and found exactly 21 Lean sources: the 19 individually pinned repository modules plus the two frozen candidates. Hashes of all 19 repository modules match the contract. A source scan found no `sorry`, `admit`, project axiom, `native_decide` or `debug.skipKernelTC` in the cone. This confirms the worker's count discrepancy: contract prose says “20 Lean modules,” while its exact pinned source list has 19 repository modules and the recursive cone has 21 after adding the two candidates. No unpinned internal import exists. This is retained as a contract arithmetic/documentation discrepancy; neither the frozen contract nor evidence was rewritten.

The exact three R62 theorem types are those printed in full in call-04.stdout and source signatures in the frozen handoff:

- `force_delay_erased_step` proves represented erasure `ComputationStep` under the unchanged let stack.
- `observed_force_control` retains `BodiesTyped d`, `HeapPayloadTyped d g e heap`, initial `StateTyped` for `force source`, the actual finite `ObservationTrace heap source (.delay body)`, and actual successful `controlStep` equality. It concludes same-context typing before/after, erased body typing, `ControlStepEvidence` and represented erasure step.
- `allocated_force_control` retains R29 uniqueness, old-graph and old-heap freshness, typed substitution/block/old heap, `BodiesTyped`, initial state typing under exactly `formals b ++ old`, and an actual observation trace on exactly `allocate b rho heap`. It obtains `finite_allocation` rather than assuming its result, then uses that same allocated heap's payload typing and same graph/target/state/body/stack/result in the Force/Delay transition and preservation. It returns `GraphLookupPreserved`, allocated heap payload typing, the exact successful transition, successor typing, erased typing, evidence and erasure step. No independent result/state/body/heap witness appears.

Source review checked `PaperFreshHeapAllocation.allocate/finite_allocation`, R59 `lookupHeap` first-match observation and recursive type-application step, R61 `controlStep`, `controlStep_force_delay`, `preservation`, `ControlStepEvidence` and `ComputationStep`. The Force/Delay equation reaches the existing successful control path through R61's extension lemmas; it does not bypass old-success priority. The heap remains an explicit coupled parameter because `State` contains only head and stack. The operand observation remains separate from executor transition; no claim says executor performs heap lookup. The self-alias witness still permits a payload-typed literal observation loop and gives no guard or termination result.

## Remaining limits and handoff

R62 is one conditional represented force-path composition toward the original execution-safety induction. Guard preservation, finite constructor observation from source typing, source-generated `BodiesTyped`, R23 caller-context embedding, source/native immutable-heap versus mutable-cell correspondence, constructor reachability, all other executor cases, whole-language preservation, inference A/B, and production remain OPEN. R59 remains FAILED as its own primary result; its exact source candidate was rechecked in R62 without rewriting R59 evidence.

Proof worker: `425.992/900s`, 5/10 calls, 48.399259153/150 checker seconds, one preserved audit-format failure and zero proof-construction failures. Primary: no failed checker calls, four calls and 41.623569481/150 checker seconds. The sprint's contract-origin-to-primary-freeze elapsed interval is within the 720s primary envelope. Reviewer has a separate 180s/zero-checker reservation. Fresh non-author `compiler_referee` review is the next gate. No root import or candidate integration has occurred. All primary and worker writes are stopped on freeze.
