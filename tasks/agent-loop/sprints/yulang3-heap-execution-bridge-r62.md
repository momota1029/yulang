# Sprint YULANG3-HEAP-EXECUTION-BRIDGE-20261026/r62

Status: PRIMARY-AUTHORIZED CONSTRUCTION CANDIDATE. Work starts only after this contract and updated current state are committed. Branch: `yulang3`. Baseline: `408c1c6a8276ca74f0760cb3d71dd11e704826c0`. UTC origin: `2026-10-25T23:24:33Z`.

## Fixed parent goal

Advance the paper's execution type-safety claim (`docs/yulang-operational-type-safety-ja.tex`, §§3 and 3.8, especially :252–326, :488–500, :981–1010, :1139–1165) by connecting the accepted finite heap-observation lemma to one actual Force/Delay transition of the accepted connected executor. Preserve all original quantifiers and source domain. This is an auxiliary represented proof; it does not prove guardedness, termination, all source-generated heap realizations, progress, or whole-language safety.

R61 accepted `PaperExtendedExecution.preservation` only under `BodiesTyped d`, initial state typing and actual successful `controlStep`; its finite interaction theorem additionally requires a represented trace and `ProtocolTyped`. R29 accepted `FreshHeap.finite_allocation` only for finite `HeapPayloadTyped`. R58 accepted represented type-beta preservation only. R59 supplied a frozen candidate `PaperHeapObservation.lean` with worker build/audit evidence but no accepted primary verification because its primary output capture failed. R62 must rebase/copy that exact candidate into a fresh workspace, pin it against the current baseline, and independently build/audit it before using it. Never modify or replace the R59 artifact.

The connected executor's `State` does not contain a heap. R62 may couple an explicit heap and its `HeapPayloadTyped` premise to a represented state transition through a finite observation prefix. It must state this as a coupled theorem with the exact same heap, graph, declaration, type environment and result type throughout. It cannot claim the executor performs graph lookup, carry an implicit heap through `controlStep`, or establish Rust/paper heap correspondence.

## Measurable outcome and exact theorem target

Produce a reviewed candidate module `PaperHeapExecution.lean` that consumes the exact R29 `finite_allocation`, the R59 finite observation of an operand to `.delay body`, and the R61 connected `PaperExtendedExecution.controlStep` Force/Delay result. The central theorem must retain:

- one concrete block `b`, old graph/heap, substitution `rho`, and the exact allocation `allocate b rho heap`;
- the exact extended graph `formals b ++ old`, target type environment, and `HeapPayloadTyped` result of that same allocation;
- the same typed state/head/stack/final result before and after the actual finite observation prefix;
- the actual successful connected `controlStep` on the observed `.force (.delay body)` state and the existing `PaperExtendedExecution.preservation` result;
- the same shared witnesses across allocation, observation and execution. No independently supplied allocated heap, body, type, state, or result witness may replace the actual values.

Use or restate the smallest useful theorem from `PaperHeapObservation.force_observation_preservation` / `allocated_force_observation`. Show a finite observation prefix plus the actual Force/Delay transition yields a typed successor in the connected control machine and its represented erasure/step relation, with the exact printed premises. If the exact theorem cannot be proved without adding the desired conclusion as a premise or changing an accepted relation, stop with the first Lean counterexample/diagnostic and preserve it. Two diagnosed construction failures maximum.

Candidate public theorem(s) must be independently enumerated and audited with complete printed types and axiom reports. A successful result moves the original executor parent by one exact conditional force-path composition; it does not close that parent.

## Authority, non-goals and falsifiers

No semantic change, source restriction, Rust/compiler edit, root import, question, dependency update, or production authority. No `sorry`, `admit`, project axioms, `debug.skipKernelTC`, `native_decide`, or checker bypass. Do not claim `BodiesTyped` for all generated tables. R23 `R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1`, guard preservation, constructor reachability, source/native heap representation, source formal order, full executor coverage, original inference A/B and production remain OPEN. Preserve R59's self-alias observation loop as a counterexample to deriving termination/guardedness from `HeapPayloadTyped` alone. Source lane's immutable native-cell identification is blocked and `NO_SAFE_CODE_SLICE` remains in force.

Falsifiers: heap or graph witness changes across stages; lookup bypasses actual first-match semantics; type-beta fires outside its accepted redex/function position; `controlStep` does not actually select Force/Delay; fallback bypasses old successful-control priority; stack or final result changes; theorem hides the target result in a premise; or any R29/R58/R61 direct input pin differs.

## Frozen inputs

Baseline commit `408c1c6a8276ca74f0760cb3d71dd11e704826c0` authenticates all repository bytes. The following are individually pinned because they directly govern or occur in the dependency cone; every pin and the exact R59 artifact copy must be checked before work and at freeze.

```text
f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258  notes/theory/lean/YulangClosure/DeclSubst.lean
58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1  notes/theory/lean/YulangClosure/PaperCombinedExecution.lean
71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e  notes/theory/lean/YulangClosure/PaperCoreControl.lean
6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144  notes/theory/lean/YulangClosure/PaperCoreStep.lean
568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a  notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean
313a550a550716e235e73690d238f1040838aeebd2cc0cf0b7753979ab6fe38d  notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
78f23b9e946b0259cdb63797ed226706112f71375a013e0b9cc8745ad5afe8b0  notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
fae64aa9a5c37572a3f654c403b7fb8ff7eb7adccaa4e3540fff85e61ce84819  notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7  notes/theory/lean/YulangClosure/PaperExtendedExecution.lean
7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925  notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean
2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0  notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean
5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935  notes/theory/lean/YulangClosure/PaperResumeExecution.lean
3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792  notes/theory/lean/YulangClosure/PaperTemplateExecution.lean
42d7f46d992e715443a7116066b51ae1748849718f6c4e716d9169ea069059d9  notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d  notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean
60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556  notes/theory/lean/YulangClosure/PaperTypeApplicationPreservation.lean
0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8  notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean
29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13  notes/theory/lean/YulangClosure/PaperTypeFormation.lean
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861  notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean
a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b  docs/yulang-operational-type-safety-ja.tex
ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c  notes/theory/lean/lean-toolchain
2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194  notes/theory/lean/lakefile.toml
058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3  notes/theory/lean/lake-manifest.json
0a31542efa94f2a6aff13bcbb1ef34b69c442d5027bcca3c0d8c40f8e061ac7a  notes/theory/lean/README.md
19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f  /tmp/yulang-r59-heap-observation/notes/theory/lean/YulangClosure/PaperHeapObservation.lean
07327b553d9f51e1e5dcfc2e352cc72953c6e7bb943d819777ce4d9967f98aed  /tmp/yulang-r59-heap-observation/notes/theory/lean/.lake/R59Audit.lean
a115016535753182240188232262e8f19613fbf6e8784137048bd5f632e8f9bf  tasks/agent-loop/inbox/paper-heap-observation-r59.md
b3847d011403975667bf2cbddb897c0934bf71912627d9200c035e51f946982a  tasks/agent-loop/inbox/paper-heap-observation-r59-worker-checks.txt
b7976c6ae7a8a276b4a59e479b71bc0bdec20696a974dff367492e02541ac5f6  tasks/agent-loop/inbox/paper-heap-observation-r59-source.md
1859d9a005b9bfbff2fd98de5bf7e2d984b48f890cd42ca37b5909f5439d8c70  tasks/agent-loop/sprints/paper-fresh-heap-allocation-r29-r1.md
d6523cba7a7b68871f56d359168f37d83bef27fa8ae2081777094e794b3cbea7  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-adjudication.md
2611315d23588db8b02f8644bc9d8c495e388566659037e59f3b3501b49e25b1  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-review.md
5c693fedf8e98a471bdf5f6712e49ca0146a0f97957acfb946732fc54dc5f60c  tasks/agent-loop/sprints/paper-type-beta-execution-r58-outcome.md
059cb2de4cdc8c1e746628f485f445671a927c13f82cef8bbf8defb6c0bbe39c  tasks/agent-loop/inbox/paper-type-beta-r58-review.md
291bafc8a58846c4be9c1e41c8d62e4c3df18275ab09dfbd24fc99bfbd9a3c90  tasks/agent-loop/inbox/yulang3-execution-proof-reconciliation-r61-primary.md
24514b97e01284969123935ec3d5ec81498a0619cbecfaca8448051db36ed747  tasks/agent-loop/inbox/yulang3-execution-proof-reconciliation-r61-review.md
29f7b0fd7fbbfe17fc3a0e0bcb5e00a7e4801c7961427d38fcc4a9b5314181e8  tasks/agent-loop/sprints/yulang3-execution-proof-reconciliation-r61-outcome.md
```

The 20 Lean modules above are the recursive import closure of the R59 observation source and R61 connected executor. `PaperHeapObservation.lean` and `R59Audit.lean` above are external-to-baseline frozen R59 artifacts; their worker checks, R59 source handoff, R29/R58 decisions and R61 adjudication preserve provenance. Do not trust old R59 dependency pins as current pins.

## Lanes, leases and evidence

One registered `lean_prover` `/root/r62_heap_execution_proof`, no descendants, owns only these paths in isolated workspace `/tmp/yulang-r62-heap-execution/proof`:
`R62-isolated/PaperHeapObservation.lean` (byte-preserved copy), `R62-isolated/PaperHeapExecution.lean`, `R62-isolated/R62Audit.lean`, `R62-isolated/run_call.py`, `R62-isolated/process-manifest.json`, `R62-isolated/proof-checks.txt`, `R62-isolated/lake-build`, `R62-isolated/call-01.stdout/.stderr` through `call-10.stdout/.stderr`, and `tasks/agent-loop/inbox/paper-heap-execution-r62.md`. No shared/root/Rust/spec/question writes or Git. One heavy Lean process at a time.

Primary `/root` owns current state, this contract, detached verification workspace `/tmp/yulang-r62-heap-execution/primary`, primary receipt `tasks/agent-loop/inbox/paper-heap-execution-r62-primary.md`, its runner/manifest/cache/call-01..04 stdout/stderr, final claim reconciliation, outcome `tasks/agent-loop/sprints/yulang3-heap-execution-bridge-r62-outcome.md`, Git and integration. Fresh non-author `compiler_referee` after primary freeze owns only `tasks/agent-loop/inbox/paper-heap-execution-r62-review.md`; 180 seconds, zero checker calls. Reviewer is read-only; primary preserves the returned receipt verbatim and labels authorship.

The primary independently checks fresh pins, resolved Lake/Lean, worker cessation and exact source hashes before primary calls. Use durable pre-call `STARTED` records, exact literal argv/cwd/environment, monotonic times, exit/signal/timeout, complete stdout/stderr and SHA-256. Preserve failed output. Do not retroactively rewrite worker or process evidence. Pin or capture mismatch stops the packet.

## Ordered work and budgets

Sprint active-work cap: 1800 seconds. Proof lane 900 seconds / 10 literal calls / 150 checker seconds. Primary 720 seconds / 4 literal calls / 150 checker seconds. Fresh reviewer 180 seconds / zero checker calls. Checker calls are serial, at most 120 seconds each, one thread, Lean `-j1 -M1024`; no more than one heavy build. No carryover. Two diagnosed construction failures, first failed primary call, any cap uncertainty or writer uncertainty stops the affected lane.

Proof lane: verify native versions; fresh focused build of R59 observation plus the new R62 module; at most two diagnostic/construction iterations; freeze source/audit/checks and one handoff. Audit every public declaration in both candidate modules, including exact kinds, full types and all axioms. Scan the complete changed dependency cone for holes/bypasses. Do not claim success from the prior R59 worker audit.

Primary after proof STOP: independently verify baseline and fresh pins; run resolved Lake `--version`, `env lean --version`, focused build of the exact candidate modules, and complete audit as its four calls. Run the bundled `validate_audit` on complete captured output using independently enumerated declaration names. Check the actual theorem quantifiers/hypotheses, exact heap/graph/state/result witness reuse, Force/Delay branch priority, and all excluded parent claims. Stop on first failure; no retry.

Only after primary freeze start fresh review. CLEAN review and Luna adjudication are required before integration. Integrate the new module and root import only if those gates pass, then validate root delta and full outbound range and non-forced push. A useful reviewed auxiliary theorem can be preserved without root import if integration exceeds the fixed envelope; parent gates stay OPEN.

No tests, Cargo, runtime probes, network, full default build, `lake update`, or source/compiler changes. R62 has no implementation lane: the actual Rust owners in the frozen R59 source receipt show no safe direct code slice.
