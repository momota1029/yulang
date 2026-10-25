# R — Force runtime normal-return constructor trace, revision 1

Outcome: **bounded source characterization; `force_normal_leave_producer_correspondence` NOT ESTABLISHED**. The actual playground runtime preserves the body's returned receiving view at completion. It does not construct the generic source Force result transport. This is a concrete implementation/export gap, not a counterexample to the accepted source semantics or a choice of replacement semantics. O-NORM, O-RESULT and the original parent remain **OPEN**. Independent review: **PENDING**.

## Packet and frozen dependencies

- Sprint: `FORCE-PRODUCER-EXPORT-TRACE-20261025/r1`; assignment R; revision 1.
- Worker: `/root/force_runtime_return_trace_r9`; delegator: `/root`. Launch evidence is this session's NEW_TASK with the exact R packet. Requested/observed model and effort were not supplied by that receipt: **UNKNOWN/UNKNOWN**. No model policy change, coauthor or descendant.
- Baseline: `9b945b0bb175e8e0919d388dc720babbdf0c2464`, inherited from Luna, not independently verified. No Git command.
- Sole leased and changed path: `tasks/agent-loop/inbox/20261025-force-runtime-return-trace.md`.

All pins below matched before reliance and again immediately before this report was written:

| Input | SHA-256 |
|---|---|
| `tasks/agent-loop/sprints/force-producer-export-trace-20261025-r1.md` | `d2765f1aabb1b2f81ff65da8a2eae6a3780cefe73f4aa2da639534364c655f7b` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| r8 R, `tasks/agent-loop/inbox/20261025-force-result-relation.md` | `9972764cc9b750fa5fc218b1c571fd29b58ffb46f6a7bc0e566aaaa4e1bfb430` |
| r8 outcome, `tasks/agent-loop/sprints/force-source-realization-20261025-r8-outcome.md` | `4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |

The r8 outcome was located by the current snapshot; an initial hash command used a nonexistent `outcomes/20261025-force-packet-result-realization-r8.md` path. No claim relies on that failed lookup. The correct path above matched the supplied hash. The outcome's accepted status is supplied by the r9 contract; the r8 R author report still says review pending historically.

Governing paper sections: bare Force at 303–307; expose at 485–492; refined input and finite templates at 1180–1209; decoration at 1231–1252; graph generation at 1517–1542. The selected source meaning and original all-latent scope are preserved. Ret identity at 1528 is reused. No mapop is traversed or equation derived here, so the corrected mapop report is not used as a premise.

## Method, hypotheses and claim class

Method: follow actual Rust constructors and their callers through inert argument formation, receiving entry/read, execution, normal return, suspension and replay. This changes the r8 paper-level investigation's input to the runtime owners. It does not supply another checker with assumed Force transitions.

H1: the machine state and its handles were produced by the inspected constructors; referenced arenas are valid. H2: the delayed evaluation reaches `State::Return(r)` with `Frame::RootCompReturn { execution: e }` on top. H3: `r.view` matches `r.value` and the top executing view equals all three fields of `e`. Under H1–H3, the inspected branch sets `State::Return(r)` with every `ReceivedValue` field unchanged and removes exactly `e` from `executing_views`. This is an established local code fact by branch inversion, **not** a theorem that every retained refined source Force reaches that branch or has the desired packet relation.

The original proposition additionally quantifies over the actual interpreted operand, body result and all finite typed result/component/latent suffixes, including recursive, nominal, aliased, instantiated and captured instances. Those coordinates are not supplied merely by H1–H3. No hypothesis identifying a runtime image with the paper's entire packet or `force.result` subtree is accepted here.

## Constructor-to-consumer trace

Locations below are in `tools/inference-playground/src/runtime/` at the pins above.

| Stage | Actual constructor/caller and retained data | Consequence and boundary |
|---|---|---|
| Code formation | `program.rs:538–574,598–604,767–805,819–857,972–988`: `from_hir` calls `from_hir_with_roots`, retrieves local source, makes labels and `Code { site, instruction }`. Parameter annotations with outer effects select Execute/Computation (`718–739,825–833`); conflicting supplied consumption evidence is rejected (`794–800`). | Static `SourceSite` retains source root, occurrence and range (`160–164`), distinct from dynamic handles. The instruction enum (`254–314`) contains implicit Name execution and Apply, not a generic decorated Force with operand/result path templates. This is the actual runtime's source envelope, not a replacement source grammar. |
| Lambda retention | `program.rs:834–850`; `machine.rs:864–885,183–196`: evaluation saves parameter, role, schemas, body label and lexical environment in an executable closure. | Captured values remain reachable through environment/cell handles. `ExecutableValue::Delay` itself has only `code` and `environment`. |
| Inert argument | `machine.rs:888–898,1181–1198`: Apply first evaluates the callee. Its Callee return allocates a fresh Computation value with `Delay { code: argument, environment }`, then calls `direct_formal_root` and `receiving.delay`. | `allocate` uses the next value-arena index and stores the Apply site (`2701–2715`). No argument prefix is evaluated here. Delay body code retains its own static site separately. The fresh delay is not the body result. |
| Inherited image | `machine.rs:2028–2040`; `receiving.rs:206–223`: inheritance recognizes only an exact argument label whose instruction is a direct Parameter Name with Execute and a Computation cell. `delay` makes a fresh Ordinary view, copying that view's `image` and `unknown`; otherwise `(None,true)`. | It copies a root-image dependency, not a path correspondence. It does not chase `Forward`, aliases or arbitrary expression structure here. Captures may still be present in the environment; failure of this shortcut does not mean their metadata is absent. |
| Computation receipt | `machine.rs:1280–1329`: a fresh invocation is minted, RootComp entry optionally prepends a boundary/image, a formal receipt is retained, and the delay is bound as a Computation. `receiving.rs:224–280` implements those arenas. | Entry keeps the actual delay value and inherited image chain. The lambda body executes with that binding; the delayed argument still waits. |
| Actual force-like use | A Name lookup calls `dispatch_name` then `consume` (`machine.rs:781–842`). `consume` authenticates view/value, makes the actual read receipt, checks Computation interface and, only if `has_root(view)`, allocates an execution and pushes RootCompReturn (`2469–2495`). `execute_with_substitution` evaluates the saved code in the substituted saved environment (`2548–2557`). | Operand value/view and read site are actual constructor inputs. `ExecutionView` stores only view, receipt, occurrence (`receiving.rs:113–117`); `execution` allocates a fresh occurrence (`429–457`). With no root image, execution proceeds without this view-completion frame. |
| Normal leave | `machine.rs:1087–1095,2042–2052`: RootCompReturn validates returned view/value, pops and checks the exact active execution, and returns `received` unchanged. | No fresh value, result view, receipt, Flow row, result schema or transport domain/image is allocated here. The frame (`238–240`) retains only the execution. Its receipt's slot can retain the read site, but no typed result mapping is consumed at leave. |
| Caller completion | `machine.rs:1426–1436`: ReceiverReturn closes the invocation and copies body result value, view and dispatch, setting interface to Value. `1000–1003`: a frameless return exposes only the value handle as Completed. | Local RootComp completion and caller completion preserve actual result provenance at the handle/view level. External Completed is not an export of the complete packet relation. |

Value entry is a distinct path: `machine.rs:1285–1296` pushes ValueEntry and executes the inert argument directly; `1447–1489` then binds its actual returned value/view. Primitives and continuation arguments likewise execute the delay directly (`1201–1222`). Operation-result consumption executes the returned request carrier (`1141–1149`). These calls do not automatically acquire a generic Force result transport by sharing `execute`.

`dispatch` is orthogonal in this trace: `dispatch_name` changes only the dispatch field (`2617–2624`), and `substitute_environment` composes dictionary substitution in a new environment (`2606–2610`). RootCompReturn preserves dispatch verbatim. No claims about the internals of the called dispatch operations or whole-packet type instantiation follow. `dispatch.rs` was hashed, not behaviorally inspected; no additional Rust read outside the exact R set was needed.

## Source schemas, provenance and latent coverage

`RootCompSchema` really retains the original lambda and formal, including its annotation (`receiving.rs:17–56`). Its constructors check source-root ownership and presence of outer effects. The generalized constructor admits variables, holes, functions and tuples as well as the four primitive results. Thus this is **not a ground-result-only return path**. Its grant consumer, however, reads the formal's **outer concrete effect row** (`530–539`), authenticates actual receipts and traverses a linked boundary image (`554–599`). It does not interpret a result-path template. An annotation retained inside `formal` must not be confused with a derived transport for that annotation's entire result shape.

`View` contains value, optional image, unknown coverage and kind; each Image contains boundary and parent (`124–145`). There is no typed suffix coordinate or force.effect/force.result projection operation in these constructors. `unknown=true` preserves a lack of complete coverage knowledge; it is not permission, negative protection or an all-path provenance oracle.

Preserving the actual result is substantive: a returned closure still owns its saved executable/environment; tuples, variants and records retain their elements' exact `ReceivedValue`s (`machine.rs:124–140,1619–1675`); locals copy result view/dispatch into cells (`1543–1548`). RootCompReturn preserves these handles without traversing or executing latent bodies. Record projection itself has a restricted parent-image check (`receiving.rs:281–292`). These facts support actual-result retention within this representation; they neither enumerate nor prove the correspondence for every finite typed suffix, recursive nominal mapper, delayed shape or instantiated packet of the paper.

The callback path is narrower again. `CallbackResultSchema` permits only a Value formal shaped `() -> [E] int`, with a nonempty concrete result row and no row variables (`receiving.rs:60–101`). ValueEntry makes an authenticated CallbackEntry (`machine.rs:1447–1464`; `receiving.rs:300–335`). Only the direct parameter-name operation Apply with its declaration checks selects a callback use (`machine.rs:1358–1386`). `callback_use` makes its so-called result view **before** operation invocation, with the callback's existing value identity and inherited image (`receiving.rs:376–415`). It is not the eventual returned integer's view. OperationResultConsumer later starts that execution (`machine.rs:1141–1148`). CallbackResult is explicitly excluded from RootComp grant queries (`receiving.rs:558–561`); its own grant authenticates the entry/use/family chain (`604–637`). This positive certificate cannot be generalized to arbitrary Force normal-return metadata.

## Suspension and current resumer

Executing a Request creates a fresh event and observations from authentic currently executing views (`machine.rs:2559–2579`; `receiving.rs:462–480`). On propagation across RootCompReturn, the execution is ended and the original frame is saved (`machine.rs:2277–2281`). `capture_template` converts it to `TemplateNode::View { original }`, retains owner/handler structure, and publishes an immutable template (`1841–1910`; `continuation.rs:13–43`).

At replay, Owner nodes resolve the per-use control map, borrowing a live owner or minting a fresh invocation from the original descriptor; pending callback ValueEntry owners follow that map (`machine.rs:1932–1987`). A View node calls `execution(original.view, original.receipt)`, allocating a **fresh execution occurrence with the historical view and receipt**, then pushes its completion frame (`2010–2017`). Existing receipts, boundaries and result metadata are not renamed to the fresh owner by this step. Future observation authenticates that new execution; local grant separately tests current invocation activity (`receiving.rs:494–503`). This accounts for control reconstruction without inventing a current-resumer result packet equation.

Template Hole returns the supplied response unchanged (`machine.rs:1928–1930`). Ordinary continuation arguments are checked as primitive responses, with one exact OperationV1 function-response exception (`1028–1075`); selected handlers restrict payloads and captured response shapes (`2143–2180`). The separate host-write entry accepts only its authenticated saved continuation, creates a ground Unit response and enters the template (`599–654`); other unhandled operations have no host template here (`2321–2346`). These restrictions prevent treating the inspected replay machinery as coverage of all source continuations. On an eventual normal completion, the same RootCompReturn branch above preserves the eventual actual response/body result; it still adds no Force result correspondence.

## First missing edge and precise falsifier

The earliest missing **generic result producer** is at inert carrier/receiving formation (`machine.rs:1189–1198`, `receiving.rs:208–223`): no constructor here exports a relation from the actual operand's typed `force.result` subtree to the future body result. The consuming leave confirms the gap: its only extra input is `execution`, and it forwards the body's `ReceivedValue` without deriving result domains/images (`machine.rs:1087–1095`). The runtime owns an authentic root execution/image protocol, not the missing all-suffix source certificate. A fresh output occurrence is also not materialized by this leave; identifying the source output with the body result would require its own source correspondence argument.

For retained derivation D, actual operand t, actual body return r and output o, the missing evidence is an accepted normal-leave construction that binds those occurrences and computes its result transport on every typed suffix p, including latent descendants. If the intended law is r8's candidate

```text
Flow*'(x,a; o,p) <-> Flow*(x,a; r,p)
                       OR Flow*(x,a; t,force.result · p),
```

the runtime facts above establish neither its operand-result disjunct nor its reverse implication, domain, embedding or output allocation. This equation remains a verification target, **not a rule selected by this report**. Copying a single image during Delay formation cannot establish it. Returning r unchanged cannot establish that every source-authorized operand-result route is already represented in r. Conversely, missing runtime fields do not prove that the accepted source equation is false.

The smallest useful latent discriminator is a returned thunk result, with p = `force.effect` and operand suffix `force.result.force.effect`. The source owner must exhibit the accepted path/occurrence binding and show how the actual returned view carries it without observing the later thunk during the first Force. This is a symbolic discriminating obligation, not an executed experiment or an admitted counterexample. No profiles or routes were fabricated. Flattening this suffix, dropping an independently licensed operand-result route, adding an unrelated alias route, or resetting the actual return view to ground would falsify the corresponding intended law; none of these mutations was run.

Owner/handoff R9-R: source normal-leave authority is the paper's d/expose/Force construction (485–492,1244–1245,1531–1532); its runtime export/consumer owners are the formation and completion locations above. Required inputs are D, the consistent packet interpretation, actual operand and return occurrences, complete result template and suspension context. Required output is the source-selected packet relation plus a constructor-to-runtime realization with derived transport domains/images. **Falsifier of this gap report:** an existing accepted producer and actual consumer that bind those inputs and derive that output, rather than a test, image dependency, proposed/shadow record or callback-only grant. No such bridge was found in the inspected path.

Recommended next action: Luna assigns the generic Force normal-leave constructor/export obligation at these exact owners, with the source-selected result equation as input or as the precise authority item to resolve. A Lean specialization of RootComp image copying would leave the missing premise unchanged. This report grants no production edits or semantic change.

## Checks, limits, resources and STOP

Commands/checks: `cat`, `rg`/`rg --files`, numbered `sed` reads, `wc -l`, `sha256sum`, the sole-output nonexistence check, clock reads and one `apply_patch` creating this note. The initial broad policy/source batches were output-truncated; the relevant source, authority, receipt and policy clauses were reread in bounded batches. Source coverage is the constructors/callers and normal-return/suspension branches cited above, not whole-workspace exhaustiveness. Some adjoining test text was displayed incidentally; no test body supplies an argument here. No additional implementation files were read.

No independent executable oracle: Rust and the paper are distinct inspected artifacts, but the missing refinement between them is the subject of this report. The r8 report and this report share the paper and do not constitute independent semantic validation. No seeds/ranges, runtime enumeration, mutation execution, Lean, test, build, native/compiler execution, formatting, network, Git, scratch file, descendant or background task. General source admission, all typed paths, nominal/recursive realization, whole-packet specialization, inference, termination and source/native adequacy remain unverified. Req/Fail/Bad do not count as normal returns.

Resources: one source-only author, cap 1,200 seconds. First recorded clock after startup reads: `2026-10-25 01:00:40 UTC`; pre-write clock: `2026-10-25 01:02:20 UTC`. Exact dispatch-to-STOP duration, CPU and peak RSS were not instrumented: UNKNOWN; charge the full 1,200-second assignment under the contract. No compute process reservation was used. Final artifact digest and final observed clock are supplied externally to avoid a self-hash.

**STOP receipt:** revision 1 is frozen by this write. All authored writes cease; only read-only digest verification and final handoff remain. No descendant, scratch output or unresolved subordinate lease exists. Fresh independent review and Luna adjudication remain pending. No shared record was edited.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/20261025-force-runtime-return-trace.md`.
- Baseline SHA: `9b945b0bb175e8e0919d388dc720babbdf0c2464` (inherited).
- Dependency hashes changed: none among the nine frozen inputs above; revalidated before writing.
- Review status: frozen UNREVIEWED bounded source characterization; no independent self-review, theorem closure or implementation authority.
- Checks already run: cited constructor/caller source reads, searches, pin equality and output nonexistence check. No executable/formal check.
- Proposed research-checkpoint commit message: `research: trace Force runtime return and isolate the missing result export`.
- Shared-record deltas intentionally left for Luna/curator: record R9-R STOP and frozen digest; charge 1,200 seconds; retain O-NORM/O-RESULT and parent OPEN; record the RootComp/body-result identity fact separately from generic source realization; route R9-R's missing constructor/export to its source/runtime owners; obtain the fresh independent review. No task/index/authority file, manifest, lockfile, other worker artifact or question bundle was changed.
