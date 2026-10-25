# CALL-PEELING-TYPING-Q — frozen handoff revision 1

- Sprint: `LEAN-CALL-ENTRY-SPINE-20261025/r1`.
- Contract: `tasks/agent-loop/sprints/call-entry-spine-20261025-r1.md`, SHA-256 `77affc0d4d0765c8fffd92fc41653a154ab66bb6598c31c039e4e518d449d4d9`.
- Assignment/handoff ID: `CALL-PEELING-TYPING-Q`; revision: **1**. The exact handoff byte hash is supplied in the final runtime receipt; it is intentionally not self-embedded.
- Contract baseline: `e5ea192c0d42bcbc470fee9fb8474d1b8cbee981`; launch packet reports post-contract baseline `73442584d`. No Git command was run by this author to establish either commit.
- Author/worker: `/root/call_wrap_typing`, sole Q author, current parent session `LEAN-CALL-CONTEXT-TYPING-20261025/root-turn-9`. No contributing descendants or delegation.
- START: acknowledged directly to `/root` before source work; subsequent active-work receipt confirmed all listed dependency pins and the inspected constructor owners.
- Requested model/effort: prover `gpt-6.1-sol/high`; observed effective model/effort: **UNKNOWN/UNKNOWN**. Role/configuration is not runtime model evidence.
- Outcome class: **candidate**, uncompiled and unreviewed. No theorem, source/native or production promotion is claimed.

## Parent claim and immediate application

The frozen sprint's syntax-only parent is `completeCallEntry_typed`: for every typed finite `f`, every closed carrier typed at `thunk argument`, and every pending adapter list typed from the function result to `finalResult`, construct an exact lambda leaf and type its assembled `callEntryBody` at `finalResult`. Operational Call preservation, raw/typed successor coverage, effects, source/native correspondence, original Call A/B (including independent arbitrary suffix quantifiers), inference A/B and the broader user goal remain OPEN.

Q supplies the exact frozen `PeelFunction` relation, `peelFunction_exists`, `delayArgument_typed`, and the exact contract proposition `peelFunction_typed`. Existence explicitly returns all lambda syntax fields plus final carrier/list, for every raw finite `Function`, carrier and pending list; it has no typing premise. Preservation inducts on the supplied decomposition and retains the original `finalResult` and entire pending suffix. Its hypotheses and existential conclusion match the contract without strengthening a premise or narrowing a domain.

Luna can apply `peelFunction_exists f carrier pending`, then `peelFunction_typed hpeel hf hcarrier hpending`, invert the resulting lambda typing derivation, and apply P's `callEntryBody_typed` with the preserved consumer input/output equations. This consumes Q directly in the unchanged parent-facing syntax theorem. Required next evidence is serialized Lean acceptance of these bytes, P/composition acceptance, and fresh independent review; owner: Luna. Q has no remaining author stage inside this assignment after freeze.

## Constructor and premise accounting

1. `PeelFunction.lambda` copies the exact mode, receipt, three syntax types, body, consumer, carrier and pending list. The two `FunctionTyped` lambda modes are retained, not reconstructed or inspected by peeling.
2. `PeelFunction.wrap` uses exactly `delayArgument carrier argumentAdapter` and `resultAdapter :: pending` before recursion. It records finite syntax decomposition, not a new operational transition or any source-coverage law.
3. Structural existence uses both and all `Function` constructors, recursing on `inner` with the changed carrier/list. No endpoint equality is used to infer a wrap or lambda.
4. `delayArgument_typed` composes `CompTyped.force hcarrier`, the stored `adapter.typed` through `CompTyped.bind`, then `ValueTyped.delay`. Explicit premises are `adapter.input = argument` and `adapter.output = innerArgument`. Therefore its output is a thunk at the inner argument type. The adapter body is preserved as syntax under delay.
5. The preservation wrap case inverts `FunctionTyped.wrap`: `hf` supplies inner function typing; `ha`/`haOut` discharge the delayed argument lemma; `hr`/`hrOut` type `AdaptersTyped.cons resultAdapter pending ... hpending`; the induction hypothesis consumes these exact new derivations. The preservation lambda case returns its existing three typing premises unchanged.
6. Arbitrarily many wraps, zero wraps, both lambda modes, empty/nonempty pending lists, distinct intermediate types, and arbitrary retained bodies/receipts/consumers are covered structurally. For outer adapter `rO` and inner adapter `rI`, recursion receives `rO :: pending`, then `rI :: rO :: pending`. No reversal or dropping of the original suffix occurs.

## Source/native evidence and limits

Inspected exact owning syntax: `CoreSyntax.lean::Function`, `FunctionTyped.wrap`, `Adapter.typed`, `AdaptersTyped`; construction: `CoreExecution.lean::delayArgument` and `callEntryBody`; consumer/order: `plugResultAdapters` and `consumeCallResult`; operational shape: `ControlSyntax.lean::CallControlStep.peelWrap`. The operational constructor uses the same carrier and pending-list equations while retaining its other state fields. The paper's “call の入口と adapter” and “call の局所保存” sections were read as the governing declared construction.

This is direct inspection of syntax and equations. There is no generated-constraint, propagation, actual source emission, metadata attachment, actual execution, native backend, ordinary-inference or effect-preservation proof here. Receipt syntax is copied unchanged by the relation; attaching it operationally is outside Q. No `CallControlStep` simulation/coverage theorem is asserted. `NO_SAFE_CODE_SLICE` remains in force for dependent runtime edits; no production code was edited.

Prior accepted work reused: r3 checked module/dependency boundary and its current syntax constructors via `import YulangClosure.CallContextTyping`. Q does not need the r3 plugging theorem directly; Luna's P/composition lane consumes it within its accepted premises. No historical failed proof, source theorem, narrowed-domain argument or assumed-transition test was reused as closure evidence.

## Frozen artifact and direct dependency hashes

Sole source output: `notes/theory/lean/YulangClosure/CallPeelingTyping.lean`, revision 1, SHA-256 **`f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`**. All entries below matched the frozen contract on initial and final author reads:

| Dependency | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CallContextTyping.lean` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `notes/theory/lean/YulangClosure/ControlSyntax.lean` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `tasks/agent-loop/sprints/call-context-typing-20261025-r3.md` | `50314a04521194eb9ec2faef2d122c7afc65f91c58d1cc0936c807d881935d42` |
| `tasks/agent-loop/sprints/call-context-typing-20261025-r3-outcome.md` | `98b9a65a899264cf739ad0ee42ed104e2c01716f530c9d11b561a9f2a0d1e9d3` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |

## Checks, resources and mutual TODOs

Author checks: two byte-hash passes over contract/dependencies, direct source/constructor inspection, static reread of the exact propositions, and `rg` inspection finding no `sorry`, `admit`, custom `axiom` or `unsafe` declaration in Q. No Lean process, compiler, test, Git, external contact, generated build output or scratch path was used. These static checks do not establish elaboration or axiom output.

Resource grant: at most 1,200 seconds, zero Astra and zero descendants. Exact active duration was not instrumented from launch, so conservatively charge the full 1,200-second assignment grant; remaining author grant: zero. No continuation or budget carryover is requested.

- `Q-CHECK-1`, owner Luna: use frozen contract/dependency/artifact bytes to run the authorized serialized checker; print signatures/axioms for existence, delayed argument and preservation. Output is the already leased verification JSONL. Falsifier: any elaboration error, changed proposition, unexpected axiom or missing output/hash. Do not treat this author reread as checker success.
- `Q-COMPOSE-1`, owner Luna: after P and Q STOP, apply Q's explicit lambda witness and preserved derivations to P in `CallEntrySpine.lean`. Falsifier: inability to obtain the exact mode-specific body typing, retained consumer equations or original pending suffix without a new premise.
- `Q-REVIEW-1`, owner Luna/fresh nonauthor reviewer: independently audit the frozen Q/P/composition, constructor equations, nested adapter order, arbitrary intermediate types, both modes and complete checker receipts. This author is ineligible to certify its own result.
- Operational/source/native parents remain with Luna's existing source/consumer owners; required missing evidence includes `CallControlStep` correspondence and FL12 source applicability. This handoff grants no new assignment, output lease or runtime edit.

## Writer STOP

All new paths are exactly the two leased outputs: `notes/theory/lean/YulangClosure/CallPeelingTyping.lean` and this handoff. Scratch paths: none. Other files written: none. Descendant leases: none. Source and handoff revision 1 are frozen after this write; subsequent actions are read-only hashing and the final STOP receipt. **STOPPED: writes ceased; no background work remains.** Pending Luna verification, independent review and integration; no parent closure is claimed.
