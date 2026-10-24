# LEAN-COMPLETE-CALL-20261025/r7 implementation handoff

Sprint-ID / contract revision and SHA-256: `LEAN-COMPLETE-CALL-20261025/r7`, `5d0409f5918748fc175e926111710977bb4d0bda6b8a00b4a185b475110e3250`.
Assignment-ID / handoff revision: `LEAN-COMPLETE-CALL-20261025/r7-IMPLEMENTATION` / **1**.
Parent gate / original theorem and scope locator: bounded typed Call context and finite-prefix safety milestone; frozen contract sections “Required propositions and theorem outcome” and “Exact metadata-realization boundary”. Parent complete Call safety and source/native gates remain OPEN.
Baseline: `7262f16cf58f0236a1a140e044d8fbbeb6cf61c6`.
Role / actual worker ID / current session / launch or resume receipt: Luna/high implementation lane / `/root/call_implementation` / runtime session ID UNKNOWN / assigned by parent; active-work receipt sent to parent.
Requested model and effort / observed model and effort: Luna / high; observed runtime model metadata UNKNOWN.
Exact leased paths: `notes/theory/lean/YulangClosure/CoreSyntax.lean`, `CoreSubstitution.lean`, `CoreExecution.lean`, `ControlSyntax.lean`, `ControlTyping.lean`, `ControlComposition.lean`, `CoreControlBridge.lean`; handoff only `tasks/agent-loop/inbox/20261025-lean-complete-call-implementation.md`. No descendants. Only the first five Lean modules and this handoff were changed. No proof-module, root import, contract/current-state, or Git edits.

## Outcome

Outcome class: **implementation candidate; proof and source/native correspondence OPEN**.

Added a separate typed Call grammar. `TypedCall.Function` retains lambda bodies, result consumers, and actual wrap adapters; `Comp` and adapters can contain typed `request` and `fail`. A Call term carries an explicit receiver-freshness witness, typed thunk carrier, receipt template, and CallView. `CallTerm` links the lambda-leaf receipt to `CallView.sourceReceipt` and the actual outer-to-inner wrap adapter spine to the per-interface plans. No endpoint type equality creates path correspondence: adapter mappings are explicit `PathCorrespondence` values with a mapping identity.

Added Call renaming/substitution over the actual Value/Comp syntax, including binder lifting under `bind` and request continuations. Typed substitution lemmas cover the new grammar. `delayArgument` builds the actual inert `Delay(bind (Force carrier) adapter.body)` term. `callEntryBody` distinguishes Value entry (Force then body) from Computation entry (substitute carrier), then sequences the declared-result consumer and pending result adapters in their stored inner-to-outer order. Executable context plugging uses syntax-bearing bind/scope/expose/adapter frames and the actual consumer/adapter bodies. No Proposition A proof body was placed in implementation files.

`CallControlStep` provides a Call-specific internal relation while preserving the literal old Control suffix. It selects one owner from the explicit fresh term, enters its Scope, peels actual wrappers outer-to-inner while delaying argument adapters, attaches the lambda receipt before entry, executes the mode-specific entry syntax, and retains current world, CallView, Scope/View data, and suffix. Per-interface exposure frames are installed in the order that makes outer interfaces enclose inner adapters. A normal return uses existing `scopeReturn`/`viewReturn` metadata operations; returned values retain their result View. `CallStateTyped` requires the actual `TypedCall.ContextTyping` witness and `FramesTyped` witness for the unchanged suffix.

**Req represented cases:** `CompTyped.request` types payload against the operation payload and types its saved continuation under the response binder at the continuation’s normal result type. `emitRequest` snapshots retained carrier/captured Call Views, currently active Call exposure Views, and explicitly supplied matching Views from every `.view` frame in the literal suffix at request creation. Later bind/adapter bubbling captures the actual continuation by substitution; crossing Scope wraps the saved continuation in that owner and invokes `suspendScope`; crossing expose wraps the remaining exposure and invokes `suspendView` without adding late observations. `finishRequest` produces the explicit requested handoff with its continuation, observed Views, Scope data, result type, world, and literal suffix. External resumption is outside this representation.

**Fail represented cases:** typed `Comp.fail` is reachable from lambda and adapter bodies. Bind/adapter/scope/expose propagation preserves the same failure reason and invokes only the existing `Metadata.failWorld` relation for that frame; `finishFailure` is the explicit terminal Fail handoff retaining world, result type, and literal suffix. No cleanup or request-observation policy was added. Nested Req/Fail are not constructors of the embedded `Original.Comp` fragment; they are available in the represented TypedCall lambda/adapter/context computation grammar.

Parent/source/native correspondence: operational requirements are represented as typed syntax, explicit call plan data, transition rules, and existing metadata operations. No frontend constraint generation, source/native generation correspondence, compiler execution, or native behavior follows from this implementation. Plan authenticity, full source View/eligibility/current-world hygiene, and all parent source/native obligations remain OPEN.

## Frozen interface and dependencies

SHA-256 interface snapshot:

- `CoreSyntax.lean`: `0250b51b7b97a98e52b76e3785a7341f2b454a422016c6945d7c4190804b07ff`
- `CoreSubstitution.lean`: `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f`
- `CoreExecution.lean`: `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e`
- `ControlSyntax.lean`: `94d9b59e7cc69dac98de9797c7627a571554b859e3906c7c1ca94881d9482864`
- `ControlTyping.lean`: `163c191584b6abb462c1e5e190bb2105d6ec3c4f0512568e87570b89ff00ffd8`
- `ControlComposition.lean` (unchanged): `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40`
- `CoreControlBridge.lean` (unchanged): `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a`
- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `CoreComposition.lean`: `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c`
- `YulangClosure.lean`: `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f`
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- frozen r6 outcome: `b6def9a2c248ccbd7a8bda1cba9489b6dab84abd8a9131f0b24ce573e0eefd4a`

All other frozen contract inputs rehashed unchanged against their table entries. Contract SHA still matches the frozen value. These are implementation-snapshot hashes, not a reviewed or checked Lean interface.

## Checks, TODOs, and stop receipt

Checks: `git diff --check` passed (no output). No Lean, Lake, Cargo, or tests were run; Luna owns serialized verification. No proof-hole or compiler-proof claim is made.

A’s exact TODO (Sol, `CallContext.lean`): against these hashes, prove actual computation plugging and context inversion for the active hole, delayed argument adapters, body/result consumer, pending result adapters, owner/Scope, receipt/View inputs, and typed literal suffix. Prove each listed internal transition’s typed context/result preservation or explicit typed handoff using the actual TypedCall substitution; do not assume body safety. The frozen handoff does not establish these lemmas.

B’s exact TODO (Sol, `CompleteCall.lean`, only after A freezes): classify every `CallControlStep` successor for every finite internal prefix, preserving typed context/result, world and literal suffix or reaching the typed Ret/Req/Fail handoff; establish no Bad state and exact prefix/exit arithmetic. Do not assume same-body safety.

Luna’s TODO: first independently inspect/freeze the interface, then run the serialized pinned checks, recheck the direct/transitive dependency component, assign fresh review, and decide whether implementation repairs are needed. Independent review must check source order, receipt-before-force, outer-to-inner wraps, inner-to-outer result adapters, event-time observations including suffix Views, actual substitution, failure propagation, and r6 declarations.

Checks and resources: implementation grant ceiling was 1,800 seconds including prep. Actual precise elapsed/remaining budget is UNKNOWN to this worker; charge the full authorized grant until Luna reconciles runtime accounting. No scratch/generated paths were created. `git diff --check` is the only check performed.
Next related step: Luna’s frozen-interface review and serialized check; A/B proof work remains gated on Luna’s seam grant. No authority expansion requested.
Worker state / writes stopped: **STOPPED, writes stopped** after this frozen handoff; no descendants or scratch leases remain. Commit-ready milestone: no; pending serialized checks, proof lanes, and independent review.
