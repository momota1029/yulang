# LEAN-COMPLETE-CALL-20261025/r7 — Proposition A

Assignment-ID: `LEAN-CALL-CONTEXT-PROOF-20261025`; handoff revision: 1.
Status: preparation candidate; representation seam NOT_GRANTED; Lean writes NOT_STARTED.

## Frozen authority and ownership

- Sprint contract: `tasks/agent-loop/sprints/lean-complete-call-20261025-r7.md`, SHA-256 `5d0409f5918748fc175e926111710977bb4d0bda6b8a00b4a185b475110e3250`.
- Baseline supplied by Luna: `7262f16cf58f0236a1a140e044d8fbbeb6cf61c6`; no Git command run by this author.
- Author/actual worker: `/root/call_context_prover`; parent launch assignment is the runtime receipt. Session: r7 Proposition A assignment; opaque host session ID UNKNOWN.
- Requested model/effort: Sol/high (`gpt-6.1-sol`/high). Observed model/effort: UNKNOWN/UNKNOWN; no independent runtime metadata supplied.
- Exact leases: `notes/theory/lean/YulangClosure/CallContext.lean` and this handoff only. No descendants; no delegation, other new paths or scratch paths.
- Resource ceiling: 1,200 seconds inclusive of preparation and waiting. No grant renewal at the representation seam. First recorded clock observation: 2026-10-24 22:54:09 UTC; launch timestamp and exact elapsed time UNKNOWN and charged.

## Parent claim and application

The parent is the original complete Yulang semantics/type-inference goal, with original inference A/B, source/native correspondence, principality and termination OPEN. The bounded child claim is exactly r7 Proposition A, `call_context_plug_preservation`: every represented typed Call context plugs a computation of its actual hole type to its result type; inversion exposes pending delayed argument adapters, body/result consumer, result adapters, Scope/owner, receipt/View inputs and literal arbitrary independently typed Control suffix. Every actual active-computation or administrative Call step preserves that context/type and the represented world/suffix, or yields its explicit typed handoff/terminal witness. No assumed same-body safety or Call beta law may discharge the operational cases.

This preparation does not establish Proposition A. It identifies the constructors and necessary proof dependencies that A must consume after Luna freezes the implementation interface. B cannot use this source map as a preservation theorem. The full parent remains OPEN.

## Governing source-to-proof map

| Source locator | Actual source constructor or consumer | Required A case |
|---|---|---|
| operational source 145–245 | Value/Computation lambda; wrap; Delay; Force; Call; let; View; enumerated Fail | Use syntax-directed lambda/wrap/let typing, with argument and result adapter code carrying ordinary typing derivations. |
| 362–376 | Call selects one fresh owner and Scope; enter peels outer wrap | Preserve exactly that owner. Construct `Delay(let z <- Force t in a(z))`; retain the result adapter in the context, with no adapter execution while peeling. |
| 377–388 | source-lambda receipt, Value Force/let, Computation substitution, declared-result consumer | Receipt preserves carrier type; Value forces the received carrier; Computation uses actual capture-avoiding substitution. Consumer is the actual final body adapter, proved by ordinary let typing. |
| 389–400 | Scope normal return and source-call distinction for user casts | Preserve returned views/latent code; do not treat an administrative wrap as another receiver. Nested genuine source Calls need the same actual typing/step machinery. |
| 535–602 | immutable decorated-plan constants; Boundary/Flow/Receive/Observe; complete Call View | Expose metadata as retained inputs, not an inferred callback. Retain each View's call.effect/result ports, typed paths, source receipt slots and captured views. No request observation may be postponed until after handler bubbling. |
| 1029–1044 | local Call preservation derivation | Reproduce finite wrap induction against actual constructors. It supplies a paper proof method, not an assumed Lean preservation law. |
| 1231–1266 | Lambda/Delay capture, Force ports, complete Call interfaces, phase classification | Complete interface Views enclose receipt-following argument adaptation, entry, body, declared consumer and all result adapters; result adapters run inner to outer. |

Req/Fail coverage is determined by the actual new body/adapter grammar. If these constructors occur, A must retain operation instance, payload/response, saved typed continuation, Call/Scope/View context and suffix; failure must retain the reason and use only its specified cleanup relation. If the represented grammar excludes them, the interface and theorem outcome must state that fragment limit explicitly and must not claim complete Call safety. A source-required case cannot be silently removed to obtain preservation.

## Candidate proof decomposition, pending exact names

No Lean declaration signature is frozen here: implementation names and hashes are not available, and inventing a substitute relation would miss the governing seam.

1. Prove context plugging by induction on the actual typed context derivation. A bind frame consumes the hole's result in its typed body; delayed argument adapters use Delay/Force/let typing; identity-type metadata/Scope/View frames use their actual source-preserving constructor rule. Keep the independent suffix judgment separate.
2. Prove inversion on the context judgment to expose the actual active computation/type, each pending adapter and consumer derivation, owner/receipt/View constants and literal suffix. A postulated endpoint type equality does not supply these facts.
3. Classify every actual successor constructor. A core computation step invokes the newly established syntax/substitution preservation theorem; wrap, receipt, Value entry, Computation entry, consumer/result adapter and Scope/View transitions use their corresponding actual constructors. A typed exit carries its result and world/suffix equality explicitly.
4. Package plugging plus one-step classification under the required name `call_context_plug_preservation`, with no body-law premise. Freeze exact helper/main signatures and all direct/transitive dependency hashes for B.

## Historical material: limited reuse

- `Original.substitute_top` proves typing for the old `Original.Comp` substitution only. It is reusable unchanged for computations in that grammar; a new Call syntax requires its actual substitution and a new/extended typing proof.
- R6 `CoreControlBridge.successor_coverage`, `segment_preservation` and finite coverage retain a literal arbitrary Control suffix for the old Original image. Their method is useful; their statements do not cover absent lambda/wrap/Call or Req/Fail constructors.
- `notes/theory/2026-10-24-corrected-core-value-continuation.md` is independently unreviewed candidate mathematics. V1–V7 are rejected as established premises. The context-induction idea can guide a new proof over actual represented rules.
- Tests or probes that assume a transition list would not prove that the source constructors generate that list. No such probe was run.

## Byte-checked preparation inputs

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md` | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `4c036531cdd599799d0b943b4c8e2f1398aa91f5cf32296d7d6c50be1ff7a001` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `6d7d5da463480fbb618072b086c5092452575c56526579e4f898babd37b4567c` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `2cc68ffc79f17c0cb478802fec10ca2861e1a558a8202796bd7599595e5907ed` |
| `notes/theory/lean/YulangClosure/CoreControlBridge.lean` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |

These are baseline preparation hashes only. Luna must confirm the new interface revision/hash and revalidate the whole dependency component before proof edits. No source/native/compiler construction adequacy is established here.

## Mutual TODOs and exact falsifiers

- `A-IFACE-1` (Luna/implementation owner): supply the frozen actual Call syntax, typing, substitution, step relation, context representation and typed exit interface plus exact revision and hashes. Falsifier: any actual Call successor has no preservation/typed-exit branch, or the typing premise assumes that same successor's safety.
- `A-SOURCE-1` (Luna/source-plan owner, remains OPEN beyond this milestone): establish authentic and complete decorated plans/receipts/Views from accepted source. Falsifier: a represented source Call lacks a required receipt slot, interface port/path correspondence or captured view, or arbitrary equal endpoint types manufacture metadata.
- `A-WORLD-1` (implementation/source owner): make each world transition correspond to its source Scope/View/Req/Fail operation. Falsifier: world reset on failure, suspension or normal return conflates distinct source cleanup rules; no policy may be selected by A.
- `A-TO-B-1` (this author): after the authorized seam, deliver actual `call_context_plug_preservation` and helper signatures/hashes; B must preserve independent arbitrary suffix quantifiers and literal prefix/exit arithmetic. A one-frame local action never certifies foreign execution after exit.

Checks performed: static source reads and SHA-256 comparisons only. Lean/Lake/Cargo/tests/Git/native runs: none. Independent review: NOT_RUN; this author is ineligible to certify A or the combined result. Production authority: none.

Current worker state: WAITING for Luna's exact frozen implementation seam; only this handoff was written. Lean module writer NOT_STARTED. No descendant leases. This revision's preparation bytes are frozen on submission; any acknowledged revision change requires a sequential revision and new hash. Next in-envelope action is actual proof construction only after Luna's interface confirmation and within the same remaining 1,200-second ceiling.
