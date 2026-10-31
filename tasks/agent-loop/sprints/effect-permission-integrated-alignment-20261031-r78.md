# R78 — Integrate checked Name/Apply alignment into inventory consumers

Status: ADMITTED after bounded R77 PASS and clarification that downstream consumer integration remained OPEN. This packet reuses R77's approved source meaning; it changes neither compiler semantics nor A/B quantifiers.

## Fixed outcome

Make the R77 owner-local source alignment authoritative for the existing private `InventoryPackage::capture` and `internal_root_view_from` consumers. A `DefinitionUse` is located at its callee `Name`; `ApplySourceInput.checking` identifies the enclosing `Apply`. Retain and validate these coordinates independently through capture and the root view.

For `InventoryPackage::capture` near line 4506, resolve each call through its owner-local HIR and supported Group peel, retaining the Apply coordinate and an optional exact module-Name/target alignment. Preserve all calls, including unrelated or non-module-definition calls. Select the Internal call by call index and input identity, receiving owner, resolved callee Name occurrence, and exact target definition. Do not equate `call.occurrence` with `DefinitionUse.occurrence()`.

For `internal_root_view_from` near lines 1791–1795, separately check the selected call's Apply occurrence against its checking/expression coordinates and the resolved Name occurrence/target against the request and use record. Preserve source-call pointer identity and all existing slot-0/slot-2 fact, permission, parameter, relation, ancestry, root and failure checks. Reuse one authoritative alignment result across both consumers; do not relabel an Apply as a Name or remove competing source rows.

## Leases and lanes

**Rust implementation — 900 seconds**

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-rust.md`

The only Rust source writer. Rework the R77 alignment into the exact borrowed `SourceInternalOwner`/`InventorySourceCall` owner path used by both consumers. Preserve complete inventories and existing native behavior.

**Constructive Lean proof — 1000 seconds**

- `notes/theory/lean/YulangClosure/IntegratedSourceAlignmentR78.lean`
- `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-proof.md`

Constructively connect R77's checked alignment to the two consumer coordinate equations. Prove exact call/use/target joins and preserve the same-use plan, global owner choice and parameter-recipe conclusions. Include a successful finite Name≠Apply witness and rejection of duplicate calls, foreign owners, wrong Name/target, substituted checking coordinate and call index. Do not assume consumer-check success as a premise.

The exact stdin slice manifest, pinned executable, source/slice hashes, full theorem type queries, and complete stdout/stderr receipts belong in the proof handoff. A maximum of two separate direct stdin audits, each at most 120 seconds, is allowed. Before each invocation, the primary independently reconstructs the exact bytes, freezes the input and execution parameters, and commits/pushes a separate authorization. No retry or third audit. Any `sorryAx` fails the Lean gate.

**Fresh independent reviewer — 900 seconds**

- `tasks/agent-loop/inbox/effect-permission-integrated-alignment-r78-review.md`

Start only after Rust and Lean authors STOP. Trace one selected borrowed call through both consumers, verify all non-selected calls remain preserved, and independently reconcile all theorem types, axiom reports, stdin/stdout hashes and source pins. Reviewer is read-only; the primary materializes its report if needed.

## Authority, baseline and evidence

Baseline: commit `68976bad8d44fd5586ac9b06ee2389743bfa4c8f`, after the R77 integration-boundary clarification. R77's bounded constructor/proof PASS remains valid; the old consumers named above remain OPEN until this packet is integrated.

Inputs are pinned in `tasks/agent-loop/sprints/effect-permission-integrated-alignment-20261031-r78-inputs-r1.json`. It includes the complete baseline receiver, call/use collectors, owner-local HIR/peel implementation, R77 constructor/review, and exact Lean parent definitions. Any changed pin invalidates only the affected result and returns through the primary.

Required evidence:

1. Rust source trace shows one R77 alignment result authenticates the selected call and flows through capture and root-view checks, while unrelated calls remain represented.
2. Lean audit prints all full theorem types and transitive axiom reports for the unchanged claims over the new consumer equations; no `sorryAx` or bypass.
3. Fresh review accepts the exact frozen Rust/Lean artifacts and retained audit evidence.
4. Static `git diff --check` and `python3 tools/agent_sprint.py check` pass. No Cargo, compiler, tests, build, formatter, Lake, cache, target, scratch, new environment, or worktree.

## Resources and boundaries

Fresh total: **3600 seconds** — Rust 900; proof 1000; reviewer 900; primary 800 including 500 closeout. Astra 0. Use the current checkout only. Preserve the 32 pending questions, every UNKNOWN worker and quarantined path, and the R77 audit/review history. Keep `current.json` at or below 16 KiB.

This closes only the source-coordinate integration gap. Authenticated full Rust-to-Lean inventory extraction, branded identity correspondence, genuine R66 incidence/Root and physical root joins, original A/B, whole-language effect hygiene/soundness/principality/termination, Rust execution, and production remain OPEN.
