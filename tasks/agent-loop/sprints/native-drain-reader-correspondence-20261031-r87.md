# R87 — source-faithful drain reader correspondence

Status: proposed bounded sprint under the unchanged Yulang soundness goal.
Sprint: `NATIVE-DRAIN-READER-CORRESPONDENCE/20261031-R87`
Baseline: the committed R86 closeout checkpoint on `yulang3`.

## Altitude and decisive question

The parent remains the original Simple-sub A/B soundness obligation at R66 `Root`, with original quantifiers, accepted source domain, effect hygiene, and birth-level qualification unchanged. R86's two authorized audits exhausted without proving seven reader theorems. Its residual `readJoin.match_3` is a dependent reduction failure; it is not a counterexample.

R87 asks whether each actual reader has a faithful finite relational specification when modeled as its own data-returning function: (1) the uncut publication selector, (2) the cut-window selector, and (3) the Internal checked/saved readers. State the branch equations explicitly, prove soundness and completeness for each reader separately, and only then construct dependent certificates. Preserve whole-inventory uniqueness versus cut-local uniqueness and do not infer that one reader's result is another's.

## Fixed outcomes and falsifiers

The proof lane uses the accepted R85 flattened input and unchanged R57/R84 definitions; it must not import R86 declarations with `sorryAx`. Model actual `Option`/finite-list branch behavior, prove relational correspondence in both directions for each reader, and apply only justified results to the unchanged R57/R84 interface. Keep relation-ID uniqueness, global occurrence/route uniqueness, and cut-local uniqueness separate. If a source branch cannot be represented, report the first exact mismatching equation and leave the theorem open.

Falsifiers include a reader branch accepting/rejecting a record differently from its proposed relation; loss or duplication of a competing Origin; conflating cut-local with global uniqueness; an invalid dependent certificate; or a claimed R57/R84 application that needs a premise not established by the modeled reader.

The source lane reads `candidate_context.rs` and `candidate_receiver.rs` together and returns one owner-local proposal for carrying pending attachment plus indexed completion through checked emission and saved consumption, or `NO_SAFE_CODE_SLICE` with the exact authority/Root-compatibility blocker. It must not edit Rust, change semantics, or inspect other source files.

Success closes only this finite reader-correspondence packet. Original A/B, whole-crate native transition exhaustiveness, source extraction, standalone imports, and production remain OPEN unless independently proved under separate authority.

## Exact lanes and artifact leases

**Proof lane** — registered `lean_prover`; writes only:
- `notes/theory/lean/YulangClosure/NativeDrainReaderCorrespondenceR87.lean`
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-proof.md`

Use the exact accepted R85 flattened input as the prefix, then the frozen R87 candidate and complete theorem/axiom queries. Preserve all original R57/R84 claims. Do not import the failed R86 candidate. No Rust/compiler edits, Git, Lake/Cargo/build/tests, `.olean`, cache, target, scratch directory, or environment.

**Source lane** — researcher, read-only; writes only:
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-source.md`

Read exactly the two whole-file inputs and hashes in the R87 manifest. Compare producer, checked emission, and saved consumption paths from those files only. No source changes, tests/builds, compiler, Git, or generated artifacts.

**Independent review** — fresh compiler/source reviewer; exact review output:
- `tasks/agent-loop/inbox/effect-permission-native-drain-reader-r87-review.md`

Before execution, review the frozen source equations, the three distinct reader definitions, proof statements, exact stdin recipe and hashes, and falsifiers. After execution, independently audit all diagnostics, printed theorem types and complete axiom reports. Authors do not review their own work. Luna owns state, exact authorization, staging, commits, and pushes.

## Budget and execution gate

Total envelope: 3,600 seconds: proof 1,400; source proposal 1,000; independent review 700; primary/integration 500; Astra 0. At most two separately committed-and-pushed Lean stdin calls, each at most 120 seconds total, `-j1 -M1024`, `LEAN_NUM_THREADS=1`. The first call requires a frozen candidate, exact in-memory input, fresh pre-execution review, and separately pushed authorization. One diagnostic-directed repair is permitted only with a versioned amendment, a new review, and a new pushed authorization. No third call.

Build the flattened input in memory from the accepted R85 exact stdin and frozen R87 candidate/queries. Record and verify every pinned dependency, candidate, executable, and exact-input hash before execution. Preserve complete stdout/stderr and process metadata in the raw-result artifact. Never write flattened input or temporary Lean source to disk.

No Rust/CST changes; Cargo, Lake, Rust compiler, tests, formatters, targets, `.olean`, caches, scratch, environment/install/worktree, nested CLI, or background service. Stay in the existing checkout. Stop on hash drift, unadmitted writer, lease collision, resource cap, counterexample, need for semantic/policy change, or exhausted call budget. Preserve UNKNOWN worker observations and quarantined paths.

## Dependencies and remaining boundaries

Use R86's failed receipts and source report only as diagnostic/source context; do not rely on its failed declarations. The proof base is the accepted R85 exact flattened input (115,884 bytes, SHA-256 `bac29ad18bd16e9a5af0422ea4d3416e049a61951d6b1545c8ba35a0548cbc79`) with its R57/R84 dependencies and full type/axiom reports. The source input hashes and exact allowed paths are pinned in `native-drain-reader-correspondence-20261031-r87-inputs.json`.

A fresh independent review is required before any Lean execution and a separate result review is required before theorem acceptance or integration. Conditional or declaration-level results do not close original A/B or production. Keep `current.json` at or below 16 KiB.
