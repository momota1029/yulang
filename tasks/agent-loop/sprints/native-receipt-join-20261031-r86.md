# R86 — authenticate the attached-pending / completed-clone receipt join

Status: ADMITTED bounded research sprint under the unchanged user goal.  
Sprint: `NATIVE-RECEIPT-JOIN/20261031-R86`  
Baseline: `a44adf1f2fda99f896debf11b5f58c207728b030` (`yulang3`).

## Altitude and decisive question

The parent remains the original Simple-sub A/B soundness obligation at R66 `Root`, with its original quantifiers, accepted source domain, effect hygiene and birth-level qualification unchanged. R85 proved a finite conditional obstruction: its producer lifecycle keeps an incomplete receipt on each attached Origin, and therefore cannot meet R84 `Primitive`'s completed-attached-receipt premise. The inspected Rust producer instead updates a separate completion clone.

R86 asks whether the actual two-record reader can be represented faithfully in Lean: for the same retained Origin, does the attached pending receipt join to exactly one completed clone with all other fields equal, while preserving every Origin competitor and the existing rejection cases? If so, what exact consumer projection follows, and can it feed the unchanged R84 record definition? If not, return the first concrete failed equation. Keep R57 relation-ID uniqueness distinct from R84 occurrence/route uniqueness.

## Fixed outcomes and falsifiers

The proof lane must provide a constructive relation between an Origin's attached pending receipt and its separate completed record, prove identity of every non-completion field and the reader's uniqueness/rejection behavior, and apply it to the unchanged R84/R57 definitions. If no same-record application is derivable, prove and report the exact interface mismatch. Do not replace the attached Origin, drop competitors, assume global relation-ID uniqueness, weaken original claims, or present a projection as the original Root.

The source lane must inventory every pinned initialization, replacement, mutation, rollback and completion of Origins/receipts/completion vectors in the admitted module closure; map producer → completion record → both checked-root and saved-receiver consumers; and return either exhaustive source equations or the exact missing owner/transition. Existing tests may be read as source evidence but must not be run or treated as proof.

Falsifiers include an unaccounted write/initializer outside the pinned closure, a completion clone that differs in any non-bit field, duplicate matching completions accepted by a reader, rollback that separates an Origin from its completion, loss of any competing Origin, an R57/R84 selector discrepancy, or an R84 `Primitive` premise not satisfied by the represented records.

Success closes only this receipt-join/interface packet. It does not close native transition exhaustiveness beyond the admitted module closure, original A/B, source extraction, standalone Lean imports, or production.

## Exact lanes and artifact leases

**Proof lane** — registered `lean_prover`; exact writes only:
- `notes/theory/lean/YulangClosure/NativeReceiptJoinR86.lean`
- `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-proof.md`

Use the pinned R85, R84 and R57 definitions. Preserve two physical records explicitly. Prove exact field agreement and indexed membership/uniqueness without adding an assumption equivalent to Root or selector uniqueness. Query every new theorem's complete type and axiom list. No Rust/compiler edits, Git, Lake/Cargo/build/tests, cache or target writes.

**Source lane** — researcher, read-only source analysis; exact write only:
- `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-source.md`

The complete pinned input paths and byte hashes are in the R86 manifest. Search the finite seven-file Rust closure and record every matching read/write plus module visibility. No source changes, builds, tests, compiler, Git or generated artifacts.

**Fresh reviewer** — read-only, exact review path:
- `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-review.md`

Review the frozen source inventory, Lean field relation, theorem application, exact stdin recipe, complete type/axiom reports and falsifiers. Neither author reviews their own work. The primary owns all state synchronization, staging, commits and pushes.

## Budget and execution gate

Total 3,600 seconds: proof 1,400; source 1,000; independent review 700; primary/integration 500. Astra 0. At most two separately committed-and-pushed Lean stdin calls, each at most 120 seconds, total at most 240 seconds, with `-j1 -M1024` and `LEAN_NUM_THREADS=1`. First call only after frozen candidate, exact input and fresh review; permit one diagnostic-directed repair only under a versioned amendment, new review and separately pushed authorization. No third/fallback call.

Build the exact flattened audit input in memory from the accepted R85 stdin recipe plus the frozen R86 candidate and queries. Hash all source dependencies, candidate, executable and exact input before execution. Keep complete stdout/stderr and process metadata in the primary review receipt. Do not write input or temporary source to disk.

No Rust/CST changes, Cargo, Lake, Rust compiler, tests, formatters, target, `.olean`, cache, scratch directory, environment, installation, worktree, nested CLI or background service. No change to semantics, production authority, accepted source domain or worker/resource envelope. Stay in the existing checkout; create no environment or worktree.

## Dependencies and remaining boundaries

Use R85's committed conditional result and separate source report, the accepted R84 exact-input receipt, R57's `Origin`/`Drain`/selector definitions, the original source-preservation claim and the 2026-10-24 birth-level correction. All exact revisions/hashes and Rust search inputs are pinned in `native-receipt-join-20261031-r86-inputs.json`.

A fresh independent result audit is required before theorem acceptance or integration. Stop for any hash drift, an unadmitted writer, lease collision, resource cap, an additional semantic premise, a real counterexample, or exhausted call count. Preserve all quarantined paths and unknown worker observations. Keep `current.json` at or below 16 KiB.
