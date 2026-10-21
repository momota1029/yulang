# R277 — pinned fmt parser diagnostic census

Status: CHECKPOINTED_UNREVIEWED; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broader playground sample goal under Authoritative R149.
Baseline: `7d9a68922` on `research/simple-sub-intrusion`.
Authority: R149 authentic `pair.say` through pinned `std::core::fmt`; R276 exact source identity checkpoint; unified design and proof companion Markdown.

## Outcome

Identify the exact parser diagnostics produced for the blob-pinned `lib/std/core/fmt.yu`, preserving each diagnostic's source range and a bounded source excerpt. Group occurrences by structural kind/parent and nearest relevant parser node so the next change targets the owning grammar/recovery rule. If evidence shows one small common owner, fix it without changing the pinned source or broadening accepted malformed syntax; otherwise stop with an exact classified owner map and minimal falsifiable parser hypothesis.

Success evidence: all diagnostics from one parse of the exact source are accounted for by source ranges and structural categories; every proposed grammar change has a regression test for valid pinned syntax and malformed-neighbor rejection. No source rewrite or `ShadowArtifact` publication while diagnostics remain.

Falsifiers: diagnostic ranges fail to map to exact source bytes; source identity differs from the R276 blob; proposed parser fix changes the pinned bytes or accepts malformed adjacent forms; diagnostics are hidden rather than resolved.

## Parent gates and lanes

- Implementation: Luna investigates diagnostic ownership and may make one bounded parser-owner fix within the exact leases below.
- Proof: R149 remains OPEN. The original source/native theorem and missing source-to-schedule/import carrier are unchanged; this parser census supplies no theorem premise. Solo work leaves no independent proof worker active.
- Independent review: unavailable under user-directed solo work; all results remain provisional and unreviewed.

## Exact write paths

- `tools/inference-playground/src/pinned_stdlib.rs`
- `tools/inference-playground/src/lib.rs`
- this contract
- `notes/theory/2026-10-21-r277-pinned-fmt-diagnostic-census.md`
- `tasks/agent-loop/inbox/20261021-r277-pinned-fmt-diagnostic-census.md`
- primary-owned `tasks/agent-loop/current.json`
- `tasks/current.md`

Parser grammar files are not leased until the exact owning rule and compatible neighboring tests are identified. If the census requires a new source owner, stop code edits and issue a versioned contract/lease before touching it.

## Verification and stop conditions

Focused diagnostic census test, `cargo check -p yu-playground`, `python3 tools/agent_sprint.py check`, and `git diff --check`. One heavy Cargo process; no broad suite. Stop after 600 seconds, or earlier when the diagnostic owner is isolated. Preserve R149 source, quantifiers, and `[io]` negative-open-row behavior.

## Non-goals

No role selection, import linking, inference, runtime, sample output, source/native proof closure, semantic approval, or production promotion. The unchanged examples and all parent proof gates remain OPEN.
