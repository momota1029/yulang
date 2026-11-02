# R275 revision 3 — constructor coverage and production-entry readiness

This version preserves the R275-r1 and r2 readiness stops unchanged. It adds
the missing root parser wrapper, the public HIR forwarding owner, the
remaining candidate collection constructor path, corrected HIR ownership, and
a production-entry/flag-provenance gate. It changes no production semantics,
source domain, parent theorem, fixture or finite outcome.

## Unchanged parent and finite outcome

Keep full inference/effects soundness → R70 →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, original source domain and quantifiers,
Simple-sub A/B, independent satisfying assignments, shared witnesses,
source/native correspondence, F1/FK1 and foreign continuations unchanged.
Parent/A/B remains 0→0; independent `Need_D` and R71 coverage stay OPEN.

For the exact fixture input authenticated in R274-E001, the intended finite
outcome remains:

```text
classifier/transaction facts
→ header and selector choices
→ recovery-free parser return and exact CST
→ exact HIR root and fourteen-slot LocalSource carrier
→ successful candidate collection and static-SCC entry
```

Establish every branch and normal-return premise from this bounded view. Freeze
a justified trace or its first exact failed constructor implication and owner.
Stop at candidate/SCC entry, before extrusion, final typing or publication.

## Failed attempts retained

- R275-r1 readiness STOP: view payloads omitted one terminal LF in 14/35
  intervals. Receipt `tasks/agent-loop/history/20261103-r275-readiness-stop.md`,
  SHA-256 `64fd4acbc229430549c30419bbf7004db4548737187976c6cec6d9a05899e9a1`.
- R275-r2 readiness STOP: byte integrity passed, but `parse_root_statements`,
  accurate HIR owner mapping, collection-to-emission calls and a positive
  production entry route were not closed. Receipt
  `tasks/agent-loop/history/20261103-r275-r2-readiness-stop.md`, SHA-256
  `60e0f21110cf7a8af54d056709828887ecb2ff16154bf552178449e470866267`.

Both consumed Sol 300 seconds each. No fixture derivation, producer write or
main trial occurred. No output path is treated as proof.

## Authenticated source and exact R275-r3 view

The 229-path inventory is
`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`,
SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`.
It derives from the authenticated R271-r2, R271-r3 and R255 manifests. The
R275-r3 ranges carry all 35 prior payloads unchanged and add six production
intervals:

- Ranges `tasks/agent-loop/sprints/source-acceptance-r275-r3-ranges.json`,
  SHA-256 `2cd3ad9dc9a66129a42ec11d8d45ef4b78a0a877d0d066dc262313d524c03c3e`.
- Binary view `tasks/agent-loop/sprints/source-acceptance-r275-r3-source-view.txt`,
  SHA-256 `6b3836953c876c40f2cda0b944ff5f8a8d912d179e5ac58f9e93c7e6d38e8373`.
- Byte-offset index `tasks/agent-loop/sprints/source-acceptance-r275-r3-view-index.json`,
  SHA-256 `0966c2429bb64896bd31de52f2e20609642c2a75bba6dae3cf5fec46ebcb94e5`.
- Corrected constructor coverage
  `tasks/agent-loop/sprints/source-acceptance-r275-r3-coverage.md`, SHA-256
  `61d22ccc8004305fb377a12556cd53550926c59cb5857a55b0f01f5921e775cb`.
- Entry/flag provenance index
  `tasks/agent-loop/sprints/source-acceptance-r275-r3-entry-index.json`, SHA-256
  `74ec95494935e803296f8ab276b6237369253f73d3df57ec2bc5f33f12426481`.

Luna's pre-contact gate validates all 41 exact byte payloads against their
whole-file and interval hashes, unique IDs, expected ID set, bounds,
non-overlap, and exact source equality. The six additions are:

- `root_statement.rs:30–56`, actual `parse_root_statements` wrapper;
- `yu-hir/src/shadow.rs:889–895`, public HIR forwarding wrapper;
- `yu-solver/src/lib.rs:1009–1027,1030–1047,1057–1482,1490–1571`, remaining
  world collection through source emission and seal/static-SCC return.

The coverage table corrects HIR ownership: E022 contains module lowering;
E023 contains local-source carrier logic. Split collection intervals avoid
interleaved `#[cfg(test)]` fields; gaps are not treated as no-ops.

## Sol readiness gate

Reuse stopped Sol identity `/root/sol_r274_source_acceptance`; prior cumulative
charge is 8,400 seconds before R275-r3. Sol first reads and hashes only this
contract, returns a WAITING acknowledgement, and confirms exact identity and
current coordination session. Luna then checks the acknowledgement and live
roster and issues a separate **300-second readiness-only GO**.

Readiness independently validates all packet and inherited pins, 229 input
hashes, 3 origin-manifest hashes, all 41 original file and excerpt hashes,
exact indexed payload equality, boundaries and coverage-table callsites. It
must also classify the entry/flag route:

```text
actual production entry
→ wrapper chain and argument forwarding
→ candidate_values / candidate_graph_effects / scoped flags
→ guarded source emission
→ collection seal and static-SCC return
```

The visible ordinary `ConstraintBatch::collect` path forwards
`candidate_values=false`. Test-call locators are excluded metadata; test bodies,
assertions, helpers and outcomes are never evidence. A text-search absence is
not a production-unreachability theorem. Readiness must exhibit a positive,
authenticated production route for the required candidate flags. If it cannot,
STOP and report the exact entry/configuration seam. Do not authorize a
hypothetical private constructor invocation or silently redefine the outcome.

Original source files are hash-only. Source bodies are read only from indexed
R275-r3 payloads. No raw-source display, tests, assertions, expected output,
`unwrap`, test execution/results, builds, probes, Cargo, Lean, network,
scratch/cache/generated outputs, nested CLI, code edits or descendants.
A readiness failure cancels main and review reservations.

After a full readiness PASS, Luna must independently adjudicate every gate and
issue a separate explicit GO for the main trial. Correct packet integrity or
owner mapping alone is not main-trial authorization.

## Accounting and outputs

All previous time remains charged: Sol R272 2,400s, R273 3,000s, R274 2,400s,
R275-r1 300s and R275-r2 300s (8,400s cumulative before r3). No reset, refund
or extension.

| Component | Seconds | Status |
|---|---:|---|
| R275-r1 readiness | 300 | charged |
| R275-r2 readiness | 300 | charged |
| R275-r3 readiness | 300 | newly reserved; gated |
| Main trial | 1,200 | newly reserved; readiness-gated |
| Fresh compiler referee `/root/r275_source_acceptance_review` | 1,800 | unissued until coherent producer freeze |
| Luna preparation/adjudication total | 750 | 600 retained + 150 revision |
| **R275 retained/allocated total** | **4,650** | fixed ceiling |

Producer outputs remain the exact absent paths
`notes/theory/2026-11-03-source-acceptance-r275.md` and
`tasks/agent-loop/inbox/source-acceptance-r275.md`. Recheck absence and exact
lease ownership before main GO. Reviewer hash pins belong in a separate
immutable contract after a coherent freeze. No production edit authority;
`NO_SAFE_CODE_SLICE` remains. Parent/A/B stays 0→0 absent a checked application
to the unchanged parent theorem.
