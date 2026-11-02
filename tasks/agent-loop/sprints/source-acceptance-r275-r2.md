# R275 revision 2 — exact-byte source-view readiness and fixture acceptance

This version preserves the stopped R275 readiness attempt as evidence and fixes
only its source-view serialization. It does not change source intervals,
coverage claims, semantic outcome, fixture, parent theorem or resource guards.

## Unchanged parent and finite outcome

Keep full inference/effects soundness → R70 →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, original source domain and quantifiers,
Simple-sub A/B, independent satisfying assignments, shared witnesses,
source/native correspondence, F1/FK1 and foreign continuations unchanged.
Parent/A/B remains 0→0; independent `Need_D` and R71 coverage stay OPEN.

For the exact 87-byte ASCII fixture authenticated in the R274 input-only
excerpt, reconstruct the complete finite implication:

```text
classifier/transaction facts for consumed tokens
→ header and selector choices
→ recovery-free parser return and exact CST
→ exact HIR root and fourteen-slot LocalSource carrier
→ successful candidate collection and static-SCC entry
```

Establish every selected branch and normal-return premise from the bounded
view. Freeze a justified trace or its first exact failed constructor
implication and owner. A different carrier, recovery branch or unmet resource
guard falsifies this finite witness, not whole-language soundness. Stop at
candidate/SCC entry; extrusion, final typing and publication remain out of
scope.

## Exact source-view authority

Authenticated inventory:
`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`,
SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`;
229 distinct path/hash entries from authenticated R271-r2, R271-r3 and R255
manifests. The unsupported R272 307 count remains withdrawn.

The failed R275-r1 packet remains immutable:

- Contract: SHA-256
  `d11832eecf024e0a81489cce5b71c979ad67328641b2fc90c6b0b6f2337bb5af`.
- Stop receipt: `tasks/agent-loop/history/20261103-r275-readiness-stop.md`,
  SHA-256 `64fd4acbc229430549c30419bbf7004db4548737187976c6cec6d9a05899e9a1`.
- R275-r1 ranges: SHA-256
  `1cdc644abb143a068cbea0113bca1a9b9ca673e7c92eff1cc81f09b863c6c114`.
- R275-r1 defective view: SHA-256
  `3c55cae2382a4f1b00d30012a3023cd3008abb5c8fbb0605577e73f8b5611cde`.
- R275-r1 ranges: SHA-256
  `1cdc644abb143a068cbea0113bca1a9b9ca673e7c92eff1cc81f09b863c6c114`.
- R275-r1 coverage table: SHA-256
  `9081065d51532ac50cb31d1d1befdc5fd601bbecd6b5257eba4148806968c598`.
- R275-r1 admission: `tasks/agent-loop/history/20261103-r275-readiness-admission.md`,
  SHA-256 `863ed315ab1b01908fafb2be314b77bc6fc3e93cd9806ce22131178d9265afca`.
- R275-r1 readiness GO: `tasks/agent-loop/history/20261103-r275-readiness-go.md`,
  SHA-256 `222c5308f8e1a64bedd19cb60fc6faea172c7aa0e43e0685bceaa1ddb323398a`.
- R274 contract: SHA-256
  `ec875f9705324e9aab328ee8aebd9bc028ab8dafffed3578d3db9fd910a72b27`.
- R274 ranges: SHA-256
  `4df81d44a22a22c7ea7d56d19f49bd75c6ed6061bbd06fc777cd80cfafa2debf`.
- R274 view: SHA-256
  `e1e03aaa65ec15e45ca25c9998b29d366b4b6f8ef16e2d2290ea7dd03935cb2e`.
- R274 stopped milestone: SHA-256
  `dd4123a585c7ebf37b3bed5dba9135363e10a3a1688977da17d760502e807b40`.
No r1 source-view bytes are reused as authority.

R275-r2 reuses the unchanged ranges JSON and coverage table, and adds a binary
source view with a byte-offset index:

- View `tasks/agent-loop/sprints/source-acceptance-r275-r2-source-view.txt`,
  SHA-256 `a7e25ef8172692ca1d3b332245d96ba736fa906a8318bb225ed0e17713683655`.
- Index `tasks/agent-loop/sprints/source-acceptance-r275-r2-view-index.json`,
  SHA-256 `cf9faefef5471c669039e74f2181beebc41226898e89acdb4c7789d20653eb79`.

The index identifies all 35 payloads by unique excerpt ID, byte offset, byte
length, whole-file hash and excerpt hash. Headers and separators are outside
the indexed payloads. Luna independently compared all 35 payload slices to
the exact original intervals, verified all whole-file and interval hashes,
checked unique IDs, bounds, non-overlap and the exact authorized 35-ID set.

## Fresh readiness gate

Use the same stopped Sol trial identity
`/root/sol_r274_source_acceptance`, with prior R272/R273/R274 charges and the
R275-r1 failed readiness charge preserved. Sol first reads/hashes this
contract alone and returns a WAITING acknowledgement. After Luna checks that
acknowledgement and the live roster, Luna issues a separate explicit GO for a
fresh **300-second readiness pass only**.

The readiness audit must independently verify the contract, view, index,
unchanged ranges/coverage/inventory pins, three origin-manifest hashes, all
229 input path hashes and all 35 exact indexed payload comparisons. Then audit
the production/test boundary and caller/callee table against the visible
header, parser, HIR, collection, and candidate/SCC route. R275-r1 did not reach
those latter checks. Identify any omitted visible active owner. Any digest,
boundary, callsite or owner failure is STOP; no fixture derivation or main
trial GO follows.

Original source files may be accessed hash-only; read source bodies only from
the pinned R275-r2 source-view payloads. The index must be used for exact byte
slices, not newline-normalized extraction. No test assertions, helpers,
expected output, `unwrap`, test execution/results, raw-source display, tests,
builds, probes, Cargo, Lean, network, scratch/cache/generated outputs, nested
CLI, code edits or descendants are authorized.

Only after readiness freezes and Luna independently confirms every gate may
Luna issue a separate explicit **1,500-second main-trial GO**. The main trial
must complete the full finite acceptance-to-candidate/SCC implication; fixing
serialization alone is not completion.

## Accounting, outputs and limits

Prior charges stay intact: Sol R272 2,400s, R273 3,000s, R274 2,400s, and
R275-r1 readiness 300s for this named Sol identity (8,100s cumulative before
any r2 work). No reset, refund or automatic extension.

| Allocation | Seconds | Status |
|---|---:|---|
| R275-r1 readiness | 300 | fully charged |
| Original Luna preparation/adjudication | 600 | retained |
| R275-r2 readiness | 300 | newly reserved; GO gated |
| Main Sol trial | 1,500 | newly reserved; separate GO gated |
| Fresh compiler referee `/root/r275_source_acceptance_review` | 1,800 | unissued unless coherent producer freeze |
| Additional Luna correction/adjudication | 150 | newly reserved |
| **Retained/allocated R275-r2 envelope** | **4,650** | no extension |

Producer outputs remain the same exact paths, absent at this admission and
owned only by Sol after main-trial GO:

- `notes/theory/2026-11-03-source-acceptance-r275.md`
- `tasks/agent-loop/inbox/source-acceptance-r275.md`

Recheck both outputs' absence and their existing exact leases immediately
before a main-trial GO. The failed readiness wrote neither. The reviewer
receives exact output pins only under a separate immutable review contract
after a coherent producer freeze; otherwise its 1,800 seconds remain unissued.

No production edit authority. `NO_SAFE_CODE_SLICE` remains. Keep Parent/A/B at
0→0 absent a checked application to the unchanged parent theorem. Any
unchecked edge means INCOMPLETE, with no parent promotion.
