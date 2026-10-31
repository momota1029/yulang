# R128 independent review — accepted local subgate

Review assignment: `/root/r128_independent_review`, fresh `compiler_referee`,
requested gpt-6.1-sol / medium; observed runtime model/effort UNKNOWN. Read-only
bounded inspection, no Lean invocation. The reviewer returned the report through
the agent final message because its role cannot write files; Luna recorded the
frozen report here after STOPPED.

## Frozen inputs and authentication

| Input | SHA-256 |
| --- | --- |
| Contract r2 | `7102e4fedd44aa6d1fd59511043e8655f487f30d5a1b252263d9d7d4852b0803` |
| Manifest r3 | `434211f70b380de57c3106e9e995c9465351789820397e5b9a20b8cff69f9d88` |
| Lean module | `2042c8ee50c8123e93857ee0eab9e95c9eab5d47d63a649ff4552568a47507d7` |
| Proof handoff r2 | `8b351bf240ca57e7a3cc489ab54e670819c7b442c6ed74ee6b0fe392d936dcf5` |
| Source handoff r1 | `42c9db25645a5e54146027ff474546cce06048d63e2a4752f8cff3f52f375323` |

All five artifact hashes matched. All 21 manifest input hashes independently
matched, including commit-pinned blobs. In-memory reconstruction reproduced the
frozen virtual receiver hash `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.
The pinned `SourceEffectId` owner hash matched
`409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`.

## Independent findings

**No BLOCKING, major or minor findings within the R128 local operational-model
scope.** Accept only this checked local subgate. No source simulation, source /
native correspondence, parent theorem or production claim is accepted.

The reviewer confirmed:

- `Step.write` forbids changes to every live borrowed location, while allowing
  unrelated locations to change. `trace_preserves` derives heap-read and token
  stability by transition induction through idle, borrow and write; stability
  is not an assumed law.
- The model separates `Fin n` location, allocation identity, family equality
  (module plus declaration), and registration. The two identity fields match
  the pinned `SourceEffectId` inventory. The unequal-module discriminator
  prevents declaration-only equality and does not equate `Arc` allocation
  identity with `ModuleId` value equality.
- Capture success yields a record read, ordered search result and first-member
  position. The contract explicitly preserves missing-search behavior as an
  open attachment condition: a Rust correspondence must establish successful
  search before claiming the stored optional index is present.
- Consumer success proves membership in the guarded read record; it does not
  alone prove first occurrence. `captured_trace_copy` joins first-position
  capture, trace stability and actual copies. `[9,9]` demonstrates capture at
  zero while local reads at both zero and one succeed.
- All ten theorem types and complete final axiom sets match the final accepted
  invocation. Historical failed-check recovery declarations are excluded.
  Axioms are only `propext` and `Quot.sound`, except
  `unequal_module_same_declaration`, which has none.
- The source handoff keeps registration/native guards and pointer/vector
  distinctions separate. No temporal stability is inferred from `ptr::eq`; a
  shared starting address is not treated as full-slice equality.

The reviewer independently confirmed the check history: invocation 1 exit 1,
invocation 2 exit 1, invocation 3 exit 0; aggregate 6.051535335005610 seconds.
Both bounded additional check slots are spent. No Lean execution, compilation,
test run, source write, scratch/cache output or descendant was used by review.

## Remaining obligations and stop receipt

Eight Rust-to-model equations remain open: full family equality and clone
fidelity; ordered vector publication; full-vector borrow and heap/transition
simulation; native family/index interpretation; ordered `.position`
correspondence; exact request transport; registration/packed-index/pointer
selection interpretation; and the same-record Option/Vec consumer read. R39 PRE
construction, R45 extraction/certificate application, R114 transport, original
A/B claims, full effect hygiene, source inference soundness and production stay
OPEN. R111's private 6-GiB verifier is unavailable, Cargo remains 0/1, and no
Rust source integration or source push is authorized by this review.

**STOPPED:** reviewer performed read-only inspection and bounded in-memory
reconstruction. No files, scratch artifacts, caches or Git state were written;
no descendants or subprocesses remain. This primary-recorded review is accepted
as the independent receipt for the exact frozen inputs above.
