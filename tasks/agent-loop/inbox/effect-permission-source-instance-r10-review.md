# R10 independent failure-receipt review

Verdict: **failure receipts authenticated, with one minor provenance limitation. R10 remains CLOSED_INCOMPLETE. No proof or production gate is accepted.**

Scope: fresh nonauthor review under amendment 02 (`1aad663842bbe6a38480dcccc8aeca067cb606febd81f9b4eed194a33b73dfb7`). Read-only; no Lean/Lake/checker/tests/Cargo executed.

## Minor provenance limitation

The frozen revision-2 proof handoff was not preserved before the leased path was overwritten by revision 3. Audit 1 records its SHA256 `1226596076500f32e82433340dd5e60dc8d736476d613d95552ef315a0ac5ff8` and size 9795 bytes, but those bytes cannot now be recomputed. The R10 scratch tree has no R2 handoff snapshot. This conflicts with `tasks/agent-loop/README.md`'s “Frozen assignment handoff” preservation requirement. The R3 history does not authenticate R2 handoff bytes. This does not invalidate the independently preserved R2 Lean artifact or raw failure receipts. Preserve this limitation in closeout.

## Authenticated checks

- Both frozen plans match evidence: attempt 1 `4a14c7674159c1de85f62159e87779b79343303a6dcad4e8650632b82440a4e2`; attempt 2 `30ae6c7a1be4872de650927dfc40589cd0ed0448e42b04d97f525371e2daf510`.
- Both 15-file project inventories match recorded byte counts and hashes. Copy receipt hashes are `1e2f260644d3eba21ea11f7810606789797d2023398996cd7eeb58bba936df85` and `a3156365534a0f2ef27c020443c7d59578d0101b74ba1857fb18c0d8d040cc3a`. All seven tool hashes in each plan match current binaries/checker. Historical `.lake` absence is recorded as prospective evidence and cannot be reconstructed retrospectively.
- All 108 manifest entries authenticate with zero mismatches. Contract, manifest, source handoff, amendments and current revision-3 artifact/handoff hashes match. R3 artifact: 14073 bytes, SHA256 `4a25b24d251494ca6c05fcc696306cedf3d9cfa36d4a90a2a3437b68a04ff977`. R3 handoff: 11480 bytes, SHA256 `d14297763ab477c2776aea78e79c263823f0364a39f00f8c0c406e48ed46f3ca`. Preserved R2 artifact: 14052 bytes, SHA256 `6638d59a39423c78e37052932a5b421932719fdeee939f94c7eec2e528467c8d`.
- Both plans select exactly the four public theorem roots `push_aligned`, `four_allocations_and_prefix`, `exact_tree_supplier`, and `exact_tree_r9_application` in `YulangClosure.FormalPermissionSourceInstance`.
- R2→R3 diff contains exactly three additions of `Frame` to `simpa only` at lines 98, 116 and 175. Statements, assumptions, constructors and other source bytes are unchanged.
- Attempt 1 diagnostics match frozen R2: conversion mismatches at 98:4, 116:4, 175:8, plus unsolved supplier at 159:182. Attempt 2 resolves the three conversion mismatches but reports unsynthesized implicit `w` at 192:10 and the still-unsolved supplier at 159:182.

Raw receipts (all hashes match evidence):

| Attempt | stdout | stderr | status | time |
|---|---|---|---|---|
| 1 | `e5a2afbd2976a470c74d3261f96167959055ea019c2da06f302b07d70c919e8d` | `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` | `f784a46651ba226ed8c393fbc26d6c35a17e300bdd0541ba2b09917a05d99e48` |
| 2 | `4fb15b5f0cd7d35c10db2dba47c53ebf0a801eef199c44171153dbcd1c7a0b5c` | `0edf2d238840b65a26de68075c964d099167cf4cae51705f162bcfa4e7addc60` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` | `760aaea0b6f393b9972acbec886b1101f0893b0b0d5aa154aba733ddd9c6a64e` |

Resource receipts show exit 1 for both: 13.51 seconds / 798448 KiB, then 13.21 seconds / 788828 KiB; combined wall time 26.72 seconds.

Neither output contains audit begin/end markers, printed theorem types, or axiom inventories. The evidence correctly says no theorem types or axiom audits were emitted and leaves all proof/production gates unaccepted. No R10 repair or audit remains authorized.
