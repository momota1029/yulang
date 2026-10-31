# Sprint contract — MODULE-SUPPLIER-NATIVE-SLICES-PAGEPACK-REVIEW/r3

Status: ACTIVE; read-only package review only. Baseline `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. No semantic/source/proof producer grant.

## Pins

- r3 preparation authority `tasks/agent-loop/sprints/module-supplier-native-slices-r3-preparation-contract.md`: `77d50d3158d67857ebbe6b8e629f9cc07926a457069cd38b3f290cdc8cc177c7`.
- primary preparation receipt `tasks/agent-loop/history/module-supplier-native-slices-r3-page-preparation.md`: `acea8cca9e0b6a8a5aa76eb31c43fea04ea5072f367be00967c1c3a8a3296564`.
- generator `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pagegen.py`: `e2990124a88099298abc5279a751c68ab87fefb2d066b5831bc59ff6bc249202`.
- consumer `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pagecat.py`: `4b50306376d8bafb187d400db7d683a6abdcb0aebfec6341c28e58804d63a6c7`.
- manifest `tasks/agent-loop/sprints/module-supplier-native-slices-r3-pages/manifest.json`: `6c2c9fe80b294518b6ea8c8995e28a1b2604c3bb5e43f28e301c388219eb2c0a`.
- governing r1 contract SHA `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`.
- authenticate all four owner hashes from the manifest against full owner bytes.

## Review

Independently authenticate all pinned artifacts and owners. Verify all 18 pages, headers, emitted/body lengths, offsets, line spans, owner pins, ordering and continuation. Reconstruct every range byte-for-byte; verify no gap, overlap, duplication or substitution; total body <=100 KiB and each emitted page <=4096 bytes. Confirm `route_internal` and `route_internal_inner` are exactly lines 18207–18230 and exclude `decode_positive_scheme`; check all other named unit/arm boundaries and context-fragment labels.

Inspect generator to confirm governing-contract hash is checked before owner reads/staging; all four owner pins/ranges/overlaps/caps are validated before private staging; staged files and manifest are validated before atomic publication. Confirm the persistent lock path `tasks/agent-loop/sprints/module-supplier-native-slices-r3-publish.lock` remains a regular file at device/inode `2096:33581817`; nonblocking exclusive OS lock covers destination/staging checks through rename; lock is not unlinked/replaced; only primary is publisher and all future permitted publishers must use that lock. Existing destination/staging or contention is STOP. Inspect consumer basename and manifest membership, regular-file, size/cap/hash/header/body validation before output. Run exactly `python3 tasks/agent-loop/sprints/module-supplier-native-slices-r3-pagecat.py page-014.txt` with at least 8192 output tokens; record exit, complete byte count/hash/ending and truncation status.

Read only contracts, scripts, manifest, lock metadata, immutable pages and declared source slices. Do not infer semantics or supplier conclusions. No writes, tests, builds, Cargo, Lean/Lake, Git, descendants or background work. Return full review receipt for primary recording at `tasks/agent-loop/inbox/module-supplier-native-slices-r3-page-pack-review.md`. STOP on unexpected failure.

## Budget

Fresh reviewer 150 seconds; primary adjudication 25 seconds. Full packet charge 250 seconds (preparation75 + review150 + primary25); cumulative 5,450/7,200 before work, 5,700/7,200 after completion, 1,500 remaining. No contingency. A pass only permits a later selector decision, not a semantic producer grant. All gates remain OPEN and `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding. Preserve all UNKNOWN reservations/quarantines and r1/r2 artifacts.
