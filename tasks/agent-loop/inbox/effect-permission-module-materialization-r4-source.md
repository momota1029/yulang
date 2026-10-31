# EPM-MAT-r4 source lane — frozen incomplete receipt

Objective/method: audit the adopted module-reference materialization source rule against the two contract-named module Call supplier owners. Method is authenticated, bounded source-text correspondence inspection. No constructive theorem, executable experiment, counterexample, or semantic supplier result was produced.

Baseline/dependencies: primary-pinned `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, session `EPM-MAT-r4`, worktree `/home/momota1029/rust/yulang`. The baseline SHA is supplied by the primary; no Git command was run. Contract and manifest authentication succeeded before any source/design/handoff body read.

## Authentication and commands

The first tool action executed the dispatch's exact `set -euo pipefail`, six-entry `/usr/bin/sha256sum -c` heredoc and `/usr/bin/python3 ...-r3-preflight.py ...-r3-manifest.json` command verbatim. Exit 0. All six bootstrap files reported OK and the preflight reported `PREFLIGHT_21_ENTRIES_ALL_MATCH`. Contract SHA-256 is `12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f`; manifest SHA-256 is `aee1a5e3c06e9c72348e45676157bdb56b57f0dc5673ddcffe58b30a8fb16f11`; preflight SHA-256 is `7ef05dc938c7f44cbbcd08004cc5fc9b306677b58415cc4276c21330a832d133`.

Subsequent body reads used one `/usr/bin/python3` process and one file/page per tool response: `b=Path(path).read_bytes(); print(b[start:end].decode())`. Each interval was at most 4096 bytes and every tool response requested `max_output_tokens:8192`. The complete pages below were received without truncation; retries 0. Separate metadata-only reads computed file sizes and SHA-256 digests. A final metadata recheck confirmed all eight governing-file sizes/digests unchanged before writing this receipt. No source bodies were read before bootstrap/preflight, and no source-rule, owner, parent-proof or prior-result body was subsequently consumed.

## Coverage ledger

Intervals are half-open raw-byte offsets. COMPLETE means complete body transport/inspection of that file, not completion of a semantic obligation.

- `tasks/agent-loop/sprints/effect-permission-module-materialization-20261028-r4.md`: SHA-256 `12d99e885af99a669007921e3ebc782b990c443781a9b6549962c12abd2f490f`; size 7378; pages [0,4096), [4096,7378); next EOF; COMPLETE.
- `AGENTS.md`: SHA-256 `0ab35669cfc43ef1b3759ea81284a7f3b55bf3e030ab3aecb5bb32086a538c1d`; size 10937; pages [0,4096), [4096,8192), [8192,10937); next EOF; COMPLETE.
- `AGENTS.pre-sprint.md`: SHA-256 `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562`; size 23767; pages [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,20480), [20480,23767); next EOF; COMPLETE.
- `rules/goal-driven-sprints.md`: SHA-256 `e57c5c23e1956e09ea0da130a137ac50ce723ce5f0a90323adb17da88dab68b7`; size 19813; pages [0,4096), [4096,8192), [8192,12288), [12288,16384), [16384,19813); next EOF; COMPLETE.
- `.agents/skills/yulang-lean-proofs/SKILL.md`: SHA-256 `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7`; size 7856; pages [0,4096), [4096,7856); next EOF; COMPLETE.
- `rules/research-lab.md`: SHA-256 `1ffdabce7cc65d4e463e9a50a7a572c2974809bed415071b57a23efed8eb3228`; size 904; pages [0,904); next EOF; COMPLETE.
- `rules/design-authority.md`: SHA-256 `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1`; size 10512; pages [0,4096), [4096,8192), [8192,10512); next EOF; COMPLETE.
- `rules/git-concurrency.md`: SHA-256 `0992b73aea3fdd9a53c624b6010e1eeaa97d308f8f9e18698b9115d1b4cf8d09`; size 8795; pages [0,4096), [4096,8192), [8192,8795); next EOF; COMPLETE.

Semantic input coverage is ZERO. Preflight hashes authenticate bytes but do not count as source-rule inspection. Metadata-only measurements (body coverage none, next 0):

- `notes/theory/2026-10-17-module-reference-materialization.md`: 28084 bytes, SHA-256 `f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb`.
- `notes/design/2026-10-17-module-environment-exposure-definition.md`: 3539 bytes, SHA-256 `d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d`.
- `notes/design/2026-10-16-module-expression-source-owner.md`: 8912 bytes, SHA-256 `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- `notes/design/2026-10-17-module-entry-provenance-contract.md`: 6285 bytes, SHA-256 `44f33397a45f5d17a0302c6b1efbfe1f7bbdf018caed2ece2acc18176a746bd9`.

All other manifest files have preflight integrity validation only, no body coverage. No partial semantic page was used. Thus neither exact supplier-owner correspondence nor the exact adopted rule premises have been evaluated in this lane.

## Claim class, gap and stop

Claim class: established execution receipt for integrity and governance coverage only; semantic audit INCOMPLETE. Exact established premise: bootstrap and the pinned preflight exited 0 over their authenticated inputs. The preflight is not an independent semantic oracle: it compares file hashes against the primary-supplied manifest and assumes that manifest/dispatch authority; it says nothing about whether source rules hold. No seeds, ranges of source programs, mutations, solver transitions or omitted-case search were exercised.

The full source materialization document alone requires seven additional bounded pages before it can support a conclusion. Required governance paging consumed the bounded grant's useful audit window, leaving insufficient time for that file plus both supplier owners and parent correspondence. I stopped conservatively rather than make claims from partial semantic coverage. The source-rule hypothesis, supplier premises, owner identities/cases and conditional theorem applicability remain unverified. This is a resource/coverage obstruction, not a counterexample or evidence that either supplier lacks an implementation.

Status: `STOPPED / CLOSED_INCOMPLETE` recommendation. No module supplier, parent, native, implementation or production gate is closed. `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding. No statement is made outside the inspected governance domain. Review is PENDING fresh independent review; this receipt is not self-certification.

Resource receipt: one lightweight Python or hash process per command; no parallel heavy work, descendants, tests, Cargo, builds, Git commands or mutations. Entire source grant charged 150 seconds, no refund requested. First explicit wall-clock sample was Unix 1793160285.0058153; freeze preparation sample is Unix 1793160449.3421466 (difference 164.336 seconds). Initial dispatch-to-first-sample interval is unmeasured, so exact total elapsed/CPU/peak RSS are UNKNOWN; the full grant remains charged. Writes stop after the single receipt is frozen; no background process was started.

Recommended next action: have the selector and primary admit a fresh exact audit packet with sufficient budget for required governance plus complete semantic-file coverage, or explicitly authorize reuse of a pinned complete governance receipt; do not rerun an equivalent undersized packet or promote integrity checks to source evidence.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-module-materialization-r4-source.md` only.
- Baseline SHA: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (primary supplied).
- Dependency hashes changed: none among the eight governing files rechecked; all 21 manifest inputs matched at bootstrap. Later changes to unconsumed manifest bodies were not rechecked and carry no semantic result here.
- Review status: frozen, independent review pending.
- Checks already run: exact six-entry bootstrap and pinned 21-entry preflight, successful bounded governance page reads, metadata revalidation. No tests/build/Lean checks.
- Proposed research-checkpoint commit message: `research: record incomplete r4 materialization source audit coverage`.
- Shared-record deltas intentionally left for primary/curator: mark this lane STOPPED with frozen hash; record 150-second full charge, complete governance/zero semantic coverage, CLOSED_INCOMPLETE disposition subject to review; keep all supplier/parent/native/production gates OPEN and existing quarantines intact. No shared-record write was performed.
