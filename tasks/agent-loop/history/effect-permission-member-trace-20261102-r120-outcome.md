# R120 outcome — CLOSED_BOUNDED_PASS_RESEARCH_ONLY

Contract `tasks/agent-loop/sprints/effect-permission-member-trace-20261102-r120.md`, SHA-256 `85246d529c175e7a2c765d575d500948d34e05d44647aa8309cdebe49484c2dc`. Admission: `tasks/agent-loop/history/effect-permission-member-trace-20261102-r120-admission.md`. Start checkpoint `fb9e49c1bf1231a880a4860b09036bb24193bb14` is pushed.

## Rust source trace

Frozen source handoff: `tasks/agent-loop/inbox/effect-permission-member-trace-r120-source.md`, SHA-256 `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e`.

The immutable receiver baseline at `d177c46ec61fcadd70a3d587c2f8934f6bc91f46` was composed in memory with the pinned R117 patch and then R119 patch. Full old contexts matched uniquely, in order, with hunk counts checked. The virtual receiver after R117 hashes to `542deb29c1143fad9adca958c3fadfa976e4505acc6f91dcf119ff0628f07e31`; after R119 it hashes to `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470` (296776 bytes). R117 hunk 6 relocates from advertised old line 5106 to actual 5109; this is unique-context composition, not strict advertised-offset application. No synthesized source was saved or applied.

The composed source visibly carries the same borrowed permission reference and `Option<usize>` from `.iter().position` through projection/request to `.get(index)` on that record's `concrete` vector. A local `[4,9,9]` read at index 2 still matches after changing the first-match index from 1, so member equality alone does not prove first-match identity; the direct field transport matters. Registration, packed permission slot, native member, concrete member index and family remain distinct.

## Proof and independent review

Proof handoff: `tasks/agent-loop/inbox/effect-permission-member-trace-r120-proof.md`, SHA-256 `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415`. It concludes **`NO_AUTHENTICATED_TRACE`**. First missing premise: no existing authorized interpretation derives `orderedSearch permission.concrete providerFamily = some permissionMember` from the actual Rust vector, equality and `.position()` computation. Existing Lean definitions also do not model projection/request transport or borrowed record identity; no new semantics or faithful-decoder assumption was added. R119 lemmas remain unchecked; no Lean execution or axiom audit occurred.

Independent review report: `tasks/agent-loop/inbox/effect-permission-member-trace-r120-review.md`, SHA-256 `ab6b4daa848196610986f62eebb7b5bbc3a32ba8bbdee0973954785b51ccc50b`. The compiler referee independently reconstructed the exact bytes and passed the research records with no new blocking, major or minor finding; it upheld `NO_AUTHENTICATED_TRACE`. Its role is read-only, so it returned a complete report rather than writing a file; the primary recorded that report, explicitly preserving its authorship boundary.

## Gates, execution and Git

No source code was integrated, applied, compiled or pushed. No Rust, Lean, Cargo, build, test or checker execution was performed by these R120 lanes. The only checker invocation was the repository's static `agent_sprint.py check`, which passed and is not independent semantic or execution evidence. No environment, cache, temp path or worktree was created or probed. Dirty Rust files and quarantined runtime paths were not read or changed.

R111's source compile gate remains BLOCKED. R39 PRE-state construction, R45 extraction, R114 transport, Rust-to-Lean operational correspondence, parent soundness/effect hygiene and production remain OPEN. This bounded research result does not close them. Only the explicit R120 contract, admission/current state and frozen source/proof/review/outcome records are eligible for this checkpoint; all unrelated and dirty paths stay excluded.
