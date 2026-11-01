# R137 outcome — authenticated structural map, correspondence still open

Contract: `tasks/agent-loop/sprints/effect-permission-hir-decoder-20261102-r137.md`, SHA-256 `d311de24018eac4774f1f0d2290e8d94ca9e7978aedf249500b160c9b5cbdf8a`. Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`.

The frozen source map is `tasks/agent-loop/inbox/effect-permission-hir-decoder-r137-source.md`, 13,233 bytes, SHA-256 `0a81bca2f61c6f8665a7c90374e2872f3a135d1c06827c4fd493f629c8180a51`. Fresh compiler-referee review passed the bounded structural mapping; receipt `tasks/agent-loop/history/effect-permission-hir-decoder-20261102-r137-review.md`, SHA-256 `f178ab6e42afa9fa84568ada3f373bc41c156528a9646c90764ae67ef857da3d`.

The source map covers supported HIR value and row branches, ordered tuple/function recursion, polarity/path updates, nested concrete-only permission emission, and the distinct outer `FormalEntryPermission`. The review confirms those structural equations agree with R136's abstract inventory. It also confirms two exact open premises: (1) authenticated, source-preserving equations for Rust owner, occurrence, formal, scope, row position and effect declaration identities to the Lean `Nat` fields; (2) the production failure envelope after native permissions/domain have been published and a later fallible resource sample. A test wrapper or local `Err` is not production success/rollback evidence.

R137's dependent proof was not launched: an abstract decoder with guessed ID encodings would not authenticate source correspondence. The source/native equality, failed-attempt publication boundary, original `SourceProblem.InferenceSoundness`, effect-hygiene H, actual arrival/capture/copy/Catch consumption, and production remain OPEN. No Rust source, build, test, Lean, scratch, or Git mutation occurred in this sprint.

Next: R138 traces each production `FormalAnnotation` caller through transaction rollback or failed-session discard/termination. This can establish the exact successful-publication boundary without requiring internal rollback if failed state cannot reach successful output or a consumer.
