# R137 source handoff independent review

Review-ID / revision: R137-SOURCE-REVIEW / 1.
Reviewer: /root/r137_source_review; fresh independent read-only reviewer.
Target: tasks/agent-loop/inbox/effect-permission-hir-decoder-r137-source.md.
Target SHA-256: 0a81bca2f61c6f8665a7c90374e2872f3a135d1c06827c4fd493f629c8180a51.
Immutable source baseline: 4c1d58a646a1101c080659ebfed6ae7862d8aded.

Verdict: PASS for the bounded structural source inventory and its explicitly open correspondence premises. No BLOCKING, major, or minor compiler-correctness finding. This is not approval of native output equality, identity decoding, failure atomicity, theorem closure, or production.

## Independent evidence

The submission maps the owning constructor rather than proposing a downstream symptom repair. Direct committed source inspection supports its structural claims:

- source_annotation.rs:496-599 constructs every scalar/variable/hole/group/function branch; 601-628 distinguishes Unit, grouping and ordered nonempty tuples; 630-687 retains separate ordered concrete/symbolic sequences, including repeated concrete declarations, while rejecting multiple symbols. local_source.rs:2771-2788 retains parameter identity and calls the source annotation parser.
- candidate_source.rs:701-715 and candidate_effect.rs:1601-1611 agree on nested polarity-sensitive row support. candidate_effect.rs:1620-1688 covers every HIR value variant. Tuple traversal appends Element(index) in source order, rejects immediate child effect rows, and restores path length before propagating child failure. Functions recurse argument value, result value, argument effects, result effects, with argument polarity reversed and result polarity retained.
- candidate_effect.rs:1697-1748 distinguishes omitted rows, singleton symbolic rows, negative nonempty concrete-only rows, and positive rows. Only the negative concrete-only branch appends FormalPermission; 1726-1734 retains the exact owner/scope/occurrence/parameter/path/row/concrete fields.
- FormalPermissionConstructorR136.lean:25-115 independently defines the same projected row support, traversal order, path extension, polarity and emission rule. Its record_identity at 170-178 preserves abstract fields, not authenticated Rust identities.
- candidate_source.rs:1323-1341 schedules FormalEntry separately and before FormalAnnotation. candidate_effect.rs:1763-1835 authenticates the entry registration/formal tuple, links a symbolic tail with slots 45/46, and publishes the distinct FormalEntryPermission. R136:187-208 keeps that outer inventory separate. A root row must not become a nested grant at path [].
- candidate_effect.rs:1936-1964 admits slots 43/44 before publishing nested permissions/domain and then performs a fallible sample. Entry publication at 1819-1831 also precedes a fallible sample. candidate_source.rs:2459-2467 propagates action failure before advancing the schedule; these blobs do not supply the surrounding transaction/discard owner. The handoff correctly leaves that envelope open.

Counterexample traces checked: a negative empty row and negative concrete-plus-tail row reject; the mixed row at positive polarity is supported without a nested grant; a singleton symbolic row emits no grant; equal concrete families at different tuple positions keep distinct paths/row identities; root mixed rows use the entry inventory. These agree with R136 definitions. Source test inspection at candidate_source.rs:751-794 and candidate_effect.rs:3106-3175,3661-3719 corroborates the intended sibling/path boundaries and explicitly wrapped test transactions. No test was executed, and test wrappers were not treated as production rollback evidence.

## Remaining gates

R137-SOURCE-ID-ENCODING-1 remains open: establish source-preserving equations and required injectivity for the retained source identities, ordered concrete sequence and structural paths. Nat record equality alone cannot authenticate Rust identity.

R137-PUBLICATION-ROLLBACK-1 remains open: establish that post-publication failed attempts cannot become successful observable output, through the actual owning transaction, safe discard/termination, or authenticated successful publication boundary. Complete internal restoration is not independently required; the authoritative top-level inference principles sections 4-5 permit safe termination/discard.

The dependent decoder may start under these explicit premises. Original SourceProblem.InferenceSoundness, effect hygiene H, consumer/capture/copy/arrival correspondence and production remain OPEN.

## Authenticated dependency hashes

409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f crates/yu-hir/src/module/source_annotation.rs
7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1 crates/yu-hir/src/module/local_source.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49 crates/yu-solver/src/candidate_source.rs
102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01 crates/yu-solver/src/candidate_effect.rs
3289bccd2b85dd4576adb1c4a870e635985b60e2e87c459d9174c4a0477eab4f notes/theory/lean/YulangClosure/FormalPermissionConstructorR136.lean
c93d2aadb82300dc4aa0ce085cef29537d2a418a2874407179f3888cd842950e tasks/agent-loop/inbox/formal-permission-constructor-r136-proof.md
5ac7e90477c4ea44b819b4988cefe7d5a6559051d407c914b022202ac440bf0f tasks/agent-loop/history/effect-permission-adapter-and-constructor-20261101-r136-outcome.md

## Checks and resource use

Read-only git show of exact pinned committed dependencies, line-numbered source/test inspection, target and committed-blob SHA-256 checks. All seven dependency hashes and target hash match. R136 explanatory records were checked as claim locators; source/Lean definitions supplied correctness evidence. Governing AGENTS files and design-authority, selected annotation-effect policy and top-level inference principles were read as instructions, outside source evidence.

No dirty diffs/status, unrelated compiler paths, builds, tests, Lean execution, scratch files, Git mutation or delegation. One attempted read-only Python hash command failed because python was unavailable; SHA-256 checks then used sha256sum. No compiler/resource probe ran; no memory or runtime measurement is claimed. Review completed inside the 240-second packet budget.

No files written. Primary owns recording this returned receipt. Reviewer state: STOPPED; no descendants.
