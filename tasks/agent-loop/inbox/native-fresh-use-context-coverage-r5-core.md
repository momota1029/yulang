# NATIVE-FRESH-USE-CONTEXT-COVERAGE-R5-CORE — revision 1

Sprint NATIVE-FRESH-USE-CONTEXT-COVERAGE/r5, contract SHA-256 `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa`.
Session NATIVE-FRESH-USE-CONTEXT-COVERAGE-20261028/r5. Worker/sole author `/root/native_fresh_use_context_coverage_core_r5`; requested Astra/medium; observed model/effort UNKNOWN. ACK sent to Luna before body reads. No descendants or coauthors.

Outcome: candidate source-footprint analysis plus an explicitly unrealized finite alias/discharge trace. No Lean declarations or completed theorem. Theorem types and axiom audit: NOT APPLICABLE (comment-only artifact); checker NOT RUN, prohibited by packet. Not independent review or production authority.

Parent: `YulangClosure.SourceProblem.InferenceSoundness`, Contracts.lean:128, unchanged `∀ s x d a, supported s → generates s x d → solves d a → ∃ e, sourceJudgment s x e ∧ sameScoped s x e a`. All supported-source quantifiers, shared witness, A/B, generalization, effects and executor obligations remain OPEN.

## Result applied to parent

The candidate artifact supplies an exact distinction needed by the native interpretation: the effective root reread during restoration is mutable, whereas readback follows immutable stored relation contexts. Already attached mapped constructors survive the inspected discharge writes. This local observation cannot establish that every prepared image was attached. A later bound can read a smaller residual root after an earlier bound replays a captured original parent. The first missing evidence is authentic reachability or exclusion of a completed capture containing a still-undischarged Replay filter parent that earlier restoration can alias.

The finite candidate has identity 0, old Prefix 1 and Replay 2, renamed Prefix 3 and Replay 4. Preparation maps 2→4, 1→3, 0→0. Earlier restoration reuses original relation p at context 2 and discharges it to 0. Later restoration attaches 0. The original dependency component can expose 2 and 1 without exposing 4 and 3. It misses the fresh weight only if no independently selected copied endpoint/view supplies it. This last exclusion must be checked, not assumed as universal behavior. This is NOT an actual source counterexample, nor a shortest reachable trace.

Exact source owners: `rename_contexts_impl` (candidate_context.rs:1566), `relation_context` (1691), `context` (2630), `relation_with_scoped` (3062), `post_check_context` (3297), `candidate_zero_word_filters` (3669), `candidate_context_execute_relation` (3800), `candidate_context_begin_replay` (4007 vicinity), `candidate_context_step_replay_child` (4097), `candidate_context_fresh_transport_scoped` (4278); `freshen_candidate_graph_retained` root preparation (candidate_scheme.rs:4419), `begin_candidate_fresh_bound` (4670); `candidate_begin_bound_restoration` and `candidate_step_bound_restoration_child` (candidate_extrusion.rs:966,1004). Context interning and relation interning are separate; use_origin is retained in the Transport dependency but is absent from RelationKey. No parent/provider/witness lineage was identified merely by endpoint equality.

## Falsifier and mutual TODO

`R5-CORE-ALIAS-1`, owner Luna for assignment to the existing source/proof lanes: retain authentic pre-prepare p/key/discharge, source B0/B1 order, original fiber IDs, weight map, per-bound restoration roots, Replay key equality and discharge writes, then completed consumer dependency/context/weight readback. A successful actual source trace missing map[p's first root] refutes full prepared-image observation. Any key inequality prevents this particular alias; already-discharged p prevents this particular root change; an authentic invariant proving all such captured p are discharged or filter-free excludes the candidate class. An alternative selected endpoint/view may recover w' but cannot alone establish observation of Replay image 4.

Minimal provisional instrumentation TODO: observations at existing preparation/root-reread/Replay-intern/discharge/readback sites only, on the already leased isolated candidate_scheme source if expressible through its test access. If additional owner writes are needed, Luna must amend first. No production edit requested. Inputs are the pinned Rust owners below. Output should be either one authentic trace with all successful completion receipts or the source-constructor invariant excluding the candidate. The next mathematical step then follows that outcome; do not assume seed inclusion or all-image observation.

Prior work: R4's immutable-constructor insight was reused by direct source inspection; its handwritten NativeRun and restoration premises are not imported or accepted. OriginalEffectHygiene remains only its existing constructor/consumer seam; no broader theorem was claimed. Original source preservation statement and birth-level SCC correction were read; no withdrawn bypass was restored.

## Frozen dependencies and artifact

Primary baseline `1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`; research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (contract locators; no Git run).
Actual SHA-256 readback matched pins:

- candidate_context.rs: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- candidate_scheme.rs: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- candidate_extrusion.rs: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- candidate_effect.rs: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab`
- shadow_apply.rs: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- Contracts.lean: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`

Artifact `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR5Core.lean`, SHA-256 `af8b87e064db2063cb2f2561f88986102271bc44a3e94e12e6df5759a02ea5d6`. Artifact is deliberately comment-only because no executed Lean proof is authorized and no source reachability theorem was established. Handoff byte hash is reported in the final message to avoid self-reference.

Resources: three substantive stages (source footprint; alias candidate and guard analysis; freeze/application). Grant 300 seconds; exact active duration UNKNOWN, charge the full 300-second reservation. Read-only shell inspection and SHA hashing only; no execution probes, checks, Cargo, Lean/Lake, caches, external contact, Git or descendants. Lean project pin read as 4.35.0, with no invocation. No extra/scratch paths. Only new writes are the artifact and this exact inbox. Main proof lane may not import/depend on this result without Luna's versioned amendment.

STOP: writer stopped after freezing revision 1. No remaining descendants or writes. Pending Luna intake and fresh independent review; original parent and native-restoration bridge OPEN.
