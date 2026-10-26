# R63 rebuild primary verification — revision 1

Sprint `YULANG3-VIEW-OBSERVATION-COVERAGE-REBUILD-20261026/r1`, contract r2 SHA-256 `909068e6aebc834ae4d6f99b8055f5448dbe26c914c9c71f1e51f81aae001cd9`. Primary verification used the isolated workspace `/tmp/yulang-r63-rebuild-20261026/primary`; proof author's workspace is separate and STOPPED.

## Frozen identity and source pins

The reconstructed candidate SHA-256 is `e2707b5387c85175948c24d3d4dd225473e796e42e7a8c5fdd5160618cd24dd0`; the exact audit source SHA-256 is `daaa660498e7c77d16075072bd06f829a2a5cebb04b2ea1fead38fb6963ec9a3`. Both match the proof handoff and the copies in primary's workspace. The 30 frozen hashes in the original R63 contract were checked against Git baseline `93d08d5867015741b3588ea3df4c56903b2bbe83`; all 30 match. Each Lean source copied into primary also matches its baseline bytes. The validation record is `/tmp/yulang-r63-rebuild-20261026/primary/proof-checks.txt`.

## Independent checker execution

Four literal calls, all exit 0, with no retry, signal or timeout. The focused build took 38.291826169 seconds; the complete audit took 0.915823980 seconds; total checker time 39.386170623/150 seconds. Toolchain outputs identify Lake 5.0.0 and Lean 4.35.0. The process manifest and all four stdout/stderr captures are under the primary workspace; capture lengths and SHA-256 values match the manifest. Calls were the pinned Lake `--version`, `lake env lean --version`, `lake --no-cache build +YulangClosure.PaperObservationCoverage`, and `lake --no-cache env lean -j1 -M1024 --root=. .lake/R63RebuildAudit.lean`.

The complete audit output SHA-256 is `08d379b8ba1aef4d38f2c9cfed3260815708ce5cb2aa1b78aeb41b62de6a1cb9`. Bundled `check_lean.py::validate_audit` passes on the complete captured output. Exact fully qualified theorem names, kinds and count pass 4/4. The first theorem has no axioms; each of the remaining three reports `[propext, Quot.sound]`. Complete types and raw output are retained in the proof worker handoff and primary `call-04.stdout`.

## Primary assessment and limits

The candidate preserves the four requested declarations and quantifiers. It establishes a closed represented force witness with empty graph/type environments and arbitrary declaration table and metadata; no frozen `ObservationStep` starts at a top-level view; no finite trace reaches the wrapped literal delay; and the unchanged connected executor returns `none` for the specified empty-stack state. The worker's handoff applies this to the exact allocated heap in R62 and explains why it obstructs only deriving R62's unqualified finite constructor-observation premise from represented closed typing alone.

This is represented auxiliary-relation evidence. It does not establish that the source compiler emits this term, change the meaning of `none`, refute R62's conditional theorem, prove whole-language execution safety, establish source/native correspondence, or authorize a semantic change. `R62-FINITE-CONSTRUCTOR-OBSERVATION-1`, R23, source/native correspondence, inference A/B, whole-language safety and production remain OPEN. No Rust or root import was changed. The proof worker is STOPPED; primary checker processes and runner are all complete. Fresh non-author review and primary adjudication remain pending.
