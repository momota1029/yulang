# R134 — source-action to effect-constraint causal observations

Status: ADMITTED for an exact two-file candidate and independent static review.
Branch / baseline: `yulang3`, `0961390608a6aadad6add22be38323709ed1a570` (`origin/yulang3`).

## Outcome and parent limits

The parent goal remains Yulang soundness and the original Simple-sub A/B
obligations. This packet completes one test-only observation path needed to
distinguish source-action failure from later effect-constraint failure. It does
not repair the R104 protected failures, change solver behavior, prove source
transport, close effect hygiene or authorize production.

Expected records preserve source-action before/after schedule/index,
occurrence, cause, error kind and diagnostic data; live-effect constraint and
candidate propagation call/result; and diagnostic additions retaining original
occurrence/cause/kind. An “after” event is emitted only when that action returns
successfully; do not claim failed actions always have paired before/after rows.

## Exact source targets

All bases are from committed HEAD `0961390608a6aadad6add22be38323709ed1a570`.
The target hashes identify the two-file candidate to reconstruct from the
scoped working diff and immutable committed blobs:

- `crates/yu-solver/src/lib.rs`: base SHA-256
  `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`,
  target SHA-256
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.
- `crates/yu-solver/src/candidate_source.rs`: base SHA-256
  `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`,
  target SHA-256
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- Recorder dependency: committed
  `crates/yu-solver/src/candidate_effect.rs`, SHA-256
  `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`.

The author may inspect working-tree diffs only for the two target source paths
and must not edit or stage them. All dependencies outside the three pinned
files must be reported as a blocker. Reconstruct the complete candidate in
memory and provide both complete unified patches, per-file target byte counts
and exact hashes.

## Review and stop limits

Implementer: Luna/high lane, 300 seconds. Sole write lease:
`tasks/agent-loop/inbox/effect-permission-causal-observation-r134-source.md`.

Fresh independent `compiler_referee`, 180 seconds, read-only. Authenticate the
handoff and hashes. Review all cfg combinations and recorder availability;
confirm disabled recording does not evaluate observation closures; inspect
borrows, return values, call counts, `?`/early returns, and which paths can emit
“after”; preserve existing assertions and diagnostic payloads. Verify no dirty
typed observer, old scheme adapter, shadow trace hook, or solver-semantic
change is included.

No compiler, Cargo, tests, Lean, checker, storage/environment probe, scratch,
source materialization or build output. Total envelope 900 seconds; Astra 0.
Hash mismatch, missing dependency, borrow/cfg defect, observer dependency or
solver behavior change blocks integration.

After independent PASS, Luna may authorize only these exact two target hashes
as an uncompiled source checkpoint, stage explicit paths through the index and
push the coherent range. Original A/B, consumer, source/native, hygiene and
production gates remain OPEN.
