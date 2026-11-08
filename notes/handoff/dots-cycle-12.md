# dots cycle 12: finite structural source positions

- Start: 2026-11-08T17:53:06Z. Proof and six artifact publication/readback completed by 17:59:46Z. Report preparation 18:00 UTC; roughly 7 minutes, within latest 25-minute cap. Final heartbeat records final publication time.
- Latest fetched integration: `0483319a3`; local merge base `740b5a1ac`. Local commits `eb1b55c34`, `4e91c91e4`, `dd6a3b1af`.
- Prior cycle11 heartbeat was completed and report present. No concurrent writer or recovery was needed.
- Latest inbox ACTIVE, max12. **This reaches the cycle cap. Do not start cycle13 unless the inbox limit is raised.** No schedule was changed.

## Result

`CommonRoleSourcePositions` supplies an independent inductive source-position judgment, proves its equivalence with the executable selector, characterizes its finite domain exactly, and transports the entire copied subtree through every variable-bearing actual producer child. Lower and upper endpoints may differ. This advances structural provenance beyond cycle11's captured-root theorem.

**T1c / general B4 / X13–X16 remain unproved.** Source positions are not global source IDs. Equality of Ty does not establish identity. No saturation/termination or full finite dynamic request domain is claimed.

## Declarations (all universally quantified; auxiliary unless noted)

Namespace `Yulang.CommonRoleSourcePositions`:

- `position_exact`: 全ての型 t, payload と自然数 n について、`atDepth n t = some payload` iff 独立判断 `SourcePosition t n payload`。局所の健全性・完全性の両方向、M1全体の完全性ではない。
- `position_bound`: 全ての t, payload, n で `SourcePosition t n payload` なら `n < t.nodes`。補助。
- `position_exists`: 全ての t,n で、ある payload が `SourcePosition t n payload` を満たす iff `n < t.nodes`。補助、有限領域の正確性。
- `atDepth_add`: 全ての n,k,t で、深さ n+k の選択は深さ n を選択してから k を選択する Option.bind と等しい。補助。
- `production_positions`: 全ての visible,q,d,lp,hp,h で、実 `production visible q = some(d,lp,hp)` かつ `captureDepth d.head = some h` なら、lower の h 位置は lp、upper の h 位置は hp を指す SourcePosition を持ち、h は両端点それぞれの nodes 未満。補助。
- `copied_subtree_origin`: 全ての visible,q,d,lp,hp,r,h,v,k で、上記 production と captureDepth の前提、`r ∈ d.requirements`、`variableDepth r.2 = some v` があれば、r の実 instantiate 後 lower/upper を v+k で選んだ結果は、各親端点を h+k で選んだ結果と等しい。補助。範囲外の none も等しい。
- `copied_positions_exact`: 全ての visible,q,d,lp,hp,payload,r,h,v,k、直前と同じ前提で、子の v+k が payload を指す SourcePosition iff 親の h+k が payload を指す SourcePosition。lower と upper の両方。局所の健全性・完全性、全体には補助。
- `child_subtree_origin`: 全ての visible,q,child,d,lp,hp,h で、上記 production と captureDepth の前提、および `child ∈ children q d lp hp` があれば、ある r∈d.requirements が child.role=r.1 を満たし、全ての v（variableDepth r.2=some v）と k について、子の両端点 v+k の選択は各親端点 h+k の選択と一致する。補助。

## Verification and actual commands

`git fetch origin integration/m1-final work/dots-main` succeeded. `git merge --no-edit origin/integration/m1-final` succeeded. Rules, current standing orders/inbox and prior report were read. Shared existing Lean cache reused.

`cd lean && lake build Yulang.CommonRoleSourcePositions --wfail` final full output:
```
✔ [271/271] Built Yulang.CommonRoleSourcePositions (1.2s)
Build completed successfully (271 jobs).
elapsed=1.361
exit=0
```

`lake env lean --trust=0 /tmp/cycle12-audit.lean` exit 0. The temporary file imports only the new module and prints axioms of all eight declarations. Output:
```
'Yulang.CommonRoleSourcePositions.position_exact' depends on axioms: [propext]
'Yulang.CommonRoleSourcePositions.position_bound' depends on axioms: [propext]
'Yulang.CommonRoleSourcePositions.position_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourcePositions.atDepth_add' depends on axioms: [propext]
'Yulang.CommonRoleSourcePositions.production_positions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourcePositions.copied_subtree_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourcePositions.copied_positions_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourcePositions.child_subtree_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Only standard `propext`, `Classical.choice`, `Quot.sound`. No sorry/new axiom/native_decide. Explicit token scan found none. All eight registered in Audit. `git diff --cached --check` passed.

`verify-lean.sh` and full lake build/Audit **not executed**, as current standing-orders/I-5 prohibit them for dot. No full PASS claimed. Supervisor verification is pending.

## Failures, limits and Yulang2 comparison

- First timing attempt used `/usr/bin/time`, absent on this machine; replaced with Bash `time`. Initial focused compilations exposed induction elaboration, reserved identifier and simp-normalized goal errors; corrected and final module rebuilt successfully.
- Audit branch fetch was rejected by auto-review: fetching stopped `work/dots-audit` was considered outside current scope. No workaround attempted. Integrated `notes/audit/x-oracle.md` was read instead. X1/X2 behavior is context only; this internal structural position construction has not been tested against Yulang2 runtime.
- A heartbeat update mistakenly had a future timestamp; immediately corrected to measured-current minute before final publication. No execution outage observed.
- No new semantic choice was needed. Regular loops remain opaque as in the existing Ty/selector, not unfolded by this judgment.
- Disk available start/end: 19G / 19G (63G filesystem, 70%). No new worktree/cache copy. No unpublished source deleted.
- Usage accounting: unknown; no supported quota measurement available.

## Publication and remaining work

Six artifact paths published individually and read back exactly on `work/dots-main`:
1. lean/Yulang/CommonRoleSourcePositions.lean
2. notes/design/2026-11-08-cycle12-source-positions.md
3. lean/Yulang.lean (append only)
4. lean/Audit.lean (append only)
5. lean/README.md (append only)
6. notes/design/INDEX.md (append only)

This report is seventh artifact; heartbeat is separate. No other branch written. Artifact publication last commit before report: `c0c607171c041f47ba31cdc55877e97573186be3`. Large existing files were appended using remote content held outside model context, with before-hash and after-readback checks.

Five substantial remaining bridge groups: (1) global source identity and allocator from actual source graph, (2) finite domain closed under dynamically generated requests, (3) monotone saturation plus termination, (4) final classification/dictionary observation connection, (5) outer-entry conformance X13–X16. These are not five small lemmas; no credible exact count is known. Current theorems cover structural source-path provenance inside group1, not its completion.
