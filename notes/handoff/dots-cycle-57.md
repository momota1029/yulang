# Cycle57: stable canonical roots under incremental source allocation

## Result and recovery
Scheduled start: 2026-11-09T22:57:19Z. Deadline: 23:22:19Z.
Fetched integration/m1-final and work/dots-audit; inbox is ACTIVE with no cycle cap.
Cycle56 was completed with its report present. No crash recovery or competing
Yulang writer was needed. Reused the existing checkout and Lean cache.

The finite append-only canonical allocation boundary is closed. For arbitrary
old and appended source tables, every old canonical root retains its exact numeric
slot. New aliases route to the old first occurrence, while genuinely new names
route to their first appended occurrence. Executable incremental newRoot equals
rebuilding the entire canonical map. This is independent of type knowledge.
Actual variable/shared captures, capture/cycle reference routing, coherent source
models, and old ordinary constraints remain connected to the allocation operation.

This is allocation alone. It neither generates child constraints/requests nor
establishes graph reconstruction, final source classification, or general B4.
It does not claim scalar inspection remains unchanged when new constraints arrive.

## Theorems and scope
New module: lean/Yulang/CommonRoleCanonicalSourceGrowth.lean.
All 17 public theorems are imported through Yulang.lean and registered in Audit.
Names below are in Yulang.CommonRoleCanonicalSourceGrowth.

1. allocated_source [補助]: 任意の有限 table、extra、新 occurrence i について、
   append 後の実スロットが元の extra の source 名を保つ。
2. representative_append / representative_retained [補助]: 任意の table、extra、
   source 名について、実 lookup は旧 table を先に検索し、無ければ suffix を検索する。
   旧 lookup が i を返すという前提なら、拡張後も同じ numeric slot を返す。
3. canonical_retained [補助]: 任意の table、extra、旧 occurrence i について、
   拡張後の正準 root は旧正準 root の retain と厳密に一致する。モデル前提はない。
4. allocated_alias_root / allocated_fresh_root [補助]: 任意の table、extra と新
   occurrence について、旧名と同名なら旧 root を使う。旧 table の lookup が none
   という前提なら、extra 内の最初の occurrence を割り当てた root を使う。
5. newRoot_exact [健全性・完全性の補助]: 任意の table、extra、新 occurrence
   について、実 incremental allocator の結果は全体を再構築した正準 root と一致する。
6. newRoot_identity_exact / newRoot_old_exact [補助]: 任意の table、extra と該当
   occurrence 対について、新 root 同士、または新 root と旧 root の一致は元の source
   名の一致と同値。既知の型や source model の存在を前提にしない。
7. route_retained [補助]: 任意の table、extra、任意の既存 Observation について、
   全 capture/cycle 参照の retain と canonical routing が可換。
8. variable_capture_retained / shared_capture_retained [補助]: 任意の table、extra、
   任意の旧 graph と新 graph、任意の capture 名（列）と旧 occurrence について、
   実 inspector の正準 root capture が retain 後も一致する。共有名の順と重複を保つ。
   graph の形や未知性の前提はない。scalar/structural 検査の保存は主張しない。
9. canonical_value_retained / allocated_alias_value [健全性の補助]: 任意の table、
   extra、旧 computation 値と fallback について、実 grow 後の旧正準 root の値は
   元の値と厳密に一致する。新 occurrence が旧名と同名なら、その root も旧値を読む。
   これは canonical root の値であり、新 alias 自身の effect 値の等式ではない。
10. coherent_canonical_extension [健全性・完全性の補助]: 任意の table、extra、
    旧 valuation と fallback について、旧 source coherence と、全旧 valuation・
    canonical root 値を保つ coherent な拡張 valuation の存在は同値。
11. solver_and_roots_exact [健全性・完全性の補助]: 任意の table、extra、旧 State
    と fallback について、実 growState 後の ordinary solver の受理は旧 state に
    identity 制約を加えた solver の受理と同値。同時に全旧 root の厳密な保存が成り立つ。
12. append_alias_regression [補助・回帰]: [7,7,9] に [9,7,11,11] を append すると、
    新 occurrence の root は順に 2,0,5,5。これは上記一般定理の具体的な回帰例。

主型性、一般 M1 の三つ組、外側 resolve_exact の完成は主張しない。有限 append-only
source table と allocation-only 操作は明示した断片の範囲であり、言語の拒否規則ではない。
既存の Lean ファイルの定理や型を弱めていない。新しい意味論判断や質問ノートは不要だった。

## Verification
Final focused build, exit 0:
cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleCanonicalSourceGrowth

✔ [299/299] Built Yulang.CommonRoleCanonicalSourceGrowth (1.3s)
Build completed successfully (299 jobs).

Trust-0 focused audit, exit 0:
cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle57-audit.lean

'Yulang.CommonRoleCanonicalSourceGrowth.allocated_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.representative_append' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.representative_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.canonical_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.allocated_alias_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.allocated_fresh_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.newRoot_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.newRoot_identity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.newRoot_old_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.route_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.variable_capture_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.shared_capture_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.canonical_value_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.allocated_alias_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.coherent_canonical_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.solver_and_roots_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGrowth.append_alias_regression' depends on axioms: [propext, Quot.sound]

Diff gate, exit 0:
bash tools/verify-lean.sh . origin/integration/m1-final --no-build

verify-lean: . @ 53da3d506 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

git diff --check and staged diff checks: exit 0.
Full lake build, full Audit, and broad axiom gate were deliberately not run by dot.
Early focused attempts caught simplification details and an unreduced lookup case;
all were fixed without weakening statements. Background shell detachment did not
persist in this executor, so focused commands used bounded resumable tool sessions
with captured logs. No unbounded or aggregate build was launched.

Exact implementation commit bdf5fc0b has completed GitHub checks:
- proof: success. https://github.com/momota1029/yulang/actions/runs/42718034823/job/129504522265
- core: success. https://github.com/momota1029/yulang/actions/runs/42718034335/job/129504515569
These named checks do not substitute for the deliberately unrun full local audit.

## Publication and corrected bookkeeping error
Local implementation commit: 53da3d506.
Remote result commit: bdf5fc0b1960c430a49cae73b033fcf5bf0af973.
Verified result tree: f28eeaddcbab27de308c0e257e1682d29ef30f95.
Seven changed/additional files were uploaded as individual blobs; every returned
SHA matched the local file. A SHA-only tree based on the exact integration commit
matched the entire verified local tree. An explicit fetch of work/dots-main and
`git diff --quiet HEAD origin/work/dots-main` both verified the result (exit 0).

The initial heartbeat a6e3bf1c incorrectly used the stale local tracking tree from
cycle51, although its parent was the correct current commit. It temporarily omitted
cycle52-56 additions on work/dots-main. Exact tree verification caught the mismatch
before the implementation was published. bdf5fc0b rebuilt from the API-verified tree
of integration commit 3ab523c4d, restored all previous content, and added this cycle.
No integration ref changed and no prior content remains lost. Future publications
must obtain the tree from the exact remote commit, and use an explicit tracking
refspec when fetching. This corrective procedure is recorded here and in the
heartbeat's resume hint; a tracking ref alone is not proof of a current base tree.

Final report and completed heartbeat add one new path (eight unique cycle paths).
All ref updates are non-force, expected-head updates to work/dots-main only.

## Yulang2 comparison and remaining work
Read the work/dots-audit x-oracle X13-X17 and C3-PARENT evidence. Those examples
support shared source/associated constraint behavior but do not validate internal
numeric allocation. No new Yulang2 run was performed, and no language semantics
was inferred from this allocator result.

General B4 still has five open bridges: source_boundary_adequate,
generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact,
resolve_dictionary_order_sound. This result closes only the finite canonical
allocation interface within the source-identity/generated-work boundary.

Next candidates:
- Connect declaration-produced child source names to newRoot and their retained captures.
- Prove graph edge reconstruction preserves inspection across allocated source tables.
- Prove allocation plus generated constraints preserves complete source models, including
  requests whose formerly absent names become represented. Allocation alone does not
  justify preserving those requests' old vacuous interpretation.

## Resources and timing
Existing workspace/cache reused; no extra worktree or cache copy. Free disk at
start and report preparation: 48 GB. Usage quota: unknown.
Report prepared at 2026-11-09T23:10:23Z; elapsed 13.1 minutes.
