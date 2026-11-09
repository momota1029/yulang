# Cycle56: canonical source-alias graph inspection

## Recovery and bounded result
Scheduled start: 2026-11-09T22:27:19Z. Deadline: 22:52:19Z.
Cycle55 stopped after local startup commit 4c93ebad9. Its heartbeat was running,
last updated 21:59Z; no cycle55 design, proof, report, or verification output was
present. Both remote branches still held completed cycle54 at 43b95fe4d. No other
Yulang native worker or visible build process was active. The retained checkout
had no uncommitted tracked changes. No implementation was lost. Recovery took
approximately five minutes and is recorded in notes/heartbeat/dots-main-crash-55.md.
The repository crash-numbering rule makes this recovered run cycle56.

The bounded finite source-alias graph bridge is closed. Original occurrences of
one source name now expose one actual finite graph root even while unknown.
Distinct source names do not merge merely because their readout values coincide.
The existing graph inspector, including its variable/shared captures, is preserved
exactly after routing captured indices. Original source-model meaning, the checked
Index producer and original occurrence diagnostics remain connected.
Storage is still occurrence-sized. This is root canonicalization, not physical
compaction, general equality-class unification, or recursive graph construction.

## Added module and theorem statements
New module: lean/Yulang/CommonRoleCanonicalSourceGraph.lean.
All 17 theorems are imported through Yulang.lean and registered in Audit.lean.
The names below are in Yulang.CommonRoleCanonicalSourceGraph.

1. canonical_source / canonical_eq_iff / canonical_idempotent [補助]: 任意の有限
   source table と occurrence i,j について、正準 root は元の source 名を保ち、
   root の一致は source 名の一致と同値で、正準化は冪等。既知性やモデルの仮定はない。
2. root_identity_exact [補助]: 任意の table、初期 Problem、有限 update 列、i,j
   について、実際に生成した Prepared graph の root が一致する条件は source 名の一致。
3. forces_alias_iff [健全性・完全性の補助]: 任意の table、Problem、同じ source 名を
   持つ i,j について、独立な全 source model が i を str に固定する条件と j の条件は同値。
4. inspect_string_exact [健全性・完全性]: 任意の有限 table、初期 Problem、有限
   update 列、元の occurrence i について、正準 root の実 inspector が str に一致することと、
   元の全 source model が i を str に固定することが同値。整合性・scope 成功の前提は不要。
5. snapshot_unknown_exact [健全性・完全性]: 同じ任意入力、任意の role と visible head
   列について、正準 root の snapshot が unknown であることと、元の source model が
   二つ存在して i の型が同値でないことが同値。整合性・scope 成功の前提は不要。
6. checked_inspection_exact [健全性・完全性の補助]: 同じ任意入力と i,j について、
   実 checked Index producer が成功することと、正準 root の str 検査成功が同値。
7. diagnostic_snapshot_exact [健全性・完全性の補助]: 同じ任意入力、元の request r、
   r が元の累積 requests にあるという前提の下で、元の occurrence pair (i,j) の waiting
   leaf は、source 名が r に対応し正準 receiver snapshot が unknown であることと同値。
8. unresolved_alias_regression [補助・回帰]: table [7,7,9] の未知な三 occurrence で、
   同じ source 名の二つだけが同じ root を持つ。unknown の値の一致で別名を統合しない。
9. solve_detected_base_str [補助]: 任意のこの断片の入力と i,b について、実 reader が
   b を検出したなら b = str。これは正の str 断片の制限であり一般スカラーの仕様ではない。
10. detect_alias_eq / canonical_node_preserved [補助]: 任意のこの断片の入力で、同じ
    source 名の occurrence の reader 全体は一致し、正準化前後の graph node は同一。
11. inspect_routing_exact [健全性・完全性の補助]: 任意のこの断片の入力、任意の既存
    Pattern と occurrence i について、正準 root の実 inspection 結果は、元の inspection
    結果中の capture/cycle 参照を正準化した結果と厳密に等しい。未知の variable/shared
    capture も含む。古い occurrence 番号とのリテラルな一致は主張しない。
12. variable_capture_identity [補助]: 任意の入力、capture 名と i,j について、実
    variable inspection の capture 結果の一致は source 名の一致と同値。モデル前提は不要。
13. capture_type_sound [健全性]: 任意の入力、i、および元の独立 source model a で、
    正準 capture の型は元の occurrence の型と同値。effect 成分の等式は主張しない。
14. shared_receiver_resume_regression [補助・回帰]: table [7,7,9]、request (7,9) で、
    未知の二番目の occurrence が root 0 を capture し、後からその occurrence に str seed
    を加えると、元の receiver と名前付き target が両方とも実 inspector で str に一致する。

主型性や一般 M1 の三つ組の完成は主張しない。有限 table、正の str/equality source、
外から有限に与えられる update 列は、明示した証明断片の制限であり言語の拒否規則ではない。

## Verification
Initial launcher using lake --dir had no selected toolchain; reran from lean/ with
its existing toolchain and cache. A direct reduction regression initially required
kernel reduction for the existing mutual inspector; the final checked proof uses
that reduction. No expectation or theorem statement was weakened.

Final focused build, exit 0:
cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleCanonicalSourceGraph

✔ [297/297] Built Yulang.CommonRoleCanonicalSourceGraph (1.4s)
Build completed successfully (297 jobs).

Trust-0 focused audit, exit 0:
cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle56-audit.lean

'Yulang.CommonRoleCanonicalSourceGraph.canonical_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.canonical_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.canonical_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.root_identity_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.forces_alias_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.inspect_string_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.snapshot_unknown_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.checked_inspection_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.diagnostic_snapshot_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.unresolved_alias_regression' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.solve_detected_base_str' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.detect_alias_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.canonical_node_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.inspect_routing_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.variable_capture_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.capture_type_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleCanonicalSourceGraph.shared_receiver_resume_regression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

Diff gate, exit 0:
bash tools/verify-lean.sh . origin/integration/m1-final --no-build

verify-lean: . @ e02dc3465 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

git diff --check: exit 0.
Full lake build, full Audit and broad axiom gate were deliberately not run by dot.
GitHub check-runs for implementation commit 8e05817f were separately read:
core succeeded at 22:38:19Z and proof succeeded at 22:38:42Z. These named CI
checks are not substituted for the unrun full local Lean/Audit certification.
Core: https://github.com/momota1029/yulang/actions/runs/42713579628/job/129489185361
Proof: https://github.com/momota1029/yulang/actions/runs/42713579643/job/129489179895

## Publication
Local implementation commit: e02dc3465cd711389bbc7d48a08e88e7844cd962.
Remote result commit: 8e05817ffc512f2e2e079e3b16a15e83c099479b.
Result tree: 10ba46d0d9fece28dd7df953cdac8f3f2c3f2534.
Eight changed/additional files were uploaded as individual blobs. Every returned
blob SHA matched its local file. A SHA-only tree based on the remote startup tree
matched the entire verified local tree exactly. A subsequent remote Git fetch
confirmed the result tree. Publication used non-force expected-head updates on
work/dots-main only. This report and completion heartbeat are final bookkeeping,
bringing the cycle to nine unique published paths. No integration branch changed.

## Yulang2 and authority
Fetched work/dots-audit and read notes/audit/x-oracle.md X13-X17 and C3-PARENT,
plus spec/06-roles.md 6.3. These examples support shared-source and associated
constraint behavior, but are not a generic graph proof. No new Yulang2 instance
was run. No semantics decision or question note was needed for canonical routing.

## Remaining bridges and next candidates
General B4 still has five open bridges: source_boundary_adequate,
generated_work_closed, saturate_terminates_and_closes, saturated_frontier_exact,
resolve_dictionary_order_sound. This closes only the named finite source-identity
sub-boundary. Recursive graphs, dynamically allocated source slots, general
candidate applicability, declaration-generated requests, dictionaries and
language-level pending/selected/ambiguous/rejected remain unproved.

Next candidates:
- Prove canonical root retention under extension of the finite source table.
- Connect recursive constructor edges to source-identified graph roots.
- Connect declaration-generated child/request allocation to this source carrier.

## Resources and timing
Retained the existing workspace and Lean cache. No new worktree or cache copy.
Free disk: 48 GB at recovery and completion. Usage quota: unknown.
Report prepared at 2026-11-09T22:38:55Z; elapsed 11.6 minutes from scheduled start.
