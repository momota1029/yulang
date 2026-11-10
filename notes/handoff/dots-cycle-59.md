# Cycle59: actual child source occurrence allocation

## Result and exact boundary

既存の unary・int materialization adapter が実際に生成した capture-bearing child について、依存 endpoint の source 名を計算し、既存 canonical root と完全な graph inspection を保つ occurrence allocation へ接続する部分目標を閉じた。親が計算された source-template closure に属すること、実際の production の成功、captureDepth の存在、実際の children への所属を前提とする。呼び出し側から source 名の等式や graph 正当性を渡す必要はない。

対象は任意の有限 source table、checked registry、root と parent の source request、ordinary state、成功した declaration と lower/upper type、capture depth、生成された child。存在する childSource は closure 内にあり、現在の状態で実 child と一致する。任意の将来状態で materializedDomain に属し、その各依存 occurrence の owner は root の依存 source に由来する。任意の旧 graph、role、visible-head list に対して、allocation 後の snapshot は旧 canonical owner の snapshot を retain したものに一致する。依存の順序と重複を保持する。

これは子ごとの occurrenceNames を追加する定理である。全 descendants を一つの計算された allocation 領域へまとめる拡張には着手予定だったが、成果は残っていない。一般 interval materialization、任意の recursive syntax node の確保、旧 node 更新、B4 全体は対象外。constructed wrapper を新 source 変数として扱わない。新しい意味論や拒否範囲は決めていない。

## Theorems and role

以下11宣言はすべて B4 の source identity/generated work に効く**補助**。M1 の健全性・完全性・主型性そのものの完成ではない。

- extract_dependencies: 任意の抽出深さと parent/child endpoint について、extract が child を返せば、child の全 source slot は parent に含まれる。
- plug_dependencies: 任意の template と endpoint について、plug 後の全 source slot は元 endpoint に含まれる。
- declaration_dependencies: 任意の declaration と parent/child source request について、child が declarationChildren に属せば、その全依存は parent に含まれる。
- next_dependencies: 任意の registry と parent/child について、child が構造的 next 列に属せば、その全依存は parent に含まれる。
- closure_dependencies: 任意の registry、root、closure 内の child について、その全依存は root に含まれる。現在状態で選択されない候補も含む構造的 closure の主張。
- owner_present: 任意の table、child と計算された occurrence の添字について、位置から求める旧 owner は child の依存列に属する。
- occurrence_source: 同じ任意のデータについて、計算された新 occurrence の source 名はその旧 owner の source 名と一致する。
- allocated_root: 同じ任意のデータについて、新 occurrence の newRoot は旧 owner の canonical root を retain したものと一致する。alias の等式は追加前提にしない。
- allocated_identity_exact: 任意の二つの新 occurrence が同じ newRoot を持つことと、二つの旧 owner の source 名が同じことは同値。未知という観察だけでは source を同一視しない。
- allocated_snapshot: 任意の table、child、旧 graph、role、visible-head list、新 occurrence について、完全な inspectSnapshot を旧 canonical owner から保存する。
- actual_child_allocation: 上記の実 production・capture・closure・child 所属の前提から、実 child の source witness、将来状態の有限領域への所属、root 依存由来、全 occurrence の canonical root と完全な snapshot 保存を同時に得る。

## Verification

ローカル実装 commit a4c10fed4859b6e2d11b73df4997fb02b9917a4e を変更せずに復旧検証した。2026-11-10T00:24:09Z に全 focused check が終了。

1. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleChildSourceAllocation` — exit 0。

```text
Build completed successfully (306 jobs).
```

2. `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle59-recovery-audit.lean` — exit 0。入力は当該 module の import と Audit.lean に登録済みの11宣言の #print axioms。11宣言すべての依存公理は propext / Classical.choice / Quot.sound の範囲内。

```text
'Yulang.CommonRoleChildSourceAllocation.extract_dependencies' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.plug_dependencies' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.declaration_dependencies' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.next_dependencies' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.closure_dependencies' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.owner_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.occurrence_source' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.allocated_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.allocated_identity_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.allocated_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildSourceAllocation.actual_child_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

3. `bash tools/verify-lean.sh . origin/integration/m1-final --no-build` — exit 0。取得し直した integration/m1-final は b579e4b341dd93e715afb1e35cadaedf08e8c37e。

```text
verify-lean: . @ a4c10fed48 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全体の lake build、全 Audit.lean、広域 AxiomGate は実行していない。focused build と11宣言の監査を全体検証 PASS と読み替えない。公開 commit の CI は未確認。復旧前から記録されていた00:06:41 UTCの306-job buildと00:07:48 UTCのdiff-only検証だけで済ませず、上のfocused checkを再実行した。

## Publication and remote preservation

復旧開始時、work/dots-main は 0c04c850f9e01a33f6544032b0deebc077b1f880、最新 tree は 8ecb7ad366ef41d42b1b7bf8069e8a2b2e1ac0bc。ローカル追加6ファイルの旧 blob/不存在と、この最新 remote tree の対応がすべて一致することを確認した。

成果6ファイルを GitHub アプリ経由で blob 化し、全 SHA がローカル blob と一致することを確認。最新 remote tree を base にした tree c4d0a3534a6cf441a008efe91322078a0d275357、commit c7a46b5c3fd51997a2055921538d78ee70719210 を、非 force・expected-head 付きで work/dots-main へ公開した。2026-11-10T00:27:24Z までに公開 tree を API から読み戻し、成果6ファイルの一致と、対象外2139エントリの保持を確認した。integration/m1-final など他枝は変更していない。

成果は lean/Yulang/CommonRoleChildSourceAllocation.lean、lean/Yulang.lean、lean/Audit.lean、lean/README.md、notes/design/2026-11-10-cycle59-child-source-allocation.md、notes/design/INDEX.md。これに本報告、完了心拍、復旧記録を加え、cycle59 の公開対象は計9パス。

本報告・完了心拍・復旧記録の公開は上記成果 commit を親として行う。公開後の head/tree/blob 照合結果は呼び出し元へ報告する。

## Interruption, recovery, and timing

開始は2026-11-09T23:57:19Z、25分枠の期限は2026-11-10T00:22:19Z。cycle58 の復旧後、実作業開始は00:03 UTC。source commit は00:07:33 UTCに残っていたが、remote は00:04:05 UTC更新のrunning心拍から進まず、cycle59成果・報告は公開されなかった。00:22 UTCの確認で関連するLean/Lake/Gitプロセスは見つからず、担当から応答も得られなかった。原因は特定できていない。

25分枠以内の公開・報告に失敗し、10分/20分の定期心拍も remote へ反映されなかった。この運用違反を明記する。local 心拍の00:07:19 UTC更新は remote 心拍の代わりではない。復旧は00:23:38 UTCに開始し、新規の証明作業を増やさず、残存実装の検証・公開・報告に限定した。cycle59を閉じる復旧であり、新しい証明サイクルは開始していない。

報告準備時刻は 2026-11-10T00:28:41Z、開始から 31.4 分、25分枠を 6.4 分超過。最終公開時刻は完了心拍のcommit時刻で確認できる。復旧開始時・報告準備時とも空き容量は48G（63G中13G使用）。元の作業開始時点の測定は未確認。使用量枠は不明。

## Yulang2 and remaining work

設計ノートに記録された照合資料は work/dots-audit の notes/audit/x-oracle.md、X13〜X16 と C3-PARENT。共有変数・兄弟義務のsource-level証拠であり、numeric graph allocationの実機検証ではない。復旧で新たなYulang2実行はしていない。新たな質問ノートや意味論の判断はない。

一般B4の未完了の橋は引き続き5本: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、saturated_frontier_exact、resolve_dictionary_order_sound。今回の断片で橋全体は閉じていない。一般 resolve_exact、X13〜X16の外側入口の完成も主張しない。

次の候補:
1. 子ごとの occurrenceNames から、closure 全体で共有する計算済み allocation 領域へ接続する。
2. 一般 interval materialization とsource carrier の適合条件を明示し、actual_child_allocation の unary/int 境界を外す。
3. 旧 node 更新・生成された ordinary constraint が source model と graph inspection に与える変化を扱う。
