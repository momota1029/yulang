# Cycle53: original occurrence diagnostics

## 基点・復旧・部分目標
予定開始 2026-11-09T20:57:19Z、期限 21:22:19Z。開始の shell 確認は 20:59:40Z。
integration/m1-final は `45e5de297fb37102cfca8f8dd82f217120471552`、前回公開枝は
`dca6eee2a16356e74a9b53c2f3f3449b1035fd44`。
最新の standing orders と inbox I-12 までを読み、ACTIVE・STOP なし。
cycle52 は completed 心拍と報告が揃い、復旧は不要。唯一の作業場とキャッシュを再利用。
統合時の競合は前回報告・心拍だけで、公開済み完了記録を保持し、`84d0dfbcf` に記録した。
開始心拍は `d1dcb821a83e23c821f3e430a591cd353bf52251` に公開した。

**今回の限定した部分目標は閉じた。** 元の batch/request occurrence を残す診断について、
実際の incremental solve から作った結果が、独立な source model の意味を満たすことを示した。
順序と重複は nested All₂ とリストの等式で保持する。名前が存在しない要求も消さない。
一方、当初調べた既存の一般 recursive diagnostic tree への直接接続は閉じていない。
その Endpoint.eval は int だけを観察し、known str を unknown にすることを実装と定理で確認した。
str を int や named に偽装せず、既存の有限 str/equality 断片の adapter として境界を明示した。

## データ・意味・量化
新規 `CommonRoleDynamicIndexOccurrenceDiagnostics` のみで実装と証明を追加。
全 table T、初期 Problem P、有限更新列 U、元要求 r、slots i,j、Bool waiting を量化する。
元入力全体は appendMany T P U。独立な Meaning は、この元入力の SourceModel 全体に
対する ForcesString の真偽であり、solve・pending・診断関数を参照しない。
RequestMeaning は元名と全 leaf の意味を対応させ、Represents は元 batch/request 列と
診断列を既存の All₂ で結ぶ。主定理 diagnose_represents に成功・model・閉包の外部前提はない。

request node は元の名前と全 slot pair のリストを保持し、leaf の Bool は実 pending 所属。
空の endpoint list は missing-name 情報であり、言語の rejected に写していない。
ready も selected 辞書ではない。固定有限 carrier、正 str seed、slot 型等式、
有限な外部入力更新列という制限は証明断片の限定で、仕様上の拒否条件ではない。
空 table、alias、循環、元要求の重複を排除しない。効果成分を新たに拘束しない。
診断 adapter は scope-error 時にも元要求を見せるが、既存 run の返値や意味は変更しない。

## 11 定理と M1 のどの側か
すべて `Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics`。
- original_order（補助・要求保持）: 任意 T,P,U、診断から元名を取り出した入れ子リストは、元の全 batch/request 列そのもの。
- inspect_endpoints（補助）: 任意 packet,r、診断の全 endpoint pair は元名を表現する canonical pairs の列と等しい。alias の別 occurrence を保持。
- inspect_missing（健全性・完全性、scope 観察）: 任意 packet,r、空 endpoint list iff 両方の名前を表す slot pair が存在しない。
- inspect_exact（健全性・完全性）: 任意元要求 r,i,j,waiting、leaf 所属 iff 元名の一致かつ独立 Meaning。r の元入力所属のみを前提にする。
- diagnose_represents（健全性・完全性、主定理）: 任意 T,P,U、実診断は元の全 batch/request occurrence に対する独立 Represents を満たす。追加の前提なし。
- original_retained（補助・要求保持）: 任意の元 batch occurrence とその要求は診断の対応する row に残る。重複の厳密な保持は original_order が保証。
- inspect_checked（健全性・完全性、実行接続）: 任意元要求 r,i,j、waiting leaf iff 元名一致かつ実 checkedProduceIndex が none。
- update_order_inspect（健全性・完全性、順序独立）: 同じ更新所属を持つ任意二列について、同一要求の診断はリストも含め完全一致。外側の batch 順序は元入力に従って保持。
- inspect_rebuild（健全性・完全性）: 任意要求の incremental 診断は、元入力全体の full rebuild による診断と等しい。
- repeated_and_missing（回帰）: 二つの重複要求が二つの waiting node として残り、欠落名を含む三つ目の要求も空 endpoint node として残る。
- legacy_endpoint_erases_string（境界の補助）: 任意 ordinary state と slot で、実 materialize が str を返すなら、旧 Endpoint.eval は unknown。

主型性の新結果はない。一般 recursive role tree、四分類、辞書、source lowering の証明ではない。

## 検証
### Focused build
`cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics`
終了コード 0:
```text
✔ [293/293] Built Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics (1.2s)
Build completed successfully (293 jobs).
```

### Focused trust-0 audit
`cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 /tmp/cycle53-audit.lean`
終了コード 0:
```text
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.original_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_endpoints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.diagnose_represents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.original_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.update_order_inspect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.repeated_and_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics.legacy_endpoint_erases_string' depends on axioms: [propext]
```

### Diff gate
`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`
終了コード 0:
```text
verify-lean: . @ 38d44d976 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全 11 定理の公理は propext / Classical.choice / Quot.sound の範囲内。
Yulang.lean に import を追加し、Audit に全定理を登録した。git diff --check も終了 0。
初回の証明では composition の簡約と pair witness の消去が不足し、手動の pair 等式に直した。
標準名 List.Forall₂ がこの環境に存在しなかったため、既存 CommonRoleOutermostResolver.All₂ を使った。
最終コードで focused build と trust-0 audit を再実行して通過。未完了の処理はない。
全体 lake build、全 Audit、全体公理 gate は指示どおり未実行。監督役の全体検証が必要。

## Yulang2 との照合
work/dots-audit の最新 x-oracle.md の X13〜X17、C3-PARENT、および spec/06-roles.md 6.3 を確認。
旧実機の有限例は、この任意有限入力の診断の一般証明の oracle ではない。
新しい Yulang2 実機実行はなし。意味論を決めずに進められたため質問ノートは追加していない。
設計ノートに、既存 tree の int-only carrier と str の不一致を明記した。

## 一般 B4 の残り
5 本のまま: source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、
saturated_frontier_exact、resolve_dictionary_order_sound。
今回閉じたのは、固定有限 str/equality 断片の exact frontier から、元 occurrence の独立診断への橋。
一般の 5 本が閉じたという主張ではない。次に必要な候補:
1. 一般 source endpoint の scalar carrier を str を保持できる形に設計し、既存候補判定との意味保存を示す。
2. その carrier 上で実宣言からの child/request 生成と診断 node の対応を示す。
3. 動的に増える child の有限領域と source identity の閉包を接続する。

## 公開・容量・時間
実装 commit `38d44d976`。個別 blob と SHA のみの tree、非 force・expected-head 指定で
work/dots-main だけに公開する。integration の全差分には cycle52 の検証済み完了追記も含める。
公開 commit/tree、全ファイル読戻しの結果は確認後に追記する。現段階は公開準備中。
開始・検証時とも空き 48GB。worktree 増設、キャッシュ複製、削除はなし。使用量の枠は不明。
報告準備時刻 2026-11-09T21:06:52Z、予定開始から 9.6 分。25 分の上限内。

### 公開・照合の完了
成果 commit `b1faebf65c3aa6dcc38b77d70d18195370f0e9e7`、
tree `1b5f395a42da7674ffe638ad4bcfc247ee7caee9`。
全 9 ファイルを個別 blob として作り、SHA のみの tree、非 force・expected-head で公開した。
公開 tree 全体がローカルの検証 tree と一致。remote ref と tree を再取得した。
全 9 ファイルの内容と blob SHA も個別に読み戻し、完全一致を確認。未確定の公開操作はない。
対象 commit の status 一覧と connector 対象の PR-triggered workflow 一覧は空。
CI PASS とは主張せず、全体検証は監督役へ残す。

完了記録時刻 2026-11-09T21:09:57Z、予定開始から 12.6 分。
10 分付近の結果公開とともに running 心拍を更新し、この最終記録で completed にする。
限定部分目標と検証・公開・照合まで完了したため、時間を埋める補題は追加しない。
終了時の空き 48GB、使用量の枠は不明。次サイクル用に既存作業場を保持する。
