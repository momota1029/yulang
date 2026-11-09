# Cycle51: finite residual update batches

## 基点・復旧・部分目標
予定開始2026-11-09T19:57:19Z、期限20:22:19Z。最初のshell時刻は19:59:02Z。
`integration/m1-final`を取得し、基点`fb7426cc9598b8ac9e1362cd94430cf65d76cbfe`、
公開枝`89ccde577c4cd30c0a930584c01850d57ac12143`を確認。
standing ordersとinbox I-12までを再読し、ACTIVE・STOPなし。
cycle50は完了心拍と報告が揃い、復旧不要だった。唯一の既存作業場を再利用し、
他の書込み・ビルドがないことを確認した。統合取り込みの競合は前回報告と心拍のみ。
統合済みコードを変更せず、より新しい検証済み完了追記を重ね、`d35ec76f3`に記録。
開始心拍は`aae96622d79c7f05d34fa3679cf9badcd9b5e916`で公開した。

**部分目標は閉じた。** 有限str/equality断片で、後から来るstr制約・slot型等式・
新しい名前付き要求を任意の有限回数追加しても、各回で既知事実と保留要求だけに
圧縮した結果が、元の全入力を保持した独立source意味論の全モデルを保存する。
cycle50の追加str seedだけの継続から、後着等式・後着要求・任意有限バッチへ拡張した。

## 定義と量化
新規`CommonRoleDynamicIndexResidualBatches`のみ。既存Lean定義・定理は変更していない。
`Problem T`はstr seed slot列、slot型等式列、名前付き要求列を持つ。
`Satisfies`は既存の独立SourceModel。`compact`は導出済みstr事実と保留要求を保持。
`advanceMany`は有限update列を順に適用し、`appendMany`は元の全制約を連結する。
`solve`は既存driverで残余Packetを作る。`run`は圧縮前の全要求のendpointを検査する。

定理は任意の有限table T、初期Problem P、任意の有限update列U、全slotの型・効果への
任意割当aを量化する。空table、重複名、cycle、未到達slotを排除しない。
SourceModelが制約するのは型成分で、効果成分は自由。外部の充足性前提はない。
受け取るsource tableは固定で、追加バッチが新しいslotをallocateすることは扱わない。

## 定理15本とM1のどの側に効くか
以下の「全モデル」はこの有限正str/equality断片のSourceModelの全モデルである。
- `append_models`（健全性・完全性、補助）: 任意P,Q,aについて、appendのモデル iff PとQ両方のモデル。
- `compact_models`（健全性・完全性）: 任意P,aについて、圧縮前後のモデルが同じ。
- `advance_models`（健全性・完全性）: 任意P,Q,aについて、圧縮後にQを足した結果と元のPへQを足した結果のモデルが同じ。
- `appendMany_models`（健全性・完全性、補助）: 任意P,U,aについて、全連結のモデル iff PとU内の全updateのモデル。
- `advanceMany_models`（健全性・完全性、本部分目標）: 任意P,U,aについて、反復圧縮・更新後のモデル iff 元の全バッチ連結のモデル。
- `solve_models_exact`（健全性・完全性）: 任意P,U,aについて、最終Packetモデル iff 全バッチの独立sourceモデル。
- `solve_checked_exact`（健全性・完全性）: 任意P,Uとslot i,jについて、実checkedProduceIndexがsomeを返すoutが存在 iff 全バッチの全sourceモデルがiをstrに強制する。
- `solve_pending_exact`（健全性・完全性）: 同じ量化で実checkedがnone iff iの型が非同値な二つのsourceモデルが存在する。これは任意slotに対するchecked失敗の特徴付けであり、Packet.pendingの所属定理ではない。
- `run_ok_iff`（健全性・完全性、入口）: 任意P,U,packetについて、run=ok packet iff 全元要求の名前が存在しpacket=solve。
- `run_success_iff`（健全性・完全性、入口）: ok packetの存在 iff 全元要求のendpointが存在する。
- `run_models_exact`（健全性・完全性、本入口）: run=ok packetを前提に、任意aについてPacketモデル iff PとU内の全updateの独立モデル。
- `run_has_model`（健全性・非空性）: run=ok packetなら、具体的な全str・空effect割当がモデルになる。
- `update_order_models`（健全性・完全性）: 任意P、同じupdate所属を持つ二つの有限列left/right、任意aで、solveの全モデルが一致する。atoms・診断のリスト順の同一性は主張しない。
- `equality_then_new_obligation`（回帰）: 4slotの初期seed0・20→30要求が保留された後、0=1の等式、続いて30→40の要求を追加すると保留が空となり、slot3で実checkedが成功する。上記一般定理の特殊例。
- `missing_requests_survive_validation`（境界回帰）: 初期10→99と追加98→20の欠けたendpointは、圧縮後も元の順に両方errorとして残る。

主型性の新結果はない。有限carrier・正str・type equality・提供済み有限update列という限定は
実装/証明断片の限定で、言語仕様の拒否規則ではない。docstringに明記した。
実checked成功は元要求所属を前提にせず、任意i,jで読める。要求にないcheckedの再実行が
モデルを保つとは主張しない。in-place cacheや計算量改善も証明していない。

## 検証
コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build --wfail Yulang.CommonRoleDynamicIndexResidualBatches`、終了コード0:
```text
✔ [288/288] Built Yulang.CommonRoleDynamicIndexResidualBatches (1.3s)
Build completed successfully (288 jobs).
```

コマンド `cd lean && ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 /tmp/cycle51-audit.lean`、終了コード0:
```text
'Yulang.CommonRoleDynamicIndexResidualBatches.append_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.compact_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.advance_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.appendMany_models' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.advanceMany_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.solve_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.solve_checked_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.solve_pending_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.run_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.run_success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.run_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.run_has_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.update_order_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.equality_then_new_obligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDynamicIndexResidualBatches.missing_requests_survive_validation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

コマンド `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`、終了コード0:
```text
verify-lean: . @ ea27c46eb (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

全15定理をAuditへ登録し、Yulangのimportも追加。公理はpropext / Classical.choice / Quot.soundのみ。
最初のfocused試行はletの簡約不足とExceptの決定可能性で失敗し、let簡約と定義による計算へ
修正後に最終コードを再build・trust-0 auditした。`git diff --check`も終了0。
独立の読み取りレビューは阻害点なし。scope保持・aliasの扱い・型成分だけの意味論、
checked失敗とpending列所属の違い、固定table・効率未主張の境界を確認した。
全体lake build・全Audit・全体公理gateは指示どおり未実行。監督役の全体検証を待つ。

## Yulang2との照合
最新`work/dots-audit`のx-oracle X13〜X17とspec/06-roles.md 6.3の
関連型等式・後からの束縛・兄弟が安定するまでの保留（88、95、132〜134行）を読んだ。
旧実機の有限例はこの内部carrier全般のoracleではない。新しいYulang2実機実行は未実施。
意味論の選択はしておらず、質問ノートは追加していない。

## 残りの橋と次の候補
一般B4の残りは5本のまま:
source_boundary_adequate、generated_work_closed、saturate_terminates_and_closes、
saturated_frontier_exact、resolve_dictionary_order_sound。
今回の結果は固定source領域での更新と意味保存を閉じるが、一般形の橋の本数は減らさない。
全strモデルが常にあるため、矛盾する任意普通制約へのrefinementは扱わない。
parser/lowering、growing carrier、四分類、辞書同値、主型性も未接続。

次の候補:
1. 最終Packet.pendingの所属を、全元要求と最終source forcingから直接特徴付ける。
2. strを保持するsource endpointと既存の診断treeを接続する。
3. 固定slot tableの外から生成されるchildへ、source領域と停止性の契約を接続する。

## 公開・時間・容量
実装commit `ea27c46eb`。GitHub appで個別blobとSHAだけのtreeを使い、
非force・expected-head付きref更新で`work/dots-main`だけに公開する。
integration基点からの差分は9ファイル（前回の完了追記も保持）。
この時点は公開前であり、commitと読戻しの結果は確認後に追記する。
開始と検証終了時の空きは48GB。使用量の枠は不明。重い未完了処理はない。

### 公開と照合の完了
成果commit `c6b0fee4a9285754c9472f1e158d7daf86e26b59`、tree `82bcd599779ff3bff10a889b132f9b69399c6b5a`。
個別blobを作り、SHAだけのtreeを構成し、非force・expected-head指定で公開した。
公開tree全体がローカル検証treeに一致。remote head・commit/tree・全9ファイルを再取得し、
全blob SHAがローカルのファイルhashに一致した。未確定の公開操作はない。
10分心拍は`98da3d058c30af1b47b8e916baefd91bf6959b29`で公開済み。
成果commitのstatus一覧・connector対象のPR-triggered workflow run一覧は空で、CI PASSとはしない。
全体検証は引き続き監督役が行う。

最終記録時刻2026-11-09T20:08:53Z、予定開始から11.6分。25分上限内で部分目標・検証・公開・照合まで完了。
時間を埋めるだけの補題は追加せず終了する。最終空き48GB、使用量の枠は不明。
この追記と完了心拍だけを最後に公開し、読み戻して一致を確認する。
