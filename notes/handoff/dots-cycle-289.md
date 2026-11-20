# dots-main cycle 289: 実際の親効果・where 子に結び付く補助 receipt

## 今回できたこと

元の mixed-kernel を変えず、実据付で生成された where 子について、
証拠を採取して検査し、証拠が揃ったときだけ親の関連出力を公開する
**実行可能な Lean の補助相**を追加した。対象は cycle 287 からの二つの
実ソース枝。親 `F(a)` の処理後、座標 2 に `F(F(a))` を要求する。
子が型を丸ごと受け取る枝は出力を公開するが、行を分解する枝は
`inspection-pending` のまま。後者は拒否ではない。既存の DecisionGuard
を満たすだけでは今回の公開には足りない。

1. **元依存先からの照合（健全性・固定二枝の完全性）。**
   `ReceiptWire289` と `ReceiptExtract289` は宣言の有限リスト、実 producer
   の記録とその対象、実際に生成された辺、現行候補の報告、alias class
   に残る出力要求を取り出す。二枝の実据付前後で
   `ReceiptWitness289.check_iff` は成功と、実 producer・Generated 辺・
   ソース由来の不活性な葉・循環しない信頼済み slice 拡張との同値を示す。
   台帳 plan の有無、古い DecisionGuard、同じ名前だけでは認めない。
   別 registry、欠落した producer、別対象・切り離した辺、残存要求には
   区別した診断を返す。

2. **有限照合の穴を二つ再現し、対象内で塞いだ（閉じた反例・補助）。**
   `ReceiptCollision289.checked_collision` では、同じ宣言でも、観測済み
   constructor key 6 の登録を除いた checked registry を宣言だけの
   検査は通すが、Frame は存在しない。`ReceiptCatalogue289` は実記述子
   のキー 6 と 0 を現行・履歴の双方で照合し、key 6 の変化を拒む。
   ただし **未観測の key 8** の変化は有限照合を通り、完全な Metadata や
   Frame を持たない（`AnchorFixture289.still_finite_metadata`）。
   さらに `ReceiptIdentityCollision289` は同じ子 ID・役割でも引数を
   slot 0 から 1 にずらすと実生成辺でも現行 Frame でもなくなることを
   示す。`ReceiptOccurrence289.encode` の固定 Roles 内の単射性を使い、
   `ReceiptExactLink289` で役割・順序付き型区間・名前付き出力まで含む
   子を、実際の同じ producer の効果と照合した。この偽子は
   `detached` になる。任意 registry / Metadata の認証ではない。

3. **保存した stamp の再検査と実行経路（健全性・固定二枝の完全性・補助）。**
   補助相は探索 → receipt 保持 → 公開。raw の一歩で補助相を探索に戻す。
   `TypedStamp289` は現在の Offer に加え、完全な親子キーと有限の
   型・行 descriptor を各々正しい identity map で符号化して保存する。
   同じ Offer でも行端点を row0 から row1 へ変えると
   `stale-typed-stamp`。型付き埋込みで個々の符号を輸送できるが、順序や
   記述子の追加まで保存すると仮定しない。現行 class に出力要求があれば
   再公開できない。cycle 264 の実 MixedKernel.Step による alias merge
   後にもこの拒否を証明したが、cycle 264 の提供済み journal を
   今回のソースから到達可能だとは主張していない。
   `StampedProduct289.paths_iff` と `StampedExport289.exact_terminal` で、
   二枝では補助 stamp を消すと元の raw 経路が正確に復元され、元経路も
   持ち上がる。`StampedCounts289.exact_terminal_counts` はラベル付きの
   停止経路が raw 1 手と補助（正 2 手／負 1 手）に、据付前の任意の
   失敗検査 0 または 1 手を加えたものと必要十分に特定する。一般の停止性
   や任意のソースへの完全性ではない。

4. **出力の checked readback（健全性・補助）。**
   `ReceiptCompile289` は有限の親 head `F(a)`、body `F(F(a))`、実型
   座標 1、要求座標 2 から `target2, ctor0 arg1` を組み立てる。
   `ReceiptPoint289` と `StampedExport289.marked_result` では正の枝のみ
   `node 0 [node 1 []]` が出力され、全 raw Models は source とその出力
   mark を満たすモデルにちょうど一致。canonical 完成では型座標 2 だけ
   を補い、行と他の型はそのまま。mark の型付き support は
   `{type1,type2}` で独立行を仮定しない。これは**補助出力**であり、
   旧 raw snapshot が型座標 2 を既に Known と認識する、旧台帳を
   仮に追記した状態へ元の経路が到達する、あるいは行の直接読みが
   解けた、という主張ではない。元 V8 診断も両枝で保存した（親 selected、子が正 selected／負 pending）。

## 境界と継続

既存 Lean module・旧 Audit・既存 Step、spec、Rust、構文、受理／拒否
は無変更。追加モジュールは同じ変更に barrel 登録した。次に進めるなら
未観測 Metadata の一般認証を有限 stamp から推論せず、真に行を直接
読める独立ソース例か、作業指示が明示する frozen 外の接続点を選ぶ。
実装・反例・境界の設計は
[補助 receipt 設計](../design/2026-11-20-cycle289-checked-receipt-sidecar.md)。

## 検査・公開

- 起動 04:30:00 UTC。統合 branch の standing orders、次いで inbox を実際に再読。
  ACTIVE I51 の standalone audit、I53 の同時 barrel 登録を適用。
  `integration/m1-final` は `dfbb9f68dc03bf095e9091be84f0584ddfced2cf`、
  tree `7edad26c323350ec76ed91ab0682872582a0dc01`。同一内容のローカル
  祖先 `aa3d3a680b6571faf60f1fdb18116de32af552fb` からの累積差分も検査。
  先行完了のブランチ先端は `ed519652eae7f3610d2a2b9e9f1bd9206495bd19`。
- Yulang2 既存 C3-ROLE-01/02（関連型と正常／未充足 where）を
  `work/dots-audit` の `55574b6052ef1534fd0fc36d6d3617ebede59a0e` で
  再読した。今回の純 Lean 補助を Yulang2 ランタイムで検証したのではなく、
  今回新たな Yulang2 実行は行っていない。
- 純 Lean 評価：素の補助は
  `["published","inspection-pending","no-producer","not-generated","has-effects","stale-stamp","wrong-registry"]`、
  stamp 付きは `["published","stale-typed-stamp"]`。両方 standalone の
  `#guard` でも検査。静的スキャンの評価マーカー REVIEW はこの評価を含む。
- 起動・早期・中間を期待先端確認のうえ `work/dots-main` のみ非 force で反映。
  `8a8c2a85f7bfa08dcc5d83c66625d62f56910baa` →
  `c7bb7c8a40c319c75dc22d990023477964d79a83` →
  `691842211b83e05f0452d7fce5709fa6af843200` →
  `7241597e2a6605b621dc8263c4fd80205d3b4111` →
  `76d2d1c0f57faab9773e7bed4537736461cdfbc6` →
  `8e4e83c5a410821323906045a1dcdd128cda8657` →
  `471936cf2b44e8b8605f5cd0b386d784ae262edc`（検査済み候補、tree
  `b9560fca2f106c4eabb63f130890d991b18cbed5`）。

### 実行可能な再生と検証結果

実 journal に依存する Lean wrapper と、有限データを処理する実行可能
な replay を分けた。`CheckedReplay289.installed_tick_exact` は**任意の
入力補助相**について、二つの実据付端点でこの二つの tick が同じ Option
を返す。最初の二 tick の実行は正で `receipt → published`・mark
`(2,0,1)`、負で `inspection-pending → none`・mark なし。
`observes_exact` は任意の到達補助 config について、補助出力を読む
ことと、正の終端でその mark を読むことが必要十分であることを示す。
任意の Yulang source/journal を入力とする汎用実行器ではない。

- Lean 4.35.0。個別 `lake env lean --trust=0 -M 3200 -DwarningAsError=true`:
  新規 **36 モジュール、7 standalone audit** すべて exit 0。
  97 宣言の `#print axioms` は `Classical.choice`、`Quot.sound`、
  `propext` のみ。独立の shadow cache から当周 36 モジュールを
  全再構築し standalone 監査 7 本を再通過。追加 36/36 の OLean が
  通常焦点ビルドと SHA-256 一致。これは旧依存を保持した当周再構築。
- 旧独立回帰 **30 本**（199/202/204/206/218/230/239/240 および
  271、276、284–288 の実経路・保留・証拠）すべて exit 0。
  `verify-lean.sh --no-build` は前周・統合内容の両ベースで exit 0、
  `git diff --check` と append-only/freeze 検査も exit 0。
  追加差分の REVIEW は上記の `#eval` 2 項目、統合ベースからの累積は
  旧 2 項目を含む計 4。全体 `lake build`／全監査は実行していない。
- 全文・終了コード:
  [焦点ビルドと公理監査](../verification/cycle289/focused.txt)、
  [独立検査](../verification/cycle289/isolated.txt)、
  [旧回帰](../verification/cycle289/legacy.txt)、
  [静的検査全文](../verification/cycle289/static.txt)、
  [ソース manifest](../verification/cycle289/manifest.txt)。
- 後続の一般化へ、実読取り由来・独立行の正証拠・raw/公開射影対応
  の三補題候補を設計ノートに記録。ただし一般停止性、四分類、主型性の
  完成には数えない。

- 最終報告書の時刻: 2026-11-20T05:20:06Z、経過 50.10 分。前周からの変更 59 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。
