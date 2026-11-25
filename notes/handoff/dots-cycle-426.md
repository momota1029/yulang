この周に閉じた C の行: **C14**（`EndpointProjection426.dictionary_sound_R14`、`EndpointProjection426.check_sound`）。

## 成果

- 正本の `SourceHead` と `HeadModel` に端点射影を足した。元の上下2端点・実中心・元の field/tail binder を保持する。任意の同じ適合モデルで、required と optional はそれぞれ元 field の区間に入り、mask は元の残余区間に入る。中心の literal record や仮の名前つき capture は要求しない。
- 正本の `DictionaryEvidence.endpointLeaf` は、元の型付き B6 本文（関連式 #92 の元 binder）と、元の固定出力先を別々に照合してから同じモデルで結び付ける。既存の literal/ordered/joined と旧 named `SourceTrace` はそのまま。R14 の旧 named view は R13 と定義的に同じで、旧 verdict 全部を含み、旧非選択 verdict および旧 check 分岐は変わらない。
- R14 の判定は実際の元出現／宣言番号／出力番号／固定先を使う。検査器は入力データだけから同じヘッドと元 B6 項を読み、正確な木・辞書・Write が一致するときだけ成功する。`verified_R14_result_classifies_in_same_State426` は実際の `I72.Classifies` と同じ State の全適合モデルでの証拠につなぐ。
- 元の split-channel 実例は required と optional が異なる同じ適合モデルを持つ。新 R14 はその元の exact report で成功し、同じ State に旧 named 形の選択はどの named family にもない。旧 `_404` の named producer inversion、旧 C422/C423 検証は元のバイトのまま。根 K2 の旧報告は通り、同じ根を射影で回避できず、未検査 payload の循環は根 K2 にしない。変更した結果／木／出力記録、保持行なしを検査器上で陰性として扱うだけで、言語の拒否を増やしていない。

## 検証・公開

`work/dots-main` の技術 pin `2ebc88a02789aae60a93506c1b5ab6d18b68dfb9`、Lean tree `efac6836b560e3180f253b5fc37b92ebbfafe9bd`。[C14 と残りの表](../design/dots-cycle-426-c-coverage.md)／[検証ノート](../design/dots-cycle-426-verification.md)。Lean 4.35.0 `--trust=0 -DwarningAsError=true`。正本 head/evidence は 279/279、R14 の変更後の影響範囲 216/216、独立監査 154/154（971宣言、標準公理のみ）。さらに staged Git バイトから正本の変更4モジュール、追加の独立監査4つ、元 C423・C404 監査を再生し、62件の公理表示はすべて標準。過去の standalone audit は変更なし。既存変更は必要な正本2ファイルと import 6行追記だけ。ソース新規6・独立監査新規6。凍結ファイルは blob ID のみ照合。

追加確認: exact 旧 C419 の point Pick は R14 の旧分岐を通り、同じ point は新しい端点分岐を通らないことを独立に確認した。任意の単一 point 入力についての同じ分離も strict Lean で検査した（これら追加対照は checkout 内での検証）。追加のクリーンな280モジュール重複再生は時間制限終了（exit 124、58モジュール通過）で、完走した上記の影響範囲の検証とは別。追加の全体再生とは数えない。

対象は、見えている一つの元 record 宣言・非点の両端区間・異なる field/tail binder・一つの元 B6 associated output・where なし・対応する実保持行。一般の候補、射影出力を次の需要が使う場合、C15、一般完全性／NoFalseRejection／停止性、全体ビルド、Rust／Yulang2 実機は扱っていない。使用量枠は不明。

**C の残り: 8 行（C15–C22）。**

実開始 `2026-11-25T21:30:34.994Z`、通常50分ゲート通過後の最終公開開始 `2026-11-25T22:20:35.995Z` UTC。書き込み担当はこの報告と completed 心拍の照合後に解放。公開前に再確認した integration/m1-final `eecb5e918bcc4ab968de47c4afd3b96651efae31`（Lean tree `4c39c19d35719c899ee333077634607203221aab`）、types `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-75 `42ed184178357af37ba86de355218d720cb36746`。統合 Lean tree は今回の work 技術 pin と一致せず。今回の完了は work 上で数える。
