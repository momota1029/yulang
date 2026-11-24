# Yulang cycle 387

閉じた補題なし・分けた補題: S13b → S13ba, S13bb

I-68 の S13b（`aligned_general_meaning_to_dictionary`）だけを検討した。元の文と最上段を維持し、同じ実 event の意味を移す **S13ba** と、その ledger を一般の同一モデル辞書証拠に仕上げる **S13bb** に分けた。選択規則、受理範囲、関連出力の意味は変えていない。

## 検証したこと

- 任意の局所述語 `P` について、`CanonicalDictionaryReplay replay` と `TreeMeaningOver P lowered` から、**その replay** の exact event、canonical の親/子順、正確な receipt 列、および各 occurrence の `P` を、同じ明示 ledger に保持する。引数の equality や別の証明の同一性から event を復元しない。
- 元の表示添字だけでは Lean が `lowered` を推論できない。同じ `lowered` を型添字として渡すと、追加の等式前提なしで 相互帰納の適用が通る。束縛した local notation で二前提の表示を維持する試験も通った。
- `Fits` を保存して、元の origin がない native slot、元の retained row がない authored view slot を、それぞれ任意に置き換えられることを一般形で証明した。この結果は未保持の量の限界であり、実選択された出力が保持されないという承認済み言語の反例ではない。
- 読み取り専用の承認済み環境で Lean 4.35.0 `lean --stdin --trust=0 -DwarningAsError=true`。C386 の immutable 入力 blob を実ファイルに照合し、C385 の既存の exact dependency を使った。設計ノートのコードを GitHub から読み戻し同じ strict コマンドで再実行。読み戻しコードの再実行は exit 0。四件の依存公理は各 `[propext, Quot.sound]`。Lean モジュールの追加・登録、独立 import 監査、全体 build、Rust は実行していない。

## 閉じていないこと

一般の `GeneralLocalMeaning` / `DictionaryEvidence` は未実装。exact source body と実 capture から元の任意長・非点・入れ子の型付き引数を評価し、その固定先を同じ model で保持する必要がある。既存 C368/C383 は正しい source と retained row を使う tagged unary point、C360 は限られた native output と別の物理盤、一般端点定理は既に与えた endpoints の比較。いずれも S13bb の一般の固定先の証明ではない。`Seen` 自体は任意長の評価済み point 列を扱うが、元の source/capture と ordinal からその列が当該 target に保持されること、非点の継承 mode を保つことは別。普通の行等式にも `Holds m.assignment` に加え exact source RHS の対応を保つ。もっともらしい view、古い solver/release の差し戻し、別 model、output を集合にする弱化はしない。承認済みの意味が順序依存する例は確認していないため、質問ノートなし。

## 残り

- **14 = 未証明 3（S01・S10・S13bb）+ 一部 11（S02–S09・S11–S12・S13ba）**。元の未解決一件を二件に分けたため +1。S13ba の kernel は strict stdin で検証済み、repo モジュールへの完成登録は次の周。S13a は変更なし。Step 1 は未完、Step 2・3 は未着手。S1/S2 全体は閉じず、C は後回し。
- 公開した変更は `notes/design/dots-cycle-387-s13b-semantic-ledger.md`、固定上段を保った checklist、心拍、今回の報告の 4 ファイル。変更先は `work/dots-main` のみ。実行環境以外の権限を広げず、固定 Lean 2 ファイルは blob だけを照合した。
- 使用量の枠: 不明。
- 最終照合開始 `2026-11-24T07:21:03.885Z`（45 分経過）。
