この周に閉じた C の行: C16（`dictionary_sound_R16` / `WhereAssociated432.check_sound`）。
Audit の import: Yulang.* 以外 0 件

# C433: 実 where 子の関連型を親の固定出力に返す

実開始 `2026-11-26T04:34:04.000Z`、経過 50 分。50分の通常完了条件を確認した。 work/dots-main の単独書き込みを終了する。I-78 `21275fefd4e9d1e11a5a88a4f0582a28472e9040`、integration `33cb37dfda2963da3b2a2e88c1887e8b864b21ac`、Lean tree `69b7cc04f527c7e4da13cf176132355885e250cc`。integration は読み取りだけで、この周では更新していない。I-65 の 1/2/3 は既存の閉じた状態を維持。

## C16 の三条件

[公開技術 pin（元の実例と厳密な負例）](https://github.com/momota1029/yulang/commit/eb15dba50001bc46a740cb1f378fd8746c84d80f)。 `R16` は、§6.3 の元の一子例 `Wrap(list 'a,out=list 'b) where Container('a,item='b)` を扱う。親の実宣言を読み、同じ State の元 where clause 0 で実 Container の関連型 output 0 / target 4 を読み、親の固定 target 12 へ `list` of slot 4 を書く。ここで `list` は実宣言の invariant 1 引数で、発行順は親、元の子。値や辞書や子の選択を witness の入力にしていない。

1. **独立宣言 + モデル**: 実選択規則と既存 R15 の名前側/端点側を保持。`dictionary_sound_R16` は、任意の State/要求/選択辞書が `Classifies R16` を持つとき、全適合モデルの固定 `DictionaryEvidence` を証明する。
2. **公開入口**: `WhereAssociated432.check` は、宣言/元 head/固定 row と有限 raw 検証データを読み、実 B6 typed receipt、元の子を選んだ tree/dictionary、全 write 列を厳密照合する。正例は true。誤った元 root、宣言位置、親・子の固定 row、逆順の receipt、unsupported は false。false を一般の言語拒否にはしない。
3. **固定定理と従前の動作**: 任意の入力の `check = true` から、その分類と全適合モデルの `ReportEvidence` を与える同じ外形の `check_sound`。旧 witness の Bool は全入力で前と同じ（`previous_R15_entry_is_identical432`）。既存端点、既存二候補の構造 where、元の C419 子経路を保持した。

## 同じ C16 の補助検証（蓄積のみ。公開範囲を広げない）

- [受理から元の typed RHS・全 receipt・実子に逆引き](https://github.com/momota1029/yulang/commit/7fdca15782c399a9b9597a93df68a17f86b5a159)：全適合モデルで親の式がまさに nominal list(child assignment)。元の二つの raw 根も確認。
- [二つの実選択子の同じ名前つき出力](https://github.com/momota1029/yulang/commit/5145f7cdc991476ff28735b0d6c1ca1f75d6d557)：異なる role の子を元の ordinal 0/1 に置き、入力 a は不変、二つの名前つき出力が同じ元 target 4、親は target 12。全順序つき receipt と実適合モデルを確認。
- [本物の raw K2 と観測外のループの対照](https://github.com/momota1029/yulang/commit/8a69cb4c847adc3c83e22a6956e4d1f21335fbb2)：元 root 6 の K2 は同じ公開入口が選ばず、別 root 13 の実ループがあっても同じ元報告を受理し、適合モデルと辞書を確認。
- [元 clause ID で名前つき出力先を固定](https://github.com/momota1029/yulang/commit/0cb5d2a5e0a92ff48c6d2d09a3c2afc026a2b948)：実宣言を入れ替えても入力と target は不変、出現 ordinal のみ移動する。別 fallback 70 を使って偶然の一致ではないことを検査。
- [二子の独立データ読取器](https://github.com/momota1029/yulang/commit/0f78d8b4f495ae7aa8068aa8d454a04c5336525e)：両方の実子を読み、取り違え、二子目の別 fixed row、receipt 逆転を退け、同じ State の辞書の健全性を確認。公開 R16 の分岐に登録していない。
- [実 B6 occurrence を付け直した子の対照](https://github.com/momota1029/yulang/commit/b18406b008ff0b44b56cecebf1b37890a175e5f4)：同じ宣言/slot でも、旧 B6 occurrence や旧 report は移動先で通らず、同じ元 source を正しい新 occurrence に読むと旧子経路が通る。

- [二子の同じ固定住所と元の保持 RHS](https://github.com/momota1029/yulang/commit/0be773dcaa3ffa4d8cc191935e9f8f23c40464a5)：辞書解釈以前に元の item/seen 座標と target 4 を保存し、限定 reader の同住所の元式が一致する。実 packet に適合モデルがあることも確認。

- [元の匿名入力は親の実 capture](https://github.com/momota1029/yulang/commit/39d652197f2397e4f6107ee0783d572b06dbc69a)：限定一子と独立二子の裸変数は、いずれも元の親 capture を使用する。fallback と出力専用 b に依存しない。

- [同じ適合値でも元と異なる typed RHS は通さない](https://github.com/momota1029/yulang/commit/c4eef8d3cd681e76eb576dfbfa3597806727062c)：同じ物理 target に元式と代替別名式の両方があり、同じモデルを満たす対照で、実公開 R16 は元 row のみ選ぶ。

- [同じ witness の exact report は一意、State の内部住所は別](https://github.com/momota1029/yulang/commit/5096401f8190fb60c0332bf92ff3b2d7484ca75f)：二つの完備な整合行束が同じ固定親出力と適合モデルを持つ実対照。各元 report は自分の実 witness でのみ通る。

順序は出典と報告の順であり、solver の更新順・安定性・停止性ではない。出力専用変数 b を兄弟の匿名入力にしない。多子を一般に受理するとは主張しない。

## 検証

Lean 4.35.0 の `--trust=0 -DwarningAsError=true`。変更されたモジュールを作業済み exact dependency 上で個別・順次コンパイルし、Git から再取得した実バイトと blob を照合。各 Audit は空の cwd、production-only LEAN_PATH、Audit の olean と他 Audit の import なしで実行、exit 0。新規の標準公理チェック 70 件（propext / Classical.choice / Quot.sound のみ）。従前の C431 構造 where 17 件と legacy endpoint 3 件も、変わらない実ファイルを独立実行し exit 0。旧 C409/410/413/414/415/426 の代表実例 6 ファイルも同様に 47 件、合計で旧 67 件は標準公理のみ。既存 Lean は `lean/Yulang.lean` 末尾の import 追記のみ、凍結二ファイルは blob ID のみ照合。追加 production 11 本、独立 Audit 11 本、報告を含め新規 32 ファイル。同じ累積差分を一つの別キャッシュでも順次 replay して exit 0。全体 verify-lean、Rust、solver 実行、NoFalseRejection/termination は担当外で未実施。新たな意味判断や質問なし。 [監督用の累積コマンド出力](../design/dots-cycle-433-supervisor-replay.md) と最後の exact readback 対照を参照。

**work/dots-main の残り: 6 行（C17–C22）。** integration は C16 entry の採用未確認で、C16–C22 の7行。今回 C17 には着手しない。
