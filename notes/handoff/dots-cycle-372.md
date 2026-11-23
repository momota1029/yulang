# cycle 372 handoff — I-65 step 1: occurrence-keyed retained ordinary body

## 指示と起点

- UTC 2026-11-23、実際の開始 2026-11-23T15:35:17.920Z。再読時の `integration/m1-final` は `a0785c5b56b866e274ca4d7f8c6048c297cf7547`。standing orders・inbox・role/inference specs を照合。最新は I-65、STOP なし。C371 は完了した正確な `4b33761db8bc66eb6a0fcb7746651139628188ae`、重複 writer なし。
- 今回の書き込みは `work/dots-main` のみ、expected-head / non-force。成果固定ピンは `47d7c146a7238067ee41f4a7664ab1659888f43d` の [retained event note](https://github.com/momota1029/yulang/blob/47d7c146a7238067ee41f4a7664ab1659888f43d/notes/design/dots-cycle-372-retained-event.md)（blob `be9c276c24c1e24af5d7645de3581fd0e633ec42`）。

## 今回詰めたこと（既存 Lean ソースに沿った論証）

1. 実際の普通コンパイラ `WitnessCompiler350.execute` で、準備済み等式のあとに where と固定出力が別々の区間として付く。非直接出力の現在行位置は、準備済み等式数に、その節より前の非直接出力数と、その節内で対象より前の非直接出力数を足した位置。直接出力は既存の生産側 binder の割当てを使い、where の等式行を出さない。変換失敗を「空」として数えない。固定出力は一出力一行で、飛ばしなし。子の要求順序と生成名前は同じ準備 port・同じ placement から出す。
2. 独立に選ばれた出現に結びつく実際の生成イベントに当該割当てがあり、その準備済み接頭部・where・固定行が現在状態にこの順に残り、準備時の普通制約と区間も保持されるとき、この三成分から `Extends` → 既存 `Receipt` → `WrittenBody` / `BodyFacts` を構成できる。任意の同一現在モデルに移せる。先に `Receipt` やモデルを与える必要はない。これは普通の append 表現における十分な経路で、全ての保持形式の必要条件ではない。
3. `FrameReadback325.Recorded.written` は行の包含、C349 の replay は位置ごとの通常導出を証明する。それだけでは元の出現・割当てを認証せず、同値行を探し直しても literal な生成イベントや typed release は得られない。選定・出現の権限・型つき書込みの証拠・再帰する子は依然別の義務。言語の受理条件や frozen statement を変更していない。新しい fixture・仕様質問はない。

## 検証

- 2026-11-23T16:13:52.709Z UTC まで承認済みの実行環境の状態は offline。既存の関連 Lean ファイルの GitHub 固定ソースを照合して上記を紙で検討した。C370 rank、C371 body/target、C372 retained event の再生入力を分けて準備したが、Lean、Lake、独立監査、Rust は今回実行できなかった。未検証 Lean は公開していない。C372 の 3 補題を含む私的草稿は次の利用可能な環境でテストする。
- この周の公開差分は design note・canonical heartbeat・本 handoff の 3 ファイル。全公開内容の UTF-8 バイトと独立 Git blob ハッシュを照合。Lean の subtree は開始時の `5f2ecd6eaa09d81f6cdcf36d68c6b37747fdf3ec` と一致。I-57 frozen 2 ファイルは Git tree の blob ID だけを比較し、内容を読んだり変更したりしていない。

## 残り

- I-65 **1 は未完**。次は実際の source candidate frontier の早い観測・K2 / 優先順位の根拠と、独立に選んだ source occurrence から本当の現在イベント・配置・捕捉（普通／型つき）を生成する橋。固定対象や論理的な値一致から出現・版・release を補わない。まず前回と今回の独立した草稿を厳密に検証する。
- **2 と 3 は未着手**。S1/S2 は未閉鎖、C は後回し。停止性・旧 Local・C334 の読み替えは対象外。
- 実際の開始からこの報告作成まで約 38 分。時刻枠は延長せず、利用量枠は不明。
