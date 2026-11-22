# dots-main cycle 347: 実 solver の where 子が現行コンパイラの子と一致しない条件

- 開始: 2026-11-22 14:36:45 UTC。前周の検証済み成果: `2f165bf31ede52a984faeecae83904ac155d4e52`。指示元: `03f8ce6e36fb6a33c58d53ff4fcad21d7a55bc5f`。作業前後で standing orders / inbox / spec 6・10 / B4 草稿の内容の差なし。I-62 に従い、旧 `Local` との対応は目標から外したまま。
- 検証したソースの固定コミット: `13fc49ad892b2fc9b75cdd9bf1a7eca98f48e68d`。最終公開には検証ログとこの報告を追加。

## (2) 実 solver が成功して停止した場合の部分正当性

1. **同一宣言・同一現需要・同一モデルでも、古い子を現行の子にはできない。** `NativeCut347.verified` は到達した C316 実 native 関係の停止・選定辞書、元と同じ宣言の実 `compileBody`、両側を満たす共通モデル、literal where 子の配置不能を一つにつなぐ。C316 の元の宣言は nominal の同じ変数 0 を二度使う。C319 実験の異なる二変数へ差し替えていない。実 source の初期ラベルと幅制約を独立の支えにし、現状態の名目読みから二つとも実中心 2 を得て、I-58 の実中心の等式を実際に加えた。現需要の引数・役割・出力要求リスト `[(0,4)]` を変えず、宣言的 compiler は下端・中心・上端がいずれも variant(2) と同値な子を一件生成する。他方、native の実登録子は variant(4) から variant(2) の真の非点区間を持つ。どの native モデルでも既存 journal の名前を保ってこの compiler 出力を満たせるが、その共通モデルで元の子へ各モードを別々に対応付ける `Placement` は不可能。名前の違いだけでなく意味の違い。これは特定の実行スケジューラの戻り値、あるいは全宣言的診断木の一致/不一致の証明ではない。
2. **任意の native 到達状態で corrected where の物理座標を取得できない。** `NativeWhere347.recorded_no_compiled_cell` と `both_missing` は親が記録済みでも、同じ seed における目的 10/11 の両端を物理 slot・補助 compiler・named nominal lookup から取得できないと示す。これとは別に `NativeChild347.current_positions` は、実 native install で生まれた元の子の centered/raw/canonical の番地、実 center、生成関係を、全ての実後続 Step と最終モデルで正確に保持する。
3. **隔離した C319 の肯定的対照。** 現在の raw 形を読み、実 journal stamp、現在の child 位置、canonical clause、引数と極性を照合して両端を release する。固定した試験用フラグは使わない。上端の以前の物理作者は stamp 0 で、現在の読取りと区別。任意の実隔離モデルで release、再帰辞書、固定出力 4 が共存する。実際に存在する corrected 下端を持つこの隔離状態は、旧 native 到達関係からは得られない。

## (4) 宣言的な型推論・辞書健全性

- 物理名目 descriptor の読みから、型と row の別の名前空間、順序付きの非点両端、実 invariant 引数の存在を任意のモデルで保持した。点型に限定せず、ordinary atom/interval と typed descriptor 側表の射影が元の raw models と双方向に一致する。raw 意味が真であることだけで選定の支えにはしない。
- 実 raw/normalized 構造読みと独立した source/完了した出力の由来を別に保持する。元の raw 入力に記録された名前付き record tail をたどる finite walk から、既存の I-61 `Spine / Read`、ソース順の field と standalone deletion の receipt、既存の有限 compound tree、固定ターゲット付き実 `compileBody` をつないだ。真に異なる lower exact-closed / upper width-open、非点 field、中心 RHS 無しの raw 入力例で確認。元の 7 個の割当てを保存し、別の同じ reader から capture 順序 `[0,1]` と固定出力 8 の有効な compiler result を得た。この例の output compiler と raw 条件の充足を確認したが、任意原始状態で全出力等式が矛盾しないとは主張しない。

## 残り

- **(4): 1 群。** 上の実 raw 由来を、任意の承認済み混在 nominal/variant/join/record 入力の証人つき分類の全階層で生産し、既存の同一モデル辞書定理へ接続する一般部分。
- **(2): 2 群。** 旧 native 足下では存在しない current where 入力生成と release の実 transaction（現在の位置/版、由来、同じモデル）。次に、真に返った snapshot の診断/順序/配置/辞書を証人つき宣言的分類に結ぶ全階層の部分正当性。
- 停止性なし。Rust 実行なし。最新の判断に反する新受理・優先順位なし。旧 `Local` 対応は I-62 で目標外（証明完了を意味しない）。

## 検証

- official Lean 4.35.0、`lake build --wfail Yulang.GeneralDeclarativeNativeCut347` (3578 jobs)、固定コミットの各追加ソース・独立 `lean/Audit/Cycle347*.lean` を `--trust=0 -DwarningAsError=true`、全スコープの公理 gate、凍結を除く差分 gate。フル無限定 build とは区別。
- I-57 の `lean/Audit.lean` と `lean/README.md` は元の blob ID だけを比較し、内容を読み書きしない。barrel は旧版全バイトの厳密な prefix を保ち、新 import だけ追加。
- 検証ログは `notes/verification/cycle347/`。35 モジュール、独立監査 5 ファイル・76 定理、許可済み標準公理のみ。closure gate 103,666 宣言。差分 gate/各ソース確認/監査は終了コード 0。固定ソースコミットの変更 64 パスを GitHub と detached Git の双方で検証。差分 gate 全文の SHA-256: `d456efb376a69519401595c8fc6bf48d42800a158e21548675e985d2e3891d41`。
- 旧 Yulang2 との実機照合なし。比較基準は現仕様の 6.3・6.5 と B4 草稿。今回検証したのは既存 Lean 原始関係、現在の宣言的コンパイルと隔離修正版。補足: `notes/design/dots-cycle-347-next-native-transaction.md`。
