この周に閉じた C の行: C19（`MergedOutput439.dictionary_sound_R19`、`check`、`check_sound`。work/dots-main の scoped 検証）

# Yulang cycle 439: 同じ出力を求めた二需要をまとめて初めて矛盾する例

I‑74 の C19 のみ。正本入力 `integration/m1-final@ff86b00b59d6439ac9584767cdf95e35950ab3d0` に C438 は exact Lean のまま統合済み。I‑79 inbox `63620853fb52ce1319c2bd85d2b42b2cca7b2e72` 変更なし。[仕様 §6.3 の原例](https://github.com/momota1029/yulang/blob/ff86b00b59d6439ac9584767cdf95e35950ab3d0/spec/06-roles.md#L231-L259)、`P int` が `R(out=int)` と `R(out=:tick int)` を要求する形を検査した。

- **元の要求と場所を保持。** 実際の元宣言、型翻訳、Compiler350 の source frame と発行行から、元の子を [7,0] / [7,1]、名前 `out` の固定先を cell 1 / 2 と確認。親入力 cell は別。旧 `WhereForest` は元の子二つに対し旧型のまま一つの子を入れられないことを証明した。旧 Tree/Result を変えず上に source/report rule を足し、元の二箇所がわかる証拠を保持したまま、併合した子一つを第一元位置で代表させてその子だけに型エラーを報告する。親の raw K2 や、二つの子に同じエラーを出すものとは違う。
- **別々なら適合し、併合した場合だけ矛盾。** 元の State に実際の適合モデルを構成。公開定理は全適合モデルについて述べ、すべての入力で前状態のモデルが存在するとまでは主張しない。任意の適合モデルでは cell 1 は `int`、cell 2 は `:tick int` と同値。実際の二つの元の要求から既存 `GeneralNominalDemandMerging.outputAtoms` が作るのは両 cell 間の双方向等式であり、これを同時に満たす適合モデルはない。上の証拠が要求する配置は実 compiler で論理的に再計算し、当該行の字面と元の子の順番を照合した。物理 allocator の実行履歴を再現したとは述べない。旧ヘッダが受け取らなかった閉じた `P int` → nullary R の縮小については、代入しても変わらないことから、従前と同じ宣言検査の条件を追加の規則で証明した。
- **公開 Lean entry の三条件。** `R19` では旧成功辞書を `dictionary_sound_R19` の全 State・全適合モデルの外形のまま保持。元の入力 origin と有限の raw guard だけの witness で実 `check` が動き、`check_sound` は元の証拠と全適合モデルでのこの矛盾を返す。先行 witness の全入力での Bool は `rfl` で同じ。元子二つを勝手に削らず、有効な可視候補が二つあるとこの矛盾分岐は通さない（一般の曖昧判定を新たに実装したわけではない）。出力名が別、実際の値が両方 int、親 input cell の流用、誤った issuer や型 metadata も区別。実 raw self-cycle で旧 raw-root report だけが通る。未対応入力を言語拒否とはしない。

## 検証

[元の source と public entry](../design/dots-cycle-439-c19-merged-entry.md) ／ [既存 mergeAtoms との exact bridge](../design/dots-cycle-439-c19-exact-merge-equations.md) ／ [全 strict ログ・実行・補助対照](../design/dots-cycle-439-c19-verification.md) ／ [残り一覧](../design/dots-cycle-439-c-coverage.md)

- exact 科学 pin `b13e03bb1f21fd33bd8153365eea811cc3ea286b`、Lean tree `3fa551ff461d24ab106f9dca1f55cdefd742b49e`。公式 Lean 4.35.0、`--trust=0 -DwarningAsError=true`。公開 Git bytes の production 5 本を個別に `-o` で build、Audit 6 本を production-only cache と別々の空 source cwd で実行し、全 exit 0、公理診断 33 件は標準 trio のみ。取り直した同じ 11 blob を strict stdin でも個別に確認。Audit の import: `Yulang.*` 以外 0 件。既存依存は exact cache provenance と照合、全再 build ではない。
- 旧 production 7,670、Audit 2,055 entries と凍結ファイルの ID を保持。barrel は末尾の5 imports のみ。今回の差分は 19 パス（production 5、Audit 6、barrel、設計5、報告、心拍）。新規の言語設計判断なし、質問ノートなし。全体 Lake／`verify-lean.sh`、Rust、solver の証人生成、完全性、停止性は未検証。使用量の枠は不明。
- Yulang2 照合: 現行 §6.3 は旧「共通型変数」の近似でなく、全名前なし入力の同一性を使用する。[既存 oracle](https://github.com/momota1029/yulang/blob/55574b6052ef1534fd0fc36d6d3617ebede59a0e/notes/audit/x-oracle.md) と roles 監査の範囲で同じ二出力の exact 実機ログは確認できなかった。旧実機は今回未実行。現行の区別を旧近似によって変えていない。

最終照合時の正本 `integration/m1-final@ff86b00b59d6439ac9584767cdf95e35950ab3d0` の Lean `2bba5d89d1e8d9c2d94c5fc3a8a359c3b3b63421` には C439 の exact entry はまだ揃っていない。C19 の完了は `work/dots-main` 上で、監督役の正式統合は別。

**C の残り: 3 行（C20–C22）。** C20 に進んでいない。実開始 10:30:18 UTC、50 分の通常ゲート後に報告し sole writer を解放。
