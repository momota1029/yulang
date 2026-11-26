この周に閉じた G の行: G00（I‑82 の局所範囲。 `selected_wire_iff_exact_local_report447`、`check_full_sound447`）。残り21行。

# Cycle 447 — G00: 選択された宣言の有限証人

- 実開始: 2026-11-26T18:30:33.460Z。通常終了の経過時刻は同じコミットの heartbeat を参照。使用量の枠は不明。
- 指示 I‑82、inbox `ac05479d3a45842a7c63d304689b28ba1d245eb1`。終了時の正本: `integration/m1-final@ec31261851fafa06fa61b14776e9fd90c19b0742`（Lean `3cbed9fc47dea8d743486f0914a1cc003ae58808`）。
- 検証済み技術 pin: `work/dots-main@d1edd759695a0fd86ba1921d34b575a52036bb68`（Lean `0ea13a53694e26936d2ea31ba06d6ad51b8cfd1a`）。正本との比較: 今回の Lean tree の統合は未確認。

## I-81 §6 / I-82 の三条件

1. **独立した局所規則と保持。** C444–C445 の `FullState`、`FitsFull`、`LocalSelection`、`RLocalFull`、`dictionary_sound`、旧 R21 の持ち上げと実 Event の `retainSelected` を変更しない。writer は元の出現・宣言番号・出力番号・型付き本文と固定先から行を作り、既存制約に連言で足す。新しい reader は実際に選ばれた元の宣言だけを `selectedHeader` で見る。既存の DeclarationCovered・DeclarationChecked・空 where に一致し、可視 singleton、原出現、raw K2、元 B6、型付き捕捉、fresh 配置、固定先と真正の保持照合は維持する。
2. **データだけの入口。** `check_full447` の旧 witness 分岐は任意の FullProblem・Result・旧 witness で C446 そのもの。lift 上の旧 R21 Bool も全入力で同じ。新分岐が受け取るのは元 authored origin の位置と順位/側の有限表だけで、報告や出力の型・配置・証明を入力の主張として信用しない。`accepted_wire_checks_exact_origin_and_report447` は true なら、同じ State の実 index の source と実 raw 位置で検査が通り、提出報告が実際の局所選択の報告だと示す。`selected_wire_iff_exact_local_report447` はこの exact report と受理される新 wire の存在との両向き。
3. **同じ状態・全適合モデルでの正しさと具体化。** `check_full_sound447` は全 p,r,w で true なら同じ State の分類と任意の FitsFull モデルでの報告証拠（辞書と元の型付き固定先）を与える。`independent_selected_report_has_finite_witness447` は任意の独立 LocalSelection から、その実辞書と元の出力列を含む exact report を通す有限データを作る。全体ヘッダー、外からの raw 証人、元の非標準配置、reader/check 成功を追加の前提にしない。配置の内部正規化は報告と保持鍵を保存する。`writer_result_has_exact_selected_witness447` は元 writer 後にも適用する。`independent_selected_report_has_compact_witness447` は同じ報告の証人で順位表長 N、側表長 N+1 とできることを示す。圧縮前後で実対象位置の側と実 raw 検査は同じ。N は元の位置番号の上界で、相異なる位置数ではない。計算可能な探索や性能は主張しない。

## 実入口での回帰

- C442 由来の実入力と signed mixed ref の元固定先21の保持は true。固定先22の同じ RHS、元固定先の既出 Int、保持なしは false。各例の原 source replay と保持位置の照合を含め、順に `[true,false,false,false]`。旧 Int を持つ状態にはモデルがあり、新しい等式との連言には適合モデルがないこともカーネルで確認した。上書きしない。
- 本物の Checked な無関係 ground where 宣言を元候補の前に入れ、元宣言と B6 を unfiltered ordinal 1 へ置いた。同じ元の独立した局所選択・報告・保持・FitsFull モデルで、旧分岐は全体ヘッダーのため false、新分岐は true。どちらも `check_full447` を通し、実 replay の宣言 ID 81・番号 1 と `[false,true]` を確認した。当該選択自身に where を許したわけではない。

## 検証と限界

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true`。7 production、9 standalone Audit を production-only import 経路で個別に確認し、44件の監査出力は標準公理のみ（または公理なし）。Audit の import: Yulang.* 以外 0 件。2件の `#guard_msgs #eval` は実入口の実行テストで、VM を証明には使っていない。独立に取得した Git ソースと検査入力を照合した。旧 7708 production、旧 2102 Audit と他の Lean ファイル、凍結 Audit.lean / README.md の blob ID は不変。集約ファイルへ 7 import だけ追記。dot で全量 Lean build / verify-lean.sh と Rust は実行していない。

閉鎖は I‑82 の where 無し・可視一候補・型付き mixed ref 出力一つ・真正 singleton 保持・既存の保守的な fresh の局所規則に限る。一般の `R_full` / NoFalseRejection、複数候補や出力・別の where・一般の保持列・release・typed retention が追加する一般の raw 観測の輸送、solver の合成・停止性は証明していない。G01 以降への着手なし。新しい意味論の質問なし。
