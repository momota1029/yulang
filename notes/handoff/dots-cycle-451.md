この周に閉じた G の行: なし。G03 の同入力の実 where 元位置は、raw 同値類の中で漏れなく保持できるようになった。併合後の正規報告は未接続、残り19行。

# C451: 同入力の元 where 位置を全部保持する

- 実開始: 2026-11-26T22:31:49.879Z。終了時刻・経過は同コミットの heartbeat。使用量の枠は不明。
- 適用 I-83、inbox `1b9ef468ce4e6f844f53533a59c431f27119f66a`。正本 `integration/m1-final@d6645e6b033c8b9512334a4de37d051ab729cc69`、Lean `75d34b1e8af7b0881d62221b6be3d9de1932b509`。
- 技術 pin `work/dots-main@aa6d9e9f39cd16ce25bf38b0849699b1044e4a83`、Lean `27176957e463256bddbffcf8b4f60ca411bb5f6a`。今回の成果は work/dots-main、正本への統合は未確認。

## 実 authored source と、その時点の raw K2

1. `known_original_clause_has_actual_payload451` と `indexed_point_from_ordered_actual_requests451`: C450 が実に選んだ invariant list-binder 親から、全ての原 literal where 節の role・実捕捉 point と子 occurrence を復元。fallback や証人から渡された demand 名は使わない。各元節に正しい順で一つずつ。
2. `exact_raw_pair_true450` / `exact_raw_pair_false450` と `finite_whole_raw_class_table450`: ordinary の実行データが証明する有向 Bound と flat Alias から、任意の有限な元入力列について同 role・raw Alias 類の正負を、有限な表で受理・反映する。検査の失敗は none。raw 非 Alias とは一般の非併合を意味しない。これは現行の raw 関係の存在定理であって、一般の solver や有限時間の合成を主張しない。
3. `indexed_cohort_label_proves_same_input_from_actual_source451`: 同じ同値類にある**実原節**について、元の出現・宣言・正しい role と arity を保った上で、同じ FullState の全適合モデル上の旧 SameInputs に含まれる。実の raw graph は各元位置の K2 を正負とも反映し、同じ raw 類の実位置には同じ K2 が付く（`equal_label_is_same_raw_diagnostic_at_each_original_location451`）。この逆をモデル値同値に広げない。
4. `readOriginalWhereProfiles451` は実 FullProblem から元位置の中間証拠を読む。独立な証拠から同じものを返す有限 wire が存在。`every_raw_original_occurrence_is_in_exactly_one_group451` と `ordered_marks_no_fewer_and_no_extra_original_clauses451` は、各元 clause が一つの類に落ちることと、省略・水増しがないことを示す。類の中は元構文順。任意の証人に付いた numeric label を改名しても、原位置と同じ類に属する関係、K2 は不変。これは内部証拠で、表示の代表位置や結果は選ばない。C450 の累積入口と全旧 witness の動作は変更なし。

## 実データの対照

- 実 authored 三つの同 role の where 節（ID 60, 61, 62）。異なる元 point 名 1 と 6 は actual flat Alias で、両方の根に K2。先頭・次の元 path `[27,31,0]`, `[27,31,1]` を同じ類へ入れ、第三 `[27,31,2]` (point 4) は別の raw-safe 類。同じモデルは再帰 nominal と scalar を実際に解釈し第三の値を区別するので、この実例では旧 SameOrigin も成り立たない。
- 類ラベル `[17,17,99]` と `[101,101,7]` で同じ原位置の組を返す。誤った類割り当て、異なる類をまとめる、原位置／表不足、順番違いの循環証明、実 Alias 行削除、実親 K2、origin 不一致を拒む。実行結果は `#guard_msgs #eval` で 3 組（定理の証明には不使用）。
- 非公開の境界 QA: 実に類が縮む場合、併合後の数だけのリストを旧 WhereForest に渡せない。既存 carrier は元 Event.kids と一対一で数が一致する。このため保持された原位置と併合後の正規報告を別に扱う。

## 検証・次へ

公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true` が、exact 8 production と 10 独立 Audit で通過。`45` 件の公理出力は標準のみ（または公理なし）。Audit の import: Yulang.* 以外 0 件、別 Audit import なし。旧 7740 production と 2142 Audit の全 blob、凍結 Audit.lean/README.md ID は不変。集約は 8 import 追記だけ。作業者も同じ公開 blob を再取得して全 source と Audit を同じ focused 条件で再検査し、採用済み C449 の複数入力・C450 の旧昇格入口の実検査も再実行した。全体 build、verify-lean.sh、Rust は未実行。

問いは一つ: `notes/questions/dots-cycle-451-g03-merged-k2-location.md`。同入力の一つの K2 診断をどの元 where 位置に表示するか。第一案は表示だけを遅延し、内部には全原位置を保存する。決まっている併合・K2・受理は変えない。一般の同入力そのものの独立な証拠、actual postmerge の graph/元状態対応、併合後の報告への接続が残る。G04、一般の診断完全性、NoFalseRejection、solver 停止性は扱っていない。
