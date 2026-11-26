この周に閉じた C の行: C17（`dictionary_sound_R17`、`check_sound`、`verified_R17_result_classifies_in_same_State434`）

# Yulang cycle 434: 未完了の関連型出力しか根拠のない元の where 子を保留

対象は I-74/C17、I-78 の追記方針と `spec/06-roles.md` §6.3 157–164 行の `impl R (list 'a) where R('a, out = 'b): type out = list 'b` の例（名前つき nominal の狭い実行経路）。親の元の要求は `R(list A, out=A)`、子の元の要求は `R(A, out=B)`。子は元のリクエスト位置と実際の where 順序で得る。入力 A に見える `A = list B` は未完了の親の関連型出力であって独立の head ではない。この子の候補は展開・選出せず、書き込みなしで `.pending` を検査する。等式を通常のグラフから消さない。判明する別経路のない未対応入力は false であり、それ自体を拒否診断と解釈しない。

## 三条件

1. `pendingAssociatedLocal434` は `OriginalPendingWhere434` を独立に必要とする保留専用の局所規則。元の宣言、実際の子、元の関連型 B6 本文と固定先、head の独立根拠の欠如は State から検査する。R17 は R16 にこの規則だけを足した。`dictionary_sound_R17` と `all_prior_R16_verdicts_in_R17_434` を証明した。既存の固定 `DictionaryEvidence` と意味の宣言を編集していない。
2. 公開 `PendingAssociated434.check` に `.pendingAssociated` を追加。証人は既存形式の raw K2 escape 二つと名前の分離表だけ。本当の親・子・ordinal、宣言、元の型つき B6 本文、出力先と保持行を照合する。選出・保留・完了を証人から信用しない。`previous_R16_entry_is_unchanged434` は以前の分岐をそのまま残す。
3. `check_sound` と `verified_R17_result_classifies_in_same_State434` は、元と同形に、同じ State での分類と、すべての fitting model での report evidence を与える。raw K2 は元の無濾過グラフで先に扱う。`real_raw_K2_refuses_pending_witness434` は一周の根の K2 が旧拒否のままで、新しい保留分岐は false と示す。

## 切り分け

- `original_retained_output_is_known_raw_but_delayed_as_source434`: この State では `A = list B` は raw では名目的な head を知らせるが、独立な出自だけに限った入力観測では子は Delayed。型付き出力を保存することと、head に使うことを分けた。
- `original_pending_child_is_not_selected434`、`original_pending_parent_has_no_selected_trace434`: 検査が読んだすべてのこの範囲の実例で、実際の子は R17 の選出に至らない。同じ State を満たす一つのモデルで B は Int であり、唯一の宣言の元の B6 出力は nominal list。固定の辞書証拠からこの両者の両立が必要になることを反証した。旧射影ルートも元の nominal head と一致しない。元の親がある現実の選出導出に載るなら、実際の子の選出導出が必要で矛盾する。このモデルは保留を決める検査器への入力ではない。
- `pending_parent_keeps_original_where_equation_in_every_model434` は、すべての fitting model で未完了の親の元の B6 式を正確な固定先 A で保つ。
- `exact_episode_unfiltered_edges_iff434` と `exact_literal_episode_has_no_raw_K2_at_any_site434`: 正の実例の旧 raw グラフは source→A→B の二辺だけ。B=B は普通の比較用で構造辺ではない。この特定の実例で K2 がないことは、外から与えた数字のランクを仮定せず証明した。`A = list A` の対照は、同じ未完了の種類でも本物の旧 K2 拒否が通り、保留は通らない。
- `independent_source_reopens_literal_head_without_releasing434`: 同じ raw グラフに実際の独立した元のソースを追加した対応 State では Ready、旧保留は false。解決器の次の選出までは主張しない。既に完了していた旧 Wrap 例は、同じ辞書と元の二つの出力順で R17 からも通る。逆順、誤った子位置、元 B6 がない場合は通らない。

## 検証・公開範囲

- Lean 4.35.0。公開ブランチから読み直した全 C434 の Lean ファイルについて Git blob の照合、既存 barrel と追加 import の完全バイト比較、production 8 ファイルを `lean --trust=0 -DwarningAsError=true -o …` でコンパイル。既に照合済みの C433 production closure を依存に使った。
- 新規 standalone Audit 5 ファイルを個別の空ディレクトリから production-only の LEAN_PATH、peer Audit の olean なしで `lean --trust=0 -DwarningAsError=true input.lean`。標準公理のみ、または公理なし 34 件。
- Audit の import: Yulang.* 以外 0 件
- 変更していない過去の公開 Audit 4 本（C432 AssociatedEntry、C433 MovedReceipts、ReceiptRefinement、SiblingReceipts）も同じ新しい環境で個別に再確認した。今回の 34 件には加算していない。さらに fixed goal、NoHead、元本文と親 frame の reader、R16 公開 entry の既存 5 モジュールを、照合済みの元 Git blob から再コンパイルし、C434 の中核と元の R/K2 Audit を改めて通した。検証の再現手順と個別 blob は `notes/design/dots-cycle-434-detached-replay.md`。
- 公開差分は計 19 ファイル。production 8、standalone Audit 5、barrel 末尾 import 8 行、C434 の新規設計・検証ノート 3、canonical heartbeat とこの報告だけ。古い Lean/notes、凍結 Audit.lean/README、spec、他 branch は不変。`tools/verify-lean.sh` 全体、Rust/パーサ、解決器全体の実行は未実施。Container/Wrap/P の下流例、別の未完了の W から P の内部位置へ伝わる形、任意の変性、一般の完全性、NoFalseRejection、停止性は未主張。質問ノートなし。
- 技術スナップショット: `5d58ae2e16fc3b5a462d2376e40d8f382e84ade6`、Lean tree `6b1fa7520125ad7a50797c9d0cf4c6083a3f66a6`。統合の状況: 報告準備時に C433（C16）までの採用を確認。C434/C17 の採用は未確認（`d9b950d07e7511501f8f7b1ae77f70a8d1b23ef3`）。
- 実開始 05:34:21 UTC。最終公開の時計は心拍参照。50 分の通常ゲートを通過して worker 解放。定時上限 06:25 UTC 内。

C の残り: work/dots-main では 5 行（C18–C22）。今回の C17 の監督側採用までは integration 側では 6 行。次の候補は C18 のみで、この周は着手していない。
