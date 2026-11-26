この周に閉じた G の行: なし。G00 は writer・局所健全性・初期 check_full と条件付きの証人構成まで。G の残り: 22 行（G00 を含む）。

# cycle 445 — G00: 保持 writer と最初の FullState checker

実開始 2026-11-26T16:33:46.822Z、I‑82 inbox `ac05479d3a45842a7c63d304689b28ba1d245eb1`。開始時正本 integration/m1-final@6ce669065ae5002a297882a1f05a4b207971d82c、Lean `ad3f986f65f00e0c7587a54980b3d84aea2fdce1`（C444 採用）。使用量の枠は不明。

## writer と局所規則

- `retainSelected` は独立した C442 原選択証拠の Event の元出力順に行を作り、固定先・元宣言/出力番号・本体・入れ子の row/value 捕捉を保って既存列の末尾に連結する。モデルや出力値を引数に取らない。`selected_rows_at_original_output445` と `fitsFull_retainSelected_iff445` は、同じ任意のモデルについて、writer 後の FitsFull が writer 前の FitsFull と元 Event の FixedTargets の連言であることを示す。上書きしない。
- `RLocalFull` は R21 の旧分類、または where 無し・可視候補一つ・元の明示された混在 ref 出力一つの選択。後者は元候補・head/B6/型付き捕捉の実証拠と、元出現/宣言番号/出力番号/本体/要求名と固定先/型引数順/捕捉名3点を比較した真正の保持行（singleton）を使う。独立な局所規則は checker やモデルを前提にしない。`dictionary_sound` はこの規則について I‑65 の全称の形、同じ State の全 FitsFull モデルで既存辞書意味を示す。`local_R21_case_in_full` は空保持の lift で旧 R21 分類を保存する。
- 保守的な適用条件として、固定先が旧式・上下界・可視引数の実読取り footprint に現れず、元の value 捕捉先とも異なることを調べる。raw 構造や nativeSyntax の書換えは行わない。`matched_fresh_singleton_has_fit_if_old_fits445`: この局所条件と真正 singleton 保持があるとき、旧適合モデルが一つでもあれば、新しい適合モデルを実際に構成できる。旧制約全体の SAT 判定ではない。

## 実行入口・対照

- `check_full` の新 witness は locator と有限 escape のデータだけ。元 source と型付き出力、保持行、元の木・判定・順序付き write を実読取りから照合し、模型値や判定を witness から受け取らない。全旧入力・報告・witness に対して lift で R21 の Bool は一致（`all_R21_Bool_unchanged_on_lift445`）。`check_full_sound` は正確に読む分類と、同じ State の全 FitsFull に対する証拠。従来の規則、checker、固定声明は書き換えない。
- 独立 [実 fixture](https://github.com/momota1029/yulang/blob/80ed049420cc3c9acdc22048c82f3a000f1eae07/lean/Audit/Cycle445I74FullMixedOutputSpec.lean) は実 source を三つとも replay し、宣言 ID 81 と writer の固定先 `[21]`・`[22]`・`[21]`、空保持を先に確認。同じ実行入口で、順に「元保持あり」「別 slot の代用」「既存 Int に混在 ref を連言」「保持なし」の実行結果 `[true,false,false,false]`（`#guard_msgs #eval`）。実行試験を公理・証明に使っていない。旧 Int state には明示モデルがあり、writer 後は任意のモデルで不適合なことを別に kernel で証明した。公開外の実行点検でも、22 に対する**その**要求と報告なら受理し、旧 Int を置いた 21 の freshness は false、元報告の書込 ordinal の変更も false。

## 証人構成と残り

- `canonical_ready_supplies_witness445`: 独立な局所規則、実グローバル header 事実、canonical placement と実 raw 辺への有限 escape 条件があれば、元 source 位置をその実登録から得て、同じ候補・frame・Event・B6 出力を再構成し、**その正確な報告**を通すデータ証人を構成する。`readSource` や `check_full` 成功は仮定しない。さらに `chosen_report_witness_without_placement_premise445` は、元の where-free 本体が読む実 head 捕捉だけを保って placement を正規化する。元の RHS と固定先・順序付き write・辞書・報告が同じなので、元の placement 関数について仮定しなくてよい。残る条件は実ヘッダーと有限 escape。独立局所規則全体から常に出るとは未証明。
- 具体的な旧 raw graph（Bound `2→0→1`、flat alias `1~2`、実構造辺 `0→1`）では、0 は実 AliasCycle でないが、現行 C410 rank パレットは rank(0)=rank(1) を強制し、異なる escape side を置けない。任意 C410 wire が失敗（`root_is_raw_safe445`、`raw_safe_does_not_imply_C410_escape_wire445`）。これは **raw safe のみから C410 証人が出ない**反例で、完全な LocalSelection の反例や言語の拒否ではない。次はこの境界を保ち、実 header の独立反映と、raw Bound SCC と flat alias を混同しない証人の再構成。非公開の小さな Lean 対照では directed Bound の rank と flat alias の side を分ける判定がこの反例を通し、元 raw K2 の否定へ反映することを確認した。一般の証人構成・現行 checker への組込みは未証明。G00 を完了とは数えない。
- `R_full` 全体、G01 以降、任意の正確な報告 B、全診断の網羅性、solver 停止性・Rust は対象外。新しい意味判断・質問ノートなし。

## 検証・公開

[技術 pin](https://github.com/momota1029/yulang/commit/a46df25f78e6a05a465ae3e17c3a7e8c66deef15)、Lean tree `f1aa56bce113c634cfd2a6a17c8495e429d3a071`。公式 Lean 4.35.0、production 7 本を個別に `lean --trust=0 -DwarningAsError=true -o …`、standalone Audit 9 本を個別の空作業位置・production-only import で実行。45 の公理監査は標準のみ、実4対照の guard は PASS。Audit の import: Yulang.* 以外 0 件。初期の単一巨大 kernel 評価による fixture 試行はメモリ上限で中断し、その試行は採らず、上記実行対照と kernel の健全性・非上書き証明を分離した。全体 Lake/verify-lean.sh/Rust は未実行。

既存 production 7,695、既存 Audit 2,085、他 Lean 直下 31 項目は metadata ID 不変。凍結 Audit.lean/README.md は ID のみ。aggregate に 7 import 末尾追記。新規 Lean 16、aggregate、報告、心拍の計 19 paths。work/dots-main のみ expected-head nonforce。Git 接続の中断は更新前の照合時に検出し、head が不変なことを読取りで確認してから exact staged tree を一度更新し、Git bytes を再照合した。

終了時の正本 integration/m1-final@6ce669065ae5002a297882a1f05a4b207971d82c（Lean `ad3f986f65f00e0c7587a54980b3d84aea2fdce1`）。今回の Lean tree の採用は終了時点では未確認。上記は work/dots-main の検証済み内容。
