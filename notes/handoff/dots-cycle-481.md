# C481: 平坦入口の段階 1

## 今回の結果

- **I-97 段階 1 を追記で実装・検証。** `Yulang.GeneralDeclarativeI65.I72.Flat481.check_full_flat` は、報告と witness のタグを一層で照合して現行 leaf を直接呼ぶ。既存の C446 基底だけは明示的に残した。`.previous` は互換 codec で剥がし、平坦側の実行に旧累積鎖を渡さない。
- C480 設計 §1 の **18 個の旧入口すべて**で全 `p r w` の Bool が一致する。C446–C450 の元 `Checker408.Result` は7段の分類域を区別し、C450 は設計どおり現行 `NoSiblingMerge`。分類と証拠は同一 `FullProblem.state`・各モデルで保存・反映し、全 `FitsFull` の元 `check_full_sound` と同じ外形を取り直した。新しい任意の平坦データの健全性も C446 基底と直接 leaf の判断から得た。
- 無損失 codec により元 report・wire がそのまま戻る。最新旧入口の正確な report 像に限り、平坦データから逆に旧データを作っても Bool は同じ。古い legacy grade はそれぞれの以前の意味域に残る。C459 の実著者 triple・旧 plain 枝・誤った terminal とタグ、および C450 の順序・重複ガード・誤った grade を実行回帰で照合。C450 の旧無ガード実験版だけが通す対照を現行平坦化に取り込んでいない。
- **G04 は未閉鎖（24 行中残り20）。** C480 の scoped `G04Producer` は証明済み。今回、source-only の旧 `Read.expose` の連続列を、既存 raw/author ordinal と同相の authored alias だけから有限検査で復元・反映した。別途根拠のある元 `PriorPhase.ExactFor` と独立した後続 Read を使えば、同じ全 `FitsFull` の Walk へ戻る。実 raw にある pending-only alias は発行済み source にならず、同じ論理名でも位置ごとに違う物理 owner を読む対照は、一つの名前単位 redirect で両者を復元できない。任意の constructor 経路での完全な出所 replay、completed release の結合と要求全体の root 優先を束ねた signed I-93 型商タグは未導入。G05 以降には進まない。
- **削除0、旧ソースの改変0。** 採用後の段階 2 でも、旧入口と同居する使用中型・leaf・I-65 補題・import 使用中のファイルを消せない。次の候補では、具体的な import と移転先を列挙してから監督例外を使う。設計・境界: `notes/design/dots-cycle-481-flat-entry-stage1.md`。

## 仕様・既存実機の照合

`yulang3@965824b7972a7166e95d0d27f0df8518ce1a66e2` は既報の同期のみで、I-93 の型商規則と parser-only の実装に変更なし。既存 `work/dots-audit@55574b6052ef1534fd0fc36d6d3617ebede59a0e` の x-oracle で、X8/X9 は意図した再帰構造を出さず、X10 は型検査の K2 診断なし、X11 は parser 側の失敗、X12 は以前の局所一致。今回は旧 Lean 判定をそのまま平坦化したので、これらを新しい I-93 対応の実機成功に読み替えない。

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task /root/yulang302_resume（追加委譲・Codex thread なし）

## 対象検証と引継ぎ

- Lean 4.35.0 の独立対象検証（--trust=0 -DwarningAsError=true）で標準集合だけに属する検査結果124件と非依存1件、実行ガード3個。新規 production 9、独立 Audit 12、集約は import 9 行だけ追記。I-94 の公式・単語境界の追加行検査に違反 0。集約を含む Lean 22 パス、設計・引継ぎ・heartbeat を含む総計 25 パス。既存 production 8,037、Audit 2,517 の blob はすべて同一（後 8,046、2,529）。Lean tree `5141bce26b20f61e25c9c0c193b1045702864d71`。
- 権威 `e36a04e087f691695e79f1deb930048bcf8c4d24` が work の祖先と確認。実開始 `2026-11-28T04:28:11.125Z`。+10 `dd669480b4fa710b932f2beb9679475ff29c750d`、+20 `61e9e604339ca46628b2352b7725a98231e54de2`、+30 `40419cd2c18abbe070a2b29b934aff47b2c2eaaf` で Lean 凍結、+40 `57ecb107400197dad8042128db3e2483a2db9641` は heartbeat のみ。開始時点の C480 Lean の採用を exact tree で確認し、それ以後の I-97 inbox は変更なし。新規9 import の同時読み込みも対象検証済み。全体の verify-lean.sh と Lake build、Yulang2 実機の再実行なし。作業者を解放し、次回は最新 inbox と統合を最初に読む。具体的なモデル名・使用量は不明。
