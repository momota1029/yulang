# C315: 再訪の端点衝突を実履歴で特定し、辞書健全性の前提を絞り直す

2026-11-21 06:30 UTC / 15:30 JST 枠。C314 完了 b923bc0dad34b3b69e69b0a49f80e5e4230ec100、
integration fc059f2157cf0dc4bcf35697ccc956951b174571 の常設指示と inbox を読み直した。
I-55 の (4) を優先。(2) 成功返却時の部分正当性の一般化、停止性、順序独立には手を広げていない。

## 強すぎた補題の反例と、実際に壊れる一行

C307 の実際に到達・安定する mixed 履歴を用い、ルートの現在の候補が **本当に Local.selected** で、
そのヘッドと class 出力を旧履歴と同じモデルで満たせること、および過去の frame の単純 replay
ではないことを確認した。一方で、同じ需要が以前に据え付けた複合 where の lower 行の番地は
変わらない。現ヘッドを満たす任意の旧 journal モデルで、その行は旧 RHS が省略可能なフィールド付きレコード
（strict empty と、フィールド 0 だけを持つ厳密レコードの和）を包む variant、現 RHS が幅に開いた
空レコードを包む variant となるため再利用できない。
対応する upper 行は成り立ち、実 where endpoint 2 行のうち lower だけが失敗する。

- GeneralVersionedEndpointObstruction315.pending / no_residual / old_endpoint_false
- GeneralVersionedEndpointBadRow315.cannot_preserve / only_lower_fails

したがって C314 の「子の証拠なしで、すべての選択ヘッドに EndpointReads を供給する」という
**十分条件は偽**。反例の実生成子は棄却され、同じモデルの子の辞書証拠は存在しないので、
**元の再帰的 B4 EvidenceNode を反証していない**。この二つを区別した。

## 本線で証明した、より小さい入力

- 実到達・安定・局所選択・非 replay のうち、対象モデルで実生成順の子証拠がそろう場合だけを
  扱う。未据付の数値 owner は C314 の一般初回据付で処理。再訪した owner は、任意の live
  モデルから旧制約と実 report の読みを保って現ヘッドを構成でき、現 class 出力も同じ割当てにある。
  GeneralVersionedCompleteInModel315.shared / preserved、GeneralVersionedHistoricalClasses315.live。
- 同じ owner の旧計画がある場合、対応する複合 where 行の番地は履歴に必ずあり、保護判定を
  別途仮定しない。現側のヘッドを満たす**一つの**モデルで旧・現の RHS **全体**が同値であることが、
  実 Residual のモデルが存在することと同値。個々のオペランドの一致や全モデルでの一致は不要。
  GeneralVersionedEndpointWholeRhs315.endpoint_iff / joint_with_rhs。
- オペランド照合の十分条件として、必要な側だけが実値と同値になる場合（point を含む）、
  または raw lower の上界全体・raw upper の下界全体の一致を証明。区間の数・順序・生の ID の
  等しさは不要。GeneralVersionedTightOperands315.operand、
  GeneralVersionedEndpointCuts315.lower_equivalent / upper_equivalent、
  GeneralVersionedEndpointReadTest315.readback。

## 別番地の隔離実験（実装変更ではない）

実際に読む (mode, name) を解決した順序付き source ID で、下端・上端の提案番地を分けた。
同じ番地なら、同じ checked compiler の実 where 位置と RHS が一致する。既存の全 journal、
現ヘッド、現 class、RHS の読み出しに干渉せず、提案された全端点の表を一つの割当てで満たせる。
今回の実履歴でも旧 lower を保ち、新番地に現 RHS を同時に記録できた。
一方で**今のコンパイラの旧番地の衝突はそのまま**。新番地を使う実 child 発生・commitment・
証拠の移植は未実装であり、受理条件も変更していない。

- GeneralVersionedEndpointSourceKey315.coherent_on_trace
- GeneralVersionedEndpointBatch315.batch、GeneralVersionedEndpointPatchCase315.preserves_old_and_sets_new

## I-55 の残り

- **(4) 2 本。** 実子に順序付き辞書証拠がある非 replay 枝に限定した (4a) 別 owner の
  alias 宣言鍵の一致、(4b) 同 owner 再訪で旧・現複合 where の RHS 全体を同値にする共通モデル。
  GeneralVersionedRevisitCut315.evidenceNode はこの2入力から元の B4 EvidenceNode を導く。
  どちらも無条件では閉じていない。
- **(2) 2 本、未変更。** (2a) 実履歴を含む一般 source observer/compiler の生成。
  (2b) Sat 成功返却を仮定した実 mixed 経路、返却地点の停止証拠、宣言的 Local/Classify と
  返却木の一致。停止性の主張はない。

数は未証明の入力群。次は実子の辞書証拠が (4b) の式を強制するか検証する。
または [技術ノート](../design/2026-11-21-cycle315-endpoint-operands.md) の最小の追加 leaf を実際の
checked registry で組み、子が選ばれる実到達経路まで確かめる。既存の棄却子だけから
一般定理の反例としては扱わない。仕様判断は未提起、質問ノートなし、消費枠残量は不明。

## 検証・公開

[対象ビルド・各ソース trust=0・独立監査・追記差分のログ](../verification/cycle315/verification.md)。
Rust・CI・全体 Lake build は未実行。通常の書き込み先 work/dots-main のみに、旧 head を指定した
非強制更新で公開し、固定コミットで全差分を読戻す。完了時刻と所要は同じコミットの heartbeat に記録。

追加23モジュール、ソース検査23件、独立監査168件、対象環境の公理検査93,413宣言、追記差分は
すべて通過。周期差分は heartbeat を除き53ファイル。終了前にも integration 側の両指示文書が
同一版であることを確認した。
