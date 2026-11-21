# dot cycle 319: 物理混在の回帰と I-56 の宣言的 where

開始 2026-11-21 10:30 UTC。最初に `integration/m1-final`
`b31b5fa0fbe056a9d3c82cca2f4aca60d7bc29ed` の standing orders と inbox、
前周の完了 `c6bfb9f6f0b7b8fc96f1b1aa9ce167f049f0183c` を照合。
11:12 UTC に integration `03c7f36c5dbf3d8d2b88911621b56676611500f5` を再読し、
inbox `f259434f2d1b233c3dde6e6e2b9d804df9349b5a` の I-56 を確認した。
以降 (4) を solver の帳簿から分離する。物理回帰は (2) の具体的な検査材料に位置付ける。
状態と宣言意味の設計は [I-56 の切替メモ](../design/2026-11-21-cycle319-declarative-where.md)。

## I-56 の宣言的な (4)

`GeneralDeclarativeWhere319` は通常の型・行制約と論理変数の区間だけの状態を定義した。
既存の式コンパイルが成功し、式が実際に上下端を読む変数の区間が通常状態に明記されていれば、
**任意の宣言的状態の任意のモデル**で、正規化された source where パターンの実値が
コンパイル済みの下端と上端のあいだに入る（`source_where`）。
ここには dictionary journal、slot、番地、install、到達性はない。
全 where 引数に対する点ごとの `declaration_where` と、順序・重複位置を保持する
`ordered_arguments`、`ordered_clauses` が局所補題をまとめる。
この補題は、候補選定がどの捕捉と区間を実際に保証するかまでは仮定から作らない。
承認済み分類規則・受理範囲は変えていない。
`GeneralDeclarativeBounds319.bound_sound` は記載済み区間だけでなく、通常の変数間の
`lo ≤ hi` 制約とその反射・推移閉包からも同じ意味が得られることを示し、その証明済み
上下界で `source_where` が適用できる。この小さな区間導出系の完全性は主張しない。

## (2) 用の具体回帰（I-56 確認前に作成）

独立な二つの nominal 捕捉を持つ C318 の具体宣言で、実際の隔離版 `InstallStep`
により最初に旧下端・上端を別々の Fin7 slot へ置く。次に既存 mixed kernel の本物の
nominal 再観測を受理させ、根の区間だけ `(4,2) → (2,2)` に絞る。ここで全モデル・履歴行・
旧子・両端の物理 slot は保存される（`GeneralWherePhysicalReobserve319.underlying_step`,
`models_unchanged`, `exact_same_slots`）。

実 observer/compiler で根を再読する。`GeneralWherePhysicalCurrentRead319.child_bounds`
の生成子は `(loNow,hi)`。新 lower の論理名は旧観測で未割当だが、upper は同じ slot を再利用する。
`GeneralWherePhysicalTicket319.current_upper_stored` は任意の再観測後モデルで、単なる slot
の存在ではなく、実際の旧コミット済み行から現在の upper 行を得る。
`raw_ticket` は任意の再観測後モデルと現在プランの `Holds` から、
fresh lower だけを追加する提案状態の raw 制約を満たすことを示す。
既存 upper と新 lower の variant 頭は通常制約から正規化している。

`GeneralWherePhysicalCommit319.physical_mixed_run` で、実際の pre-install `Frame` と
`Local.selected` による二度目の隔離版の据え付けを行い、旧下端も履歴に残す。
一つの割当が最初の据え付け後・再観測後・二度目の据え付け後を同時に満たし、
旧・新両方の履歴行が同じ割当で成り立つ。新しい子は実際に生成され、旧子は新子と
異なる需要を持つ。`GeneralWherePhysicalChildRead319.actual_report` は新しい子で fresh
lower・再利用 upper を正しく見つけ、捕捉を論理変数 2 の点区間にする。

I-56 確認前に型検査済みだった具体証明も回帰として保持した。
`GeneralWherePhysicalEvidence319.recursive` は任意のこの具体的最終 journal モデルで、
根の隔離版コミット・出力証明と、実際に生成された子の現行 Frame/Holds を同じモデルの
二節点辞書に組み立てる。公開された範囲は子のフレームと証明書までで、子の `Local.selected` も
既存 mixed/source 境界の一般 `EvidenceNode` も主張していない。C316 の反例はそのまま。
これは宣言的な (4) の閉鎖に数えない。

## 残る橋（定理単位ではなく、一般主張のまとまり）

**宣言的な (4): 2 本。**
1. 承認済み宣言的 `Classify` の局所選定から、任意モデルにおける実 head と捕捉、where の
   順序つき子需要および出力を導く。今回 where の区間評価を一般状態で閉じたが、この
   構成全体（特に選定から区間・head を得る方向）は未完。
2. その局所定理を、実際に選ばれる子の診断木と辞書木の順序つき再帰へ接続する。
   任意モデルに対する宣言的 `Evidence` まで。具体回帰は本数を減らさない。

**(2): 2 本。**
1. solver の到達状態から通常制約・区間への射影を定義し、一般の observer/compiler と
   journal を含む solver ステップが射影を正しく詳細化することを示す。
2. solver が停止して診断を返した場合、その木が射影後の宣言的 `Classify` と一致する
   ことを、実行経路から導く。停止自体、手数、有限商は証明目標にしていない。

次周の第一候補は、物理側を広げず、そのまま使える head/capture の既存補題を通常制約
状態へ移し、(4)-1 の「宣言的な選定が全モデルで head と区間を供給する」所を閉じる。
言語の意味や受理範囲を変える判断は行わず、質問ノートなし。使用量の枠は不明。

## 検証・公開

Lean 4.35.0、30 個の new target の focused `lake build … --wfail` は exit 0
（依存込み 3103 jobs）。全 30 新規ソースを個別 `--trust=0 -DwarningAsError=true`、
I-51 standalone audit 9 本を個別に再検査し全 exit 0。I-52 の
`tools/verify-lean.sh . 85197e90c --no-build` は diff-only PASS / exit 0。
I-53 の 30 件を同じ成果物公開の barrel 追記に含め、変更差分でチェックした。
指定二 roots の transitive axiom gate は標準公理だけを許可して 95,208 宣言 PASS。
ログ全文・コマンドの範囲は [検証](../verification/cycle319/verification.md)。
全体ビルド・Rust・Sat 実行は未検証。

心拍の照合済み pin: 10 分 `557b4da101a409e220731337f1eed950d4089ea6`、
20 分 `671e111be8177d3e03950abeb9710f18b933e88b`、
30 分 `b6bbef75789ba78ad1563d9825e0a28b5cbed5ee`、
40 分 `fa568d41a2483544e6f335fd4aafacbf4c6481be`、
50 分 `6709f14a0ceb0bba05bb046fc2d9b3e5202074e5`。
未公開の追加の子選定実験のコンパイラは 137 で終了した。I-56 を確認してその方向は
追わず、選定の成功には数えていない。11:20 UTC までに報告準備、以降は最終公開と照合。
公開先は `work/dots-main` のみ。
成果・検証・報告は前周 pin から 69 ファイル、別に定時心拍 1 パス。
