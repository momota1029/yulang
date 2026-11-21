# C317: 版つき where 端点で C316 の辞書証拠を回復

2026-11-21 08:30 UTC / 17:30 JST 枠。開始時に integration
`fc059f2157cf0dc4bcf35697ccc956951b174571` の常設指示と inbox を確認し、
C316 の完了 `32376552c732c7743b310211f5c46a00aa9045e8` を照合。
終了前の再確認でも常設指示・inbox の版は不変。
I-55 (4) の型推論・辞書健全性を優先した。

## 結果

**C316 の実反例について、隔離した修正版では同じ辞書を受理し、修正版の全 live
model で再帰辞書証拠を構成できた。** 旧境界の `EvidenceNode` の反例もそのまま
同一定理で確認した。現行カーネルや仕様の修正完了ではない。

1. **実コンパイラと子の番地を同時修正。** `GeneralWhereVersionCompiler317` は、
   checked canonical emission 自体の割り当てを換えた。実出力行は従来のまま、
   二つの where 行と生成子の区間端点には同じ新番地を渡す。
   宣言鍵・数値 owner・role・関連出力・実 center を保存し、裸変数区間も変えない。
   `Case317.rows`、`descriptor`、`ordered_children` が実計算結果。
2. **実配置から受理と証拠まで。** 旧8スロットを保存し、点2を payload に持つ実構造
   スロットを二つ追加し、元の観測・通常制約・予約・割り当て全てを保つ
   refinement を確認。実 install 前 frame・候補選択・過去の鍵互換・refinement・
   同一モデルを備えた隔離 successor が本物の子 edge と descriptor を記録する。
   旧形式の誤った親 packet は追加せず、新形式の行を別 journal に載せる。
   新しい子は実 raw lookup、候補選択、Frame、既存カーネルの `Committed` と
   辞書証拠まで確認。**旧 binder を流用せず**、新しい捕獲区間は `(2,2)`。
   `Regression317.regression` は同じ `238→316` 辞書の受理・モデル存在・全モデルでの
   再帰証拠をまとめた。葉の既存 `Committed` を示したのであり、二度目の既存
   カーネル据付 Step を実行したという意味ではない。
3. **旧意味の保存と再観測。** `Preserve317.no_legacy_model_lost_or_created` は旧 journal の
   全意味的支持座標への射影が、修正の前後で双方向に一致することを示す。拡張後の
   raw snapshot を再読して現 root の同一宣言選択と同じ修正版行・子記述子を再計算。
   `CurrentCert317.current_certified` は現 frame・全行・子サイトと子 schema・
   親出力・実生成 edge が同一モデルで成立すると示す。現葉選択も再確認。
   `Frontier317.historical_and_current` は旧 edge と新 edge をともに保持するが、
   同じ数値 owner の旧出現は異なる demand で、現コンパイラの ordered frontier に
   含まれないと示す。旧ローカル選択 API は依然として旧子を返すため、
   この区別は修正版のコンパイラ／辞書インターフェース側が担う。
4. **再読は新規割り当てではない。** `EndpointChoice317` は raw の slot がある／
   真に新規／予約・言及だけ、の三分岐を定義し、条件を証明した。この実例では初回は
   二端点とも新規、同じ観測の再読では二つの既存 slot を引く。
   `ReuseCertificate317.read_only` は後者について、二度目の据付をせずに全行・
   現 Frame・親出力・現葉選択・同じ辞書証拠が保たれることを全モデルで確認する。
   `StoredRow317.same_target_iff` は、同じ checked registry・解釈・seed で、
   両者が実ソース位置と版つき番地を証明済みなら、同番地の行は任意の同一モデルで
   同値と示す。slot が見つかったという事実だけからはこの条件を導かない。
   `RecordedReuse317.from_recorded_rows` はこの補題を、実 journal に記録された
   二行から現再観測の二行を証明するのに使った。

## 残り

- **(4) 2群。** (4a) 別 owner に関する prior-choice/alias 宣言鍵の一般互換。
  (4b) 本例の旧／現 where 端点衝突は隔離版で解消したが、一般の到達履歴・
  複数 owner・既存の版つき書き込み・子 commitment を維持する一般 compiler/journal
  と再帰健全性は残る。旧形式の (4b) に同じ定理を立てると C316 により偽。
- **(2) 2群、未変更。** 一般 observer/compiler の証拠生成、および停止成功を
  仮定した実到達経路・返却地点の安定・宣言的分類との一致。停止性は対象外。
- 次は三分岐を版つき journal を含む一般の実履歴に接続する。特に既存 slot が
  実際にどの版つき行に由来するか、同じ checked 設定・宣言・位置の証拠がどこから
  来るかを示し、真に新しい版と既存版が同一要求内で混在する場合を扱う。旧出現の owner だけで現 frontier を代用しない。
  詳細は[設計ノート](../design/2026-11-21-cycle317-versioned-where.md)。
  新しい承認依頼はなし。使用枠の残量は不明。

## Yulang2 との照合

新しい言語規則や受理例は追加していない。今回は C316 の Lean checked fixture、
既存の宣言・where 生成・選択規則と照合し、同じ辞書、関連出力、役割を保持した。
Yulang2 実機との比較は未実行。ここで示したのは Lean の証拠レイヤの回帰。

## 検証・公開

[対象モジュール、全ソース trust=0、独立監査、追記差分ログ](../verification/cycle317/verification.md)。
全体 Lake、Rust、CI、実 Sat は未実行。既存の Lean 規則や言語仕様は変更なし。
`work/dots-main` のみに旧 head を指定した非強制公開を行い、固定コミットの全差分を読み戻す。
所要時刻は同コミットの heartbeat に記録。
