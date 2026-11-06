# M1 の共通モデルに残る契約の選択

状態: **問い。言語仕様の変更ではない。**

既存の定理・テスト期待値・旧 `{}` の width 上界としての意味は変更しない。
以下では数学的に両立しない組合せを、Lean で検証した反例とともに分離する。
新しい候補モデルについて証明した定理は、採用の決定を意味しない。

## Q1. 旧全 instance の反映と、新しい部分型の意味

**回答済み(2026-11-07): 選択肢 2 に近い、ただし集合論的な部分型は使わない。**
`spec/04-types.md` 4.7b と、引き継ぎメモの決定 46・47 を読むこと。要点:
- `|` は正の位置にだけ現れ、要求(負の位置)は union を含まない。union どうしを比べる比較は起こらない。
- 作る側の順序は要求で定義する: `S ≤ T :⇔ ∀ 要求 D, T ≤ D ⇒ S ≤ D`。構成子の union への分配は定義から出る。
- 旧入口との要件は「全 instance が一致」ではなく、「旧 instance は新 instance に入る(保存)。新 instance は
  旧 instance と要求で等しい(反映は同値を除く)」。
- 標準形は、同じ構成子の union を成分ごとにまとめた形。
以下は質問の記録。


**問い:** 新しい common carrier の部分型は、旧型の間では旧 structural order を保持するか。

例として、閉じた supported 式

```text
pair (lit int) (branch (lit bool) (lit int) (lit str))
```

は、実際の旧入口で `int × (int | str)` を instance に持つが、
`(int × int) | (int × str)` をどの結果行でも instance に持たない。
一方、data の述語包含では前者から後者への包含が全有限観測深さで成立する。

`Core.PresenceLegacyObstructions.source_supported`、`source_minimum_instance`、
`source_not_distributed_instance`、`regular_data_distributes` がこの比較を証明する。
`no_semantic_legacy_instance_exact` は、full data inclusion による subsumption と
旧 supported 式の全 instance の保存・反映を同時には要求できないことを示す。
presence 拡張全般の不可能性を示す定理ではない。

選択肢:

1. 旧型間の structural order を反映する新しい構造的 presence モデルを作り、
   data 述語への橋は所属の正確性・部分型の一方向の健全性として使う。
2. full semantic data inclusion を新しい部分型に採用し、旧 instance の契約を
   一方向保存などへ変更する。これは今回の「旧全 instance と一致」という要件と両立しない。

**旧作業時の仮の前提（決定46で置換済み）:** 旧全 instance の反映を維持する。2 は採用しない。
具体的な新 structural carrier の構成は未完。predicate モデルの補題を、その構成の
代用として扱わない。model-parametric な制約生成の exactness はこの選択に依存しない。

## Q2. demand の mask が観測する同値

**回答済み(2026-11-07): 案1を今回の作業前提として継続する。** すべての外側 mask を観測に含める。

**問い:** 共通モデルで、現在の demand-mask が保存すべき同値は何か。

`required l never` と `bottom` は unmasked な data 述語として等しい。
しかし `l` を mask すると、前者は `records`、後者は `bottom` になる。
`Core.PresenceMaskObstructions.no_extensional_mask` により、現在の mask を
data 述語の外延的な商上の関数として実装することはできない。
同 module の `Counterexample.masked_root_retraction_fails` は、
`x ≤ bottom` の二 node graph で実際の coalescer の root-mask 回収が失敗する例である。

選択肢:

1. demand の観測にすべての外側 mask を含め、unmasked で等しいだけの demand は同一視しない。
2. value 型と demand の型を分ける。value 型では外延的同値を使い、
   demand-mask は追加の構造を保持した demand 側だけで使う。
3. 現在の demand-mask を変更し、value の意味的な image として別の演算を定義する。
   これは既存の shadow/record 法則の再検討を要し、今回勝手に行わない。

**今回の仮の作業前提:** 1 を `PresenceMaskedCoalescing` の明示的な候補モデルとして
追加した。全 root mask について独立な constructor 等式と辺を満たす解を定義し、
coalesce に渡す cache のすべての独立な mask つき解を回収する定理を証明した。
実際の flow 飽和 cache では、元入力のすべての独立な mask つき解まで回収できる。
既存の unmasked 型や関係は変更しない。
1 を言語全体に採用したことにはせず、2 との接続も未証明とする。
今後の inspector は、採用する観測に対して完全でなければならない。
`required l never` を unmasked な意味だけで `bottom` に縮約しては、1 の観測を保存しない。

`PresenceMaskedFlatSolver` は固定 presence/absence bound の上下界・flow の断片で、
全 mask の独立な predicate family を対象に、solver 成功や比較 oracle を仮定しない完全性を示す。
ただし自由 family は `Fin n → List Nat → (Value → Prop)` の全体であり、mask の順序・重複で
異なるものも含む。任意の family が regular 型の mask 解釈として表現可能とは主張しない。
この表現可能性を仮定して共通モデルへの接続を済ませることはしない。

## Q3. exact/closed record を共通 carrier にどう保持するか

**回答済み(2026-11-07): `exactEmpty` を独立な演算として持つ前提で継続する。** 旧 `{}` は幅の上界のまま保つ。

**問い:** 任意の未知 field の不在も含む exact record 情報を、どの構成子で保持するか。

既存 `PresenceLayers.Layer` は有限個の外側 label しか観測しない。
その有限集合より新しい field を一つ加えても、任意の payload 割当て・mask の下で意味は変わらない。
`PresenceLayerExpressiveness.meaning_fresh_insert` がこの不変性を証明する。
したがって `no_exactEmpty_layer`、`no_exactEmpty_all_observations`、
`no_exactEmpty_some_observation` により、既存 layer だけでは exact empty を表現できない。
全有限深さの共通部分／和集合を取ってもこの問題は残る。

選択肢:

1. 共通 carrier に exact/closed record の構成子を加え、その演算・mask・部分型を定義する。
2. exact な descriptor と open な demand を別に保持し、共通 carrier への埋込みを定義する。

**今回の仮の作業前提:** `Core.PresenceGeneration.Model` は独立な `exactEmpty` 演算を
interface に持ち、継承した width 上界 `emptyRecord` と分ける。これらの具体的な
regular 表現は選択していない。既存の `{}` を exact empty に読み替える解決は採用しない。

## どの選択にも依存せず必要な未完の補題

以下は solver の成功や存在を仮定して済ませてはならない義務である。

1. **constructor を含む全入力に対する分岐付き飽和:** 対応断片の任意の有限入力 graph `G,C` から
   有限 alternative 列を全域に計算し、任意の独立な元 slot 解について、元入力の充足と
   いずれかの alternative の充足を同値にする。各受理枝から coalescer に必要な閉 cache の証明を得る。
2. **open-tail の深さを保つ移送:** tail 参照の mask・展開を、payload の guarded 参照と区別し、
   任意の元 slot 割当てと全観測に対して constructor 等式・制約の充足を保存・反映する。
3. **関数と行を含む具体モデル:** 負の引数位置・共有参照・行を保持する carrier/部分型と、
   `exactEmpty`・`required`・全 recordDefault image を実装する。arrow の空の data 投影だけで代用しない。
4. **旧結果型への embedding の保守性:** 任意の旧 supported 式 `e` と任意の旧結果型 `c` について、
   旧 instance を新 instance に保存し、新 instance はある旧 instance と要求で同値であることを示す（決定46）。全 instance の文字通りの一致ではない。
5. **source 全体の結合:** 上記モデル上で、任意の対象断片の閉式 `e` と任意の結果 `c` について、
   独立 `Typing [] e c` と、実際の `infer e` が返す有限 family の自由 parameter 具体化からの
   subsumption を同値にし、`.rejected` と型付け不能の同値・`.unsupported` の排除を導く。

`PresenceFlowSaturation.saturate_masked_models_iff` により、純粋な flow 飽和の計算した
cache と元入力の独立解は、constructor を含む任意の graph で同値になった。
`coalesce_saturated_retraction` はその入力解を全 mask で回収する。
全 node が変数なら `variable_models_exact` で自由 parameter family 全体の exactness も閉じた。
これらや固定された有限 presence bound の solver の完全性は、1 の constructor-rich な
入力に対する `Closed` の生成・拒否完全性を置き換えない。README の表で完了範囲を区別する。
