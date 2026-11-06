# M1 の具体共通 carrier と残る compiler 境界

Status: Draft — concrete implementation choices; no new language decision.

Date: 2026-11-07

Scope: `integration/m1-common`。正本は spec 4.3・4.7b、決定46・47。

## 1. 構文と要求意味

`CommonFinite.Ty` は base、bottom/top、union/intersection、pair、width/exact record、
record head/tail、whole default、variant、両行を持つ arrow、外側 mask の有限構文である。
`CommonSyntax.Layer` と有限 `State.block` が regular 表現を与える。要求、環境、観測は
solver や Typing に依存せず、型構文と負文脈 rank による再帰で定義する。

要求の変数は任意の型構文を名前で参照する。`Common.Parameter` は finite と regular の
二つの具体構文の和である。finite はその有限型全体を保持し、regular は producer と同じ
constructor depth で展開する。`Environment.atDepth` の同じ環境を負の arrow 観測にも渡す。
有限 rigid 観測列や任意の述語を parameter の代用品にはしない。

regular だけを環境に許す案もあるが、各 depth における任意有限環境の実現補題が余分に必要に
なる。二つの構文を明示する案では、その実現は `.finite` により直接得られ、任意 regular 型の
割当ても `.regular` で保持できる。source/scheme の自由変数は `TyTerm.var` の代入として扱う。

## 2. optional と旧型の保存

optional 要求は「field が存在すれば payload 要求を満たす」を表す。未知 width 型に対しては
自明な payload 要求だけが成立し、exact empty にはすべて成立する。record head が要求 label と
同じなら payload へ降り、それ以外は tail の optional 観測と自明要求へ分解する。

旧型への新 optional 観測は、payload が自明なら旧 records 観測、そうでなければ旧 field 観測へ
射影できる。負位置では、新しい任意 parameter が満たす関連 arrow 引数の有限リストを取り、
それらの旧 intersection を witness とする。rank ごとの保存・反映を帰納することで、
新環境を旧型に限定せず有限 embedding の iff を示す。

`CommonLegacy` では旧 graph の各有限観測と埋め込みの交換を証明し、この有限定理を全深さへ
持ち上げる。`Common.contextual_embedding_exact` は任意の旧 regular 型の比較を保存・反映する。
これは新 infer の instance 保存・反映を定義だけで置き換えるものではない。

素朴な「構文にその label がない」という absence 判定は採用しない。例えば旧モデルで同値な
`record 0 bottom bottom` と `record 1 bottom bottom` を区別してしまうためである。
この選択は集合論的包含を導入するものではない。

## 3. mask、record tail、default の深さ

producer mask は要求の mask と異なる。隠れた field の要求を消し、payload 内の mask と外側の
mask を混同しない。外側の hidden-label 集合は tail と default source へ同深さで渡し、
payload へ降りるときには空へ戻す。合成は hidden-label の和集合に一致する。

record/default の型判断は、tail/source が width record 以下であることを別途要求する。
head の比較のために tail へ同名 field の要求を追加しない。

default は新しい field を構築するので、その payload も普通の record と同じ深さを消費する。
`Layer.evalAt 0` では default の head を bottom に置き、source の残りの観測は同深さで保持する。
正の深さでは具体的な finite default 演算を使う。この初期層を設けず finite default を全深さで
そのまま使うと、`default l width F ≤ required l any` が深さ0で壊れる。
旧構文には default がないため、旧 graph の観測保存には影響しない。

## 4. 行と独立した data readout

`Common.Row` は `(key : Nat, signedWeights : List Int)` の集合である。行自体は無限でもよく、
負の重みも各座標も捨てない。M1 の空行・join・包含をこの具体集合演算で定義し、前順序、
反対称性、空行と join の法則を証明する。これは M2 の全 source scope 解決の統合ではない。
行を有限集合や空行に固定する案は、自由 parameter と無限行を失うため採用しない。

`Common.DataReadout` は同じ構文上で、既存 `SourceDataRuntime.Value` の有限値を読む独立な
帰納的解釈である。exactEmpty は空の field 列だけ、width は任意の record を受ける。
whole default は既存 `Fields.insertDefault` の正確な像であり、present source でも fallback の
値の存在を残す。要求同値な型の data 集合が等しいとは仮定しない。

## 5. solver との残る接続

上の構文と constructor 法則だけで、残契約の全入力 compiler や公開 infer が完成したとはしない。
特に、既存の positive data-demand `Body.record` を producer record へそのまま移すことはできない。
`inter(required l A)(mask [l] bottom)` と producer の `record l A bottom` は同じ意味ではない。
必要なのは、field 要求だけを同深さの方程式へ移す独立な projection と、その完全な compiler bridge
である。default の有限完全 inspector、型・行の simultaneous な自由 parameter family、全 source の
公開 principal/rejected/unsupported、完全 interface canonical encoding は別々に検証する。

`Common.common_record_iff` は、任意の同名 head の比較を payload と残る tail 要求に分ける。
tail に渡すのは、先頭 label を除いた field と非自明 optional の観測だけである。optional の
自明な payload は構築済み head が常に満たすため、tail に戻さない。required target なら tail の
要求はすべて消える。構築時の tail ≤ width は生成器の別制約として残る。

同深さ record 方程式には、次の正しい producer polynomial を採用した。

```text
record l A R ≈ inter (record l A top) (union (record l A bottom) R)
```

record の各観測は head／shape による定数か、そのまま tail に渡る観測である。観測の真偽に
関して `F(false) ∨ (F(true) ∧ p)` に分解でき、任意の外側 mask でも同じ証明が成立する。
代案は required-bottom と masked-tail を含む polynomial だが、採用案は新たな mask label を
増やさず、二つの端点 atom だけを追加する。`CommonRecordTailElimination.compile_models_exact`
は実際の record 構築を含む独立な方程式と変換結果の両方向を証明する。

`CommonTailElimination` は全 mask 座標の有限 Boolean 方程式を、型の intersection による上昇と
union による下降で解く。反転は producer union が観測の論理積になるためである。反復数は graph
から計算する内部値であり、公開定理に fuel 前提を置かない。任意の Common 型 parameter が解に
なり、任意の独立解をそのまま parameter に選ぶと回収できる。mask の単調性は fresh label の
観測で別途証明済みなので、全 mask 下の同値と通常の Common.Equivalent は一致する。

## 6. whole default の同深さ方程式

default は source の一つの観測だけで決まらない。選択 label の optional payload と、存在または
fallback の観測を組み合わせる。そのため record と同じ一観測 polynomial へ無理に縮めず、
元の型構文のまま反復する。証明側では、元の query、optional query、存在、optional な存在の
4モードを追う。default は label を変えず、このモード集合の中だけで遷移する。

`CommonPresenceTailElimination` は各 slot × 全構文内 mask × 4モードの有限座標を使う。
外側 mask は任意の List Nat のままであり、深さ・rank・環境・元の観測もすべて量化する。
反復回数は座標数から決まり、有限個の要求をサンプルするものではない。独立な Models は
元の Body.eval による各 constructor 方程式そのもので、solve を参照しない。

payload と fallback は任意の固定された Common 型でよく、型自身は regular/mask/arrow/default を
含められる。ただし、解いている同じ未知 slot を guarded payload や負の arrow の子で参照する
graph は別の closure 義務である。`Layer.evalAt_congr` は全 rank の payload 要求同値を保存し、
負位置を理由に型を除外せず、この closure の深さ帰納に使える。

presence だけを見て default を source に消す案は採用しない。
`inter exactEmpty (required l int)` は width 以下かつ required l top 以下だが、default 後の str field
要求を元の source が満たさない。`CommonDefaultBoundary.presence_does_not_erase_default` が任意 label
についてこの境界を証明する。source が構文上同名 record head である場合の既存法則とは区別する。

## 7. 行・formula・旧型付け

`CommonRowTailInference` の入力は有限 syntax であり、行右辺を var/empty、左辺を var/empty/join とする。
型 atom、record payload、default fallback の両 arrow 行も同じ symbolic row ID を共有する。
まず実 RowFlowSchemes の有限 scheme を作り、その行代入で実 presence-tail solver を実行する。
任意 parameter が元の独立 Models を満たし、任意解は行を文字通りの等号、型を要求同値で回収する。
元の行を保持できるため、型内部の行を交換する法則を model の前提として追加しない。

実生成 Formula の正規化では、局所 existential を有限 slot に移し、値と行を同じ computation slot と
して保持する。捕捉環境を一般化し直さず、value-let の両枝と strict fallback の全制約を残す。
`PresenceNormalForm.closed_core_exact` は全 Core 式・任意結果の型判断との iff だが、右辺に原子制約の
充足を残すので solved family ではない。explicit row と新観測 inspector の row 保存もこの区別を保つ。

旧モデルへの transport で、literal な ModelMap の構成子等号を強制する案は採用しない。
`.legacy (.node A)` と `.node (embedOld A)` は構文上異なるが、全深さの観測は等しい。
`CommonLegacyTyping` はこれを使い、評価の観測等号、実 existential witness の移送、旧 Typing と
旧 infer instance の独立 Common Typing への保存を証明する。新 infer の instance や反映は未完である。

## 8. 標準形の実装範囲

scalar lattice は最小 Boolean clause の有限表へ正規化する。共有 variable ID を先に並べ、具体 base は
bool/int/str/unit の辞書順とする。同じ ID の全 Common 型割当てについて、要求同値 iff 同じ encoding を
証明した。有限の固定 Shape 内では pair/required/tag/同じ行 ID の arrow の union を成分ごとにまとめる。

この equality は同一割当てでの pointwise equality であり、存在的 instance 集合の equality や binder の
α 同値ではない。Shape の code は label・行 ID を Shape 側に保持する。全 interface の standalone
encoding、混合 head、一般 record/default/mask、役割・nominal の義務、regular graph の一意化は残る。
全 concrete Common.Row は任意の述語なので、正規化対象は有限 interface 構文にする必要がある。

参照アルゴリズムは n+4 atom の全 profile を列挙する。最小性判定はその表を繰り返し走査し、
出力も指数的になり得る。既存 infer/display の呼出経路は変更せず、完全な interface encoder への統合時に
共有表現・未使用 parameter・費用を別途検討する。
