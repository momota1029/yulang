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
