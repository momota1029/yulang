# Cycle150: 実更新から導出する named/no-merge locality

一般 V5 は 6/14 供給・8/14 未解決のまま。任意 reachable state の完成ではない。

## 必要な区別

alias graph が空であっても、同じ ID を持つ異なる occurrence が存在すれば、
Related site の occurrence が focus と等しいとはいえない。
`GeneralSourceDictionaries.Occurrence` 自体は ID の一意性を要求しない。
このため「merge しないだけで一般 locality を得た」という主張は避ける。

## 有限実行の構造的な条件

固定写像 `names : Nat → Occurrence roles` を用いる。初期 root、enqueue で新しく
追加する occurrence、install が実際に emit する各 child について
`names occurrence.identity = occurrence` を検査する。
新しい `At` は既存 ordinary support の enqueue/equate/install と同じ linked・
absent・enabled・novelty・PacketGuard をすべて保持する。merge は含めない。
追加条件に Models・Instance・Evidence・Joint・key equality は含めない。
任意有限 trace について、全 sites の naming と空 alias graph を実 constructor の
帰納から導出し、Related locality を結論として得る。

`initial_joint` は任意 roles / names / registry / root / focus / context / state / packet /
selected key / children / current model を量化する。InitialSource、root naming、
この有限 trace、focus の実 packet、現在の selected、現在の Models が前提。
最終 state の locality、空 alias graph、全 sites naming、focus naming は追加前提でなく
証明から得る。既存 finite-journal Joint 定理へその結果を渡す。

## 非空な回帰例

`GeneralDictionaryNamedLocalityExample` は既存の実 `Display(List Int)` 一回 install
履歴に naming 写像を与え、元の全 operational 条件を保持した trace を構築する。
任意の最終 Models assignment について Joint を得る。一般定理は任意有限長だが、
この回帰例だけは一回 install である。任意プログラムに naming discipline が成立する
こと、refresh/reobserve・merge、一般 alias compatibility、全 V5 は未証明。

## 検証

Lean 4.35.0 の direct compile `-DwarningAsError=true` は両新規モジュール exit 0。
同じ元 commit 7a7b330 の focused build の依存 olean を使い、新規 olean は独立一時
ディレクトリに配置した。full build は実行していない。
12件すべての `#print axioms` と完全修飾 `#check @initial_joint` を
`lean --trust=0 -DwarningAsError=true` で検査し exit 0。
依存公理は propext / Classical.choice / Quot.sound のみ。
開発中の失敗は member 名の衝突、新規 olean 用 import path、具体 child ID の簡約、
非推奨 if_neg（ite_eq_right に修正）。最終版ではすべて解消した。
