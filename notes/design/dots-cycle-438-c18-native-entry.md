# C438 I‑79: C18 native lower の scoped entry

正本: `integration/m1-final@0512c698732a0aeeb444f869f586bccc0a15866d`, Lean tree `07eaa114f990a25365054ea6bd17ddc2b4ad46c2`。I‑79 inbox blob `63620853fb52ce1319c2bd85d2b42b2cca7b2e72`。対応表は [C18](dots-cycle-423-c-coverage.md)。仕様は [6.3](../../spec/06-roles.md#63-関連型の制約) の有限に完了した別需要を独立の根拠とする側のみで、未完了の出力の支持や raw K2 の扱いは変えない。

## 三つの検査

1. **新しい独立規則。** `CompletedEntry438.R18` は R17 の元の判断を左にそのまま保ち、右に元の有限 producer trace と元 B6 output/保持行を持つ `Selected18` を加える。producer と consumer の occurrence は別。選択にモデルを使わない。
2. **外の検査器。** `CompletedEntry438.check` の `.completedLower` は demand と元の位置・行 locator・有限 raw escape データのみを受ける。実 book の一候補、header と宣言モード、真の seed occurrence、`readOriginalOutput432` による元 B6 plan と literal retained row、独立の upper を読んだ後に consumer を選択、元 center を照合する。Tree、辞書、空 write をそれぞれ検査。既存 witness は `previous_R17_entry_is_unchanged438` で全入力に対し旧 Bool と定義的に等しい。
3. **固定形の健全性。** `dictionary_sound_R18` は任意の s,q,d と全適合モデル m の量化を保つ。旧証拠を変更せず、新証拠は実 producer にある元 plan の評価、同一 L の retained equation と同値、consumer の上端/中心/捕捉を同じ m に置く。`check_sound`、`verified_R18_result_classifies_in_same_State438`、`checked_completed_has_original_same_model_dictionary438` が同じ State 上の判定と報告と元 producer の辞書まで結ぶ。lower の authored Origin を捏造しない。

実 entry を検査した fixture では producer [101]/宣言0/出力0/保持行0/固定先40、consumer [202]/宣言1/捕捉 (30,32,34)、別 authored upper [303]。下端の独立 authored route が存在しない。nativeSyntax 40 = none の明示した適合モデルで同じ定理が適用できる。同一固定先の decoy row、異なる元発生箇所、同じ型/位置でも異なる issuer の center、別 upper、候補 ID／辞書／旧 producer write 再発行の誤りは false。実 raw alias 1 行を足して typed atlas も含む State を組み直すと、選択は false、旧 witness の raw K2 拒否は true。他の未対応には言語拒否を作らない。任意の witness が発見されることや全入力の完備性は主張しない。

## 対象と検証

```
902883eb9c68410213bd78895e9b76d0981e859d  lean/Yulang/GeneralDeclarativeI65I74CompletedLowerRule438.lean
2888117b722c0eeca21d737001520ffed9a43534  lean/Audit/Cycle438I74CompletedLowerRule.lean
deebced65525ccf7854348ca0ba3255c435a5782  lean/Yulang/GeneralDeclarativeI65I74CompletedLowerPorts438.lean
10af2732f70684d435b7ae506bdb7faddd93bc74  lean/Audit/Cycle438I74CompletedLowerPorts.lean
8e92685d4456c0b1e485ce0b8656d2141475b3b6  lean/Yulang/GeneralDeclarativeI65I74CompletedLowerReplay438.lean
e528002702a3e75a3d72fda55e08e10632ad07db  lean/Yulang/GeneralDeclarativeI65I74CompletedLowerEntry438.lean
b319b37da730ea1b5e96d241eeb9d28b732a0109  lean/Audit/Cycle438I74CompletedLowerEntry.lean
a45334fc6abc41bfd7b016d4781b67bdd16e1401  lean/Audit/Cycle438I74CompletedLowerEndToEnd.lean
dc3e7210153dc41f19a7a6eb1800672a9780d0da  lean/Yulang/GeneralDeclarativeI65I74CompletedLowerSameModel438.lean
f1990d179a21bc6ba08ff97967add7a66119236a  lean/Audit/Cycle438I74CompletedLowerSameModel.lean
```

公式 Lean 4.35.0 で、正本の既存依存 182 本の blob を照合し、依存順に個別 strict build。上の新規 production 5 本も個別 `lean --trust=0 -DwarningAsError=true -o ... file.lean`、Audit 5 本はそれぞれ独立した空の source dir に一ファイルだけ置き production-only path で `lean --trust=0 -DwarningAsError=true file.lean`。すべて exit 0。Audit の import: `Yulang.*` 以外 0 件、Audit 相互 import／既存 Audit oleans なし。28 の公理監査はそれぞれ propext / Classical.choice / Quot.sound のみ。全 Lake／Rust／solver による証人生成／停止性は未検証。
