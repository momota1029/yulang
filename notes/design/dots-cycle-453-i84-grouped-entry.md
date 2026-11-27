# C453 / G03: I-84 の全元位置を持つ内部報告を累積入口へ

正本 C452 採用 (c6569e6701c1b107b34a46e3dd17758993eb154a)、I-84。spec §6.3 の利用者向け診断の表示は遅延する。診断 report と witness に代表を入れない。旧 Result の Tree は元 where 節との一対一のため、短縮した木を旧判定へ渡さない。

- report 側は旧 Result との追加の和。新しい要素は真の親要求パス・選択宣言 ID・実 cyclic 類ごとの全元位置を持つ。類内は元の宣言順、類間には新しい順序を課さず、重複の個数も比較する。raw の一時クラスラベルは report にしない。
- witness 側も旧 witness との追加の和。旧組は実昇格済み `WhereSites450.NoSiblingMerge.check_full450` をそのまま呼ぶ。新組は C452 の同じ FullProblem 上の元 where 有限 wire を読む。
- 独立な宣言側は実親、原 where の各位置、子ごとの実 K2 または独立な authored leaf を持つ `ScopedLiteralReport`。旧 positional trace は証明に残す。C452 実 outputAtoms が空の段階だけを使い、変更した別 raw へ証明を移さない。
- 受理 iff 正確な独立 report と、その同じ report の有限 witness、全 FitsFull の健全性を示す。I-84 関連の真の親子、重複同入力、複数類、第二位置のみ、元位置改変、旧累積入口を実行試験する。入力原型・phase が違うところ、一般の solver、表示位置は別。
