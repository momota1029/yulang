# M1 のあと: Simple-sub 並みに速い推論実装 (2026-11-08)

状態: 構想。ユーザーの合意あり（2026-11-08「まあありですね」）。意味論の決定ではない。

## 位置づけ

- M1 の Lean solver は、証明のための reference solver（明示的な DNF と有限 list）。
  `let` の選択肢の展開は最悪で指数的になりうる。M1 は正しさの証明で、時間・メモリ性能は保証しない
  （`spec/10-inference-core.md` 10.15 末尾の区別）。
- 速い実装は M1 の外。reference を正本として固めたあと、核から実装を導く段階で作る。
  先に速さを入れると、モデルのずれを抱えたまま証明が積み上がる（B4 の経験）。

## 目標

- Simple-sub 並みの速度。変数をその場で量化せず、境界（bound）を伝播して必要になるまで遅らせる。
  区間・遅延の方針（`spec/06-roles.md` 6.5）と相性がよい。
- 「速い版が reference と同じ答えを返す」ことを、まず differential test、次に Lean の証明で確かめる。

## 素材

- 旧世代の高速化の証明系: tag `archive/proof-sprint-2026-11-04` の `notes/design/2026-07-02-speedup-proof-system.md`
  （存在すれば）。サルベージするときは、何のために要るかを確認し、旧スプリントの前提を持ち込まない。
- Simple-sub の extrusion・intrusion・generalization は M1 の外の証明義務
  （`spec/10-inference-core.md` 10.4 付近の「残る」記述）。

## 先に決めること（そのときユーザーに聞く）

- 速い版の「同じ答え」の定義（主型が構文的に同じか、同値か）。
- 量化を遅らせたときの、多相の扱い（let 多相との関係）。
