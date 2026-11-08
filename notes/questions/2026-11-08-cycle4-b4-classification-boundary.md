# B4Statement の翻訳時に露出した二つの境界（未決定）

承認済みのB4草稿をそのまま翻訳すると、次の点は補う意味論が必要になる。
既存コードを変更せず、MainB4のtarget schemaに未接続と明記した。

## 1. 唯一候補だがwhere子に辞書がない場合の親の最終分類

例（概形）:
```yulang
role Left 'a
role Parent 'a
impl Parent (box 'a) where Left 'a
```
`Parent(box int)` の候補が唯一だが `Left int` に候補がない場合、親自身の
K2も候補消滅もなく、草稿のselectedには全子selectedが必要なので成立しない。
草稿の四規則だけでは親に分類がない。これはLean上の全体停止/分類定理の前提でなく、
独立Classifyのどの規則に入るかの問題である。

1. **遅延案（推奨）**: 親の独立結果は子結果を保持する未完成の診断treeとし、最終言語分類の
   写像をユーザー決定後に追加。現在のschemaでは未証明のまま置く。
2. 子の拒否・曖昧・保留を親へ伝播。ただし「rejectedはrootK2/candidateK2/候補消滅だけ」の
   (5)を子由来の理由まで拡げる必要がある。
3. 最終survivorを全whereの成立も含むものに再定義。候補消滅と関連型・子の再帰の循環を
   独立判断として整理する必要がある。

同様にlowerの頭は既知だが、ある候補の検査がpendingである場合の最終pending規則も、
草稿の「lower頭未解決」のみからは出ない。実装に合わせて無断で追加していない。

## 2. whereの順序を替えた辞書の「内容が同じ」

`impl Parent 'a where Left 'a, Right 'a` と逆順の宣言では、既存Dictionary.nodeの子Listは
構文的には逆順になる。子辞書の列のliteral equalityと、同じ義務への証拠の一致は別。

1. **遅延案（推奨）**: 需要/宣言位置を対応させた独立な辞書観察同値を設計してから
   instantiate。今回は`DictionaryEquivalent`という明示的な未接続境界にとどめる。
2. source義務の正規順序で辞書をcanonicalizeしliteral equalityを証明。
3. 子列のPermutationで同値を定義。ただし重複where・同じroleに異なる引数がある場合に
   需要との対応が必要で、単なるkey multisetでは足りない可能性がある。

既に確定したwhere連言の順序独立そのものを再質問しているのではなく、その辞書の
Lean上の表現・観察同値を問う。新しい意味論は採用していない。

## 回答（ユーザー, 2026-11-09）

- 境界 1（唯一候補だが where 子に辞書がない親の最終分類）: **選択肢 1（遅延案）**。親の独立結果は子結果を保持する未完成の診断 tree とし、最終言語分類の写像は後から足す。現在の schema ではこの点を未証明のまま置く。
