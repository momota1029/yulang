# Yulangの構文とCSTリファレンス

このリファレンスは、受理するYulangの`syntax-v0`表層構文と、対応するsource-orderのlossless Rowan CSTを記録する。まず[構文の内容モデル](conventions/syntax-content-model.md)でsource文脈に置ける形式を調べ、各形式の生成規則はリンク先の構文ページで確認する。

受理可能な内容モデルを先に読む。[CST共通規約](conventions/index.md)は、source順のtree配置、表記、別層であるrecoveryの参照先を記録する。recovery構造は、受理する表層構文を広げない。

2026年9月17日のAuthoritativeな「Syntax freeze and vertical-implementation completion-policy amendment」が`syntax-v0`を凍結する。構文ページがまだ扱わない詳細な生成規則は、Authoritativeな設計記録が定める。実装、test、fixture、commitは規範的な出典ではない。
