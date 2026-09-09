# Yulangの構文とCSTリファレンス

このリファレンスは、受理するYulangの表層構文と、対応するsource-orderのlossless Rowan CSTを定める。
CST共通規約のsliceは、node、token leaf、trivia、recoveryの位置を定める。
parserの制御手順や保守作業の経緯は扱わない。

[CST共通規約](conventions/index.md)は、共通のtree表記と、source root、header、recovery diagnosticの責務を定める。
既存の構文ページは、段階的な再構成を待つlegacy implementation materialである。
それらにはparser behavior、AST、implementation path、fixtureが残ることがある。
まだ再構成済みの構文schemaではない。
review済みのbatchが、これらをlanguageとCSTのreferenceへ置き換える。

このリファレンスにはAuthoritativeな設計記録を適用する。
承認済みのCST targetがまだ実装されていないときは、ページがその状態を明記する。
現在の実装を言語仕様として扱ってはならない。
