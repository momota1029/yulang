# C466: 実 capture 座標と native 発行の境界

## 検証したもの

- 既存 `NestedDecode332.normalized` → `NestedMaterial332.assemble` の実出力を読み、選んだ生成仕事の元 capture ordinal、元 binder、同じ post raw 行の exact ordinal・物理 slot を返せる。既存 GD 表・本当の単一可視 head の元宣言/引数/端点を読み、有限 replay に接続する。旧 source-only read が本物なら `InlineGround331.certify` が古い ordinary `Supported` の source 由来を保つ。
- modern compiler と旧 compiler がどちらも読めるときだけ、同じ元 head と同じ literal binder pose のコードでも一致する。正規化した pose を実元 AST へ引き戻す補助は join-free（既存 scope check）であり、shadow の削除を正確に戻す。生き残る二つの位置を同じ元位置に丸めない。元の default/union の新しい訪問規則ではない。
- 旧 `keep` に既知の物理 origin slot と route の logical/physical の列が**明示的に**含まれるとき、その列を避ける。keep の違いで同じ元 capture/元位置/raw ordinal を選び直さない。これを full freshness/発行の条件と同一視しない。
- C465 の exact Native360 release は、真正な旧出力・別に供給済み同相・完全な board write・期待 endpoint と同じ物理 slot を検証できる。健全性は **post** FitsFull（旧から拡張する全モデルの主張でない）。値や旧 ordinary の source provenance だけで新しい Origin / issuer / route を作らない。

## 具体的な最短境界

実同一 head の旧 producer は fresh slot 7 / raw ordinal 3 / capture ordinal 0 を生成する。C464 の独立 cut と old 行から作る供給済み 2 行は、raw 表示を 4→6→7 にできる。ただし同じ保存済み I65 origins/routes に 7 の本物の payload route がなく、既存 inline field は開かない。さらに実 payload の `{40: var 5}` は普通の非変数 endpoint なので、同相を別に供給しても Native360 の literal write では表せない。既存の正しい modern unary covariant head が旧 producer では一切 encode できない別の実対照もある。これらは **現在の実装範囲**であり、言語拒否や G05 の優先判定ではない。

次は実 compiler が出す許可済みの発行レコードに、元 source/capture ordinal と full address/issuer/route の生成を同時に結ぶ。旧 C332 allocation、C401 lexical 形/値の読み、C464 supplied cut、C465 既存 board の exact read のどれも単独で発行器にならない。I-89 の境界を保ち、実位置の裏付けのない新名・新 raw 辺・新 issuer・新 ルールは採用しない。G05/G10/G08/G06/G07/G20/G21/GD へは移らない。
