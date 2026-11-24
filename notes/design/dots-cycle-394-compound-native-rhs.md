# Cycle 394: record/join 内の宣言型を元 RHS の構造に残す

I-69 の先頭 S13bbba のみ。正本 `9546c99d2ce53db79b1493046f850cb5c818f75d`、inbox `5e202637769e290325b60e4425812e784428f3d7`。[二つの不足の出所](https://github.com/momota1029/yulang/blob/e44176405150be94e27ea50b306dd534ebbde340/notes/design/dots-cycle-392-i69-missing-source-facts.md) は C392 の (a) のまま。局所 rule は元の source body/capture から RHS を作るもの。retention の S13bbbb は変更しない。

## 新しい構造的な論理 RHS

`SourceRhsCode394` は元 binder と実 logical center、record のラベル・payload/tail、variant の tag、join の左右、宣言済み nominal application の順つき引数を再帰的に保つ。record/join の中の実名目型を、普通の translation に誤って回したり、内側の native 型を scalar に潰したりしない。さらに native の value argument 自体が構造式でも subexpression を保持できる。type/row を区別し、捕捉点と inherited invariant の下端/上端を残す。構造式を勝手に interval の点に評価するのではなく、式として別に持つ。古い pure native に戻せる場合だけ、C392 と同じく型式は explicit point に射影する。

`CompoundSourceRhs394` の actual 元 source rule は、C392 と同じ actual `Use` と現 (kind/variance) table、C393 の actual head/where/default slot read と、その位置の independent `TypedBodyCapture392` を使う。候補選択は行わない。構造 node は子の証拠を独立に再帰して元順を保持する。元 Body は `Supplies`、same original output `Fin` ordinal/target は actual demand から読む。`OriginalCompoundOutput394.emit` がこれらと typed RHS tree を持つ **論理的中間式**を作り、`compound_emit_is_original_source394` が元の normalized source を正確に取り戻す。`compound_source_rhs_functional394` は同じ source と同じ actual capture/context でこの code が一意。

## 元 wire を変更しない

`native_rhs_embeds_in_original_compound394` で既存 C392 の pure-native RHS の任意長/任意深さの実導出を埋め込み、端点/元 vector をそのまま復元する。 `existing_native_output_has_same_wire394` は実 C393 `AuthoredOutput` の native/tagged branch から、same Body / same requested のまま、**既存 C386 の literal write と同じ bytes-level syntax**（Lean の write 値の等式）へ射影する。新しい compound に flat vector の順や出力 constructor を勝手に与えない。 `none` は既存 wire への部分射影がないということに限り、言語の拒否ではない。

## 残る本物の論点

この新しい tree で元の structural RHS を作る規則は追加したが、既存 `.declared target Pattern Arguments` は bare/tagged root の flat typed vector。任意の compound/code を同じ receipt に運ぶ全体の実生成規則と、型付き source の primitive 等の参加、及び **全ての実選択**からこの source frame/typed body proof が出る事実がまだない。C393 の `AuthoredBodyFrame` は実 source 宣言と actual placement を要求するが、C384 key/kids・C386 arbitrary eventAt から勝手にそれを得ない。既存 wire、固定 theorem の文、`LocalSource` の全域、受理条件、再帰/停止性、S13bbbb、Step 2/3 を変更しない。これは spec の意味未決ではなく、論理中間表現から固定 receipt への対応の未実装。S13bbba の全称は未完で、追加分割なし。
