# I-70 質問: 混在 RHS と `.declared` の厳密な順付き表現

**先に保留案:** B6 が渡す元出現つき型付き RHS を B4 の source 入力とし、B4 では同じ role 選択、出現、output ordinal、fixed target への等式を照合する。混在 body の既存 `.declared` ベクタへの機械的な対応だけは、定まるまで証明を保留する。言語側に型の判定や拒否を増やさない。fixture/新しい encoding は追加しない。

[spec/06-roles.md §6.3](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/06-roles.md#L88-L95) は関連型を普通の等式として元出力へ足すことを指定。[spec/04-types.md](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/04-types.md#L75) と [spec/10-inference-core.md §10.2](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/10-inference-core.md#L25) は型の意味を与える。ところが [C386 LiteralWriteSyntax](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean#L17) は full Pattern と List Argument の内部表現で、record/join と declared nominal が入れ子になった RHS の vector の対応を指定する spec の文を見つけられなかった。例として、関連型 `type out = {item: box 'a}` のような構造＋名目型を考える（仕様を示すための記述例。fixture 追加・新たな受理主張ではない）。

**確認事項:** この内部ベクタの対応は保留し、型つき RHS の元出現・順序・固定先を B4 が読む境界でよいか。それとも内側 nominal の引数をどの位置・順序に置くかまで、すでに準拠すべき対立しない仕様/設計があるか。後者の場合は正本を指してほしい。言語としての mixed shape の可否を問い直す質問ではない。
