# Email Draft

件名: Yulang の型推論と effect-only annotation についてのご相談

相談先の先生

突然のご連絡失礼いたします。○○大学大学院○○研究科博士課程の［氏名］と申します。

個人で設計・実装している実験的プログラミング言語 Yulang の型推論について、専門的なご意見を伺いたく、ご連絡いたしました。

Yulang は代数的エフェクトとハンドラを備え、値型と effect row を subtype 制約によって同時に推論する言語です。現在の実装と形式化では、主に次の性質が得られているように見えています。

1. 具体的な値型や effect family 集合を明示しない高階関数に対して、比較的一般的な公開型を推論できること
2. 返り値型と residual effect row に関して多相な handler combinator を、effect-only skeleton によって扱えること
3. 表面の annotation が値型の指定ではなく、handler に見せてよい effect と外へ残す residual を局所化する契約として働くこと

内部では、subtype 制約に方向付き stack weight を付与し、handler が effect row から実際に除去できる部分を、境界を通して可視な effect の共通部分に限定しています。現在、単相再帰までを対象として、推論の停止性、handler hygiene の健全性、および principal weighted scheme の存在を形式化しています。

特に、次の三点についてご意見を伺えればと考えております。

- subtype と内部の hidden evidence を含む体系で、主型性をどの scheme に対して述べるのが適切か
- effect-only annotation を、既存の型推論・effect system 研究の中でどう位置づけるべきか
- 現在の停止性・健全性・主型性の議論で、優先して疑うべき補題はどこか

概要と小さな例をまとめた短い技術資料を添付いたします。より詳細な形式化と実装もありますが、初めからお読みいただく必要はありません。

もし可能でしたら、30分から45分ほどオンラインでご相談する機会をいただけないでしょうか。

どうぞよろしくお願いいたします。

［氏名］

所属: TODO

メールアドレス: TODO

Yulang repository: TODO
