# C418: C10 の実際の構造的不一致

[仕様 6.2](https://github.com/momota1029/yulang/blob/2d470a6a0f6dace69f35b878010726a9cdd6711f/spec/06-roles.md#L51-L76) は候補が重ならなければ共存、実際に重なれば曖昧です。そこに載る `Display (list 'a)` と `Display (list int)` の組は重なり得るので、不一致の例として使いません。今回の具体化は同じ role の `R :{tick 'a,tick 'b}` と `R :{tick str}` を、元の一点 `R :{tick int}` で全走査する場合だけです。

- 実入力の元 variant、元の自分への join、実 int 行、実 payload を指す一意の元 `.ordinary (.base .int)` を照合。検査器は元行や元観測を生成しません。
- 勝つ宣言の二つの binder は、同じ実 payload 全体を捕捉します。負ける宣言は、単なる read 失敗でなく、同じ実 payload の既知 int と、その実宣言のコンパイル済みの str が違うことに基づきます。任意の fitting model で variant 全体がその str head の部分型でないことを証明。
- 整合チェックは別です。誤った生の全体 str 行や生の payload str 行を証人として供給しても選択できません。固定 source derivation の三系統（ordered 内の direct/endpoint と declared、joined）を反転し、このチェック範囲で負ける側の `SourceHead` はモデルを仮定せず存在しないことを証明。
- 生の K2 は根と rival の実到達 payload で確認し、入らない循環を一律に排除しません。C09 の真の重複と従来の分岐は変更しません。二宣言のどちらの順でも選ぶのは元の plain 宣言、空 where・関連出力です。

追加検証: `source_head_for_rigid_rival_iff_its_raw_receipt418` は、このリテラル
範囲の負ける head が構文上作れる条件を、元の全体 str 行または同じ実 payload の
str 行のどちらか、という同値にしています。モデルなしの必要十分条件は
入力の型の不一致とは別です。一方、元の int と宣言の str が確かなら、
任意の fitting model でどちらの生 str 行も存在できません。
したがって生行の整合 guard は、不整合を避ける追加の確認であって、
型の不一致の理由そのものでも、仕様全体の完全性の証明でもありません。

追加検証では、有限の where と完了済み出力 producer の部分木を含む全導出で
旧 R9 の局所資格だけを使うなら、同一 event と順序・書き込みで R9 の report
に戻せることを宣言的に示しました。今回の実 C10 範囲は旧 R9 が report を
持たないため、単なる別証人ではなく実際の適用範囲拡大です。既存の入口は不変です。
