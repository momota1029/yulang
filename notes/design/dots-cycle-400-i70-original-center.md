# C400: 選定を変えず、同じ出現の実中心名を保持する

I-70 の S13bbba のみ。新しい正本 `39eb39011dbd5032f9d5e5b8b07700a26f47bcd2` は C399 を統合済み。同じ Lean tree `8c4327cecfc840081178d679818dece6e3eec91e`、inbox `b9b52159d2e018bfa65f9f7daacd58308a64c027`、role と推論 spec の本文は不変。混在 `.declared` は既存質問の保留のまま。

- **足りない事実**：同じ有限選定に保存された元 head の各 binder 出現と、その出現が持っていた実中心識別子の対応。候補の決定は中心の構造的な行を読まずに成立しうる。両端の観測や意味上の同値では、どの中心名を RHS に書くかは決まらない。
- **根拠**：[role §6.5](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/spec/06-roles.md#L382-L410) の中心の仕様。選定までは、分散付き端点と既存 K2／候補規則を変えない。中心は実の名前であり、読み出せる center row の証明とは別。反復する binder では元の中心名を出現別に保ち、選定の後に既決の等式を足す。等式が真だから名前を置換する規則は増やさない。[推論 §10.8.1](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/spec/10-inference-core.md#L275-L283) の型/行情報は B6 入力。
- **直接読める場合**：元の request の位置と元宣言の正規化した bare binder の位置を対応させ、その literal `Capture.center` を保持する。これは `getElem?` による名前の読みで、center row、モデル、solver release に依存しない。where で作られる binder は C395 の original clause/equation と C399 の同じ有限子イベントから、実の固定 target を読む。default は同じ demand の元位置で読む。
- **残る投影**：入れ子の native/record の中心は、既存の元構文・要求経路で実名が保持された場合だけこの読みに接続する。候補の native bounds に適合する任意の数を補充せず、見える中心行がないだけで保留にも変えない。C399 の `DeepRead` の再中心化を、同じ可視候補テープの選定情報まで運べるか調べる。この負の境界は一般の受理や実プログラムの反例ではない。
- **到達点の形**：同じ guarded `LiteralLocalEvent`／元 raw declaration ordinate／元 `where` の子を保持し、元 binder に由来する実名の読みに C399 の B6 projection 同値を適用する。前提が強い確認部品だけを固定 S13bbba の完了に数えない。開いた 14 行、固定定理、受理条件、他の行、混在 wire は変更しない。
