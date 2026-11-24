# Yulang C400: I-71 型つき RHS 木・元選定・同じモデル

閉じた補題なし・分けた補題なし。

## 指示と今回の範囲

- 実開始 2026-11-24 19:32:07 UTC。冒頭に C399 完了 `66af2822a6b22f5f67efdffcfd9320cddfda7621`、正本 `39eb39011dbd5032f9d5e5b8b07700a26f47bcd2`、standing orders、inbox、role／推論 spec を照合。正本は C399 を取り込んでおり、その Lean tree は work と同一。
- 途中で [I-71](https://github.com/momota1029/yulang/blob/ad54e4f9703bc43501a605c58eec813f9fcf199f/notes/plan/dots-inbox.md)（inbox `eb64179ca0cf4f86fe36697b824b58fac3ffec12`）を確認。C397 の質問は解決した。**混在 RHS は B6 の型つき木のまま保持し、旧 C386 の `.declared` ベクタへの平坦化は義務から外す。** [新出力の設計](https://github.com/momota1029/yulang/blob/71f1597f312bae8910de85a711d3c8c8d6ab25ae/notes/design/dots-cycle-400-i71-typed-tree-receipts.md) に移行した。言語の判定・受理は変更せず、新しい質問もない。

## 証明したもの

1. **元の中心名。** `guarded_where_compound_uses_original_port_center400` は、実の C350 preparation と同じ placement、元 where 節・引数の位置、独立に選定が裏付けられた有限子のもとで、C327 の original Port が持つ中心名を同じ子の要求に読む。新たに中心の構造を観測する条件はない。bare なら `direct_where_argument_preserves_named_center400` が親の実 lexical slot を読ませる。[C400 source 経路](https://github.com/momota1029/yulang/blob/f79ec23353abe9c3b8ac7f7b633e86edc30f8cac/notes/design/dots-cycle-400-guarded-where-name-flow.md)。検査済み同一元宣言と同じ exact where ledger に対し、`original_where_slots_agree_from_same_exact_ledger399` は列を検索し直さず同じ元 where binder の固定出力名を導く。ただし native head 全体の中心名を端点から復元する主張ではない。
2. **木を直接受け取る。** `TreeOutput400`／`TreeLocalEvent400` は旧 C386 レシートを入力とせず、元の pre-output frame と元 supplier／出力 ordinal／固定 target の位置に、B6 の記号的な型つき木を data として残す。`typed_output_from_B6_without_old_receipt400` は、当該元 Body の B6 入力と実 slot の kind 適合があるとき、元の実 lexical 名を代入した typed RHS を保持。record・variant・join の中の nominal、点と不変な区間、行の区別を落とさない。既存 ordinary の正確な式も別の constructor で保持できる。`exact_preoutput_frame_produces_tree_event400` は、検査済み元 role と各元出力の B6 入力がある任意の frame について全出力を元の順に構成する。
3. **同じモデルでの実値。** `typed_fixed_equation_matches_B6_value400` は、任意の同じ `Model` で、元 B6 plan の直接の読みと保持した typed RHS の読みが、同じ実型の `some` 値になり、出力式の左辺が元の固定 target であると証明。nominal 引数の区間は構文に残し、実値を読む箇所では実の中心名を使う。端点から中心を選ばず、全型を不変として比較しない。これは型／行の同じ割当てでの source 値の一致で、任意のモデルがその出力等式を充足する主張ではない。
4. **有限木全体。** `same_selected_source_B6_actual_equations400` は、任意の既に独立の guard を持つ有限 pre-output source 木と検査済み元宣言、その各 frame での型つき B6 入力について、その**同じ木に索引づけた**型つきレシート木を作る。元の選んだ frame、辞書のキー、where の順と重複はそのまま。得た一つのレシート木について任意の同じモデルを全節点・出力に適用する。別の frame を同じ辞書キーや等しい端点から再構成しない。

## 残り

**閉じた補題なし・分けた補題なし。残り 14 件 = 未証明 3 ＋一部 11。** S13bbba の固定全称文はまだ閉じていない。新 carrier の純粋な source 出力と同一モデルでの読みを、任意の一般 `Classifies`／同一イベントの `GeneralLocalMeaning` から得る実 pre-output source guard と B6 データ供給に接続する必要がある。`FrameChoice400` はその入力インターフェースであって一般分類器ではない。現在の `SourceRhsCode394` の型つき範囲に対する結果で、すべての B6 term の供給を完了したとも主張しない。特に C357 の `names (.primitive _) = none` なので、現状の tree branch は primitive application を任意の混在子として構成する手前。primitive を純 ordinary で保持できることとは区別し、内部形式の不足を言語の拒否にしない。旧平坦ベクタの互換性は未完ではなく **I-71 により証明対象外**。別件 S13bbbb の retention、I-65 の 2/3、停止性、旧 Local/C334、新 fixture は触れていない。

## 新規ソースと別監査

- [GeneralDeclarativeI65B6SameWhereProjections400.lean](https://github.com/momota1029/yulang/blob/81f2991d8192290f3dc989be7caaf585db0a6185/lean/Yulang/GeneralDeclarativeI65B6SameWhereProjections400.lean) (`ee9b868c1a01efd181e68faff4d5fa4df9016b66`) / [独立監査](https://github.com/momota1029/yulang/blob/81f2991d8192290f3dc989be7caaf585db0a6185/lean/Audit/Cycle400B6SameWhereProjections.lean) (`ab643ecb1881d024068da1f66a436679a5508e29`), exact `81f2991d8192290f3dc989be7caaf585db0a6185`。
- [GeneralDeclarativeI65B6TreeReceipts400.lean](https://github.com/momota1029/yulang/blob/255872ef91cd80f1989c76255bf162ab7fdb0b20/lean/Yulang/GeneralDeclarativeI65B6TreeReceipts400.lean) (`f2564a6be2ef49b6fcd1270a8f9acde2d88b2939`) / [独立監査](https://github.com/momota1029/yulang/blob/255872ef91cd80f1989c76255bf162ab7fdb0b20/lean/Audit/Cycle400B6TreeReceipts.lean) (`226ede986c7b6f1325314402f719256d14d373f8`), exact `255872ef91cd80f1989c76255bf162ab7fdb0b20`。
- [GeneralDeclarativeI65GuardedWhereCenter400.lean](https://github.com/momota1029/yulang/blob/255872ef91cd80f1989c76255bf162ab7fdb0b20/lean/Yulang/GeneralDeclarativeI65GuardedWhereCenter400.lean) (`d7c1a4d771fb59f83fa2449352ba5e06d8685bc3`) / [独立監査](https://github.com/momota1029/yulang/blob/255872ef91cd80f1989c76255bf162ab7fdb0b20/lean/Audit/Cycle400GuardedWhereCenter.lean) (`4d6b2105c49e7e42bcdd6ea7068a2f7c8d92a5bf`), exact `255872ef91cd80f1989c76255bf162ab7fdb0b20`。
- [GeneralDeclarativeI65B6TreeActualMeaning400.lean](https://github.com/momota1029/yulang/blob/61c1a1e483697432fa1e422985cc02091f621b04/lean/Yulang/GeneralDeclarativeI65B6TreeActualMeaning400.lean) (`a7405388bd7c20caff392c43233c34e4ad8d1229`) / [独立監査](https://github.com/momota1029/yulang/blob/61c1a1e483697432fa1e422985cc02091f621b04/lean/Audit/Cycle400B6TreeActualMeaning.lean) (`3440bf6a5c2d59c6724561e994d8b7aa3e570653`), exact `61c1a1e483697432fa1e422985cc02091f621b04`。
- [GeneralDeclarativeI65B6PairedTreeReplay400.lean](https://github.com/momota1029/yulang/blob/61c1a1e483697432fa1e422985cc02091f621b04/lean/Yulang/GeneralDeclarativeI65B6PairedTreeReplay400.lean) (`4ef8bc7098ee342d9df2aa4cf2ec2c8b62351696`) / [独立監査](https://github.com/momota1029/yulang/blob/61c1a1e483697432fa1e422985cc02091f621b04/lean/Audit/Cycle400B6PairedTreeReplay.lean) (`4f21b42feca3167ea7736bf7df0454767a441a1b`), exact `61c1a1e483697432fa1e422985cc02091f621b04`。

## 検証と公開

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) を用い、新規五モジュールを `lake env lean --trust=0 -DwarningAsError=true -o … Yulang/<module>.lean`、別 import の監査を `lake env lean --trust=0 -DwarningAsError=true Audit/<audit>.lean` で検証、すべて exit 0。五モジュール の exact commit から再取得した同一バイトで各 source／audit を別 workspace に再構築し、全件 exit 0。29 補助定理と original-plan accessor の公理は `propext`、`Classical.choice`、`Quot.sound` の範囲。追加五 import の同時 import も strict、exit 0。起動時は offline、正規の環境復旧後に検証。全リポジトリの build・verify-lean.sh・Rust は実行していない。利用量の枠は不明。

C399 からの変更は設計三本、五 source・五監査、barrel の import 追記、心拍、今回の報告の計 16 本。固定定理・一覧と凍結二ファイルの blob ID を保持し、凍結二ファイルの内容は読んでいない。work/dots-main の期待 head から非強制で公開し、変更パス・本文・barrel の旧全文＋追記を照合する。
- 最終照合開始 `2026-11-24T20:22:22.384Z`（50 分経過）。
