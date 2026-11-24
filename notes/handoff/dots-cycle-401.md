# dots cycle 401

**閉じた補題なし・分けた補題なし。** S13bbba の元の全称文は開いている。Lean の変更あり。次は、一般 Classifies の元の選択節点で同じ pre-output frame と B6 の元入力が揃う接続。

## 指示と開始

- 実開始 `2026-11-24T20:30:20Z`、前周 `6601c59528413726906e88eb509f004a396b6db0` 完了を照合。integration は `793febb8a7f2069c7315a1a37954209395461c03`。Lean tree は前周公開分と同じ `0d450ec836bd71c202c6d411345929f2d345d115`。standing orders・inbox・仕様・心拍を冒頭に確認。
- [I-71](https://github.com/momota1029/yulang/blob/793febb8a7f2069c7315a1a37954209395461c03/notes/plan/dots-inbox.md)（inbox `eb64179ca0cf4f86fe36697b824b58fac3ffec12`）適用。B6 から渡す型つき RHS を木のまま読み、旧 `.declared` ベクタに戻す証明は対象外。新しい仕様判断・受理変更・質問はない。
- [初期設計](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/notes/design/dots-cycle-401-i71-primitive-tree.md)・[未接続の実入力](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/notes/design/dots-cycle-401-i71-source-gap.md)

## この周で示したこと

1. **実 primitive の入れ子** `mixed_primitive_has_exact_authored_mode401`・`exact_mixed_source_and_retained_values401`。scalar、pair、emptyRecord、exactEmpty を元の `Use.mode` で取り、任意の表現された有限 RHS の元 tree/reference と代入後 tree は任意の同じモデルで同じ値になる。pair の両子に declared nominal、その逆方向や record/variant/join の下の混在も構造のまま持てる。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65B6MixedTree401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401B6MixedTree.lean)
2. **出力の出どころ** `source_tree_retains_exact_original_mixed_outputs401`。独立な guard を持つ同じ有限 source 木に対し、受領済みの B6 RHS を元 `Request`・宣言番号・出力番号・実 body で照合。元の順・固定先で、すべての同じモデルについて検証した。可能な場合は別途型つき endpoint 証拠付きの経路。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65B6MixedOutput401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401B6MixedOutput.lean)
3. **従来の型付き入力の保存** `original_typed_plan_keeps_reads_and_values401`・`exact_original_primitive_interpreter401`。C398 plan は元の正確な読み列と同じモデルでの値を保つ。authored primitive の独立な解釈は現行 `application` と元アリティで一致。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65B6TypedPlanConservative401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401B6TypedPlanConservative.lean)
4. **元の lexical 名** `mixed_reads_are_exact_original_variables401`・`stored_head_emits_exact_ordered_mixed_values401`。正規化された元 RHS の変数列（重複も順もそのまま）だけを読み、実際に保存された候補について explicit は元宣言の scope、default は元 role の引数位置と実 head arity から値／行の読み先を出す。すべての要求された関連出力の ordinal と固定先を保つ。名前を得るだけなら中心行の観測や native 端点証拠は要らない。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65B6MixedLexical401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401B6MixedLexical.lean)
5. **同じ保存済み候補** `single_positive_tape_stored_head_is_unique401`・`same_stored_choice_has_same_mixed_equation401`。同じ可視走査の唯一の positive は実候補 object・可視番号・レジストリ中の原 ordinal まで一致。元 placement が同じなら範囲外の詰め値で元 frame の lexical 観測・元 where・同じモデルでの値が変わらない。異なる走査の同一性は主張しない。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65SingleStoredFrame401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401SingleStoredFrame.lean)
6. **実 preparation と子** `prepared_source_has_exact_mixed_output401`・`prepared_mixed_where_slot_reads_original_child401`。実 C350 preparation の元 frame と選んだ内部候補を使う。元 where 節の番号で同じ子の部分木を引き、その子の原出力 ordinal を読ませた。実 lexical slot は元の固定 target を指す。同じモデルの元 typed RHS を読むが、その target に等式が保持されたとは言わない。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65PreparedMixedWhere401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401PreparedMixedWhere.lean)
7. **子ごとの署名を仮定しない** `original_guarded_tree_produces_mixed_source_values401`。任意の同じ有限 guarded source 木について、根の role signature、検査済み元宣言、元の出現を指す B6 注釈があればよい。全 where 子の arity と出力の宣言を元 `Clause.Signature` から導き、explicit/default の全 lexical 名、元 body、順、固定先と同一モデルでの右辺の値を得る。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65CertifiedWhereInputs401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401CertifiedWhereInputs.lean)
8. **型付き端点証拠は別** `qualified_tree_erases_only_proofs401`・`exact_name_does_not_supply_bound_ticket401`。追加の認証がある場合、証明だけを消すと同じ元の木（中心・両端点を保持）になる。名前があっても端点証拠が無い場合には、前者から後者を作れない。 [Lean](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Yulang/GeneralDeclarativeI65MixedQualification401.lean)・[独立監査](https://github.com/momota1029/yulang/blob/b2872fd7327e301df215ad3153ff1228bcca888a/lean/Audit/Cycle401MixedQualification.lean)

## 残り

- **残り14件 = 未証明3＋一部11。** S13bbba は、実際の一般 `Classifies`／`GeneralLocalMeaning` の同一イベントから、この独立な guard つき pre-output source frame と元の B6 注釈を得るところが未証明。B4 の選択は未フィルタの根／実到達候補での K2、根拠付きの入力と where 依存の有限完了を独立に扱う必要がある。元 C386 event の住所だけではこの証明にならない。
- B6 の渡す木は現在の正規化済み role Pattern domain で、複合 row 式や全型言語・B6 本体の一般化までは主張しない。実の記号注釈を `State` または `Request` の入力に載せる接続はまだ無い。仕様が認めた表現拡張と、型推論を B4 で再実装することは別。旧ベクタは仕様の義務ではない。
- S13bbbb の State における保持・固定先の充足は別で未着手。固定した I-65 step 1 の文・組み立て・チェックリストは不変。step 2/3、停止性、旧 Local/C334、fixture は触っていない。

## 照合・検証

- Yulang2 は audit の X7（record の元仕様と旧 syntax が直接対応しない）を読んだ。これは混在型の実機確認ではない。今回の内部表現は現行 spec/04-types・spec/06-roles（6.3、名・区間・関連型）・spec/10-inference-core §10.2 と I-70/71 を正本にし、Yulang2 を新規実行しなかった。
- Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）。新規8モジュールそれぞれの source と独立監査を `lake env lean --trust=0 -DwarningAsError=true`（source は `-o …` 付き）で確認。各 exact pinned byte からの別 build と八つの実追加 import＋全監査の同時 import を再検証した。41 定理＋子読取り accessor の基礎公理は `propext`、`Classical.choice`、`Quot.sound` の範囲。`sorry`、新しい公理、`native_decide` は追加せず。
- 触れた21ファイルは新規 Lean8、独立監査8、import だけを追加した barrel、設計2、標準報告、心拍。固定文と禁止2ファイルは変更なし。`work/dots-main` のみ expected-head・non-force で公開し、同じ exact Git bytes を確認。全体 build・verify-lean.sh・Rust は実行していない。使用量の枠は不明。
- 最終照合開始 `2026-11-24T21:20:35.111Z`（50 分経過）。
