# C418: C10 の検証記録

固定技術コミット `4455d3f5f98b43be20222cc59cb38571d71aab3d`、Lean tree `5f7186c32c4d8e34ad47da6b82f2642155c39da4`。
[仕様 6.2](https://github.com/momota1029/yulang/blob/2d470a6a0f6dace69f35b878010726a9cdd6711f/spec/06-roles.md#L51-L76) の「重ならなければ共存」の具体化です。掲載の `Display (list 'a)` と `Display (list int)` は重なり得るので、非重複とは判定していません。

## I-74 の三条件

1. `R10` が `R9` を保って選択規則を一つ追加します。元の `R :{tick int}` に、同じ role の実可視リストを構成する二候補 `R :{tick 'a,tick 'b}` と `R :{tick str}`。plain の二 binder は同じ実 payload 全体を捕捉し、str の不一致は独立した元 int 観測と actual str 宣言を照合して決めます。単なる照合失敗ではありません。`dictionary_sound_R10` は同じ固定 `DictionaryEvidence` のままです。
2. `RigidRival418.check` では、元観測・元行・二候補の実番地、元入力一意性、根および actual rival が降りる payload の raw K2、矛盾した生の str 行がないことをデータで検証します。検査器は元行を追加しません。report は実際に勝った元宣言の選択、where/出力は空。既存の入口への委譲は定義上不変です。
3. `RigidRival418.check_sound` は実際の同じ State と Request に対する report と、同じ State の全 fitting model の意味を与えます。この範囲の分類は当該宣言の元辞書だけ（`at_a_real_rigid_scan_only_canonical_selected_classifies418`）。C09 の本物の重複は従来どおり曖昧です。

## 独立した不一致の二つの根拠

- `actual_variant_does_not_satisfy_the_full_rigid_str_head418`: 全ての fitting model で実 variant 全体がその str head の部分型ではありません。元の `int` と宣言の `str` のタグ差を、共変 variant の反転を通して示します。
- `source_head_for_rigid_rival_iff_its_raw_receipt418`: 宣言的 `SourceHead` が作れるのは、検査する元の全体 str 行または同じ実 payload の str 行がある場合に正確に限ります。direct、endpoint、structural、whole と別形の declared/joined を明示的に扱います。健全な入力の型不一致は上の独立した事実であり、この追加の生行 guard は矛盾した raw receipt を避ける確認です。実 int と str の資料が揃う fitting state ではその guard が成り立つことも証明し、検査した State で負ける head の不在にはモデルを必要としません。

## 厳密な再検証

- 公式 Lean **4.35.0**（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）。固定コミットから対象 blob を取得して `git hash-object` で各バイトの一致を確認。その差分を `lake env lean --trust=0 -DwarningAsError=true -o <olean> <source>`、別の audit を同じ厳密フラグで実行しました。
- 独立 C418 **9 source / 3 audit**、C417 との合同 **19 / 7**、C409–C418 の連鎖 **87 / 52**。全部 exit 0。表に含むのは scoped replay であってプロジェクト全体ではありません。追加 import 集合の全バイトを確認して厳密に検査し、新たな **38** 個の `#print axioms` は標準公理のみ。
- 両候補順、各順に ordinary 元行の六順、誤番地や異なる元型観測、第三の可視候補、実重複、偽 ledger、根および実到達 payload K2、off-path の実ループの対照。矛盾する生 str 行が根や実 payload にあると通らず、入らない別 slot の str 行は勝者を妨げません。
- 固定式での補助試験も終了 0。旧入口込み 27 分岐対照と、両候補順で 0–3 の七番地（合計 32,768 組）を列挙し、各順の実番地一組だけが通過。十グラフ状態の有限色試験では、根・実到達点の K2、元観測不足、別 alias payload、矛盾した生 str 行を選択せず、off-path 実循環と実同一 payload の alias は選択を妨げませんでした。宣言・実 input・番地を固定して宣言表の同じキーの意味を str から int へ変える対照では、C10 選択から C09 曖昧に変わりました（同じ入力モデルが両 snapshot に適合）。実 off-path 再帰がある fitting model の辞書と、型が同じでも別の元 slot では選択できない fitting model も厳密に検証しました。補助試験は公式の 38 監査の個数に含めません。

凍結 `lean/Audit.lean` と `lean/README.md` は内容を開かず、blob ID の不変を確認。C365 の固定文、C380 の一覧、C402 固定 carrier はこの周の対象外で変更しません。
この枝は一点・二候補・空 where と出力・元の自己 join をすでに保持する範囲だけです。非対応の false は言語の拒否ではありません。Rust、証人生成の完全性、一般停止性、全体ビルドは実行・主張していません。
