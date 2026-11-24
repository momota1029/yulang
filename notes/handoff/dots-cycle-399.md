# Yulang C399: 実の有限選定子と B6 を読む exact source

閉じた補題なし・分けた補題なし。

## 冒頭の照合と復旧

- 2026-11-24 18:31:13Z に実開始。integration/m1-final `be3aaeb1d3d27dc31e42a2ee3a5def68db47318e` の standing orders・inbox（I-70 blob `b9b52159d2e018bfa65f9f7daacd58308a64c027`）、[role §6.2/6.3/6.5](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/06-roles.md) と [推論 §10.8.1](https://github.com/momota1029/yulang/blob/be3aaeb1d3d27dc31e42a2ee3a5def68db47318e/spec/10-inference-core.md) を読み直した。
- C398 は `1565ac82c740745341db584d68af399e3e6376fd` の時間上限による検証済み中間引継ぎであり、通常完了ではない。旧 worker は活動しておらず、exact C398 の三モジュールは公開済み。新たな未公開差分を復旧したとは数えない。
- [C399 設計](https://github.com/momota1029/yulang/blob/20c35fdd730a5f692cf267f73dc3afdf68fb56bf/notes/design/dots-cycle-399-i70-child-source.md) に従い、実の有限子イベントの特定と元 source/slot の接続のみ実装した。混在 `.declared` を新たに定義していない。

## 検証済みの補助命題

1. **実の有限 where 子と元 supplier。** `addressed_child_event_at399` と `original_where_selected_event399` は、任意の独立な `ReplayJudgment` に対し、既に元の request に結び付いた有限 `AddressedDictionaryForest` から、元 clause ordinal にある同じ guarded event と dictionary 子節点を取り出す。role／関連名の検査済み元宣言から `selected_where_supplier_exists399` は元の明示 Body または正式な role default の存在を導き、子の既存 RHS を使わない。その actual event と supplier の B6 plan と実 slot の kind 適合が与えられれば、`selected_where_B6_produces_from_actual_event399` は元の occurrence・出力 ordinal・固定 target と C394 source relation を持つ論理 RHS を返す。一般 `Classifies` からこの event-bearing forest が任意に作れるとは主張しない。
2. **出力前の実フレーム。** `positive_tape_produces_original_frame399` / `positive_tape_B6_source_output399` は実の正の complete candidate tape（C367）に現れたヘッドから raw declaration ordinal と入力 capture を取り出す。ordered head と既存の承認済み unary covariant joined head を区別し、後者は実の merged payload 名を両 binder に使う。`origin_frame_where_independent_outside399` は実宣言 scope と同じ placement の下で範囲外の値を変えても where 列が動かないことを示す。tape は一般の native K2 を含む完全な選定規則ではない。
3. **順序付きの全イベント。** `addressed_ledger_B6_logical_rhs399` は任意の有限 addressed dictionary で、元の各 guarded event に B6 入力があるとき、各元 ordinal で同じ supplier・固定要求・occurrence と論理 RHS の意味を証明する。論理 RHS は `rec.written` から読み取らない。code / kind 未表現のセルを詰めない。
4. **既存 ordinary literal。** 検査済み宣言・正の tape・元 placement・宣言された各要求名および B6 の ordinary 翻訳入力の下で、`positive_tape_constructs_ordinary_literal_event399` が全元 ordinal の ordinary receipt と `SameEventRhs393` を出力前から構成する。`default_positions_from_authored_role_decl399` が明示的だった default 位置範囲の前提を実の `RoleDecl.defaultsScoped` から無条件に供給する。型推論の仕事を B4 に移さず、未読の位置を 0 や別の binder で埋めない。
5. **同じ宣言と必要な実投影だけを照合。** 検査済み registry で同じ選定 ID なら raw 宣言位置が同じ。B6 の同じ元 plan が実際に読む投影だけ（点は中心、有効な不変引数は両端）が一致すれば、`frame_event_same_rhs_from_original_reads399` は実 event とフレームが literal に同じ論理 RHS を作ることを示す。未観測の全 capture や where を同一視しない。
6. **実中心を端点から復元できないことの厳密な境界。** `native_bound_reads_do_not_identify_point_rhs399` は任意の `DeepRead` に対し、両端を保った再中心化で同じ typed head 読みを証明できる一方、同じ point 変数の RHS 名前は変わることを示す。これは単に型／モデルの値が同じことや native head の readback だけから中心名を回復できない、という実証。別の中心を一般の言語が受理するという反例ではない。spec 6.5 の「中心を明示して持つ」「根拠のある端点だけで選ぶ」「反復は選んだ後に中心の等式を足す」のまま、中心名そのものと中心の構造的な行の観測を分ける。

## 未完・質問

- **閉じた補題なし・分けた補題なし。残り 14 = 未証明 3 + 一部 11。** 固定文・一覧を変更していない。S13bbba 全称は、元の同一イベントを一般の宣言的選定から裏付ける橋、B6 が実出現ごとの kind/plan を正しく供給する義務、型付き混在 RHS の元 literal carrier がなお必要。S13bbbb、I-65 の 2/3、旧 Local/C334、停止性、新 fixture は対象外。
- [C397 の既存質問](https://github.com/momota1029/yulang/blob/d195b1cef01ecd96b25d33f35a7c258541daa8f1/notes/questions/dots-cycle-397-mixed-rhs-declared.md) は回答待ち。混在 wire は保留、再質問・新しい意味論はなし。
- 次は実の source-selected head/center 名の対応を同じ有限導出上で保持する。端点から中心値を決めず、中心行が未解決というだけで選定を保留しない。元 where 出力の字面位置同一性の追加は検証できた分のみ別記する。

## 追加ソースと独立監査

- [GeneralDeclarativeI65B6SelectedChild399.lean](https://github.com/momota1029/yulang/blob/ab8d3d0901211895680e6a9887c498f5c39e07dd/lean/Yulang/GeneralDeclarativeI65B6SelectedChild399.lean) (`42e5ac6923cf5cb0e48ab90bc59d4b927964b01e`) / [独立監査](https://github.com/momota1029/yulang/blob/ab8d3d0901211895680e6a9887c498f5c39e07dd/lean/Audit/Cycle399B6SelectedChild.lean) (`6db1b2d1638a7a10f54544260091e8e6d41b2a1b`), exact `ab8d3d0901211895680e6a9887c498f5c39e07dd`。
- [GeneralDeclarativeI65B6TapePreoutput399.lean](https://github.com/momota1029/yulang/blob/b96b32d2207ff3bf170d10c2495915006b4699fc/lean/Yulang/GeneralDeclarativeI65B6TapePreoutput399.lean) (`7cf33485fa3b85f9b305e60f4f1c4eae2450c433`) / [独立監査](https://github.com/momota1029/yulang/blob/b96b32d2207ff3bf170d10c2495915006b4699fc/lean/Audit/Cycle399B6TapePreoutput.lean) (`5ac12b5520ceeb921041301f3691bdf6e3eee6f8`), exact `b96b32d2207ff3bf170d10c2495915006b4699fc`。
- [GeneralDeclarativeI65B6AddressedLogicalLedger399.lean](https://github.com/momota1029/yulang/blob/2a9dece177f39c30936e7435c392de53ed4420b8/lean/Yulang/GeneralDeclarativeI65B6AddressedLogicalLedger399.lean) (`bafd8b610b783de039728dfa7079bb422300cf89`) / [独立監査](https://github.com/momota1029/yulang/blob/2a9dece177f39c30936e7435c392de53ed4420b8/lean/Audit/Cycle399B6AddressedLogicalLedger.lean) (`0c7a342ed4a4c7090a3a4b6ed87ecf543ce047ab`), exact `2a9dece177f39c30936e7435c392de53ed4420b8`。
- [GeneralDeclarativeI65B6OriginalOrdinaryEvent399.lean](https://github.com/momota1029/yulang/blob/85d489d032f20289514a6645c3503a8de6f6b56d/lean/Yulang/GeneralDeclarativeI65B6OriginalOrdinaryEvent399.lean) (`8299275bcfee0f6c97df4aa8b8c40eaaffbd60af`) / [独立監査](https://github.com/momota1029/yulang/blob/85d489d032f20289514a6645c3503a8de6f6b56d/lean/Audit/Cycle399B6OriginalOrdinaryEvent.lean) (`d1a53a2028c8e701490ff8c018c67970eff3511f`), exact `85d489d032f20289514a6645c3503a8de6f6b56d`。
- [GeneralDeclarativeI65B6ExactProjections399.lean](https://github.com/momota1029/yulang/blob/f133e567efd4877a1092f83ffd5550ae654f1172/lean/Yulang/GeneralDeclarativeI65B6ExactProjections399.lean) (`965c496b3cd5b01cfc5d29a3ab55eb6a641fee1e`) / [独立監査](https://github.com/momota1029/yulang/blob/f133e567efd4877a1092f83ffd5550ae654f1172/lean/Audit/Cycle399B6ExactProjections.lean) (`26c30a846734f407452af54d28c74c33d9370a7d`), exact `f133e567efd4877a1092f83ffd5550ae654f1172`。

## 検証と公開

Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) で、新規各 source を `lake env lean --trust=0 -DwarningAsError=true -o … Yulang/<module>.lean`、各 standalone audit を `lake env lean --trust=0 -DwarningAsError=true Audit/<audit>.lean` で検証した（すべて exit 0）。38 公開補助定理と recenter 定義の公理は `propext`、`Classical.choice`、`Quot.sound` の範囲。A–D は exact commit の GitHub 再取得バイトで別 directories から再ビルド済み。E は初回 strict source/監査と GitHub 本文・blob hash の完全一致まで確認。 途中でクラウド環境が unavailable になり、以降に準備した元 where 位置の追加草案は未検証のため Lean として公開しない。全リポジトリの build・verify-lean.sh・Rust は実行していない。利用量の枠は不明。

C398 基準から変更したファイルは、上記 source/独立監査と append-only barrel、設計、心拍、この報告の計 14 本。凍結した `lean/Audit.lean`・`lean/README.md` は内容を読まず blob ID のみ照合。固定文と一覧の blob も保持。work/dots-main の期待する head に対して非強制更新し、exact change set・本文・barrel 旧全文＋追記を照合する。
- 最終照合開始 `2026-11-24T19:21:37.626Z`（50 分経過）。
