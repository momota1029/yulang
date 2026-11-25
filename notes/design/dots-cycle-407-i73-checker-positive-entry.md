# I-73: 正の checker 分岐へ再利用できる検査（設計監査のみ）

前提: `DictionarySound R₀` が integration に載った後に着手する。固定 `check` の実装や判定規則は、この文書では追加していない。

1. **state を先に固定する。** C402 `p.state.core.current.environment.source` の表だけを `Header349.checkedRegistry` に渡す。witness から別の SourceBundle は受け取らない。`Header349.registry_checked` は旧 `Coverage` も要求するため、`Problem349.covered_iff` と `Roles291.check_exact` を同じ表で使う。これは初期の狭い正分岐としてよい。declared 分散のため旧 Coverage が失敗した判定は未対応 `false`。C357 `ModeCoverage357.declaration_exact` は別の新しい `DeclarationCovered` を要求する R₀ 本体のために同じ `Environment` で使う。
2. **元の可視行を先に見る。** `State365.visible` の全 authored registry を同 role で絞ったリストを使う。witness が指定した候補だけを判定しない。変数だけ・正の可視一行・元の arity などを実構文から反映し、`VariableScope403` / `RepeatedScope403` の不足を確認する。子の where/出力型を見る前に、候補数と root raw K2 を定める。
3. **元の argument 根拠。** `SourceArgument403` の `OriginRoute` は `State365` の二経路だけ (origin slot の直結、または同じ slot / issuer の authored route が明示リストにある)。候補出力から名目形を復元しない。witness は元 origins/route 番号と `Bound349.Range` を渡せる。`Bound349.bounds_sound` は同じ current ordinary を用いる。コンストラクタ metadata は `ConstructorModes357.readUse` を同じ `Environment` に適用。root raw 不在には `Rank350` の同状態反映を使うか、その確認不能な入力を通さない。初回の正分岐を引数/where/出力が空の実際の選択に狭める場合、該当していることを既存の実 source 規則で確かめる。
4. **結果は元の report と比較。** 選択後、元 B6 atlas の実出現の型木と固定先、元 where 子順で再生。子や書込みを witness の主張から採らない。複数の形式で表現した内容を比較するだけでは、同一 Model の意味や固定 scope を得ない。後続の一般分岐には正確な data-only report encoding / receipt 比較の反映補題が別途必要。

最短の堅実な入口は C350 の raw root K2、次に C403 の実変数 zero-output leaf。既存の旧 C350 whole/recursive checker の成功を、ただの型変換で R₀ の成功にしない。