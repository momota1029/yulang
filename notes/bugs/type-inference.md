## 進捗メモ（2026-05-16）

**Priority #1（record_spreads visitor 漏れ）— DONE**

- `compact_pos_type`、`compact_neg_type`（best-effort: Neg は spread variant が
  無いので fields のみ Neg::Record 化、tail は drop して注記）、
  `collect_compact_type_free_vars`、`root_non_fun_parts_empty`、
  `single_compact_var`（freeze / compact_var 両方）、`compact_type_is_empty`、
  `compact_type_preserves_through`、`compact_pos_parts_with_subst`、
  `lower_levels_compact_type`、`absorb_upper_vars_from_row_lower`、
  `normalize_rewritten_compact_type_in_place`、
  `rewrite_compact_type_vars_in_place`、
  `collect_effect_atom_interval_pairs` まで通した。
- regression `freezes_pub_record_tail_spread_through_compact` を追加（`pub make_full v = { x: 1, ..v }`）。

**Priority #3（root 関数 body 構築と free-var 収集の差分）— DONE**

- `collect_compact_root_body_free_vars` を `compact_root_fun_pos_body` と
  同じ slice 取り方（arg/arg_eff は common、ret/ret_eff は merge）に揃えた。
  これで upper 側だけに出る変数が body に混ざりつつ quantified から
  漏れる経路が閉じた。
- 既存テスト全 0 failed。

**Priority #2（frozen body vs compact lower 経路の統一）— 保留**

- `propagate_upper_to_lowers` の `constrain_compact_instance_to_neg` を
  `constrain_frozen_instance_to_neg` に差し替えると、`hover_resolves_method_selection`
  の signature 表示が変わって test が落ちる。frozen body は
  `compact_root_fun_pos_body` で lower/upper を merge した形なので、
  upper info を逆向きに lower 側 chain に流すことで意図しない narrowing
  が起きる可能性があり、結局やめた。
- 正攻法はおそらく「frozen body の構築自体を lower 一本に統一して、
  signature 表示も同じ値を使う」方向か、もしくは
  `propagate_upper_to_lowers` から流すのは body ではなく
  lower の方を materialize したものに揃える方向だが、いずれも
  hover / signature display との接点を一緒に直さないと既存
  semantics を崩す。次セッションで切り出してやる方が安全。

**Priority #4（typed effect handler の型引数伝播）— 未着手**

- `typed_effect_handler_inference.yu` の症状で挙がっている、`act state 'a`
  に `[state int]` を渡しても handler 内で `'a` が int に固まらない件は
  これとは別の handler 特化経路（role / dispatch / scheme 凍結を絡む）。
  今回は触っていない。

**残っている類似バグ（destructure 側の record_spread）**

- `pub get_rest({x, ..rest}) = rest` を check すると `{x: α} -> {x: α}` に
  落ちる症状は Neg 側に spread variant が無いという architectural な
  制約に起因していて、Visitor patch だけでは届かない。Neg::RecordTailSpread /
  Neg::RecordHeadSpread を新設するか、pattern lowering で spread の demand
  を別経路に逃がすかの設計判断が要る。

---

うん、ぶっちゃけ **あると思うよ〜**。
しかも「型推論後の単一化がちょっと弱い」だけじゃなくて、**凍結した scheme と compact 化した型の表現がズレて、後段で型情報が落ちる**タイプのバグが見える。

テスト実行まではしてないから「再現ログ付きで確定」とは言わないけど、コードを読んだ限りかなり怪しい箇所が複数あるねぇ。

## 1. 既存 upper と後から来る upper で、伝播経路が違う

`constrain_instantiated_ref_instance` は、凍結 scheme を instantiate したあと、まず `compact_lower_instance` として target に保存する。その時点で target に upper が既にある場合は、`constrain_frozen_instance_to_neg` を使って **frozen body** を upper に流している。

でも、upper があとから追加された場合は、`propagate_upper_to_lowers` 経由で `constrain_compact_instance_to_neg` が呼ばれる。こっちは **`instance.scheme.compact.cty.lower`** だけを materialize して流している。

一方で frozen 側は **`instance.scheme.body`** を使う。

つまり、

* upper が先にある → frozen body で制約
* upper が後から来る → compact lower で制約

になってる。

これ、`scheme.body == compact.cty.lower を再構成したもの` が常に成り立つならセーフだけど、実際には成り立ってない。たとえば root function は `compact_root_fun_pos_body` で lower/upper の両側を見て body を作っている。

なのでここは **制約追加順に結果が依存するバグ** になりうる。
型推論系でこれはかなり危ないやつだねぇ。

## 2. `record_spreads` が compact の再構成で落ちてる

`CompactType` にはちゃんと `record_spreads` がある。

しかも `Pos::RecordTailSpread` / `Pos::RecordHeadSpread` は compact 化すると `compact_type_from_record_spread` に入る。

でも、そのあと `compact_pos_type` / `compact_neg_type` で `CompactType` を型ノードに戻すところを見ると、`records`、`variants`、`tuples`、`rows` は処理してるのに、`record_spreads` の処理が無い。

さらに `constrain/compact.rs` 側の `compact_type_is_empty` も `record_spreads` を見てない。つまり **record spread だけを持つ CompactType が empty 扱い** されうる。

これはかなり直球でバグっぽい。
repo 内にも `my { x, y, ..rest } = ...; rest` で型変数が残る既知バグメモがあって、症状としても「record spread の型情報が後段に届いてない」にかなり近い。

## 3. root function の凍結で、body に使う変数と quantify する変数がズレてる

`compact_root_fun_pos_body` は、upper fun がある場合に

* `arg_eff` は lower/upper の common
* `ret_eff` は lower と upper の merge
* `ret` も lower と upper の merge

で body を作ってる。

でも `collect_compact_root_body_free_vars` は、その root function 特例に入ったあと、

```rust
collect_compact_type_free_vars(&arg, &mut out);
collect_compact_type_free_vars(&lower_fun.arg_eff, &mut out);
collect_compact_type_free_vars(&lower_fun.ret_eff, &mut out);
collect_compact_type_free_vars(&lower_fun.ret, &mut out);
```

だけを集めてる。つまり **body 構築では upper 側の ret/ret_eff を混ぜるのに、quantify 対象には upper 側だけに出る変数を入れない** 可能性がある。

instantiate 側は `scheme.quantified` だけを fresh type var に置き換えるから、quantified から漏れた変数は古い live `TypeVar` のまま残る。

これは「凍結済み scheme のはずなのに閉じてない」系のバグになりやすい。
単一化後に「まだ `'a` が残ってる」みたいな症状の原因としてかなりありそうだよ〜。

## 4. typed effect handler も、型引数の情報が伝わってなさそう

`typed_effect_handler_inference.yu` のメモでは、`act state 'a` に対して `[state int]` を与えても handler 内で `'a` が `int` に固まらず、runtime type inference まで残る症状が書かれている。

これは凍結そのものだけじゃなく、handler / role / dispatch の特殊経路も絡んでそうだけど、見え方としては同じで、**「前段で決まってるはずの型引数が後段の単一化まで届いてない」** になってる。

## 直すなら優先順位

私ならこの順で潰すかなぁ。

1. **`record_spreads` を全 visitor に通す**
   `compact_pos_type`、`compact_neg_type`、`compact_type_is_empty`、`lower_levels_compact_type`、`collect_compact_type_free_vars`、`single_compact_var`、`root_non_fun_parts_empty` あたりを総点検。`CompactType` に variant を増やしたあと、再構成・空判定・free var 収集が全部追従してない感じがある。

2. **frozen body と compact lower の伝播経路を一本化**
   既存 upper と後発 upper で別の表現を使うのは危ない。`compact_lower_instances` に入れた instance を伝播するときも、基本は `constrain_frozen_instance_to_neg` を使う、または `scheme.body` と `compact.cty.lower` の等価性を型レベルで保証する、のどちらかが必要だと思うよ〜。

3. **root function body を作ったあと、その実体から free vars を集める**
   `collect_compact_root_body_free_vars` と `compact_root_fun_pos_body` が同じロジックを二重に持ってるのが危ない。body を先に作って `collect_pos_free_vars_in_arena` で集める形にしたほうがズレにくい。

結論としては、**「Yulang の型推論後の単一化や凍結、バグない？」への答えは “ある。特に凍結と compact 再構成の境界が怪しい”** だねぇ。
現状の症状は単一化が悪いというより、**単一化に渡される前の frozen/compact 情報が欠けたり、順序依存で別物になったりしてる** と見るのが一番しっくり来る。
