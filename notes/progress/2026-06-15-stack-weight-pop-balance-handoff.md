# stack-weight push/pop balance handoff

この handoff は、`floor[Empty]` 吸収で timeout を止める方向が誤りだったことと、実際に観測された
push/pop 増殖の根を、次の調査者が追えるようにするためのもの。
Claude Code など別 agent に渡す前提で、確定事実、仮説、触る場所、避ける修正を分けて書く。

## 目的

effect subtraction の stack weight では、寿命境界として導入した push と pop が、通常は同じ `#id` で対応するはずである。
`floor[Empty]` が後続の stack / pop を吸収する正規形は元仕様にないため、停止策として使ってはいけない。

調査の目的は、「なぜ `floor[Empty]` の上に `Empty` stack 高さ違いが観測されたのか」を、lowering / constraint replay の責務に沿って説明すること。
単に再生状態を小さくして止めることではない。

## 現在の作業状態

- workspace は dirty。推論ハング修正や tracing が差分に含まれているので、全 stash して base の挙動を見ることは避ける。
- `crates/poly/src/types.rs` では、`floor` は同じ id の floor 同士だけを交差で畳む。`floor[Empty]` は後続 stack / pop を吸収しない。
- `spec/2026-05-31-effect-variable-subtractable.md` に `floor[Empty]` 吸収則は残していない。
- smoke は、今回の修正後に通っている。
  - `cargo test -q -p poly`
  - `cargo test -q -p infer`
  - `cargo build -q -p yulang`
  - `timeout 20s ./target/debug/yulang --no-cache dump-poly-std examples/10_effect_handler.yu`
  - `timeout 20s ./target/debug/yulang --no-cache dump-poly-std examples/showcase.yu`

## 確定事実

- trace では `floor[Empty]` と `push[Empty]` の高さ違いが増えて、seen / hash-cons の重複検出が外れていた。
- ある再現では問題の `#id` が `std::text::parse::run_str` 周辺の parse 注釈 stack 由来に見えた。ただし、これだけが原因とは限らない。
- `floor[Empty]` 吸収は正規形ではない。`common_stack` の見え方が似ていても、後続 stack / pop の順序情報を潰すため不正確である。
- 今回観測した増殖は、右辺 replay weight の合成順と、終端値型 bound へ保存された weight が var-cycle で太ることの組み合わせだった。
- 以前試した「catch continuation に scrutinee effect view の pop を追加する」方向は、怪しく、timeout を直さなかったため戻してある。そこを同じ形で再導入しない。

## 期待する理論モデル

`#id` は「ある effect budget をこの境界でだけ引いてよい」という寿命境界を表す。

- push は budget が見える場所に入る。
  - 注釈付き引数の effect view。
  - 注釈付き関数引数の戻り effect。
  - 未注釈 callback を呼んだときの callback return effect。
  - act method receiver effect など、明示的に stack fact を持つ場所。
- pop はその budget が外へ漏れない関数 predicate の返り側に入る。
  - defined lambda では、引数ごとの `FunctionPredicateFrame` に溜まった subtract id が、返り effect/value へ `NonSubtract` として付く。
  - 再帰関数では、body lowering 前に自己参照用 skeleton が同じ pop 付き predicate を見えている必要がある。
- `push; pop` が同じ経路で並べば、stack 正規化で相殺される。
- `catch` が row item を消費すると、残差 weight に floor が残る。これは消費済み予算が pop の後に `All` へ戻らないために必要である。
- ただし、正常な経路では、同じ周回で「push が増え続け、対応する pop が後から追いつかない」形にはなりにくい。

## 今疑っていること

最有力の疑いは、pop を追加する位置または時刻が遅すぎること。

以前の実装は、defined lambda の body を下げた後に出力型を pop で上から抑えていた。
この場合、再帰 self を body 中で参照した瞬間には、まだ pop 付きの skeleton が自己型に接続されていない可能性がある。

その対策として現在の `crates/infer/src/lowering.rs` には次が入っている。

- `fresh_defined_lambda_skeleton` で安定した skeleton slot を先に作る。
- `constrain_defined_lambda_skeleton_shape` で関数 shape を body 前に自己型へ接続する。
- `connect_defined_lambda_skeleton_predicates(..., KnownBeforeBody)` で、注釈から body 前に分かる空 predicate 層を先に接続する。
- body 中に未注釈 callback subtract が発見されたら、`refresh_active_defined_skeletons_for_frame` で active skeleton に非空 predicate を追加接続する。
- body 後に `connect_defined_lambda_skeleton_predicates(..., All)` で最終接続する。

この修正でも `floor[Empty]` の上に stack 高さ違いが出るなら、次のどれかが残っている可能性がある。

- `KnownBeforeBody` で body 前に接続すべき predicate がまだ漏れている。
- 未注釈 callback subtract の発見時 refresh が、対象 frame / 対象 skeleton layer を取り違えている。
- curry 層が複数ある関数で、push を作った引数 layer と pop を置く返り layer がずれている。
- `lambda_predicate_subtracts` の sort / dedup により、意味上必要な順序または重複が消えている。ただし別 `#id` の entry は独立なので、順序が本当に意味を持つかは要確認。
- `SignatureConstraintLowerer` と `ExprLowerer` の二つの注釈 lowering 経路で、push と pop の責務が食い違っている。
- `instantiate` が stack quantifier に入れる `pop(u32::MAX)` など、対応する push/pop を要求しない経路を、通常の寿命境界と混同している。

## 調査対象ファイル

優先順:

1. `crates/infer/src/lowering.rs`
   - `lower_lambda`
   - `fresh_defined_lambda_skeleton`
   - `constrain_defined_lambda_skeleton_shape`
   - `connect_defined_lambda_skeleton_predicates`
   - `unannotated_local_callee_return_effect`
   - `refresh_active_defined_skeletons_for_frame`
   - `lambda_predicate_subtracts`
   - `lambda_output_predicate_vars`
   - `wrap_pos_with_subtracts`
2. `crates/infer/src/annotation.rs`
   - signature annotation 由来の push/pop 生成。
   - `wrap_non_subtracts` と `EffectStack`。
3. `crates/infer/src/constraints.rs`
   - `step_subtype` の `Pos::Stack` / `Pos::NonSubtract` / `Neg::Stack`。
   - `add_effect_row_upper_bound`。
   - `intersect_row_items_with_stack`。
   - `subtract_row_items_from_stack_weight`。
   - `RowResidualKey`。
4. `crates/poly/src/types.rs`
   - `StackWeight::compose`。
   - `push_floor` / `push_stack` / `push_pops`。
   - ここは観測された重みを正規化する場所で、push/pop 生成の根本原因を直す場所ではない。
5. `crates/infer/src/instantiate.rs`
   - scheme instantiate 時の stack quantifier clone と `pop(u32::MAX)`。

## 再現と計測

基本の smoke:

```sh
cargo build -q -p yulang
printf '1 + 2\n' | timeout 20s ./target/debug/yulang dump-poly-std
printf '(each 1..3 + each 1..2).list.say\n' | timeout 20s ./target/debug/yulang dump-poly-std
```

ファイル単位 timing:

```sh
printf '1 + 2\n' | YULANG_INFER_TIMING=files timeout 20s ./target/debug/yulang dump-poly-std
```

既存 trace:

```sh
printf '1 + 2\n' | env \
  YULANG_TRACE_SUBTRACT_IDS=50 \
  YULANG_TRACE_VAR_BOUNDS=123,456 \
  YULANG_TRACE_VAR_BOUND_LIMIT=20 \
  timeout 20s ./target/debug/yulang dump-poly-std
```

`YULANG_TRACE_SUBTRACT_IDS` は明示した id だけを出す。全 id を見たい場合は、調査用に `fresh_subtract_id` の trace を一時的に広げるとよい。
その変更は debug 用であり、原因修正として commit しない。

`floor[Empty]` 吸収を再導入して止める方向は採らない。
再調査する場合は、stack/floor を保持した状態で、どの replay 経路が同じ `#id` の高さを増やすかを
`timeout` 付きで見る。

## 追加するとよい一時 trace

原因を追うには、`#id` ごとに push と pop の生成源を対応づける必要がある。
次の trace があると見やすい。

- `fresh_subtract_id`: id, caller location, semantic kind。
  - semantic kind は caller だけだと分かりにくいので、可能なら呼び出し側で `annotation`, `unannotated_callback`, `act_receiver`, `signature_effect_stack` などを出す。
- `unannotated_local_callee_return_effect`: `#id`, `frame_index`, callee def, local arg def, push `Empty` の作成。
- `lambda_predicate_subtracts`: lambda scope, param index, frame subtracts, annotation subtracts, final subtract list。
- `connect_defined_lambda_skeleton_predicates`: mode, layer index, `output_effect`, `current_effect`, subtract list。
- `wrap_pos_with_subtracts`: `#id` と作った `Pos::NonSubtract`。
- `ConstraintMachine::step_subtype`: `Pos::Stack` を左 prefix へ移す瞬間、`Pos::NonSubtract` を `pop` prefix へ移す瞬間。
- `StackWeight::push_floor/push_stack/push_pops`: floor と stack/pops が順序どおり保持されているか。ここで `floor[Empty]` 吸収を足してはいけない。

## 正しい修正の形

望ましい修正は、`#id` の寿命境界が lowerer の構造と一致することを示すもの。

- 注釈から body 前に分かる push なら、body 前の recursive skeleton に対応する pop が見えている。
- body 中で初めて分かる未注釈 callback push なら、その場で active skeleton に対応する pop が追加される。
- nested lambda / curry layer / handler continuation のどれであっても、push を作った frame と pop を置く predicate layer が説明できる。
- `StackWeight` の吸収則を外しても、少なくとも小さい structural test では同じ `#id` の push/pop が期待どおり相殺される。

## 避ける修正

- `Any` を fallback として使う。
- `floor[Empty]` があるからという理由で、lowering 側の push/pop を調べずに stack を捨てる分岐を増やす。
- path / module / fixture 名の文字列比較で型を決める。
- `catch` continuation へ scrutinee effect view の pop を機械的に付け直す。
- timeout した再現だけを早期 return で握りつぶす。
- test expectation を現在の出力へ合わせて書き換える。
- `StackWeight` の normal form を増やして、pop 生成位置の不整合を見えなくする。

## spec との関係

2026-06-15 追記: この見立ては今回の再調査で否定した。
`floor[Empty] pop(p)[H...] ≡ floor[Empty]` は元の subtractable 仕様にはなく、
`floor[Empty]` が後続 stack / pop を吸収する正規形として扱うと、push/pop 対応の破れを
下流の normal form で隠してしまう。`floor` は既存 floor の交差だけを畳み、後続 weight は
保持するのが現在の修正方針。

今回の根因は `floor[Empty]` の意味論ではなく、constraint replay で右辺側 weight を合成する順序と、
子を持たない終端値型 bound に stack weight を保存し続けたことだった。
右辺側 weight は upper 側 stack wrapper を表すため、後から replay される upper bound の weight が外側に
nest し、既存 right weight の前に来る。この順序が逆だったため、有限 stack と pop が隣接できず、
`pop(max)` と `stack[Empty...]` が別々に増殖していた。
さらに `.get` のような値側制約では、`bool` などの終端型が同じ変数に上下から固定されたあとも
weighted な `bool <: α` / `α <: bool` が var-cycle に保存され、row subtraction に届かない weight だけが
replay で太り続けていた。非 effect 具象型の terminal edge は row subtraction に到達しないため、
その weight は空に畳める。effect family の terminal atom は `ModuleTypeKind::Act` 由来の path 登録で
区別し、値型側の weight だけを消す。

研究相談用の理論資料にするなら、次の二層を分けて説明する必要がある。

- stack weight 代数: `floor` は同一 id の floor 同士だけを共通部分で畳み、後続 stack/pops は順序どおり保持する。
- lowering / replay の well-bracketing 条件: 寿命境界として導入した push には、対応する predicate pop が同じ再帰 skeleton と replay 経路から観測可能でなければならない。

後者が破れているように見える場合でも、`floor[Empty]` 吸収で停止させるのは間違い。
今回のように、実際には replay の合成順や終端 bound に保存された weight が、push/pop の隣接を壊している可能性を先に見る。

## 追加したい regression

- std に依存しない、注釈付き recursive handler の小さい例。
  - `spec/2026-05-31-effect-variable-subtractable.md` の `loop/pick` 手計算に近いもの。
  - 期待型は、外側の残差から別 effect が引けないことを確認する。
- 未注釈 callback subtract を body 中で発見する recursive function。
  - 現在 `recursive_header_skeleton_keeps_late_callback_subtracts` が近いが、実際の dump 型または constraint weight で対応 pop を確認する test へ強めたい。
- curry 層が複数ある再帰関数。
  - push を作った param layer と pop を置く output layer がずれないことを確認する。
- `floor[Empty]` 吸収に頼らず、pre-normalization trace で `push; pop` が同じ周回に現れることを確認する debug test。
  - permanent test にしにくければ、trace 手順をこの handoff に残すだけでもよい。
