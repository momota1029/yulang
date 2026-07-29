# local mutable state の effect residual が specialize で衝突する

発見日: 2026-07-28
状態: 未修正
発見経緯: `notes/design/2026-07-28-subtype-fallthrough-closure.md`（STF-A〜I、17コミット）
の一環である `650fec0b`「parameterized effect row residual の修正」を push した直後、
CI の契約スイートで `file_mock_text_with_rollback_on_error` が回帰した。

## 症状

以前は成功していたプログラムが specialize 段階で拒否されるようになった。

```yu
use std::control::var::*

pub error edit_err:
    abort

my text_with_mock(backing, f) = {
    my $buffer = backing
    my r: std::control::var::ref _ str = ref {
        get: \() -> $buffer,
        update_effect: \() -> &buffer = ref_update::update $buffer
    }
    my result = f r
    (result, $buffer)
}

my run(backing) = {
    my $store = backing
    my wrapped = edit_err::wrap:
        my (_, next) = text_with_mock $store: \&text ->
            my before = $text
            &text = before + " dirty"
            edit_err::abort.throw
        &store = next
    (wrapped, $store)
}

run "start"
```

```console
$ yulang --std-root lib --no-cache run --print-roots <上記>
conflicting type candidates: [&buffer#5:0(std::text::str::str), std::control::flow::loop, &store#6:0(std::text::str::str)] vs [std::control::flow::loop, &store#6:0(std::text::str::str)]
```

以前（`650fec0b` の前）は `run roots [(result::err(edit_err::abort), "start")]` を返し、
`edit_err::abort` を正しく捕まえて `$store` が `"start"` のまま残っていた。

## `650fec0b` が原因ではなく、隠していたバグを露出させた

`650fec0b` は `pos_is_effect_marker_row_item`
（`crates/infer/src/constraints/machine/propagate.rs:735`）を
`args.is_empty() && effect_family_paths.contains(path)` から
`effect_family_paths.contains(path)` へ一般化した修正である。これ自体は正しい
——`std::control::var::var 't` のように引数を持つ parameterized effect family を、
引数なしの場合と同じく row-tail item として扱うべきだった。この修正がないと
`std::control::flow::sub <: EffectRow` のような正当な effect-family 使用が
誤って拒否される（`notes/design/2026-07-28-subtype-fallthrough-closure.md` の
STF-D0c として同日に修正済み）。

`650fec0b` を revert すると、その穴が再び開く。したがって revert は選択肢にない。

`650fec0b` が正しくなったことで、以前は「引数ありの parameterized effect は
naked constructor として bounds replay され、たまたま緩く扱われていた」ために
隠れていた**別のバグ**が、正しい row 分類の結果として表面化した。

## 根本原因（調査済み、未解決）

`var.run` 形の local mutable state boundary（`my $buffer = ...` のような束縛が
callback へ渡る経路）は、概念上次の関係を作るべきである。

```text
callback effect: [local-state-family; ρ]
handler result effect: [ρ]
```

つまり、handled local family（`buffer`）は callback 側にだけ現れ、handler の
結果側では閉じて（subtract されて）消えているはずである。

調査の結果:

- `var.run` の宣言型自体と `catch` の制約構築は正しく、上記の形になっている。
- しかし `text_with_mock` のような**別のローカル関数を介して** local ref が
  渡された scheme を specialize へ渡す段階で、callback effect と handler
  result effect が**同じ変数**になってしまい、local-family の subtraction
  関係が失われる。
- compact な constraint graph の時点では local family と callback の
  stack evidence は見えているが、local `ref` binding の generalize/instantiate
  を越えて handler 側の scheme と共有されない。
- つまり specialize 自体の候補比較ロジックの欠陥ではなく、**local-var lowering
  と local binding generalization の間で、effect subtraction の対応
  （どの `SubtractId` がどの binder に対応するか）が失われる transport gap**
  である。

## 試して失敗した修正の方向（2回、いずれも time-box で正しく停止）

**1回目**: 同じ `SubtractId` を local effect の push（`wrap_var_binding_run`）と
handler result の pop の両方に使う案。local `ref` scheme の
generalization/instantiation で binder が複製され、対応が崩れた。
monomorphic な use-site 化だけでは解消しなかった。

**2回目（2026-07-28、act-method boundary との比較調査後）**: act-method の
receiver boundary は `push(Set(owner))` を receiver effect へ、同じ
`SubtractId` の `pop` を `Fun.ret_eff`/`Fun.ret` へ置くことで、**関数の戻り値の
polarity boundary の内側**に push/pop の両方を収め、一つの scheme として
generalize されるので対応が保たれる、と判明。同じ機構を `wrap_var_binding_run`
へ移植しようとしたが、**具体的な不整合**に当たって断念:

- `wrap_var_binding_run` の時点では body は既に lowering 済みで、
  既存の local-family lower を持つ `body.effect` へ後から push edge を
  足そうとすると、その既存 lower が push を迂回してしまう
- 既存 body effect を強制的に push edge へ合流させると、同じ `SubtractId` に
  対して `Empty` と `Set(local-family, payload)` が直接 replay で衝突し、
  `directed_weight.rs:413` の「一つの stack id は複数の family を持てない」
  という solver の不変条件に違反した（`panic`）
- act-method では `Fun.ret_eff`/`Fun.ret` という**関数戻り値の polarity
  boundary** がこの直接合流を防いでいるが、`wrap_var_binding_run` が
  扱う `Computation` slot だけの wrapper には同じ boundary が無い

**教訓**: 「既存の動くパターンを後から移植する」だけでは足りない。push/pop の
boundary は body を lowering する**前**に確立する必要があり、かつ
`Computation` slot 用に act-method の `Fun` polarity boundary に相当する
何かを新設するか、body lowering の順序自体を変える設計判断が要る。
これは実装の粘りでは埋まらない、**設計レベルの決定が要る箇所**と判断し、
2回目もここで停止した。

## 設計文書を起こして3回目・4回目の停止（2026-07-28深夜〜2026-07-29）

ユーザ承認を得て `notes/design/2026-07-28-local-var-effect-boundary-fix.md` を
起案・承認・着手した。LVB-A（characterization のみ、production 未変更）で
2回さらに停止した。

**3回目（設計初版の LVB-A 実装）**: 設計文書初版は「同じ `SubtractId` が
push/pop の両方を持てば、一つの `Fun` の中で generalize/instantiate を
越えて stack binder として生存する」と説明していたが、これは**誤り**だった。
act-method の実コードを直接 trace したところ、生の `SubtractId` は
generalization 後に **一切残っていない**（`stack_quantifiers: []` が
act-method の正常形）。実際に起きているのは:

- body が receiver を実際に使うことで、`receiver_effect` という**同じ通常の
  型変数**が argument 側から return 側へ流れる
- compact が `push.union(pop)` を合成する際、同じ chain 上で
  push と pop が**相殺**される（`StackWeight::push_pops`）
- 残るのは stack binder ではなく、argument effect と return effect を結ぶ
  **通常の type variable 対応**

つまり「同じ `Fun` に push/pop を置けば binder が生存する」という初版の
因果関係そのものが取り違いだった。設計文書を訂正（`19a014b6`）し、
承認状態を「未承認・ユーザレビュー待ち（改訂あり）」へ戻した。

**4回目（訂正後の LVB-A 再実装）**: 訂正された不変条件——
「push/pop は相殺されるが、`[local-family(payload); ρ] -> [ρ]` という
残余の対応は残る」——を狙って、`get`/`update_effect` の実使用を忠実に
再現した witness を組んだ。push/pop の相殺自体は成功した
（`stack_quantifiers: []` を確認）。しかし**最終 scheme から
local-family の情報自体が消えていた**:

```text
std::control::var::ref 'a 'b -> ['a] ()
```

argument と return は通常変数 `'a` を共有していたが、狙っていた
`local-family(payload)` という row item の痕跡が最終 scheme のどこにも
残っていなかった。「family は閉じるが `ρ` は共有する」という訂正後の
target invariant すら、忠実な reference use だけでは成立しなかった。

control（reference を使わない独立 fresh construction）は正しく
correspondence を示さなかった——witness 自体は歯が立っている。
問題は「local-family が丸ごと消える」という、さらに一段深い場所にある。

**教訓**: act-method の receiver は単純な `Set(owner)`（引数なし）だが、
local-var の family は payload 付きの parameterized family
（`Set(local-family, [payload])`）である。今日の `650fec0b` も
「引数なしの effect と引数ありの effect で挙動が違う」という同じ形の
非対称性が原因だった。この4回目の停止は、**parameterized family が
compaction を通るときに、単純な family とは違う経路で情報を失っている**
可能性を示唆している。次に調べるべきはこの非対称性そのもの。

## 5回目: read-only investigation で作業仮説を反証（2026-07-29、Sol xhigh）

4回目が立てた「payload 付き parameterized family は `args.is_empty()` の
非対称性で compaction 中に消える（`650fec0b` と同じ形の穴）」という作業仮説を、
Codex MCP (`gpt-5.6-sol`, xhigh, read-only) による単独調査で検証した。
**結果: 反証された。** 消失点は `pos_is_effect_marker_row_item` でも
`args.is_empty()` 分岐でもなかった。

判明した実際のメカニズム:

1. `pos_is_effect_marker_row_item`
   （`crates/infer/src/constraints/machine/propagate.rs:836`）は空/非空の
   引数リストを完全に同一に扱う。消失点ではない。
2. payload は row tail を消費・unify しない。row item の payload と
   row-tail transport は別々の制約辺として構築される
   （`enqueue_derived_row_item_neu_args` / `enqueue_derived_upper_tail_to_lower_row_tail`,
   同ファイル 955行目・1044行目付近）。
3. **独立した具体的 row item として存在する** parameterized family は
   compaction を問題なく生き残る（`compact_pos_row`、
   `merge_row_items_with_sink` が path・payload とも保持する）。
4. 実際に消しているのは **push/pop 相殺**
   （`StackWeight::push_pops`、`crates/poly/src/types.rs:541`）。ここは
   `Subtractability::Set(path, args)` を path・payload ごと丸ごと消す。
   `args` が空かどうかは一切見ていない。`merge_same_id_family`
   （同一 ID の push が同じ family かを確認するだけ）は無関係。
5. local ref の effect は `std::control::var::ref` の
   **invariant な引数の中**にいるため、正の `Pos::Stack` 収集経路は
   push を具体的な row prefix として表面化させず、`CompactVar` の重みへ
   畳み込む（`compact_neu_id`）。具体的な stack prefix を作るのは
   negative 側の `compact_neg_stack_effect`
   （`crates/infer/src/compact/collect/type_nodes.rs:543`）だけ。
6. stack liveness は `Fun.arg` を **反変的に**辿る
   （`crates/infer/src/generalize/core/stack_ids.rs:95`）。ref とその
   invariant effect 引数はこの負の位置の下にあるため covariant に
   生きている扱いにならず、`cleanup_stack_weights_in_root_and_roles` /
   `prune_dead_subtract_weights_in_type` で完全に刈られる。
7. act-method の `Set(owner)` も **全く同じ機構で完全に消える**。
   act-method が正しく見えていたのは family 情報が残っているからではなく、
   body が実際に receiver を使うことで生まれる**普通の型変数の対応**
   （`receiver_effect`）が別途残っているから。今回の witness の
   `ref 'a 'b -> ['a] ()` にも同じ対応（`'a` の共有）は正しく残っていた
   ——4回目が「消えた」と報告した `local-family(payload)` という
   追加の具体的 row item は、**push-only なスコープ機構では push/pop
   相殺前に一度もその形で存在しない**、という構造上の帰結だった。

**訂正された理解**: 区別すべき軸は「引数あり/なし」ではなく、
「**独立した具体的 row item として存在するか、stack evidence（push/pop の
中）だけに埋め込まれているか**」。設計文書が目標にしている
`[local-family(payload); ρ] -> [ρ]` という追加の具体的 row item は、
現在の push-only スコープ機構のままでは原理的に届かない。

## v3 改訂と LVB-A の成功（2026-07-29）

5回目の投資調査を受け、設計文書を v2 から v3 へ改訂した
（`notes/design/2026-07-28-local-var-effect-boundary-fix.md`、`0f015c82`）。
target を ref の invariant effect argument から、compiler-private な
callback-form helper の **negative side `ret_eff`** へ移す
（`(ref [F(P)] P -> [F(P); ρ] R) -> [ρ] R` という helper scheme）。

LVB-A（characterization のみ、production 未変更、`35a53830`）はこの新しい
target invariant を **isolated witness で構造的に証明できた**: payload 付き
family `F(P)` が callback の negative `ret_eff` から独立した concrete row
prefix として materialize され、helper result 側と同じ `TypeVar` の `ρ` を
共有する。引数なし family の control、旧 push-only carrier の negative
control も含め4件のテストが通った。5回連続の停止の後、初めて狙った
correspondence が実機で成立した瞬間だった。

## 6回目: LVB-B production wiring で新しい stop condition（2026-07-29）

LVB-A 成立を受け、production wiring（LVB-B）に着手したが、最初の call site
（ordinary block `my $x = ...`）の段階で `notes/design/2026-07-28-local-var-effect-boundary-fix.md`
§7.1 の stop condition 6（「同じ ID に `Empty` と `Set(F, [P])` が現れる」）に
到達し、`directed_weight.rs:413` の one-ID-one-family invariant 違反で panic した。
workaround は試さず、該当 slice を完全に rollback（commit なし、working tree
clean を確認済み）。

**原因**: LVB-A の isolated witness は、helper の function scheme（callback
の明示的 effect contract `F(P)` on `ret_eff`）だけを手で組んでいた。しかし
実際の production body lowering では、helper 自身の実装
`with_ref init callback = run init (callback var_ref())` の中に、
**既存の `run` 自体が local-family に対して持つ独自の push/pop 機構**が
別途存在する。isolated witness にはこの (2) が無かったため見えなかったが、
実機では次の**2つの独立した subtraction の主張**が同じ `SubtractId` に
競合する:

1. callback 自身の明示的 effect contract（LVB-A が証明した、`ret_eff` への
   `F(P)` の push/pop）
2. helper 本体の既存 `run` が local-family に対してすでに持つ、独自の
   push/pop

**教訓**: v3 の §4.1 helper contract は「callback の effect contract」と
「helper 内の既存 `run` の handler 機構」を、別々の subtraction 源として
併存させられる、という前提を検証していなかった。isolated witness は
mechanism の**片方**しか証明していなかった。

## v4 改訂と LVB-A2 の成功（2026-07-29）

6回目を受け、設計文書を v3 から v4 へ改訂した
（`notes/design/2026-07-28-local-var-effect-boundary-fix.md`、`cf82dbc0`）。
helper の callback `ret_eff` へ explicit な family contract を手置きするのを
やめ、既存の `run` definition を通常どおり resolve/instantiate し、
`run init (callback var_ref())` の application constraint だけで
`[F(P); ρ] -> [ρ]` を導く single-source 方式へ変更した。

LVB-A2（characterization、`4eb5ad49`）はこの v4 の core hypothesis を
isolated witness で証明した: 実際の yulang source を `parse` /
`lower_module_map` / `lower_binding_bodies` で end-to-end lowering し、
`run`/`var_ref` を直接呼ぶ `my h(init, callback) = my $x = init; callback &x`
という関数の中で、callback の `ret_eff` が bare fresh 変数のまま、
explicit push も generic unannotated-call の `Empty` pair も入らず、
`run` の resolve+application だけで `[F(P); ρ]` / `[ρ]` の対応が成立する
ことを確認した。negative control で v3/LVB-B の衝突も意図的に再現し、
今回の成功が偶然でないことも確認済み。

## 7回目: LVB-B 二度目の挑戦、semantic stop condition ではなく IR 形状の不一致（2026-07-29）

LVB-A2 成立を受け production wiring（LVB-B、v4 版）に着手したが、
slice (a)（ordinary block）の試作段階で **§7.1 の15個の semantic stop
condition のどれにも当たらないまま**、別の壁で停止した。

**原因**: LVB-A2 の witness は「`run`/`var_ref` を直接呼ぶ普通の関数」
という形（`h` 自体が `my $x = init; callback &x` を直接書いている）を
証明した。しかし v4 の実際の production 設計（§4.1）は、
`run init (callback var_ref())` を**別の private helper 定義の内部**に
封じ込め、call site 側はその helper を resolve/apply するだけ、という
もう一段の間接層を持つ。

LVB-A2 が固定したテストの IR 形状（`Let` block + 直接 resolved `run`）と、
v4 の finish lifecycle が実際に作ろうとする形（helper 適用へ置換、
`run` は helper 定義の内側へ移動）が両立しなかった。Codex は LVB-A2 の
assertion を弱めることも、旧経路との併存で誤魔化すことも行わず、
LVB-B の全差分を rollback した（commit なし、working tree clean 確認済み）。

**教訓**: 「resolve+apply が single-source になる」ことは証明済みだが、
「その resolve+apply を、もう一段 private helper 定義でラップしても
同じ性質が保たれるか」はまだ証明されていない。この間接層自体が
LVB-A2 の isolated witness には存在しなかった。

## 次に調べるべきこと

- **新しい characterization スライスが要る（LVB-A3 相当）**: `run init
  (callback var_ref())` を、call site が直接書くのではなく、独立に
  resolve/instantiate される **private helper definition の内部**へ
  封じ込めた形で、LVB-A2 と同じ single-source 性質（`stack_quantifiers`
  空、explicit push 不在、`ρ` の共有）が保たれることを証明する。
  `notes/design/2026-07-28-local-var-effect-boundary-fix.md` §6 へ
  この slice を明示的に追加してから着手する。
- LVB-A2 の characterization 自体は生きている（direct-call の
  isolated mechanism としては正しく証明済み）。反証されたのは
  「その mechanism を、production が要る helper-indirection の形へ
  そのまま転用できるか」という、より広い前提。
- push/pop boundary を **body lowering より前**に確立する、という設計の
  骨格自体はまだ反証されていない。
- generalization 全体を変える修正は影響範囲が広いため避ける。

## 現状の扱い

`tests/yulang/cases.toml` の `file_mock_text_with_rollback_on_error` は、
`STF-A` が確認済みバグへ最初に採った方式（known-gap witness、現在の
誤った挙動を pin して将来の修正時に反転する）と同じ形で、現在の
`conflicting type candidates` エラーを固定してある。CI を通すための
一時的な措置であり、修正を諦めたわけではない。

## 関連

- `notes/design/2026-07-28-subtype-fallthrough-closure.md`（`650fec0b` の由来）
- `crates/infer/src/lowering/expr/block_local.rs`（`wrap_var_binding_run`、
  `local_var_effect_value`）
- `crates/specialize/src/specialize2/type_resolver.rs:441`（`ConflictingTypeCandidates`
  を発生させている箇所）
