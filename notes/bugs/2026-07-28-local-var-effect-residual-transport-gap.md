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

## LVB-A3 の成功（2026-07-29）

7回目の gap を受け、`notes/design/2026-07-28-local-var-effect-boundary-fix.md`
§6 へ LVB-A3 を追加し、production gate を LVB-A2 から LVB-A3 へ置き換えた
（`5eff6fe5`）。helper を独立した definition として resolve/instantiate し、
call site 側は inline せずその definition を apply するだけ、という
production の実形状で single-source 性質を証明。2つの別 call site が
同じ resolved helper definition を apply する control も含めて成立した。

## 8回目: LVB-B 三度目の挑戦、witness 自身の自己参照（2026-07-29）

LVB-A3 成立を受け production wiring（LVB-B、三度目）に着手したが、
slice (a) の試作段階で **§7.1 の15個の semantic stop condition のどれにも
当たらず、IR 形状の不一致でもない、第三の種類の壁**で停止した。

**原因**: LVB-A3 の witness は、helper 定義の body を書くために `my $x`
sugar を含む yulang source を使っていた。LVB-A3 を書いた時点では `my $x`
はまだ旧経路で lowering されていたため、これは単なる記述手段の一つに
過ぎなかった。しかし LVB-B が実際に `my $x` を新しい helper 経由へ
migrate すると、**LVB-A3 の witness 自身が使っている `my $x` も新経路で
解決される**ことになり、helper の定義自体が「もう一つの `with_ref` を
再帰的に呼ぶ」形になってしまう。LVB-A3 が固定した「flat な
`run init (callback var_ref())` そのもの」という前提が、migration 完了後には
もう成立しない——**witness が自分自身の前提を破壊する自己参照**。

Codex は該当 slice の特殊ケース化や witness の書き換えでごまかさず、
全差分を rollback した（commit なし、working tree clean 確認済み）。

**教訓**: `var_ref` と `run` 自身の定義が `my $x` を一切使わず、直接
`get`/`update_effect` のクロージャで構築されているのと同じ理由で、
production の **helper 定義自体も、一般的な `my $x` local-var lowering
経路を経由せず、`var_ref`/`run` と同じより低いレベルで構築する必要がある**。
これは type-soundness の問題ではなく、bootstrap 順序の設計要件。

## LVB-A3 witness の訂正（2026-07-29）

8回目を受け、LVB-A3 の witness を `my $x` sugar に依存しない形へ書き直した
（`031a06e8`）。helper body を `var_ref`/`run` 自身と同じ primitive 層
（`CopiedSourceInternal` member の直接構築）で組み、single-source
correspondence が訂正後も成立することを再確認した。副産物として、
LVB-A2 の `h` witness にも同種の潜在リスク（`h` 自身が `my $x` を使って
おり、migration 後に意味が変わりうる）があると判明したが、LVB-A2 はもう
production gate ではないため、今回はブロッカーにしなかった。

## 9回目: LVB-B 四度目の挑戦、unit test は通るが CLI end-to-end で
stop condition 1（2026-07-29）

訂正済み LVB-A3 を根拠に production wiring（LVB-B、四度目）に着手。
今回は初めて `infer` crate の unit test が全部通った（999/999、
LVB-A/A2/A3 含む）。ordinary block（slice a）の実装、regression test、
CPROV-A targeted test まで全部 pass。

しかし bug note の最小 repro を実際の CLI（`run`→specialize の完全な
pipeline）で流すと、`file_mock_text_with_rollback_on_error` と同種の
conflict が再発した:

```console
conflicting type candidates: [&store#6:0(std::text::str::str)] vs []
```

元の症状（`[&buffer...; std::control::flow::loop; &store...]` vs
`[std::control::flow::loop; &store...]`）とは candidate の中身が違う
——`&buffer` 側が消えて `&store` だけになっている。完全に同じ失敗では
なく、構造が変わった形跡はあるが、本質的にはまだ conflict。

これは §7.1 の stop condition 1（「real `run` scheme の instantiate+
application だけでは、payload-bearing `F(P)` が callback parameter の
negative `ret_eff` へ independent concrete row prefix として届かない」）
に該当すると Codex は判断し、workaround・solver 緩和を試さず LVB-B
全体を rollback した（commit なし、working tree clean 確認済み）。

**教訓**: isolated witness（LVB-A3）は unit test レベルの
lowering/generalize/instantiate では single-source correspondence を
証明できたが、**production の実際の registration/generalization
lifecycle**（synthetic act copy の module 境界を越えた登録、
specialization の cache 境界等）には、まだ witness が捉えていない
差分がある。この差は `infer` crate の unit test では見えず、CLI の
full specialization を通して初めて表面化した。

## 10回目: unit-vs-CLI 乖離の read-only investigation（2026-07-29、Sol xhigh）

9回目を受け、rollback 済みだが `target/debug/yulang` に残っていた LVB-B
四度目の binary を `YULANG_TRACE_DEFS` / `YULANG_TRACE_SCHEME_DEFS` で
trace し、実際の production scheme を直接観察した。

**判明したこと**:

1. helper（`with_ref`）自身の producer-side scheme は v4 §4.1 通り正しい
   形だった（`buffer`/`store` 両方）。
2. しかし **enclosing source `run` の finalized scheme には `&buffer`、
   `&store` が両方とも残っていた**——helper 自体は正しくても、それを
   concrete callback へ apply した結果が enclosing 関数の scheme から
   family を落とせていない。
3. specialize は、この時点ですでに壊れている infer 出力を fresh
   instantiate して再推論しているだけで、conflict の原因ではなく
   顕在化させているだけ（`type_resolver.rs:441`）。
4. cache/re-instantiation の問題ではない（`--no-cache` で persistent
   cache を排除済み、specialize 内の instance cache・candidate cache も
   別 scheme を作らないことを確認）。
5. `&buffer` → `&store` の shift は「一部だけ新経路」の混在の証拠では
   ない。両 helper とも正しく形成されていた。resolver が最初の conflict
   で止まるため、`&store` が先に出ただけで `&buffer` 側が本当に解決した
   かは確認できていない。

**教訓**: LVB-A2/A3 が証明したのは「generic な callback parameter を
helper へ forward できるか」まで。**concrete な callback lambda を
helper へ実際に apply したとき、enclosing 関数自身の finalized scheme
から local family が正しく消えるか**は一度も characterize されていな
かった。v4 の core mechanism（helper 自体の scheme）は反証されていない
——production 十分条件がまだ一段足りなかった。

## LVB-A4 の成功（2026-07-29）

10回目を受け、`notes/design/2026-07-28-local-var-effect-boundary-fix.md`
§6 へ LVB-A4 を追加した（`03574c1c`）。concrete な callback lambda を
helper へ実際に apply し、その application を含む enclosing 関数自身を
generalize したとき、finalized scheme から local family が正しく落ちる
ことを証明。single-boundary と、実際のバグ構造そのもの（`$store` →
`text_with_mock` → `$buffer`）を模した nested two-boundary variant の
両方が成立した。

## 11回目: LVB-B 五度目の挑戦、CLI は成功するが scheme が契約に違反
（2026-07-29）

LVB-A4 成立を受け production wiring（LVB-B、五度目）に着手。今回は
初めて **CLI end-to-end の実行結果が正しかった**:

```console
run roots [(result::err(edit_err::abort), "start")]
```

しかし、LVB-A4 が固定した契約（concrete callback application 後、
enclosing 関数の finalized scheme から local family が消える）を
実際の production scheme で確認したところ、まだ残っていた:

```text
["&buffer#5:0" ..., "&store#6:0" ..., std::control::flow::loop]
```

Codex は「実行結果が正しいから良い」とはせず、証明済みの契約と食い違う
ことを理由に、workaround を入れず LVB-B 全体を rollback した（commit
なし、working tree clean 確認済み）。

**この結果の意味**: 実行結果がたまたま正しくても、scheme に family の
残留物があるということは、型レベルでは「実際には discharge されていない
のに、たまたま今回の repro では表に出なかった」状態である可能性がある。
これは soundness の観点では受け入れられない——別の repro や別の
call site の組み合わせで、残留した family が今度こそ実際に conflict を
起こす、あるいは誤って許可されるべきでない状況を許してしまう危険がある。
「一つの CLI 出力が正しい」ことは、この bug の completion contract
（§8）が求める水準ではない。

## 12回目: read-only investigation、SCC/cache を容疑から除外し3択へ
（2026-07-29、Sol xhigh）

11回目を受け、read-only investigation を実施。reflog / stash /
`git fsck` を確認したが attempt 5 の diff は残っていなかった
（今回は binary も clean HEAD から再 build 済みで、stale binary trace の
手も使えなかった）。

代わりに現行コードの読み込みだけで、SCC-based generalize による
row の merge/widen 仮説と、stale cache 仮説を**根拠付きで否定**した:

- SCC は component 内でも root ごとに個別 generalize/finalize/store
  している（`instantiate.rs:19-82`）。merge は実際に cycle が閉じた
  場合だけ（`scc.rs:267`）。
- generalize の compact cache は `(root, constraint epoch)` で照合し、
  final scheme は上書き（merge ではない）（`generalize.rs:579,955`）。
- specialize の instance cache も `(DefId, runtime signature)` 単位で
  別 scheme を作らない。

残った容疑は3択:

1. helper application の結果（二段目 application の result effect）
   自体に family が残っている（callback/helper wiring 自体の問題）
2. helper application result には family がないが、attempt 5 の
   custom finish が **旧 body `Computation` の effect を enclosing
   effect へ直接残してしまった**（新旧の再接続ミス）
3. callback value 自体の evaluation effect を**通常の lambda
   構築の不変条件どおり exact pure にできていなかった**
   （`lambda.rs:954-975` の invariant からの逸脱）

`finalize.rs` は runtime 到達性を見ずに compact root を構造的に freeze
するだけなので、「runtime では発生しなかった」という理由だけでは
family は消えない——static scheme が over-approximate（実際より広い）
になっていて、たまたま今回の repro の runtime path では問題にならな
かっただけ、という説明が最有力。

## 13回目: LVB-B 六度目の挑戦、5-slot 計装で仮説1を確定（2026-07-29）

12回目で絞った3択を、production の実際の `my $x` prepare/finish 経路へ
5-slot 計装を入れて検証した。今回は rollback する前に診断値を記録する
よう明示的に指示し、実際に記録できた。

**観測値**（`&x` 一本の local-var boundary、production primitive-layer
construction）:

- (a) callback body effect: `TypeVar(195)`、compact row
  `["&x#18:0"(P), std::control::var::observe(P)]` — family **あり**
- (b) callback value の evaluation effect: exact pure（non-bottom lower
  なし、closed empty-row upper あり）— 正常
- (c) callback `Fun.ret_eff`: `Pos::Var(TypeVar(195))`、(a) をそのまま
  保持 — 正常
- helper producer scheme: `'a -> (ref '["&x#18:0" 'a] 'a ->
  ["&x#18:0" 'a; 'b] 'c) -> ['b] 'c` — LVB-A3 の target structure と
  **一致**（helper 自体は正しい）
- (d) helper application（二段目）の result effect: compact row
  `["&x#18:0"(P), observe(P)]` — family **残留**
- (e) enclosing finalized scheme: `('a & 'b) -> ["&x#18:0"('a & 'b),
  std::control::var::observe('b | 'a)] 'b | 'a` — family **残留**

family presence: `(a)=true, (d)=true, (e)=true`。

**結論**: **仮説1が確定**。helper 自体の producer scheme は
（LVB-A3 が証明した通り）正しいのに、**helper を実際に concrete
callback へ apply した二段目 application の結果自体**に、すでに
family が残っている。仮説2（finish の再接続漏れ）は divergence が
finish 後ではなく application の時点で既に存在するため refuted。
仮説3（callback value の非 pure 化）は slot (b) が正常だったため
refuted。

**新しく判明した本質的な違い**: LVB-A3/A4 の witness は、helper 自身の
body 構築だけを primitive layer（`my $x` 非依存）にしていたが、
**helper を呼び出す application 自体は parsed yulang source**
（`h(init, callback) = ...` のような、通常の parser 経由の application
lowering）を使っていた。一方、production の `wrap_var_binding_run` の
finish は、この二段 application を **プログラム的に直接構築**
している（parsed source を経由しない、Rust レベルでの AST/IR node
構築）。この「parsed source 経由の application」と「programmatic に
直接構築した application」の違いこそが、LVB-A3/A4 が証明した性質が
production では成立しない理由である可能性が高い——通常の application
lowering（`tail.rs` 等）が持つ、まだ特定できていない何らかの副次的な
配線を、直接構築が再現できていない。

## 14回目: 「parsed source 差」仮説の反証と正しい construction pattern の
特定（2026-07-29、Sol xhigh）

13回目末尾の推測——「parsed source 経由の application と、production の
直接構築 application で配線が違う」——を read-only investigation で
検証したところ、**この推測自体が誤りだった**。

- `make_source_app`（parser 経由）と `make_internal_app`
  （programmatic）は、どちらも同じ `make_app_with_origins`
  （`tail.rs:535`）を呼んでいる。parsed source 側にしか無いのは
  source span・expected-type provenance・`ApplicationProvenance` の
  ような**診断用の付帯情報だけ**で、effect の配線そのものは完全に同一。
- しかも、**現行の（rollback 前の、まだ移行していない）
  `wrap_var_binding_run` 自体がすでに正しいパターンを使っている**:

  ```rust
  let run_with_init = self.make_internal_app(run, init);
  Ok(self.make_internal_app(run_with_init, body))
  ```

  （`block_local.rs:945-957`）——`make_internal_app` を2回、段階を
  追って chain する形で、これは今この瞬間も動いている実証済みコード。

**正しい construction pattern**（次回実装がそのまま複製すべき形）:

```text
helper = resolved-ref helper_def
step1  = make_internal_app(helper, init)
step2  = make_internal_app(step1, callback_value)
```

守るべき4つの不変条件:

- 各段が独立した fresh `result_value` / `result_effect` / `call_effect`
  を持つ
- **二段目の callee は元の helper ではなく、一段目が返した
  `Computation` そのもの**（helper の `Neg::Fun` を使い回さない）
- callback の `arg_eff` には exact-pure な callback value evaluation
  effect を使う
- callback body effect は callback value の `Fun.ret_eff` にだけ置き、
  application result へ直結したり `call_effect`/`result_effect` と
  slot を使い回したりしない

**教訓**: 13回目の推測（「parsed source にだけ秘密の配線がある」）は
反証された。attempt 6 が実際に family を残した原因は、この
`make_internal_app` を2回使う既存の正しいパターンから、**何らかの形で
逸脱していた**（元の helper の `Neg::Fun` を再利用した、fresh slot を
使い回した、prepare/finish の分割特有の TypeLevel/timing 順序の問題、
のいずれか）と考えられるが、rollback 済みで diff が残っていないため
一意には確定できなかった。

## 15回目: LVB-B 七度目の挑戦、4不変条件を満たしても漏れる（2026-07-29）

14回目が特定した「既存の証明済み pattern」（`make_internal_app` を
2回、二段目の callee は一段目の `Computation`）と4つの不変条件を
**すべて満たした状態で実装**したが、それでも family が漏れた。
今回は前回よりさらに細かく、二段の application それぞれの
value/effect を個別に記録できた。

**観測値**（helper finalized scheme は LVB-A3 の target と一致、
`'a -> (ref '["&x#19:0" 'a] 'a -> ["&x#19:0" 'a; 'b] 'c) -> ['b] 'c`）:

- (a) callback body effect: family **あり**（正常、body が実際に
  local ref を使うため）
- (b) callback value evaluation effect: family **なし**、exact pure
  （不変条件3 満たす）
- (c) callback `Fun.ret_eff`: family **あり**（不変条件4 満たす、body
  effect がそのまま乗っている）
- (d1) 一段目 application（helper に init を apply）: family **なし**
  （正しい——init 自体に local family は無い）
- (d2) 二段目 application（helper_with_init に callback を apply）
  **自体の result effect**: family **あり** ← ここで漏れている
- (e) enclosing finalized scheme: family **あり**

**この結果の意味**: 4つの不変条件（fresh slot の分離、callee chaining、
callback value の pure 化、body effect の配置）は**必要条件ではあるが
十分条件ではなかった**。callback の実際の型（`ref[...] 'a ->
["&x" 'a; observe] 'c`）を、helper が期待する callback 引数の型
（`ref[...] 'a -> ["&x" 'a; 'b] 'c`）へ apply したとき、本来なら
family 部分は「helper が処理する」契約として discharge され、二段目の
application 自体の result effect には `'b`（residual）だけが残るはず
だった。しかし production では、この discharge が起きず、二段目の
result effect に family がそのまま残る。

LVB-A3/A4 の witness（parsed source 経由で同じ apply を行った）では
この discharge が正しく起きていた。14回目で `make_source_app` と
`make_internal_app` の semantic core が同一だと確認済みなので、
**application 自体の配線の問題ではなく**、callback lambda **値**の
構築方法（parsed source の `\r -> body` 由来 vs. production の
finish が手で組む Fun 値）に、まだ特定できていない違いがある可能性が
高い。attempt 6/7 は callback value の evaluation effect（pure 化）は
確認したが、それ以外の——generalization boundary の扱い、quantifier
scoping、occurs-check 関連など——構築上の細部までは検証していない。

## 16回目: constraint edge 比較、callback/helper 機構そのものは
無罪確定（2026-07-29、Sol xhigh）

15回目を受け、parsed-source callback（動く）と hand-built `Fun` 値
callback（動かない）を、isolated な比較 harness で個々の constraint
edge レベル・TypeLevel scoping レベルで比較した
（`519fff63`、`local_var_effect_boundary_edge_comparison.rs`）。

**結果**: 両ケースで **構造差は一切見つからなかった**——canonical な
6本の edge（callback value → helper expected callback、
`Pos::Fun <: Neg::Fun` 分解、callback body effect → 期待される
`[F(P); ρ]`、concrete row match、payload invariance、residual
propagation）も、TypeLevel の割り当て順序も完全に同一。

**この結果の意味**: callback を helper へ apply する機構そのものは、
（LVB-A3/A4 に続いて）**今回も無罪だと確定した**。isolated な比較では
両ケースとも正しく discharge される。したがって attempt 7 で実際に
漏れた原因は、**この callback/helper application 機構の外側**——
production の実際の enclosing local-var binding lifecycle（
`wrap_var_binding_run`/`local_var_effect_value` 全体の文脈、synthetic
act の登録タイミング、outer generalize/SCC の frame wiring 等、
10回目で調べた module 境界周りとも関係しうる領域）にある。

## 17回目: LVB-B 八度目、16回目の比較方法自体に見落としが判明
（2026-07-29）

16回目の isolated harness を production の実際の enclosing 文脈へ
移植して同じ6 edge を比較したところ、production 側では6本中5本が
「まだ存在しない」（欠落ではなく、endpoint 自体が未確立）という
大きな divergence が見つかった。

**原因**: production の resolved helper ref は、二段目 application を
lowering する時点では **`ApplyRefResolution` を enqueue するだけ**で、
実際の `UseResolved` 接続は analysis work 処理まで**遅延**する
（`lifecycle.rs:1061`）。一方 16回目の isolated harness は、比較の
ために helper scheme を `TypeLevel::root()` で**明示的に eager
instantiate** してから application を組んでいた
（`edge_comparison.rs:93,108`）。

**これは16回目の結論自体への訂正を要する**: LVB-A3/A4 の parsed-source
witness も、実際には `lower_module_map`+`lower_binding_bodies` という
**通常の full pipeline**（つまり deferred `ApplyRefResolution`/
`UseResolved` を経由する、production と同じ遅延解決）を通っている。
つまり「parsed source（動く）」も「production hand-built（動かない）」
も、どちらも実際には deferred resolution を使っている。16回目の
isolated harness は、そのどちらとも異なる**第三の変種（eager
instantiate）**を比較していたことになる——「両ケースで edge が一致
した」という16回目の結論は、実は「parsed source（動く）」と
「production（動かない）」のどちらとも異なる基準に対する比較であり、
本当の分岐点を隠していた可能性がある。

**教訓**: eager instantiate はほぼ確実に成功する（型がすでに具体化
されているため）。真の比較対象は「deferred resolution を経た**後**、
`UseResolved` 接続が完了した時点」での6 edge でなければならない。

## 18回目: post-quiescence 比較でも callback/helper application は
潔白確定（2026-07-29）

17回目の指摘どおり、slot ID を `ApplyRefResolution` → `UseResolved` の
deferred resolution 完了後まで保持する snapshot seam を作り（
`8808ff61`）、parsed-source 側と production hand-built 側の両方を
**同じ full pipeline（`lower_module_map`+`lower_binding_bodies`）**へ
通した上で、post-quiescence の6 edge を再照合した。

**結果**: 今度こそ本当に同じ条件での比較になったが、**それでも構造差は
見つからなかった**。6 edge すべてが両ケースに存在し、どちらの
result effect からも local family への到達性はない。

**この結果の意味**: callback/helper application 機構は、(1) LVB-A3、
(2) LVB-A4、(3) 16回目の eager 比較、(4) 今回の post-quiescence deferred
比較——**4回とも独立に潔白が確定した**。この機構そのものに原因がある
可能性は、現実的にはもう排除してよい水準に達している。

真の divergence は、この二段 application の**外側**にある。疑うべき
次の軸:

- local-var binding **自身の definition 登録**が、enclosing scope の
  generalization/SCC root とどう関係しているか（10回目で「SCC は
  merge/widen しない」と確認済みだが、merge/widen 以外の順序依存が
  残っている可能性）
- 同じ enclosing scope 内の **sibling binding との相互作用**
  （実際のバグ repro は `$store` と、その中で呼ばれる
  `text_with_mock` の `$buffer` という、ネストした2つの local-var
  boundary を持つ——この「同じ関数内に複数の local-var 由来 helper
  application が存在する」状況そのものが、まだ characterize されて
  いない）

## 19回目: nested 固有の divergence を発見（2026-07-29、大きな前進）

18回目の指摘どおり、実際のバグ repro の完全な入れ子構造
（inner 関数 `text_with_mock` 相当が自身の `$buffer` boundary を持ち、
outer 関数 `run` 相当がその inner を呼ぶ callback body の中に
`$store` boundary を持つ）を hand-built helper application で
再現したところ、**単一 boundary の比較では4回とも出なかった
divergence が、nested の組み合わせで初めて現れた**
（`765d6131`、`nested_hand_built_outer_retains_family_despite_matching_edges_and_ordered_generalization`）。

**発見**:

- parsed inner・parsed outer・**hand-built inner 単体**は、いずれも
  正しく family を discharge する
- **hand-built outer だけ**、nested のときに限って、canonical
  six edges が全部存在するにもかかわらず、outer 自身の
  `$store` family が result effect と finalized scheme に残る
- 漏れるのは outer の `$store` family だけ——inner の `$buffer` family
  は outer scheme に漏れない
- SCC は inner/outer とも別々の単独 component、順序も
  `inner quantify → outer use instantiate → outer quantify` で
  merge は起きない——**SCC ordering は原因ではないと確定**

**この結果の意味**: 単一 boundary では起きず、「hand-built な outer
callback body の中で、別の（inner）関数への呼び出しがある」ときにだけ
起きる。次に疑うべきは、`wrap_var_binding_run`/`local_var_effect_value`
が実際に扱う、**nested call の引数評価 effect が outer callback body
effect と第二 application の result へどう接続されるか**という、
まだ検証していない配線。

このテストは、**元のバグの最小 isolated 再現**にもなっている——CLI
全体を経由せず、production の全体パイプラインより遥かに軽い形で、
同じ漏れを確実に再現できる。今後の investigation はこの test を
起点にできる。

## 20回目: 真因を特定——callback body 内の逐次文の effect 集約方法
（2026-07-29、決定的な前進）

19回目の nested test をさらに深掘りし、「七本目の edge」自体
（nested call の argument effect → call effect → result effect、
`propagate.rs:234` の pure passthrough + `tail.rs:615` の通常接続）は
**両ケースで存在し、正しく機能している**と確認した。問題は edge の
有無ではなく、**その edge に何が流れ込むか**だった。

**決定的な差分**（`d1365b1c`）:

- **parsed lowering**（動く）: nested call の引数には、その call が
  実際に必要とする値の effect（`r.get()` 単体の effect）**だけ**が
  流れる。callback body 内の**それより前の文の effect**は、call の
  外側に留まり、call の**後で**新しい block-aggregate effect
  （`block_local.rs:1289`）へ合流する。
- **hand-built construction**（漏れる）: 前の文の `body_value`/
  `body_effect`——**それまでの callback body 全体の、すでに集約済みの
  computation**——を丸ごと nested call の引数として渡していた。

つまり hand-built 側は、nested call の**引数そのもの**に、outer の
family を含む「それまでの callback body 全体」を混ぜ込んでしまって
いた。診断上、この結果 outer family へ到達可能な constraint 経路の
数が、parsed 側で3本、hand-built 側で9本——**3倍**に膨れ上がっていた。

この時点で「一つの statement の effect」ではなく「それまでの
callback body 全体の集約 effect」を次の nested call の引数へ
渡していた、という**construction 上の具体的な誤り**が特定された。
これは production の `wrap_var_binding_run`/callback body lowering が
逐次文をどう繋ぐか、という、次に実装すべき箇所への直接の指針になる。

**教訓**: production の callback body lowering（複数文を含む場合）は、
**各文・各 nested call の effect を個別に保ちつつ、正しい aggregation
point（parsed lowering と同じ block-aggregate 方式）で後から合流させる
**必要がある。前の文の効果を後続の call の引数へそのまま伝播させては
いけない。

## 21回目: LVB-B 九度目の挑戦、block-aggregate 修正は必要だが
まだ不十分（2026-07-29）

20回目の知見（callback body の逐次文は通常の `Expr::Block`/
`lower_block_items` の block-aggregate 経路へ正しく通す）を production
実装へ反映して九度目の LVB-B を試みたが、**それでもまだ family が
漏れた**。

**新しい観察**: 今回初めて、**単独（nested じゃない）でも複数文の
callback body**（実際の block-aggregate 経路を通したもの）を持つ
inner 関数のケースを試した。結果、inner 単独でも
`("&buffer" ('a & 'b), observe('b | 'a)) 'a` という不正な finalized
scheme になった——これまでの単一 boundary 成功例（LVB-A4 等）は
恐らく単純な（単一文の）callback body だけを使っていて、複数文の
callback body という条件自体がまだ検証されていなかった可能性がある。

**現状の理解**: helper producer scheme は今回も正しい
（`stack_quantifiers` 空、target structure と一致）。しかし正しい
block aggregate を callback `Fun.ret_eff` に載せた**後**の、helper
二段目 application で、やはり local family が discharge されない。
20回目の修正（先行文を nested call 引数へ混ぜない）は必要条件では
あったが、production landing の十分条件ではなかった。

**教訓**: これで LVB-B は9回連続で停止した。callback/helper
application 機構（4回独立検証）、4つの construction 不変条件、SCC
ordering、七本目の edge、block-aggregate による逐次文集約——すべて
個別には正しいと確認済みなのに、それらを**すべて production の
実際の enclosing 文脈で組み合わせる**と、まだ漏れが起きる。

## 22回目: 必要十分条件を特定——callback parameter への concrete ref
構造の早期接続（2026-07-29、決定的な前進）

21回目で見つかった最小失敗ケース（単一・複数文 callback body）を、
8地点で deep instrument して比較したところ、**必要十分な再現条件**が
特定できた（`23459b3b`）。

**発見**: callback body を lowering する**前**に、callback パラメータへ
**concrete な local-ref 構造**（`ref [F(P)] P`）を接続することが、
漏れの必要十分条件だった。wrapper・block-aggregate・TypeLevel を
全て同じに保ったまま、この reference 構造の接続だけを
**helper resolution まで遅延**させると、**漏れが消えた**。

8地点の比較（parsed / failing hand-built / TypeLevel を揃えた対照 /
reference 接続を遅延させた対照）:

- (a) 各文の effect、(b) block-aggregate、(c) callback `Fun.ret_eff`、
  (d) callback evaluation effect（exact pure）——**すべて4ケース共通で
  正常**
- (e) 一段目 application の result effect——**4ケース全て family なし
  （正常）**
- (f)/(g) 二段目 application の result effect（post-quiescence）——
  **parsed と「reference 接続を遅延」ケースは family なし（正常）。
  failing hand-built と「TypeLevel だけ揃えた」ケースは family
  あり（漏れ）**
- (h) enclosing scheme——同様のパターン

つまり漏れは block-aggregate の構築時ではなく、**事前に concrete 化
された local-ref parameter を持つ callback が deferred resolution
（`UseResolved`）を完了する際**に発生する。その条件下では、statement/
aggregate effect が enclosing level へ extrude し、
`propagate.rs:257` の function return-effect decomposition の後、
二段目 result へ family が残る。

**設計への直接の示唆**: v4 §4.2 の `prepare` は「callback パラメータを
concrete な `ref [F(P)] P` 型で pure な `Def::Arg` として束縛」すると
記述しているが、この記述自体が漏れの原因だった。正しくは、callback
パラメータは body lowering 中は**抽象的な placeholder**のままにして、
concrete な local-ref 構造との接続は helper resolution の時点まで
**遅延**させる必要がある。

## 23回目: v5 反映で LVB-B 十度目、単一 boundary は完全にクリーン、
nested は inner family だけ残留（2026-07-29、大きな前進）

設計 v5（`62c151a7`、prepare 時点の concrete ref 接続を遅延）を
production へ反映して LVB-B 十度目を実施した。

**前進**:

- **単一 boundary（複数文含む）は完全にクリーンになった**——finalized
  scheme が `'a -> 'a`、family 残留なし
- **実際の CLI end-to-end repro が成功した**
  （`run roots [(result::err(edit_err::abort), "start")]`）
- outer（`$store`）の family は nested のケースでも正しく消えている
  ——これまで9回連続で問題だった箇所は解消

**残る問題**: nested のケースで、今度は **inner（`$buffer`）の
family** が outer の finalized scheme に残った:

```text
('a & std::text::str::str) ->
["&buffer#5:0" std::text::str::str, std::control::flow::loop]
(std::data::result::result('b | (), 'c | edit_err), 'a)
```

inner helper scheme・outer helper scheme はどちらも LVB-A3 の target
structure と一致していて正しい。つまり helper 自体・単一 boundary の
discharge は完全に機能してるのに、**nested call から outer の
callback aggregate・第二 application result へ、inner の residual が
伝わってしまう**という、これまでとは違う経路の問題が新たに見えた。

**この結果の意味**: CLI が成功しただけでは dirty な finalized scheme
を検出できない、という22回目までの教訓が改めて有効だった証拠でもある
——今回も CLI だけ見てたら「直った」と誤認するところだった。

## 24回目: inner family 漏れの正確な機構を constraint solver 内部まで
特定（2026-07-29、最深部の発見）

23回目の続きとして、v5 修正済みの構成で inner/outer 両方を
deferred parameter binding で構築した nested test を作り、
post-quiescence で trace したところ、**constraint solver 内部の
具体的な関数まで漏れの機構が特定できた**（`c6a4d824`）。

**発見した機構**:

1. inner 関数自身の finalized scheme は正しい（LVB-A3 の target
   structure と一致）
2. 問題は、この**すでに generalize 済みの inner scheme が nested
   call site で instantiate された後**に起きる
3. **hand-built 側**: outer callback の body TypeVar（`propagate.rs:257`
   の `FunctionReturnEffect` 関係を通る時点）が、**すでに concrete な
   inner-family lower を持っている**状態で instantiated expected row
   に接続される。これが `row_effect.rs:96` の
   `add_unweighted_effect_row_upper_bound_from_existing_lowers` という
   分岐へ入り、`row_effect.rs:258` で matching handled prefix を消費、
   `row_effect.rs:287-309` で「reduced upper」（residual だけ）を
   計算して、それを callback body の TypeVar へ**直接**格納する。
   ところがこの reduced upper（residual のはずの変数）が、なぜか
   再び concrete な `[inner-family]` row を獲得してしまう
4. **parsed 側**: 同じ状況（callback body が concrete inner-family
   lower を持つ）でも、instantiated residual 変数には inner-family
   lower が付かず、正しく clean のまま call → result → aggregate →
   outer 第二 result まで伝わる

つまり両者の違いは、「callback body の effect 変数が、この
`row_effect.rs` の unweighted reduction 経路を通るときの、既存
lower の持ち方」にある。hand-built 側だけがこの reduction 経路に
入り、residual のはずの変数へ family を再付与してしまっている。

diagnostic は provenance rule を2つ記録した: `FunctionReturnEffect`
（上流の関係）と `UnweightedReduction`（実際の contamination 発生点）。

**この発見の位置づけ**: これは lowering の construction 方法の問題
というより、**constraint solver 内部（`row_effect.rs` の unweighted
reduction）が、特定の bound の持ち方の組み合わせで正しく residual を
分離できていない**、という一段深い層の問題である可能性が高い。
これが本当に solver のバグなのか、それとも lowering 側が
`row_effect.rs` の想定する前提条件（この reduction 経路に入らない
ような bound の持ち方）を満たすよう construction を変えるべきなのか
は、まだ設計判断が必要。

## 25回目: root cause 確定——solver 内の one-shot reduction が
late-arriving lower を取りこぼす（2026-07-29、Sol xhigh read-only）

`add_unweighted_effect_row_upper_bound_from_existing_lowers` の
read-only investigation により、正確な defect mechanism と
安全な修正の方向性が確定した。

**関数の役割**: `source <: [expected-items; tail]`（empty weight）を
処理する際、`source` がすでに持つ concrete lower から、期待 row の
prefix をどれだけ消費済みかを判定し、未消費分（residual）だけを
`source` の新しい upper bound として保存する。

**影響範囲**: 直接の呼び出し元は `row_effect.rs:97` 一箇所、その親
`add_effect_row_upper_bound` の呼び出し元も `propagate.rs:131`
一箇所——だが**入口自体は普遍的**で、solver が処理する**すべての**
empty-weight `Pos::Var <: Neg::Row` 制約がここを通る。local-var 専用
経路ではない。production の std ライブラリだけで54〜128回発火する、
core な hot path。

**正確な defect**: prefix の消費計算自体（走査・reduced upper 計算）
は、処理時点の lower snapshot に対しては正しい。欠陥は、
**reduced upper を保存する際、元の prefix との関係を保持しない**点。
具体的な time series（hand-built ケース）:

```text
1. TypeVar(1524) に18個の lower が既存
2. FunctionReturnEffect から 1524 <: [inner-family; 1669] が到着
3. 既存 inner-family lower が prefix を消費、remaining が empty に
4. reduced upper として 1524 <: 1669（plain Neg::Var）を保存
5. 後から PosId(2133) = [inner-family] が1524の19個目のlowerとして到着
6. 通常の lower-bound replay は保存済み plain Neg::Var(1669) しか見えず、
   original prefix と照合できないまま、そのまま 1669 の14個目の
   lower として直送される
```

つまり **residual の別名との取り違えでも、reduction が早すぎるのでも
ない**。「reduction 一発で終わらせて、それ以降に到着する family
lower をこの reduced upper と正しく再照合する仕組みがない」という、
**順序依存の solver logic gap**。parsed 側で漏れないのは、単に
family lower が reduction 発火**前**に揃っていて、one-shot 計算に
問題が出ないタイミングだったから。

既存テスト（`unweighted_row_upper_matches_each_lower_independently`
等）はこの独立照合規則を**初期 snapshot 内の lower**についてしか
固定しておらず、reduction 後に到着する late lower は一度も
検証されていない——テストの盲点でもあった。

**修正の方向**: lowering 側の回避策（呼び出しパターンを変えて
reduction 経路を避ける）は不適切——同じ row-subtyping 関係が構文の
出処によって異なる意味を持つことになる。正しい方向は **solver 側**:
reduction を一発の plain upper で潰さず、`source` ごとに永続的な
reduction state（元の items/tail、消費済み items、残り items、現在の
reduced upper record、provenance）を保持し、reduction 後に到着する
新しい lower にも同じ独立照合規則を incremental に適用する。

**blast radius**: 意味論的に変わるのは「reduction が発火した source
に、その後さらに lower が追加されるケース」だけ。初期 lower が
揃っている既存 passing test の結果は維持される見込み——修正の性質は
「漏れを塞ぐ narrowing」であって新しい許可を作るものではない。ただし
発火頻度が高いため、現在 passing している他のプログラムにも同種の
潜伏したケースがあれば、scheme・制約数・provenance census が
変わりうる。「既存 passing 出力に絶対に影響しない」とは言い切れない
——実装前に regression suite の再確認が要る。

追加すべき test（実装前に用意）:

- lower `F` → upper `[F; ρ]` → late lower `F` の順で `ρ` に `F` が
  入らないこと
- 制約の挿入順序を変えても同じ fixpoint になること
- late の unmatched `G` は正しく `ρ` へ流れること
- partial/multi-item row、payload-bearing family invariance
- alias 経由・pop-only の late lower
- reduction bound の prune/subsumption 後も state・provenance が
  stale にならないこと

## URR 着地と LVB-B 十一度目、まだ nested が直らない（2026-07-29〜30）

`notes/design/2026-07-29-unweighted-row-reduction-fix.md` の solver 修正
（v2、狭域スコープ）を実装・着地した（`82c79dd2`、`215ba17f`）。
1012 tests 全通過、独立再検証済み。ただし CLI で実際の repro を流すと
まだ直っていなかった——production の local-var lowering 自体
（`wrap_var_binding_run`）が旧経路のままで、v5 helper 機構へ一度も
migrate されていないため（LVB-B は10回とも rollback 済み）。

これを受け LVB-B 十一度目に着手したが、production wiring の前提
gate として `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
（既存の nested characterization test）を再実行したところ、**URR の
solver 修正後もまだ inner family の漏れが再現した**。single-boundary
（複数文含む）は完全解決のまま、nested のケースだけがまだ直っていない。

**新しく判明した原因**: URR の設計は「reduction-owned な reduced upper
の replay は、incremental path だけが所有する」ことを求めていた
（§5.4）。しかし実際の nested trace では、reduced upper が**既存の
canonical upper へ subsume される**状況で、その canonical upper に
`FunctionReturnEffect` 由来の**独立した derivation が同居**していた。
このとき `upper_record_requires_generic_replay`（実装名は暫定）が
「state 外の独立 derivation がある」と判定し、plain residual への
generic replay を許可してしまう。結果、正しい incremental route が
存在するのに、late matching lower が plain residual へも同時に
流れる経路が残る——URR が「二重処理しない」と定めた不変条件（§4.4）
を、この co-owned survivor という形では満たせていなかった。

URR の7つの regression test はこの「subsumption + 独立 derivation の
共存」という形を一つもカバーしていなかった——実際の nested local-var
の複雑さが、テストでは想定してなかった組み合わせを露呈させた形。

## URR v3 承認・URR-E 一度目、cross-source な漏れ経路を発見（2026-07-30）

URR v3（`d4819f04`、`904ee2cb`）を起こし、承認を得て URR-E に着手した。
§8.1 の3 regression test は先に red/green/red で確立（`0db4bf91`）。
本体実装（claim/coverage モデル）を試作したところ、**3つの v3 test は
全部 green になり、既存 URR 契約も全部通った**のに、実際の nested
local-var characterization test だけがまだ漏れを示した。

**新しく判明した経路**: 漏れは、reduction state が正しく coverage
してる canonical record（`BoundRecordId(10172)`、source
`TypeVar(1524)`）を直接 generic replay することでは**なくなった**
——そこは今回の実装で正しく抑止できていた。しかし `PosId(2133)` は
**別の source 変数（`TypeVar(1670)`）**の bound record
（`BoundRecordId(10389)`）経由で residual `TypeVar(1669)` へ届いていた。
`TypeVar(1670)` は 1524 の reduction state とは無関係な、別の
producer constraint（`ConstraintRecordId(3726)`、`6483`）から生まれた
row-derived relation を持ち、自分自身は reduction を一度も起こして
いない（matching lower が無かったか、別の経路で `NegId(2055)` という
**同じ endpoint** を共有してるだけ）。

**この結果の意味**: v3 の coverage モデルは source 単位で設計されて
いたが、実際の漏れは「同じ endpoint を共有する、別の source からの
独立した bound」という、source を跨ぐ経路で起きていた。この経路を
塞ぐには 1524 の coverage token を 1670 へ伝播させる必要があるが、
それは URR v3 §10.1(16) の stop condition（「coverage token が別
source へ伝播する」）に直接抵触する。かといって 1670 側を後着 lower
で lazy に activation する案は、v2 で明示的に deferred にした
zero/no-match lazy activation（§6.6）そのものに踏み込む。

v3 承認済みの範囲内では、この2つを両立させる linkage 規則が無い。
production コードは全て rollback 済み（commit なし、working tree
clean 確認済み）。3つの v3 test 自体は生きたまま——今回否定された
のは「source 単位の coverage だけで十分」という前提。

## cross-source 経路の正体を特定（2026-07-30、Sol xhigh read-only）

read-only investigation の結果、`TypeVar(1670)` が `TypeVar(1524)` と
`NegId(2055)` を共有するのは、**arena の偶然の interning ではなく、
本物の意味論的な型関係**だと確定した。

**判明した由来**:

1. `ConstraintRecordId(6462)` で 1524 の reduction が `NegId(2055)`
   （= `Var(TypeVar(1669))`）を materialize する
2. `ConstraintRecordId(6611)` が `1670 <: 1524` という**正当な
   subtype 関係**を成立させる——`inner_r.update` 自身の scheme
   instantiation（`DefId(13)`）が fresh 化した先頭量化変数 `'a`
   （local ref 自身の effect component）が 1670 で、`r.update` の
   結果効果 `['b, 'a]` が callback body へ入る Union decomposition/
   `FunctionReturnEffect` 経由の、正しい派生関係
3. `ConstraintRecordId(6613)` が 1670 自身へ 2055 を upper として追加
4. `ConstraintRecordId(6620)` で inner-family row が 1670 の lower に
5. `ConstraintRecordId(6647)` がその lower を 1670 の 2055 upper へ
   replay し、1669 を汚染する

**3方向の verdict**:

- **(a) endpoint 単位の coverage は不健全**——同じ 1669 を target に
  する本当に独立した direct-tail relation まで抑止し、v3 §5.8 と
  §8.1 test 2 を破る
- **(b) 1670 の生成や `1670 <: 1524` を禁止するのも誤り**——
  `r.update` の正しい型関係そのもの
- **(c) 最も根拠のある方向**: 1670 側の bound は「独立した ordinary
  upper」ではなく、**covered reduction から派生した claim
  lineage を継承すべき**もの。1524 の reduction claim が、正当な
  派生鎖（`1670 <: 1524` のような証明済み関係）を辿って 1670 側の
  bound へも伝わる必要がある。無関係な producer の claim へは伝播
  させない

つまり v3 §10.1(16) の「coverage token の cross-source 伝播を全面
禁止」という stop condition 自体が、**無関係な claim への伝播**と
**証明済み派生鎖に沿った lineage 追跡**を区別できていなかった、と
いうことになる。ここは URR v4 相当の設計改訂が必要。

## URR-F 一度目、v4 の6テストは全部 green なのにまだ nested が漏れる
（2026-07-30）

URR v4 の§8.2 の3 regression test（`051be5fc`）は正しく red/green/red
で確立できた。本体実装（claim lineage、`BinaryReplayDerivation` を
proof carrier とする root compression）を試作したところ、**対象4
テスト（v3の2件 + v4の2件）は全部 green、control 2件も green 維持**
——単体テストレベルでは v4 の設計通りに動いた。

それでも実際の nested local-var characterization test はまだ漏れを
示した。原因を trace すると、今回漏れを起こしてた未 covered な
claim（source `TypeVar(1522)`、producer `ConstraintRecordId(6472)`）
は、`StructuralDerivationRule`/`BinaryReplayDerivation` の chain を
一切持たず（`structural_derivations=[]`、`replay_derivations=[]`）、
代わりに **`RowDerivationId(196)` という別の derivation 経路**
（row-item matching 由来）だけを持っていた。

**この結果の意味**: v4 の設計は「証明済みの subtype edge
（`StructuralDerivationRule::UnionBranch`/`FunctionReturnEffect` が
運ぶ `BinaryReplayDerivation`）」を proof carrier として選んだが、
実際の production graph には、**それとは別種の伝播経路
（`RowDerivation` 経由の row-item matching）**もあり、こちらは
v4 の 3 regression test では一度も構築されてなかった。テストの
盲点——3つの unit test は「union decomposition から来るケース」
だけを構築してて、「row-item match から来るケース」を見ていなかった。

これを covered にするには、(a) `BinaryReplayDerivation` 無しでも
lineage を継承する経路を追加する（v3 §10.1(16)/(20) の趣旨に抵触
しないか要検討）、(b) initial row route 自体を binary replay 形へ
変える（承認済み §5.9 の carrier 設計を越える変更）のどちらかが要る
——今回はどちらも承認済み範囲を超えると判断し、production コードは
全て rollback した（commit なし、working tree clean 確認済み）。

## RowDerivation の正体を特定——reduction 自身の unmatched-lower
routing だった（2026-07-30、Sol xhigh read-only）

read-only investigation の結果、`RowDerivationId(196)` は「別の
claim から covered reduction へ証明済みで繋がる経路」ではなく、
**covered reduction 自身が、その場で作った副産物**だと判明した。

**判明した具体的な処理**:

1. `TypeVar(1524)` の18本の lower に対する reduction が、
   `producer ConstraintRecordId(6462)` の expected row
   `[&buffer#36:0(...); TypeVar(1669)]` を処理する
2. 実際に family item を消費した concrete lower は `PosId(1680)`。
   これを含む5本の top-level matching lower（alias closure 経由で
   同じ `PosId(1680)` へ到達するものも含む）が
   `RowDerivationId(196)` という N-ary `UnweightedReduction`
   aggregate の parents になる
3. `PosId(1725) = Var(TypeVar(1522))` は 1524 の4番目の lower だが、
   reduction 時点では `observe` family しか持たず、`&buffer` には
   マッチしなかった
4. reduction の**末尾にある matched/unmatched routing 自体**が、
   この unmatched lower を reduced upper（`NegId(2055) =
   Var(TypeVar(1669))`）へ送るために
   `enqueue_row_derived_subtype(1725, 2055, 196)` を発行する——これが
   `ConstraintRecordId(6472)` そのもの
5. 後から 1522 へ別の `&buffer` lower が2本到着したとき、この claim
   6379 が「独立した root-self な claim」として誤分類されてたせいで
   generic replay され、family が漏れた

**この結果の意味**: v3・v4 が対象にしてきた「別の claim から covered
reduction へ、証明済みの edge を辿って繋がる」という形ではなく、
**reduction 自身が最初から所有すべき、自分自身の unmatched-lower
routing の副産物**だった。つまり別 source からの cross-source
propagation を新たに設計する必要はなく、**reduction が自分の
unmatched routing で作る claim に、最初から reduction 自身を
lineage parent として明示的に taggingする**だけでよい——v4 の
lineage 機構より narrow で、原理的にはシンプルな拡張になる。

`RowDerivation` は N-ary hyperedge だが、v4 の lineage モデルと
根本的に不適合ではない。result constraint は exact
`RowDerivationId` を持ち、carrier は概念上
`(result ConstraintRecordId, RowDerivationId)` として扱える。

## URR-G 一度目、self-tagging 自体は成功したが別種の漏れ経路が残る
（2026-07-30）

URR v5（`12086949`、`b1692ffd`）承認後、URR-G に着手した。§8.3 の
preflight 2件は先に red/green で確立（`b2cc6eff`）。v3・v4・v5 の
機構をまとめて production へ試作したところ、**self-tagging 自体は
正しく機能した**——実際の nested trace で `1522 → 1669` の claim が
exact `RowDerivationId(196)` carrier・reduction root・covered=true に
なることを確認できた。18 個の unit test も全部 green になった。

それでも nested local-var characterization の isolation gate は
まだ失敗した。原因を追うと、covered な `UpperBoundAdded` replay を
正しく抑止しても、**別の経路**が残っていた:

```text
1669 <- Var(1522) <- Row([inner-family])
```

これは generic replay の抑止では触れない、**alias bound を
finalization/projection が直接辿って到達する経路**——claim/coverage/
lineage の仕組みは「generic replay を抑止する」ことは正しくできてる
のに、finalization 側がそれとは別に、covered claim が作った alias
bound を直接辿って family を拾ってしまう。

**この結果の意味**: v1〜v5 で積み重ねてきた claim/coverage/lineage
という枠組みは、「generic replay という特定のアクションキューを
抑止する」ことだけを対象にしてきた。しかし今回見えたのは、それとは
別の経路（finalization が bound を直接辿る）で漏れが起きるケースが
存在する、ということ。これは §10.1(4) 相当（「late matched lower が
current residual にも replay される」）の一種だが、self-tagging
だけでは閉じない**新しい種類の gap**。

今回も production コードは全て rollback 済み（v5 preflight test の
commit だけは残した——`.git` read-only で Codex が commit できな
かった分を Claude が代行）。

## compaction 経路の正確な特定と lowering 側代替案の反証（2026-07-30、
Sol xhigh read-only ×2）

URR-G 一度目の finalization bypass を受け、2つの read-only
investigation を行った。

**1つ目（compaction の正確な機構）**: 漏れの中心は「finalization が
直接 bounds を読む」という粗い表現より正確には、**compaction と
pre-finalization alias projection**にあると確定した。

- `TypeBounds::add_lower`（`constraints/mod.rs`）は
  `1669 <- Var(1522)` を通常の `BoundRecordState::Ordinary` lower
  として `VarBounds.lowers` へ保存する——これは union-find alias でも
  compaction-time discovery でもなく、`step_subtype` の通常の
  Var–Var 処理が作る、ごく普通の subtype bound
- `projection_lowers()`（`constraints/mod.rs:669`）は evidence lower
  と ordinary lower を無条件に全部連結するだけで、claim ID や
  coverage を一切見ない
- `compact_var_bounds`／`compact_lower_bounds`（`compact/collect/mod.rs`）
  がこの `projection_lowers()` を無条件に走査し、`Var(1522)` を
  secondary compact variable として compact graph へ引き込む
- `positive_aliases_within_scheme`（`generalize/mod.rs:543`）も同じ
  unfiltered lower graph を推移的に辿る
- 一方 `finalize_generalized_compact_root`（`generalize/finalize.rs`）
  は machine bounds を読まない——すでに出来た `CompactRoot` を凍結する
  だけで、主因ではない

つまり claim/coverage の情報を、compaction が bound を読む時点でも
参照できるようにする必要がある。「coverage の boolean を lower
endpoint へ雑にコピーする」「record 全体を隠す」という単純な案は
どちらも不適切——独立した uncovered claim が同じ endpoint に同居する
ケース（v3 test 2、v4 control）を壊す。必要なのは、compaction・
positive alias expansion・scheme provenance が**同じ semantic
projection view**を共有し、生の bounds/provenance は audit 用として
別に保持する、という設計。

**2つ目（lowering 側の代替案）**: compaction を触らずに、LVB-B の
lowering 側で alias 自体を作らせない案を検証したが、**反証された**。
漏れの原因 `TypeVar(1522)` は、正当な後続文（`inner_r.update
(\_ -> before)` / `std::control::var::observe::mark:inner_r.get()`）の
block-aggregate 効果——省くと実際の実行を取りこぼす、本物の必要な
効果。v5 が「local ref を後まで抽象のままにしておく」設計を意図的に
選んでるため、lowering の時点ではこの文が最終的に `&buffer` family を
必要とするかどうか判定できない。これを避けるには (a) v5 の
prepare/finish という中核判断を巻き戻す、(b) local-var callback body
だけ block-aggregate を特別扱いする（プロジェクトが繰り返し却下して
きた道）、(c) block aggregation 全体（あらゆる block で共有される
一般機構）を広く再設計する、のどれかが要る——どれも今回は避けるべきと
判断した。

したがって **compaction 層の claim-aware projection が本当に必要**、
という結論に戻った。ユーザ承認を得て URR v6 として進める。

## URR-H1 一度目、MCP timeout 経由での回収と census 差分での正しい停止
（2026-07-30）

URR v6 承認後、URR-H1（claim model 再構築 + inert scheme view）に着手した
Codex MCP 呼び出しが、30分応答なしでタイムアウトした。プロジェクトの
確立手順（`feedback-codex-timeout-recovery`）通り、まず working tree を
確認したところ、実装は完了していた（4ファイル、1168行、v3〜v6 の
claim/coverage/lineage/self-tagging/scheme-projectable-view を含む）。
Claude が独立に検証:

- `cargo check -p infer` は clean（新しい `scheme_projectable_lowers`
  等が未配線ゆえの dead-code warning のみ、これは意図通り）
- `constraints::tests::case_02` の50 test 全部 pass、0.00秒（ハングなし）
- diff review で `row_effect.rs`（unmatched arm だけの self-tagging）、
  `mod.rs`（`UpperReplayClaim` 等の新データ構造）が設計文書の記述と
  正確に一致

ここまでは良好だったが、five-case characterization
（`cprov_a_characterizes_constraints_replay_std_and_regressions`）が
fail した。最初の目視確認では `provenance_epoch`（internal counter）
だけが違って見えたため、それが「新しい bookkeeping による無害な増加」
かを狭く再調査させたところ、**Claude 自身の目視確認が不十分**だったと
判明——実際には5ケース中4ケースで、`provenance_epoch` 以外にも
canonical constraint 数・replay derivation 数・lower/upper replay
census が本物にズレていた（例: `ref-update-local-buffer` で
canonical/lower bound が11件減、subsumption が8件減、replay
derivation が69件減）。poly/check hash は5ケースとも不変だったが、
これは「late-lower narrowing」「追加 provenance」の二分類では説明
できない census 差分であり、v1 由来の stop condition 11 に該当すると
Codex は正しく判定し、実装全体を rollback した（commit なし、working
tree clean 確認済み）。

**この結果の意味**: 巨大な `assert_eq!` の出力を人間が目視で diff
するのは信頼できない——今回、Claude 自身が「epoch だけの違い」と
誤読しかけたところを、より丁寧な再調査が正しく訂正した。URR-H1 の
claim/lineage 機構自体は（unit test レベルでは）正しく動いてるように
見えるが、production の real std を含む compile 全体を通すと、
まだ何らかの経路で replay/bound の実際の生成数が変わる——単なる
epoch bookkeeping の増加では済まない、まだ特定できていない副作用が
残っている。

## 次に調べるべきこと

- **最優先**: `ref-update-local-buffer` 等で見えた canonical/lower
  bound・subsumption・replay derivation の減少（および
  `config-read-false-positive-repro` での duplicate lower replay の
  増加）が、具体的にどの新しいコードパスから来ているかを read-only で
  特定する。poly/check hash が不変なので**最終的な型推論結果は
  変わっていない**——内部的な reduction/replay の回数だけが変わって
  いる可能性が高いが、それでも stop condition の趣旨通り、明確に
  説明できるまで先に進まない。
- URR v6 の設計（claim-aware scheme projection）自体は反証されて
  いない——反証されたのは「今回の実装がまだ完全に副作用フリーか」
  という点。
- 単一 boundary（複数文含む）の discharge、CLI での成功は維持されて
  いる——退行はない。v1〜v5 の regression test も生きている。
- LVB-B の production wiring は、この追加修正が着地するまで再開しない。
- LVB-A2 の `h` witness の潜在リスク（`my $x` migration 後に意味が
  変わりうる）は未対応のまま残っている。
- generalization 全体を変える修正は影響範囲が広いため避ける。
  `row_effect.rs` の追加修正も同様に、regression suite を十分に整えて
  から着手する。

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

## 26回目: v3〜v5 live-wiring checkpoint と blocker 2 の扱い
（2026-07-30）

今回の作業は、最初に HEAD の
`upper_record_requires_generic_replay` が行っていた owner / derivation
判定を「legacy-pinned な real decision」と見なし、claim model はその
既存判断を観測するだけ、という枠で始めた。しかし commit 履歴と production
code / test helper を突き合わせると、この枠自体が誤りだった。

HEAD に存在した v3〜v5 は preflight test と観測 helper だけであり、
`observed_replay_lineage` が reduction state と raw bound derivation から
test 内で claim を組み立てていた。production の `TypeBounds` には
`UpperReplayClaim`、coverage root、lineage index がなく、claim-based
suppression が generic replay の可否を決めたことも一度もなかった。
実際の判断は、reduction owner と bound derivation の一致を見る従来の
heuristic のままだった。したがって必要なのは legacy decision の保存ではなく、
承認済み v3〜v5 の claim / coverage / lineage を live decision として再構築する
ことだった。

再構築では、canonical upper record ごとの claim、compressed coverage root、
live reduction state、replay / reduction-route parent を `TypeBounds` に保持した。
initial unmatched route は exact `RowDerivationId` と root claim を admission 時に
self-tagging し、binary replay は constraint / evidence のどちらを通っても
parent claim を次の upper recordへ運ぶ。generic replay の判断は
`claim_requires_generic_replay` が covered / uncovered claim を見て行い、
test helper も合成観測をやめて production claim table を直接読むようにした。
これで v3〜v5 の claim model が初めて live generic-replay decision になった。

その途中で multihop lineage の coalescing bug も見つかった。
`derived_upper_replay_claim` は child 用の
`derived_claim_by_record_and_root` だけを検索していたため、
`alpha -> beta -> gamma -> alpha` の reverse replay が root の canonical
recordへ戻ると、index に original root がないまま root の derived copy を
一件増やしていた。修正後は、target record が compressed root claim の
`current_record` と一致する場合に original root 自体へ coalesce し、それ以外の
既存 child は従来どおり `(record, root)` indexへ coalesceする。これにより
二hopは depth 2 のまま root-compressされ、reverse edgeは新しい claim を作らない。

残った
`unweighted_row_upper_initial_unmatched_route_inherits_reduction_root`
は blocker 2、すなわち**設計と test 作成時期の不一致**に分類した。これは
「v6 scopeだから理由なく deferする」という問題ではない。この test は v5
時点で作られ、まだ projection view がなかったため、「F contamination が
到達不能」という outcome を raw stored bounds の推移走査で代用している。
一方、承認済み v6 の §4.10 は raw `beta <: residual` を audit と
re-projectability のため永久に保持し、scheme projection 時だけ
`scheme_projectable_lowers` で covered claim を除外する。したがって現在の
raw traversal は設計どおり relation を見つけ、最後の assertionだけが赤になる。

ユーザ確認により、この checkpoint は test body・期待値を弱めず、`#[ignore]`
にもせず、URR checkpoint 18件中17件 green の状態で commitする。次の H1b
sliceでこの一件の reachability check を raw traversal から
`scheme_projectable_lowers` viewへ切り替える。変わるのは contamination の
観測方法だけで、「schemeへ F を混ぜない」という outcome expectation は
変えない。最終再確認は `cargo check -p infer` が成功し、
`constraints::tests::case_02` が45 pass / 1 fail / 1 known-ignore、失敗は
この一件だけだった。

## 27回目: URR-H1b inert scheme-projectable view の着地
（2026-07-30）

v6 §5.11 の `scheme_projectable_lowers` を constraint machine に追加した。
Var–Var admission で upper claim と mirror lower の canonical
`BoundRecordId` を対応づけ、lower record ごとの claim、compressed root
ごとの lower record、claim を持つ lower owner の逆引きを `TypeBounds` に
保持する。raw `BoundRecord` と既存の `projection_lowers` /
`generalized_projection_lowers` は変更していない。

view は record に claim linkage がなければ evidence / ordinary の raw 順序、
record ID、endpoint、weight をそのまま `Unclaimed` として返す。linkage が
ある場合は、query のたびに各 claim の `coverage_root` から
`live_coverage_by_root` を引き、uncovered claim が一つ以上ある record だけを
一回返す。mixed record の reason には uncovered claim だけを残す。coverage
を claim 作成時の boolean に焼き付けていないため、最後の live state を外すと
raw relation を変更せず再び projectable になる。その transition は global
constraint epoch、該当 lower owner の epoch、provenance epoch を進める。

§8.4 の H1 regression として次の4件を追加し、すべて green にした。

- `covered_unmatched_route_lower_is_raw_but_not_scheme_projectable`
- `scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record`
- `scheme_projectability_returns_after_last_live_coverage_state_leaves`
- `ordinary_scheme_projectable_lowers_are_byte_for_byte_raw_passthrough`

前 checkpoint で唯一 red だった
`unweighted_row_upper_initial_unmatched_route_inherits_reduction_root` は、
最終 reachability helper の走査元だけを raw lower bounds から
`scheme_projectable_lowers` へ切り替えた。「F contamination が residual
へ到達しない」という outcome expectation は変更していない。

この slice では compaction、positive alias expansion、scheme provenance、
real generic-replay decision の consumer を一つも view へ切り替えていない。
`cargo check -p infer` は成功し、`constraints::tests::case_02` は
50 pass / 0 fail / 1 known-ignore（51 selected）となった。指定に従い
five-case characterization は未実行であり、次の H2 slice の gate として残す。

## 28回目: URR v3〜v5 live-wiring の five-case baseline 更新
（2026-07-30）

`f73910ed` の claim-based replay suppression と `45bbf367` の inert v6 view が
載った HEAD で five-case characterization を native 実行し、全5ケースの
constraint / replay census を live-wiring 後の値へ意図的に更新した。

先に test harness 自身の replay storage proxy を修正した。従来は
accepted / semantic-duplicate の全 replay derivation が保存されると仮定して
`considered * size_of::<BinaryReplayDerivation>()` 相当を計上していたが、実際に
保存されるのは deduplication 後の derivation だけである。そこで
`(considered - deduplicated) * size_of::<BinaryReplayDerivation>()` 相当へ変更し、
trivial drop record の別単価は従来どおり分離した。
`ref-update-local-buffer` では deduplicated 5件 × 16 byte = 80 byte の減少と
storage proxy の実測差が一致した。baseline helper も
`inserted = considered - deduplicated` を表す形へ更新した。

formula 修正後の native run で最終 baseline assertion まで到達し、その実測値から
5ケースを更新した。各ケースの `poly_dump_fnv1a64` と
`check_report_fnv1a64` は既存 baseline から一件も変わらず、最終的な poly 型と
check 結果が不変であることを確認した。更新後に同じ characterization test を
再実行し、1 pass / 0 fail を確認した。

## 29回目: URR-H1 全 completion gate 通過、完全完了
（2026-07-30）

URR-H1、すなわち v3〜v5 の claim / coverage / lineage 機構を live な
generic-replay eligibility decision とし、v6 の
`scheme_projectable_lowers` view を genuinely inert な状態で追加する slice が、
次の3 commit で完全に着地した。

- `f73910ed`: v3〜v5 live-wiring checkpoint。URR 17/18 green の状態で着地し、
  multihop lineage の coalescing bug 修正も含む
- `45bbf367`: inert な v6 `scheme_projectable_lowers` view を追加。
  URR 18件 + 新規 v6 4件の 22/22 が green
- `8ea20004`: five-case characterization baseline を更新。実際の
  deduplication を反映するよう storage-proxy formula を修正し、全5ケースの
  baseline を更新

最後の characterization では、全5ケースで `poly_dump_fnv1a64` と
`check_report_fnv1a64` が作業前から **UNCHANGED** であることも確認した。
つまり内部 census は live claim machinery を反映した新 baseline になったが、
最終的な type-checking output はこの作業前と byte-identical のままである。

設計文書が H1 completion gate として要求した項目は、これですべて通過した。

- `case_02` の URR + v6 対象 test は 22/22 green
- no-claim-owner の view path は byte-for-byte の raw passthrough。
  `ordinary_scheme_projectable_lowers_are_byte_for_byte_raw_passthrough` で固定
- claim / coverage lookup は全 claim scan ではなく、requested owner の
  records に触れる claim 数に対して O(claims touching the requested owner's
  records)。`crates/infer/src/constraints/mod.rs` の code review でも、
  `FxHashSet` / `FxHashMap` による owner-local / record-local lookup、
  compressed-root reference、reverse-indexed な liveness invalidation を確認
- five-case characterization は、意図的に更新した baseline と完全一致
- full contract suite は 287/287 green。現在の system load では suite runtime が
  単一 Codex MCP call の実用的な window を超えるため、直前に direct background
  run で完走を確認した。出たのは、まだ配線していない v6 view に対する想定内の
  dead-code warning だけ

これにより **URR-H1 は fully complete** とする。次の slice は、設計文書自身の
H1 / H2 / H3 分割どおり、`scheme_projectable_lowers` を compaction **だけ**へ
配線する H2 であり、まだ着手していない。H2 はそれ単独で full 287-case
contract-suite gate を再度通す必要がある。その後、alias expansion と provenance
にも配線する H3 でも、同じ gate をもう一度通す。H2 だけで当初の motivating
nested local-var isolation test が偶然 green になっても、H3 とその gate を
省略してはならない。

今回の arc は、直前まで「URR-H1 attempt 1」の characterization divergence として
見えていた謎も解消した。最初の「real decision は legacy predicate に残し、
claim machinery は観測だけにする」という framing は、HEAD の実態と整合して
いなかった。以前の rollback 後、v3〜v5 は preflight test と観測 helper として
しか残っておらず、live decision になったことは一度もなかった。必要だったのは
legacy decision の温存ではなく、v3〜v5 を faithful かつ atomic に live-wiring
し直すことだった。今回実際に着地したのは、その正しい再構築である。

## 30回目: H2前提のscheme-projectability invalidationを両方向で閉じた
（2026-07-30）

H2でcompactionを`scheme_projectable_lowers`へ接続する前提を再監査し、
H1のinvalidation contractに二つの未配線方向が残っていることを確認した。
last live stateが外れるnon-empty→emptyは既存helperからglobal
`ConstraintEpoch`、該当owner epoch、`DependencyKey::ConstraintBounds(owner)`、
`ProvenanceEpoch`を更新していた。一方、row reduction登録時の
`live_coverage_by_root`直接insertによるempty→non-emptyと、lower recordへ
claim linkを追加してunclaimed / partly-uncovered / all-covered分類を変える経路は、
projection metadataだけを更新し、同じpublishを行っていなかった。

claim-link helperは`TypeBounds`に属し、`ConstraintMachine`のglobal epochと
mutation outboxへ直接触れない。この境界を崩さず、
`SchemeProjectionMutation::{None, ProvenanceOnly, InclusionChanged { owner }}`
を返す形へ変更した。constraint claim登録のreplay parent、reduction-route parent、
direct original claim、replay evidenceの四call siteとrow reductionのoriginal claim登録が
outcomeを受け取り、`InclusionChanged`だけを既存のscheme-projection publishへ渡す。
link追加前後のrecord inclusionを比較するため、covered-onlyへの遷移だけでなく、
covered-onlyへuncovered claimが加わって再びprojectableになる方向も同じ規則で扱う。
duplicate linkは何も更新せず、metadataだけが変わってinclusionが同じ場合は
provenanceだけを進める。

coverage livenessはinsert / removeを同じnarrow helperへ揃え、mutation前後の
root emptinessを比較する。empty / non-empty境界を跨いだときだけreverse indexから
active lower ownerを列挙してglobal / owner / dependency / provenanceをpublishし、
non-empty→non-emptyは`ProvenanceEpoch`だけを進める。これにより、H2後の
`GeneralizeCompactCache`がprojectability transition後に古い
`(root, ConstraintEpoch)` entryを再利用する穴を両方向で閉じた。

`case_02`にはempty→non-empty、covered claim linkによる
projectable→non-projectable、non-empty→non-empty provenance-onlyの三testを追加し、
既存のnon-empty→empty testもowner dependency publishまで強化した。
`cargo check -p infer`は成功し、`constraints::tests::case_02`は
53 pass / 0 fail / 1 known-ignore（54 selected）。既存期待値は変更していない。
`compact/`と`generalize/`には触れておらず、H2 consumer wiringは引き続き次sliceである。

## 31回目: H2のinert mode plumbingとlower-bound kernel分離
（2026-07-30）

H2のstep 3+4として、`CompactCollector`へcollector lifetime中不変の
`Raw` / `SchemeProjection` modeを追加した。既存の`new` / `new_recording` /
`new_recording_owner_dependencies`はrawのまま残し、scheme専用の
`new_for_scheme` / `new_recording_for_scheme`を追加した。local compact cacheの
`(var, polarity, weight)` keyは変更していない。

`compact_type_var_for_scheme`、`compact_negative_type_var_for_scheme`、
`compact_type_var_recording_merge_constraints_for_scheme`と、generalizeが使う
reachable-role collectorだけをscheme constructorへ切り替えた。generic compaction、
generic recording、owner-dependency、boundary capture、通常のrole/selection/conformance
surfaceは既存raw constructorのままである。

positive lowerの処理本体は`WeightedLowerBound` iteratorを受け取る
`compact_lower_bounds_from`へ分離し、weight合成、stack-family coexistence記録、
再帰変数の収集経路を複製せず共有した。このcheckpointでは両modeとも
`VarBounds::projection_lowers()`を渡すため、claim-aware filteringはまだ発生しない。
`scheme_projectable_lowers`は呼んでおらず、実際のiterator切り替えは次sliceへ残した。

`cargo check -p infer`は成功した。compact test suiteは新しいinert-mode同値testを含め
65 pass / 0 fail、`constraints::tests::case_02`は53 pass / 0 fail /
1 known-ignore（54 selected）。既存testの期待値は変更していない。

## 32回目: H2のscheme compactionをclaim coverageへ接続
（2026-07-30）

`CompactCollector`の`SchemeProjection` branchだけを
`ConstraintMachine::scheme_projectable_lowers(var)`へ切り替え、各entryの`bound`を
既存のlower-bound処理kernelへ一回渡すようにした。`Raw` branchは従来どおり
`VarBounds::projection_lowers()`を使う。collectorからmachine参照を先にcopyすることで、
iteratorを`Vec`へcollectせず、viewのno-claim fast pathとO(claims) contractを維持した。
negative upper collection、weight合成、stack-family coexistence、recursive detection、
`compact_pos_bound_id`、`generalize/`は変更していない。

compact固有のregressionとして、既存`case_02`のunmatched-route fixtureをtest-only helper
経由で再利用し、次の四contractを追加した。

- covered-only lowerはraw compactionではsecondary positive variableとして残り、
  scheme compactionでは除外される
- covered claimとindependent claimが同じcanonical lowerに同居するmixed recordは、
  scheme compactionへ一回だけ残る
- last live coverage stateを外す前はscheme compactionから除外され、global epochが進んだ後の
  fresh compactionでは同じraw lowerが再びprojectされる
- claimを持たないownerではraw / schemeの`CompactRoot`がnode、weight、順序を含め完全一致する

`cargo check -p infer`は成功した。compact test suiteは69 pass / 0 fail、
`constraints::tests::case_02`は53 pass / 0 fail /
1 known-ignore（54 selected）、`cargo fmt --all -- --check`も成功した。
既存testの期待値は変更していない。指定どおりfive-case characterizationと
287-case contract suiteは実行しておらず、次sliceのfinal H2 gateとして残す。

## 33回目: H2 five-case characterization gate通過
（2026-07-30）

H2のcompaction wiring後のfive-case characterization差分をrecord単位で追跡した。
`lib/std/data/list.yu`と`lib/std/text/str.yu`にある5個のstd index-implementation
definitionから、claim-covered lower recordが合計10件
`compact_type_var_recording_merge_constraints_for_scheme`で除外された。4個の
scheme compaction entry pointのうち、このfive-case差分に関与したのはこのentry
pointだけである。各recordには`UpperReplayClaimKind::Reduced`の正当なlive claim、
`ReductionRouteConstraint` lineage、non-emptyな`live_coverage_by_root`があった。

この除外により、8個のcanonical union constraintに付随していた重複
`UnionBranch` derivation 16 edgeが消えた。全5ケースでcanonical constraintは8件、
semantic duplicate resultは8件、`full_unary`と`union_intersection`は各16件減り、
upper replayはacceptedが8件増え、duplicateとprefilteredが各8件減った。これは
「replay candidateを作ってからduplicateと判定する」経路を、covered claimにより
candidate自体を正しく作らない経路へ置き換えた結果である。

`provenance_epoch`の約11.5万〜12万の増加は、H2 wiring自体ではなく、先行する
`92f990b4`がclaim-link / liveness mutationを正しくpublishするようにした結果である。
`09b8e857`のwiringは、unwiredなraw projectionなら生じる24件のcanonical /
structural insertionと、それぞれのprovenance bumpを消すため、むしろそのraw比較
よりepochを24減らしている。

HEAD `09b8e857`で実測した値へfive-case baselineを意図的に更新した。更新前の
failureで全5ケースの`poly_dump_fnv1a64`と`check_report_fnv1a64`が既存baseline
から不変であることを確認し、更新後はcharacterizationが1 pass / 0 failとなった。
compact test suiteも69 pass / 0 fail、`constraints::tests::case_02`も
53 pass / 0 fail / 1 known-ignore（54 selected）である。これによりH2の
characterization gateは通過した。287-case contract suite gateはClaudeが別途
実行中であり、この記録時点では結果未確認である。

## 34回目: URR-H2全completion gate通過、完全完了
（2026-07-30）

URR-H2、すなわち承認済み設計文書のH1 / H2 / H3分割どおり、
claim-awareな`scheme_projectable_lowers` viewをcompactionだけへ配線するsliceが、
次の4 commitと全gate通過をもって完全に着地した。

- `92f990b4`: epoch / liveness-invalidationの前提を閉じた。claim coverageが変わる
  両方向のtransitionを、以前から正しかったremoval方向だけでなくaddition方向も
  `GeneralizeCompactCache`のinvalidation機構へ正しくpublishする
- `c6770c5a`: `CompactCollector`へinertな`Raw` / `SchemeProjection` modeを追加。
  behavior-preservingなcheckpoint
- `09b8e857`: real wiring。`SchemeProjection` modeが
  `machine.scheme_projectable_lowers(var)`を使うようにし、
  `compact_type_var_for_scheme`、`compact_negative_type_var_for_scheme`、
  `compact_type_var_recording_merge_constraints_for_scheme`、generalizationの
  reachable-role collectorという4個のscheme-compaction entry pointだけへ配線。
  negative-upper collection、generic compaction、role-solving compactionはscopeどおり
  すべてrawのまま
- `25f4ec5c`: record-levelの検証済みattributionを根拠にfive-case
  characterization baselineを更新

characterization gateは、通常より強いrecord単位の根拠を伴って通過した。
全5ケースで同一だった差分、すなわち`canonical_subtype_constraints` -8、
structuralの`full_unary` / `union_intersection`各-16、upper replayの
accepted / duplicate / prefilteredがそれぞれ+8 / -8 / -8、
`provenance_epoch`約+11.5万〜12万、poly / check hash **UNCHANGED**を、
`lib/std/data/list.yu`と`lib/std/text/str.yu`の5個のstd index-implementation
definitionにある、exactly 10個のclaim-covered lower recordまで追跡した。

10 recordはすべて
`compact_type_var_recording_merge_constraints_for_scheme`だけで除外され、このケースでは
他の3 entry pointによる除外は0件だった。各recordを個別に確認し、
`UpperReplayClaimKind::Reduced`の正当なlive claim、
`ReductionRouteConstraint` lineage、non-emptyな`live_coverage_by_root`が
そのrecordをcoverしていた。この10 recordの除外が、8個のcanonical union
constraintに付随する重複`UnionBranch` derivation 16 edgeをcollapseした。
つまり「replay actionを生成してからduplicateと判定する」経路が、
「冗長なcandidate自体を生成しない」経路へ変わったことが、replay dispositionの
差分を正確に説明する。

`provenance_epoch`増加も`09b8e857`のwiring由来ではなく、先行する
`92f990b4`が新たに正しく行うmutation publishingへ帰属した。wiring自体は、
unwired projectionとの比較ではepoch総数を24減らしている。したがって、
characterization差分の全項目について、record・claim・lineage・replay disposition・
epoch sourceまで説明が閉じている。

最後のfull contract-suite gateは、`tests/yulang/cases.toml`の287ケースが
287/287 greenで完走した。今回のsystem loadではsingle-threaded local runに
24分以上かかり、先に起きたCodex MCP transport timeoutのriskがあるため、
Claudeがbackgroundで直接、別runとして完走を確認した。

これにより **URR-H2はfully complete** とする。本session中に先行して行った
full `cargo test -p infer`では、当初のnested local-var isolation test
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`も
passしたと報告されている。ただし、これはH3を省略する根拠にはならない。
設計文書自身の明示的な指示どおり、H2だけでこのtestがgreenになってもH3は必須である。

次かつ最後のsliceはURR-H3である。alias expansionの
`generalize/mod.rs::positive_aliases_within_scheme`とprovenance consumerを
`scheme_projectable_lowers`へ配線する。両方とも現在はrawのままであり、
H3にはまだ着手していない。全体のarcでは、H1がconstraint-machine replay層を直し、
H2がcompaction層を直した。残るH3がalias expansionとprovenanceを直すことで、
ORIGINALのmotivating bugであるnested local-var effect boundary leakを、
部分的にmaskされた状態ではなく、fullyかつ正しく閉じる。

## 35回目: URR-H3 alias / finalized-scheme red baseline
（2026-07-30）

URR-H3のstep 1として、production codeを変更せず、alias expansionとmotivating
finalized schemeのpost-H3 contractをtest-firstで固定した。
`generalize/mod.rs::positive_aliases_within_scheme`は引き続きraw
`projection_lowers()`を走査している。

`case_02`の既存unmatched-route fixtureを再利用し、`generalize/tests.rs`へ次の四testを
追加した。

- covered-only lowerはalias expansionから除外する
- covered / uncovered claimが同居するmixed recordは、covered-only controlとの差を保ちつつ
  uncovered relationを一回だけ残す
- last live coverage stateの除去前はaliasを除外し、除去後は同じraw relationを再び含める
- claimを持たないdirect / transitive aliasは順序と重複度を含めて従来どおり残す

現行productionに対する結果は、最初の三testが意図したred、no-claim controlがgreenだった。
covered-onlyの実値は`[TypeVar(1)]`、mixedの
`(covered, mixed)`実値は`([TypeVar(1)], [TypeVar(1)])`、livenessの
`(before, after)`実値も`([TypeVar(1)], [TypeVar(1)])`である。post-H3 expectationは
それぞれ`[]`、`([], [TypeVar(1)])`、`([], [TypeVar(1)])`であり、raw lowerを読む現在の
consumerがlive coverageを無視していることだけで三failureを説明できる。no-claim controlは
`[TypeVar(1), TypeVar(2)]`でpassした。

`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`は、
hand-built outer finalized schemeにinner familyが**存在しない**ことだけを要求するように
既存assertionを反転した。現行schemeは
`["&buffer#36:0"('a & 'b), std::control::var::observe('b | 'a)]`を含むため、そのassertionで
意図どおりredになった。raw constraint / audit traceのassertionは変更しておらず、
hand-built traceは引き続きinner return、call、result、outer aggregate、second applicationに
family lowerが存在することと、`FunctionReturnEffect` / `UnweightedReduction`経路を観測する。

`RUSTC_WRAPPER= cargo check -p infer`と`cargo fmt --all -- --check`は成功した。
このcheckpointはfailing testを意図的に含む。次sliceは
`positive_aliases_within_scheme`とgeneralized provenance collectionを同じ
`scheme_projectable_lowers` viewへ配線し、この特定の四redをgreenへ変える。

## 36回目: URR-H3 step 2、positive alias expansionをclaim-aware viewへ接続
（2026-07-30）

`generalize/mod.rs::positive_aliases_within_scheme`がraw
`VarBounds::projection_lowers()`を直接読むbypassを再確認し、lower sourceだけを
`ConstraintMachine::scheme_projectable_lowers(var)`へ切り替えた。iteratorは
`Vec`へcollectせず、各entryの`bound`を既存処理へ一回渡す。`reason`はこのsliceでは
使用していない。weightのneutrality判定、`Pos::Var`判定、scheme内allowed set、
再帰順序、重複除去、pass-local alias cacheは変更していない。

直前のred baselineで追加したalias testは4件すべてgreenになった。covered-only
lowerは除外され、mixed recordはindependent uncovered relationを一回だけ残し、
last live coverage state除去後はrelationが再び見える。no-claim controlも従来どおり
`[TypeVar(1), TypeVar(2)]`を同じ順序で返した。test期待値は変更していない。

`RUSTC_WRAPPER= cargo check -p infer`は成功した。broader
`generalize::tests::`は31 pass / 0 fail、`constraints::tests::case_02`は
53 pass / 0 fail / 1 known-ignore（54 selected）、compact suiteは
69 pass / 0 failだった。

これはH3のalias expansion wiringだけである。`generalize/provenance.rs`と
witness collectionには触れておらず、別sliceへ残す。motivating test
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`も、
provenance wiring前の結果をcompletion条件に混ぜないため今回は実行していない。

## 37回目: URR-H3 step 3、claim-qualified provenance表現とconsumer plumbing
（2026-07-30）

`GeneralizationParent`へ
`BoundClaim { bound: BoundRecordId, claim: UpperReplayClaimId }`をadditiveに追加した。
このsliceでは`capture_generalized_witnesses`を変更しておらず、production pathはまだ
`BoundClaim`を構築しない。

claim-qualified parentの解決は`ConstraintMachine::generalization_parent_carriers`へ集約した。
`bound`が存在し、`scheme_projection_claims_by_lower_record[bound]`へ`claim`が実際にlink
されていることを検証し、debug buildではinvalid pairをassertする。release buildでmetadataが
壊れていた場合もcomplete provenanceとして黙ってdropせず、local explanationとoccurrence
provenanceをincompleteにする。

projectionはclaim自身のlineageだけを公開する。`Original`は
`producer_constraint`、`ReplayConstraint`と`ReductionRouteConstraint`は記録済み`result`
constraint、`ReplayEvidence`はexact replay lower / upper boundsへ投影する。raw mixed
`BoundRecord`はaudit linkとしてparent内に残るが、semantic explanation parentにはしない。
local explanationとoccurrence provenanceは同じprojection helperを使い、portable exportは
投影済みのconstraint / bound carrierだけを変換する。

manually constructed `BoundClaim`を使うdirect testを追加し、四lineageすべてについてlocal
explanationとoccurrence-to-portable round tripを確認した。同じraw boundへ置いたsibling
derivationがlocal nodeにもportable originにも現れないことも固定した。既存expectationは
変更していない。

検証結果:

- `RUSTC_WRAPPER= cargo check -p infer`: pass
- `RUSTC_WRAPPER= cargo test -p infer claim_qualified_ -- --nocapture`: 2 pass
- `RUSTC_WRAPPER= cargo test -p infer generalize::tests::`: 31 pass
- `RUSTC_WRAPPER= cargo test -p infer constraints::tests::`: 174 pass / 1 known-ignore
- `RUSTC_WRAPPER= cargo test -p infer compact::tests::`: 69 pass
- `RUSTC_WRAPPER= cargo test -p infer explain`: 14 pass
- `RUSTC_WRAPPER= cargo test -p infer occurrence_provenance`: 1 pass

次sliceは予定どおり`generalize/provenance.rs::capture_generalized_witnesses`が
`scheme_projectable_lowers`の`reason`を使って実際の`BoundClaim` parentを構築するwitness
collection wiringである。

## 38回目: URR-H3 step 4、production witness wiringと既存snapshot gateの衝突
（2026-07-30）

`generalize/provenance.rs::WitnessCollector`のpositive branchを
`ConstraintMachine::scheme_projectable_lowers`へ接続した。`Unclaimed`は従来どおり
`GeneralizationParent::Bound(record)`を使い、`UncoveredClaims`はclaimごとの
`GeneralizationParent::BoundClaim { bound, claim }`を使う。選択したparent集合を一つの
structural traversalへ渡すため、mixed recordのendpointは一回だけ走査し、nested pathにも同じ
claim qualificationを保つ。negative-upper branchの本体は変更していない。

production captureを直接通す四testも追加した。covered-only relationはwitness parentを作らず、
mixed relationはuncovered `BoundClaim`だけをroot lowerとnested `ConstraintRelation`へ残し、
no-claimの二段Var lowerはraw traversalの`Bound(record)` edge列と完全一致した。同じ
`(bound, claim)`がunionの二経路から到達するcaseは、arena insertion前に2 edgeをconsiderし、
1 edgeをinsert、1 edgeをdedupして、既存のbudget accounting式を保った。

局所test、generalize、explain、occurrence provenance、case_02、compactはgreenだった。一方、
full provenance filterでは既存characterization二件がredになった。

- `general_subtype_failures_have_infer_analogs_but_carry_no_record_identity`:
  tuple-arityのlocal explanationが36 nodes / 48 edgesから35 / 47へ変化
- `pusp_a_characterizes_parameter_and_scheme_provenance_gaps`:
  claim-qualifiedなparameter / call queryの既存node / edge countとhashが変化

一時的なread-only相当のtrace（最終diffから除去済み）で、前者の変化元は
`TypeVar(0)`の`BoundRecordId(27)`が
`UncoveredClaims([UpperReplayClaimId(14)])`としてprojectされたrelationだと確認した。同じcapture
内の`BoundRecordId(26)`と`BoundRecordId(29)`は`Unclaimed`だった。したがって、no-claim common
pathの回帰ではなく、step 4が初めてproductionで`BoundClaim`を構築し、step 3のconsumer contract
どおりmixed/raw audit boundをsemantic explanation parentとして展開しなくなった結果である。
node / edgeが一つずつ減る形もこのprojectionと一致する。

ただし今回のsliceには「pre-existing testの期待値を変更しない」という明示gateがあるため、
characterization期待値は更新していない。要求された全test greenとこのgateを同時には満たせず、
commitを作らずprepared working treeのまま停止した。motivating nested testも指示どおり未実行。

## 39回目: URR-H3 step 4完了、witness wiringとbenign topology baseline更新
（2026-07-30）

前回未commitだった`generalize/provenance.rs::WitnessCollector`のproduction wiringを再確認した。
positive lower collectionは`scheme_projectable_lowers`を一回materializeし、`Unclaimed`を従来の
`Bound(record)` parentへ、`UncoveredClaims`をclaimごとの`BoundClaim { bound, claim }` parentへ
写す。選択済みparent sliceをstructural traversalへ渡すため、mixed lowerのendpointをclaim数だけ
再走査せず、nested witnessにも同じclaim identityを保つ。covered-only lowerはiteratorから除外され、
negative upper collectionは従来経路のままである。production captureを通す四testは、covered-onlyの
除外、mixed lowerのuncovered claim限定、ordinary no-claim edge列の完全一致、duplicate claim pathの
considered / inserted / deduplicated accountingを固定する。

前回redだった二characterization baselineは、実測と保存済みrecord-level traceに基づいて更新した。
general subtype failure四caseのlocal explanation topologyは次の結果だった。

- tuple arity: 36 nodes / 48 edgesから35 / 47
- tuple arity through generic: 71 / 94から69 / 92
- nested tuple arity: 41 / 53から40 / 52
- poly variant tag: 17 / 18のまま不変

新規観測した前二変化はredundant raw-bound wrapper除去と整合する小さなnode / edge同数減で、
poly variantは影響を受けないcontrolだった。全caseでcanonical constraint / lower / upper count、
matching record、nominal-cast count、origin列は不変だった。

PUSP-Aは、inferred parameter / call、annotated parameter / call、imported parameter、
multiple-use parameter / callのnode / edge / query Debug hashだけを実測値へ更新した。
imported callとgeneric caseは既存baselineのままである。baseline全体の比較により、max depth、
completeness、origin列、source-leaf count、original parameter bound到達性、schemeとそのhash、
constraint / bound / replay count、nominal-cast classification、poly hash、diagnostic hash / countが
すべて不変であることも再確認した。これは`BoundClaim`がuncovered claimをraw mixed bound wrapper
経由ではなく、自身のproducer / lineage carrierへ直接解決することで生じたinternal explanation
graph topology normalizationであり、user-facing diagnostic payloadの変更ではない。

更新後はsubtype provenance characterization 8件、PUSP characterization 13件がgreenだった。
broader gateも`generalize::` filter 41件（generalize core / witness 35件を含む）、
constraints 174 pass / 1 known-ignore、compact 69件、explain 14件、occurrence provenance 1件が
greenだった。

informationalにmotivating test
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`も実行したが、hand-built outer
finalized schemeに`"&buffer#36:0"` familyが残る既知assertionで引き続きredだった。raw traceは
inner return、call、result、outer aggregate、second applicationへのfamily lower到達と、
`FunctionReturnEffect` / `UnweightedReduction`経路を引き続き観測した。full H3 gateは後続sliceに
残る。

## 40回目: URR-H3 step 5、shared snapshot / liveness contractを統合testで固定
（2026-07-30）

`compact_scheme_projection_unmatched_route_fixture(false)`が作るcovered-onlyの同一claim / lower
recordを使い、`scheme_projectable_lowers`、`positive_aliases_within_scheme`、
`capture_generalized_witnesses`、`compact_type_var_for_scheme`の四consumerを一回のtestから
同じmachine snapshotに対して照合した。assertionは各consumerの完全な出力を重複して固定せず、
同じrecord / endpointの包含判定がshared viewと一致することだけを比較する。

live coverageがある最初のsnapshotでは四consumerがすべてrelationを除外した。
`remove_last_scheme_projection_coverage_for_compact_test`でclaim rootの最後のlive stateを外した
snapshotでは四consumerがすべて同じrelationを包含した。さらにtest-only reinsertion helperで
同じreduction stateをrootへ戻したsnapshotでは、四consumerがすべて再び除外へ戻った。
これによりnon-empty→emptyだけでなくempty→non-emptyでも、各consumerのpure queryとH2の
scheme compactionが同じ時点のliveness classificationを共有することを一つのintegration-style
testで固定した。consumer間の不一致は観測されず、production codeと既存test期待値は変更していない。

`cargo check -p infer`は既存の`generalized_projection_lowers` dead-code warning一件だけで成功した。
新規testは1 pass / 0 fail。broader gateはgeneralize 42件、compact 69件、explain 14件、
occurrence provenance 1件、subtype provenance characterization 8件、PUSP characterization
13件がすべてgreenで、`constraints::tests::case_02`も53 pass / 1 known-ignoreだった。

## 41回目: URR-H3 step 7 completion gateでmotivating failureが残存
（2026-07-30）

H1 / H2 / H3の全commitが載った`63b062cf`でcompletion gateを実行した。最重要の
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`は、corrected assertionの
まま**失敗した**。parsed outer finalized schemeは
`('a & 'b) -> [std::control::var::observe('b | 'a)] ('b | 'a, 'a)`でinner familyを除外したが、
hand-built outer finalized schemeは
`('a & 'b) -> ["&buffer#36:0"('a & 'b), std::control::var::observe('b | 'a)] ('b | 'a, 'a)`
となり、inner familyを残した。raw traceも従来どおり、instantiated inner return、call、result、
outer aggregate、second applicationの全slotでfamily lowerを観測した。

一時的なreadoutを追加して、failureをshared viewの単純な未配線ではなくrecord単位で局所化した
（readoutは調査後に完全に除去した）。最初のcontamination alias
`TypeVar(1669) <- Var(TypeVar(1522))`は`BoundRecordId(10185)`で、説明は
`ConstraintRecordId(6472)`、`RowDerivationId(196)`、`UnweightedReduction`、
`FunctionReturnEffect`へ到達する。このrecordはraw graphには残る一方、
`scheme_projectable_lowers(TypeVar(1669))`から正しく除外されていた。したがってH1/H2/H3の
covered-alias suppression自体はこのproduction witnessでも働いている。

残っているgapは、その後にmaterializeされたconcrete row recordである。inner-familyの
`Row([PosId(2132)])`はactual callback bodyの`BoundRecordId(10318)`から、callの`10472`、
resultの`10478`、outer aggregateの`10484`、outer second applicationの`10555`へ到達していた。
これらはすべてshared scheme viewで`Unclaimed`としてprojectableだった。各下流recordの説明は
binary replay / structural decompositionを通って同じcallback-body sourceへ戻るが、元のcovered
claim / coverage identityを持たない。つまりH3 consumer wiringはclaim-linked aliasを正しく
除外している一方、すでに下流へ複製されたderived concrete-row lowerへclaim qualificationが
運ばれていない。step 5のcross-consumer testは一つのclaim-linked recordに対するview / alias /
provenance / compactの一致を証明したが、このproduction materialization経路を覆っていなかった。
これは期待値やtest fixtureの問題ではなく、H3の前提より深いclaim/projection propagation gapである。
原因を理解せずにprojection側でconcrete rowを一括除外する修正は入れていない。

motivating testが失敗したため、指示の条件分岐に従いbroader local-var lowering suiteは実行しなかった。
five-case characterizationは`actual == expected_characterization()`の構造体比較で1 passとなり、
全5ケースのcensus、`poly_dump_fnv1a64`、`check_report_fnv1a64`に差分はなかった。したがって
approvedなnested principal narrowingはまだproduction characterizationへ現れておらず、
baseline更新対象は0件である。

設計文書§9のbroader gate結果:

- constraint characterization: 5 pass
- explanation: 7 pass
- portable provenance: 7 pass
- `timeout 240s cargo test -p infer`: motivating test failureを観測し、最終集計前に240秒timeout。
  観測範囲の他testにfailureはなかった
- `timeout 240s cargo test -p specialize`: 163 pass
- `timeout 300s cargo test -p yulang`: 376 pass / 1 fail。failureは既知flakyの
  `embedded_std_compiled_unit_artifact_persists_to_user_cache`で、artifact countが期待1に対して
  実値3だった。同testの単独再実行は1 pass
- `timeout 600s cargo test --workspace`: `control-ir`の
  `source_not_callable_application_reaches_its_final_control_site`と
  `source_not_record_selection_reaches_its_final_control_site`が既存analysis diagnosticを受けて
  4 pass / 2 failで早期停止し、workspace全体は未完走

287-case contract suiteは指示どおり実行していない。今回の結果だけではURR-H3をfully completeと
宣言できない。motivating failureのderived-row claim propagation gapと、Claude側の287-case
結果を合わせてreviewする必要がある。

## 42回目: DCP-A red baseline と proof model preflight
（2026-07-31）

承認済み
`notes/design/2026-07-30-derived-row-claim-propagation-gap.md`
§8.1〜§8.8を`constraints/tests/case_02.rs`へ追加した。production codeと既存test expectationは
変更していない。test-only inspectionはarena IDを使わず、canonical constraint / lower record、
exact `BinaryReplayDerivation`のlower / upper side、exact `StructuralDerivation`、
producerから引いたstable one-sided lower、lowerごとのclaim root / independent direct carrier /
scheme view inclusionを読む。

current productionに対する個別結果は次の通り。

- §8.1 replay lower-side inheritance: **red**。exact replayは
  `lower = R_lower`を保持しsemantic replayも1件だが、result parentはordinary upper側の1claimだけ。
  `R_lower`へlink済みのcovered rootはresultへ届かない。
- §8.2 existing upper-side control: **green**。existing H1 pathはexact upper recordからcovered
  rootを1件継ぎ、semantic replayは1件のまま。
- §8.3 both-side mixed replay: **red**。canonical result / replayは1件だが、観測parentはupper側
  1件だけ。mixed lowerのcovered rootとindependent uncovered rootの両方が欠落した。
- §8.4 structural row aggregate: **red**。`MarkerAggregateToUpperTail` childはexact
  `StructuralDerivation { parent, rule }`を1件持つ一方、structural claim parentとchild lowerの
  root linkは0件。
- §8.5 non-row structural control: **red**。ordinary one-sided controlはraw 1 / project 1 /
  independent support 1を保つ。`FunctionReturnEffect`と`TupleElement`はいずれもexact structural
  carrierを持つが、child claim parentは0件。
- §8.6 one-sided concrete lower: **red**。producerはexact replay claim parentを1件持ち、
  stable concrete-row lowerも1件あるが、そのlowerにlinkされたrootは0件。
- §8.7 independent same-key lower: **green**。direct-first / claimed-firstともcanonical raw lower
  1件、scheme projection 1回、independent direct carrier 1件、exact replay carrier 1件、
  `IncompleteReplay = false`で一致した。current semanticsがindependent relation自体を失って
  いないcontrolであり、covered siblingが未linkのままというleakを正しい期待値にはしていない。
- §8.8 duplicate / evidence / promotion: **red**。canonical structural carrierは1件にdedupされ、
  evidence-only recordからordinaryへのpromotionもstable IDを保ち、`IncompleteReplay`はない。
  しかしstructural one-sided lowerにlinkされたrootは0件。

比較用censusは、§8.1の`(exact replay, lower-root parent, upper parent) = (1, 0, 1)`、
§8.4の`(structural carrier, child claim parent, child lower root) = (1, 0, 0)`、
§8.6の`(producer replay claim parent, stable lower, lower root) = (1, 1, 0)`、
§8.7の各順序`(raw, projected, independent, replay, incomplete) = (1, 1, 1, 1, false)`、
§8.8の`(structural carrier, linked root, incomplete) = (1, 0, false)`として保存する。

baseline / regression結果:

- motivating testはhand-built outer schemeに`"&buffer#36:0"`が残る既知assertionで**red**。
  parsed outer schemeはinner familyを含まない。
- five-case characterizationは80.48秒でpassし、保存済みbound / replay census、poly hash、
  check hashに差分なし。claim censusは上記DCP fixture snapshotとして別に保存した。
- 287-case contract suiteは指示どおり未実行。DCP-Aはproduction無変更なので既存baseline不変を
  期待し、Claude側の別実行へ残す。
- `cargo check -p infer`は既知dead-code warning 1件だけで成功。
- existing `case_02`は53 pass / 1 known-ignore、generalize 42、compact 69、explain 14、
  occurrence provenance 1がすべてgreen。

## 43回目: DCP-B、replay両側のside付きclaim parent
（2026-07-31）

approved design §5.1案Dと§6.1に従い、binary replay actionがexact lower recordの
`scheme_projection_claims_by_lower_record`とexisting upper-side claim selectionの双方を読むようにした。
各parentは`Lower` / `Upper`のsideを持ち、一つのsemantic action上で加算的にmergeする。
lower×upperの直積やclaim数ぶんのenqueueは作っていない。new、queue duplicate、
prefiltered duplicate、evidence-onlyの全pathへ同じside metadataを通し、canonical
`(result, compressed root, parent side)` indexで再到達をdedupする。lower / upper replayの
semantic eligibilityは既存条件を維持したため、claim metadataだけでは新しいsubtype actionを作らない。

DCP-Aの§8.1、§8.2、§8.3はすべてgreenになった。§8.4、§8.5、§8.6、§8.8は従来と同じ
structural / one-sided linkage assertionでred、§8.7はgreenのままで、DCP-C / Dのscopeを先取りして
いない。URR-H1はoriginal 18 pass / 1 known-ignore、v6 4/4 passで期待値変更なし。
`cargo check -p infer`は既知dead-code warning一件だけで成功し、compact 80、generalize 42、
explain 14、occurrence provenance 1、claim-qualified provenance 2もすべてgreenだった。

five-case characterizationは保存済み構造体とのexact comparisonを三回試したが、assertion結果へ
到達する前に240秒timeout二回、約4分半での手動中断一回となった。期待値は変更しておらず、
programmatic zero-diffはこのrunでは未確認として残す。287-case contract suiteは指示どおり
実行していない。

## 44回目: DCP-B five-case characterization baseline refresh
（2026-07-31）

DCP-B（`5b492709`）はreplay action planningでlower / upper両recordのclaim parentを対称に読み、
各parentへ`Lower` / `Upper`のsideを付けた。再到達は
`(result, coverage_root, parent_side)`でdedupし、`should_replay`のdecision logicは変更していない。
このため変更はside付きclaim metadataとprovenance bookkeepingに限られる。

five-case characterizationをrelease testで再実行し、失敗出力のactual / expectedを
programmaticに比較した。各ケースの`provenance_epoch`だけを正規化したserialized structureは
ともに12,969 bytes、SHA-256
`34d7c880f80b91cdfac5a9305b936f9e9da240c8f3752a48b8a1d81916377ac9`でbyte-identicalだった。
したがって差分は全5ケースとも`provenance_epoch`だけであり、残る86 fieldsはすべて不変である。
特に`poly_dump_fnv1a64`と`check_report_fnv1a64`は全5ケースで既存baselineと一致した。

実測値に合わせ、five-case baselineの`provenance_epoch`だけを次の値へ更新した。

- repository-std-only: 2,398,021
- effect-callback-residual: 2,400,896
- ref-update-local-buffer: 2,446,796
- config-read-false-positive-repro: 2,473,200
- file-rollback-false-positive-repro: 2,440,266

更新後のfive-case characterizationは1 pass / 0 failとなった。最終sanity checkではcompact 80、
generalize 42、explain 14、occurrence provenance 1がすべてgreenだった。full `case_02`は
57 pass / 4 fail / 1 known-ignoreで、DCP-B対象の§8.1〜§8.3とcontrolの§8.7はgreen、
既知のDCP-C / D scopeである§8.4、§8.5、§8.6、§8.8だけが従来どおりredだった。

## 45回目: DCP-C、generic structural claim propagation
（2026-07-31）

承認済み設計§5.2案B、§6.2、§9 DCP-Cに従い、DCP-Bのreplay / reduction-route parentを
汎用`claim_parents_by_constraint` reverse indexへ統合した。
`enqueue_derived_subtype`がcanonical childを得た後、親constraintのclaim-qualified parentsを
exact `StructuralDerivation { parent, rule }`と組にしてchildへmergeする。
new、canonical duplicate、`merge_structural_derivation`のsecondary carrierは同じhelperを通り、
dedup keyは`(result, compressed coverage root, exact structural derivation)`である。
canonical resultを作らないtrivial childはclaim entryを作らない。
structural ruleのwhitelist、row / `MarkerAggregateToUpperTail`専用分岐、arena ID条件、
derivation graph walkは追加していない。

DCP-A regressionは§8.4 row aggregateと§8.5 function-return-effect / tuple controlがgreenになった。
§8.4はDCP-Cのconstraint-level lineage gateまでを検証し、stable one-sided lower linkageは
§8.6 / §8.8に残した。§8.6と§8.8はどちらもlower rootが未linkというDCP-D境界で予定どおりred。
duplicate structural admissionはexact carrierとcompressed rootを一件へdedupし、
追加したtrivial controlもgreenだった。

regression結果:

- `cargo check -p infer`: 成功（既知dead-code warning 1件）
- `case_02`: 60 pass / 2 expected-red（§8.6、§8.8）/ 1 known-ignore
- compact: 80 pass
- generalize: 42 pass
- explain: 14 pass
- occurrence provenance: 1 pass

five-case release characterizationのactual / expectedをprogrammaticに比較した。
両payloadは12,943 bytes、`provenance_epoch`正規化後はともに12,968 bytes、SHA-256は
`15e02d75907dfa4d3734ec187f2d297250184862e3d5f09a72d779b6eddbe4de`で一致した。
全5ケースの`poly_dump_fnv1a64` / `check_report_fnv1a64`も一致し、差分は
`provenance_epoch`だけだった。baseline refreshはproduction変更と分けて次commitへ置く。
287-case contract suiteは指示どおり実行していない。

## 46回目: DCP-C five-case characterization baseline refresh
（2026-07-31）

45回目のprogrammatic classificationに基づき、five-case baselineの
`provenance_epoch`だけを次の実測値へ更新した。

- repository-std-only: 2,937,880
- effect-callback-residual: 2,940,791
- ref-update-local-buffer: 2,991,884
- config-read-false-positive-repro: 3,021,873
- file-rollback-false-positive-repro: 2,983,969

更新後のrelease characterizationは1 pass / 0 failだった。
production semantic census、poly hash、check hash、formatted scheme、diagnosticのbaselineは
変更していない。

<!-- bug-append-anchor: 2026-07-30 -->
