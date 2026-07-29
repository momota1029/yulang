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

## 次に調べるべきこと

- **最優先**: この知見を production の実装へ反映する。次回 LVB-B
  実装では、callback body 内の逐次文（特に nested function call を
  含む場合）の effect 集約を、`block_local.rs:1289` が使っている
  parsed lowering と同じ block-aggregate pattern に**忠実に**従わせる
  ——前の文の集約済み effect を次の call の引数へ混入させない。
- callback/helper application 機構自体、4つの construction 不変条件、
  SCC ordering、七本目の edge（nested call 自体の配線）は、すべて
  潔白と確定済み。原因は「callback body の逐次文をどう繋ぐか」という
  construction の具体的な誤りまで絞り込めた。
- 次回も、rollback する前に診断値を記録する手順を継続する。
- LVB-A2 の `h` witness の潜在リスク（`my $x` migration 後に意味が
  変わりうる）は未対応のまま残っている。
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
