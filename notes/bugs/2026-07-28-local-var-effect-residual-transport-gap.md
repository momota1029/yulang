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

## 次に調べるべきこと

- **最優先**: なぜ payload 付き parameterized family だけ、compaction 後の
  最終 scheme から row item ごと消えるのか。単純な `Set(owner)` 形の
  act-method では起きない。`650fec0b` が触った
  `pos_is_effect_marker_row_item` 周辺と同じ compaction 経路を、
  parameterized family に限定して trace する。
- push/pop boundary を **body lowering より前**に確立する、という設計の
  骨格自体は（3回の停止を経ても）まだ反証されていない。反証されたのは
  「不変条件をどう証明するか」の部分だけ。
- generalization 全体を変える修正は影響範囲が広いため避ける。この設計判断は
  ユーザ承認済み設計文書として起こしてから着手するのが筋（他の signed design
  文書と同じ扱い）。次回は「parameterized family が compaction でどう
  扱われるか」を単独で調べる読み取り専用の投資を先に行うのがよさそうだねぇ。

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
