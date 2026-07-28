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

## 試して失敗した修正の方向

同じ `SubtractId` を local effect の push（`wrap_var_binding_run`）と
handler result の pop の両方に使う案を試したが、local `ref` scheme の
generalization/instantiation で binder が複製され、対応が崩れた。
monomorphic な use-site 化だけでは解消しなかった。

## 次に調べるべきこと

- generalize 前後、および local-ref instantiation 後の `SubtractId` 対応を
  記録して、正確にどの段階で対応が失われるかを特定する。
- 既存の act-method receiver boundary（同じ形の「handler が state を
  provide し、callback の残余 effect だけを外に見せる」パターン）が
  binder を維持できている理由との差分を確認する。
- 解決には、synthetic local-var boundary ごとの subtraction binder を
  `ref` effect 側と `wrap_var_binding_run` 側の両方で共有し、その binder を
  local binding generalization が複製・prune しない表現が必要と見られる。
- `SyntheticVarActUse` 単位の boundary object を lowering 中に保持し、
  local-var reference 専用の scheme capture へ渡す形が最も狭い修正候補だが、
  stack quantifier と最終 poly scheme の整合を要確認。
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
