# LSP hover type projection

## Purpose

Yulang の hover は、ユーザーが書いた式の上で「その場所に見える型」を返すべきである。
特に method selection の hover は、method 定義本体の scheme ではなく、receiver を選択済みの
call-site value type を表示する。

現在の `hover_for_selected_method` は、解決先 def の public scheme を直接表示している。
これは `p.pick` の hover で impl / role member 側の型を見せる形になりやすく、
source 上の `p.pick` が実際に持つ callable value type からずれる。

## Current Shape

Lowering は dot selection で次の型変数を作る。

- `method_value`: 解決される method 関数そのもの。
- `receiver_value`: receiver 式の value type。
- `receiver_effect`: receiver 式の evaluation effect。
- `result_value`: `receiver.method` 式そのものの value type。
- `result_effect`: `receiver.method` 式そのものの effect。

そのうえで、

```text
method_value <: receiver_value -> result_value
```

に相当する制約を入れている。
したがって hover に必要な call-site type は、解決先 def の scheme ではなく
`result_value` から得られる。

ただし現状の `SelectionUse` は unresolved selection を解決するための table であり、
解決時に `remove` される。`source_spans` だけは残るため、hover は range と
`poly::Select.resolution` だけを見られるが、call-site type までは見られない。

## Design

### Add resolved selection hover metadata

`infer::uses::SelectionUseTable` に、解決後も残る metadata を追加する。

```rust
pub struct ResolvedSelectionUse {
    pub parent: DefId,
    pub method_value: TypeVar,
    pub selected_value: TypeVar,
    pub receiver_value: TypeVar,
    pub receiver_effect: TypeVar,
}
```

`SelectionUse` にも `selected_value` を追加し、lowering が `result_value` を入れる。
selection resolution を適用する時、`SelectionUse` を unresolved table から取り出して
`ResolvedSelectionUse` として保存する。

これは型推論規則を変えない。既存の `method_value` / `receiver_value` constraint を
そのまま使い、hover 用に既にある type var を保持するだけである。

### Hover display rule

`hover_for_select` は次の優先順で表示する。

1. `SelectResolution::RecordField`: 今まで通り hover なし。
2. resolved selection metadata がある method / typeclass method:
   - label は source の select name を使う。
   - type は `selected_value` を `format_inferred_value_type_with_path_rewriter` で表示する。
3. metadata が無い古い / incomplete route:
   - 既存の target scheme hover に fallback する。

この fallback は互換性のためであり、通常の current pipeline では first slice 後に
使われない想定である。

### Label rule

label は解決先の def label ではなく `poly.select(select).name` を使う。

理由:

- source に見えている名前と一致する。
- attached impl / role member の内部 label、`#act-method`、local copied def を出さない。
- module path / function name の文字列一致による特別扱いを避けられる。

Definition / references はこれまで通り解決先 def を使う。
hover の label だけを call-site 表示へ寄せる。

## Non-goals

- 型推論、method resolution、role demand の意味を変えない。
- receiver 専用 role demand を作らない。
- `Any` を hover の fallback 型として使わない。
- std path / fixture name / method name の文字列分岐を入れない。
- LSP 側で CST を再走査して型を推測しない。
- record field hover をこの slice で実装しない。

## First Slice

1. `SelectionUse` に `selected_value` を追加する。
2. lowering の dot selection で `result_value` を `selected_value` として登録する。
3. `SelectionUseTable` に resolved metadata map を追加する。
4. selection resolution 時に resolved metadata を保存する。
5. `hover_for_selected_method` は resolved metadata があれば selected value type を表示する。
6. source hover regression:
   - nominal method `u.id` は `id: User` 相当の selected value type を出し、
     `User.id:` の target scheme label を出さない。
   - attached role method `p.pick true` は source label `pick:` を出し、
     hidden label / `#` を出さない。
   - selected type に std paths があっても import/prelude visible shortening を保つ。

## Validation

Focused:

```text
cargo fmt --all -- --check
timeout 240s cargo test -q -p yulang hover_entry_source_reports_selected_method_type -- --test-threads=1
timeout 240s cargo test -q -p yulang hover_entry_source_reports_attached_role_method_selection_type -- --test-threads=1
timeout 240s cargo test -q -p yulang hover_entry_source_shortens_selected_method_type_paths -- --test-threads=1
```

Broader:

```text
timeout 240s cargo check -q -p yulang
timeout 240s cargo test -q -p yulang hover -- --test-threads=1
```

## Rollback

Rollback if:

- method resolution changes;
- public signature golden changes;
- role method diagnostics change;
- hover needs name/path string special cases;
- selected value type cannot be formatted without adding placeholder `Any` / `Never`;
- source hover starts exposing hidden `#...` labels or internal evidence.
