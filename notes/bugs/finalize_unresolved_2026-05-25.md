# Finalize 残バグ報告（2026-05-25 深夜）

「Seed role-impl member paths from canonical paths」(commit 7d3c41a) で
list の Fold dispatch は通ったあと、同じ runtime-finalize 経路で関連症状
の snippet を当たり直したが直りきらなかったものをまとめた。

直前に積んだ追加の試行（pattern bind ty 伝播、`close_role_associated_types`
の発火条件拡張、apply spine arg.ty の narrow）は別 commit にまとめて
te(っちゃん)が後で整える方針。本ファイルは「次に手を入れるときの取っかかり」を
残す目的のメモ。

## 1. `solved/role_method_in_for_body_pattern.yu`

### 期待 / 実際

```
my pairs = [(1, just "a"), (2, nil)]
my $sum = 0
for p in pairs:
    case p:
        (n, just s) -> &sum = $sum + n + s.len
        (n, nil)     -> &sum = $sum + n
$sum
```

- legacy: `[0] 4`
- finalize: `[0] request std::prelude::Len::len "a" blocked=None`
  （`s.len` の role dispatch が立たず Len::len request が漏れる）

### 根本原因

Variant pattern `:just _ as s` の `s` の runtime type が Unknown のまま role
rewrite に届く。階層は：

```
case p : (int, opt str)
   pattern = Tuple [As (Wildcard, n), Variant("just", Some(As(Wildcard, s)))]
```

外側 Tuple は scrutinee の `(int, opt str)` から component tuple 分解で
`n := int` / inner Variant 用の scrutinee `opt str` までは降りる
（pattern propagation 拡張で対応済み）。**ただし `Variant` の payload を
`opt 'a -> just => 'a` で projection する経路が無い**ので、`s` は
Unknown のまま。

### 試したこと（採用していない）

- `collect_pattern_local_types` の `Pattern::Variant { value, .. }` で
  scrutinee_ty を伝えるのは試した。が、value pattern (`As(Wildcard, s)`)
  に対応する payload type を導けないので結局 None を渡す形にした。
- pattern 自身の `value.ty` field を見る案：lower 段で Unknown のままに
  なっているので、ここからは情報を引けない（dump で確認済み）。

### 次に手を入れるなら

1. **runtime_ir::Module に enum_variants を持たせる**。
   `EnumVariantGraphNode { enum_path, tag, type_params, payload }` は
   `yulang_typed_ir::CoreGraphView::enum_variants` にすでにあるので、
   lower 段で `module.enum_variants` に詰めて runtime-finalize へ運ぶ。
2. `collect_pattern_local_types` の `Pattern::Variant { tag, value, ty }`
   分岐で、scrutinee_ty が `Named { path, args }` の形なら
   - enum_variants から `(path, tag)` で payload template を引く
   - `infer_type_substitutions(template, scrutinee.args)` で type params
     を解消（`project_role_impl_associated_type` と同じやり方）
   - 解消後の payload type を value pattern に scrutinee_ty として渡す
3. tag が見つからない / type params 不一致のときは Unknown のまま落とす。

ついでに `Pattern::Record` の field 別の type 分解も同じ枠でやれる。

## 2. `solved/wrap_inside_for_body_leaks_fail.yu`

### 期待 / 実際

```
error fail_err: bad str
my $hits = 0
for x in [1, 2, 3, 4]:
    my res = fail_err::wrap:
        if x == 3: fail fail_err::bad x.show
        else: x
    case res:
        ok n -> &hits = $hits + n
        err _ -> ()
$hits
```

- legacy: `[0] 7`
- finalize: `error: function application type mismatch: expected int, got ()`

### 試行中に観測したこと

`close_role_associated_types` の発火条件を unconditional に広げると、
このファイルだけ `ConflictingBounds { var: t10095#0, previous: Tuple([]), next: int }`
に変わる。つまり：

- 別経路でグラフに `t10095 == Tuple([])`（unit）が積まれている
- close 経由で `t10095 == int` を入れると衝突
- 制限版（`is_complete()` または `solution_has_unknown_components` が真の
  ときだけ close）に戻すと、衝突は再発しないが元のエラー（int / unit 取り違え）
  に戻る

`t10095` は for_in の lambda param ('item) の流れ。`Tuple([])` は for body
の RETURN 型 (unit) と混線している疑い。`x` (lambda param) と body return
の typevar が graph で同一視されている可能性がある。

### 次に手を入れるなら

- まず `t10095 == Tuple([])` の出処を絞る。graph 構築段の
  `solve_simple_apply` あたりに「lambda param と return の typevar を
  両方 `current` に紐付けているステップ」が無いか確認。
- もし graph 構築の typevar 配線が同じ var に乗っているなら、別 var に
  分けてから close を当てる。
- そうでなければ、`Tuple([])` を「unit defaulting」由来とみなす可能性。
  `default_unbound_lower` 群の引数集合に lambda param 由来の var が
  紛れ込んでいないかチェック。

## 3. その他の sweep 差分（既存・finalize 未対応）

「`examples/` + `notes/bugs/` + `notes/bugs/solved/` の 88 件を両モードで
sweep」で finalize ≠ legacy の差分は 6 件残っているが、本 commit より前から
ある既存差分。私の修正で新規に増えたものは無い。

| snippet | 状況 |
|---|---|
| `solved/labelled_for_var_effect_collision.yu` | legacy 側が `cannot infer all runtime types` で死ぬ、finalize は `[0] 3` で通る。**finalize の方が良い**ケース。legacy が type inference で詰むのを直したいなら別タスク。 |
| `solved/list_fold_method_inference_failure.yu` | legacy `[0] 6` / finalize `runtime validation type mismatch: expected int, got list<int>`。Fold 経由の集計で result type の取り違え。dispatch 自体は立っているので Fold path とは別経路。 |
| `solved/native_ref_list_mut_lost.yu` | legacy `request &ys#var::get` blocked / finalize は `ConflictingBounds` で type mismatch。`ref` の type arg と list element type が衝突している。 |
| `solved/result_methods_undocumented_missing.yu` | legacy `[0] ok 42` / finalize `function application type mismatch: expected result<int, 'a>, got int -> int`。Result の method call 周りで apply の方向が逆転している疑い。 |
| `solved/role_method_in_for_body_pattern.yu` | 上記 #1。 |
| `solved/wrap_inside_for_body_leaks_fail.yu` | 上記 #2。 |

## 4. 余録：pattern propagation の現状

今回触った `collect_pattern_local_types` は scrutinee_ty を受け取れる形に
なっていて、Tuple は分解、Variant / Record / List は scrutinee_ty=None を
ヘルパに渡すだけ、で止まっている。**`Pattern::Or` の左右は scrutinee_ty
を共有しているが、現状 `is_complete()` 拡張側からのみ恩恵がある程度**。

将来 Variant / Record / List も分解する場合、`tuple_component_runtime_types`
と同じ作りで以下を追加すれば良い：

- `record_field_runtime_type(scrutinee_ty, field_name) -> Option<RuntimeType>`
- `list_element_runtime_type(scrutinee_ty) -> Option<RuntimeType>`
- `variant_payload_runtime_type(scrutinee_ty, tag, enum_variants) -> Option<RuntimeType>`

enum_variants が要るのは Variant だけ。残りは scrutinee_ty を直接覗くだけ
で済む。

## 5. 確認に使ったコマンド

```bash
# 単体テスト
cargo test -q -p yulang-runtime-finalize --lib

# snippet 単体
target/debug/yulang run --no-cache --print-roots <file>.yu
env YULANG_RUNTIME_FINALIZE=1 target/debug/yulang run --no-cache --print-roots <file>.yu

# IR ダンプ
target/debug/yulang dump --finalized-ir --no-cache <file>.yu
target/debug/yulang dump --runtime-finalize-ir --verbose-ir --no-cache <file>.yu

# sweep（88 件）
bash /tmp/sweep.sh
```

`/tmp/sweep.sh` の内容：

```bash
#!/usr/bin/env bash
set -u
fail=0
for f in notes/bugs/*.yu examples/*.yu notes/bugs/solved/*.yu; do
  [ -e "$f" ] || continue
  legacy=$(timeout 30 target/debug/yulang run --no-cache --print-roots "$f" 2>&1 | head -20)
  final=$(timeout 30 env YULANG_RUNTIME_FINALIZE=1 target/debug/yulang run --no-cache --print-roots "$f" 2>&1 | head -20)
  if [ "$legacy" != "$final" ]; then
    fail=$((fail+1))
    echo "=== DIFF: $f ==="
    diff <(echo "$legacy") <(echo "$final") | head -20
    echo
  fi
done
echo "differences: $fail"
```
