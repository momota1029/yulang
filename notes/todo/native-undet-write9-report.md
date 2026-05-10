# write9.md 実装報告

## 受領した方針

`native-undet-write9.md` での指示は、「この到達点を壊れない成果に固める」という方向性。具体的には:

1. デバッグ出力・暫定 ignore・計画メモを整理する
2. 今回のバグを小さい regression として固定する
3. `std::undet.once` の分岐探索が本当に queue/resumption を使っているか追加テストする
4. Cranelift JIT だけでなく object / executable / native-run でも確認する
5. その後に std::undet.list / logic / non-scalar print へ進む

## 進めたこと

### 1. cleanup

- `eval_cps_module` 内の `eprintln!("[debug] root {} returned {value:?}", ...)` を削除した。

### 2. CPS eval primitive の追加

`eval_cps_primitive` で list ops が VM primitive にフォールバックしていた。resumption を含む `CpsRuntimeValue::List` を直接扱えるように、以下を CPS domain で実装した。

- `PrimitiveOp::ListLen` — `CpsRuntimeValue::List` から長さを取得して `Plain(VmValue::Int)` に
- `PrimitiveOp::ListIndex` — i番目を `CpsRuntimeValue` のまま返す
- `PrimitiveOp::ListIndexRangeRaw` — 範囲を `CpsRuntimeValue::List` のまま返す
- ヘルパ `cps_value_to_usize` を追加

これにより `std::list::uncons queue`(`ListLen` + `ListIndex` + `ListIndexRangeRaw`) が resumption を含む queue でも動くはず。**ただし end-to-end で確認するテストは下記の root thunk leak 問題でブロックされていて、まだ exercised されていない。**

### 3. regression テストの追加（4本、すべて `#[ignore]`）

`source.rs` に以下を追加し、すべて `#[ignore]` 付きにした。理由は下に述べる。

- `compares_recursive_closure_self_reference_through_cps_repr_cranelift` — `MakeRecursiveClosure` self-reference 単独 regression。**`sum_down` が polymorphic として infer され `ResidualPolymorphicBinding` で落ちる**。direct recursion でも `MakeRecursiveClosure` を踏むはずだが、そもそも runtime lowering まで届いていない。型パラメータ付きの再帰関数として lower されているか、monomorphizer の挙動を要確認。
- `compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift` — `each [1,2,3]` + `guard: n > 1`、期待 2
- `compares_std_undet_once_returns_nil_when_all_rejected_through_cps_repr_cranelift` — 全 reject、期待 0 (nil 経由)
- `compares_std_undet_once_two_nested_choices_through_cps_repr_cranelift` — 2 重 each + guard、期待 21 (VM compare)

下 3 本は **CPS eval (Layer 1) の段階で root thunk leak している**ため、Cranelift 比較以前にダメ。詳細は次節。

### 4. 切り分けテスト `debugs_std_undet_once_skip_eval_layers`

write9.md 4 章の手順で「CPS eval / CPS repr eval / Cranelift JIT」3 層を順に確認するテストを足した。`#[ignore]`。

## 判明した問題点（要相談）

### A. Helper 関数経由 + reject 経路で root が thunk を返す（最重要）

```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}

case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

これを CPS eval にかけると、root が

```
Thunk(owner: work__mono0, entry: cont(1),
      handlers: [HandlerFrame { once_arms with envs containing
                  recursive_self closure once__mono4 ... }])
```

を返してくる。`int` を期待しているのに **root の値が thunk のまま漏れている**。`ExpectedPlainValue { id: usize::MAX }` で落ちる。

注意: 同じ Phase F.5 step 5（return type ベースで root / function return も `force_if_non_thunk_demand` する）を write8.md でも提案されていたが、私はそこまで触らずに **「ApplyClosure result / DirectCall result の force だけで std::undet.once scalar-unwrapped が通った」** で commit していた。今回 helper 関数経由で reject path を入れると、その実装漏れが顕在化した。

### B. しかし「ほぼ同じ形」のテストは通る

```yulang
case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
```

これは 3 層全部通る (`compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift`)。

つまり「`case scrutinee.once: arm`」というパターンは正しく動くケースもある。

```yulang
my work(): int = each [1, 2, 3]
case work().once:
    ...
```

これも 3 層通る (`debugs_std_undet_once_skip_eval_layers` を `each` だけにしたら全層 OK だった)。

```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}
case work().once:
    ...
```

これは Layer 1 で thunk leak。**guard を入れると壊れる**。

VM では正しく `2` を返す。

### C. なぜ「guard 入りの helper 関数」だけ壊れるのか（仮説）

write8.md で予想されていた通り、これは **return type 駆動の forcing が抜けている場所がある** という問題に見える。`work()` の body は `MakeThunk(cont(1))` を返し、その `cont(1)` 内で `each` と `guard` の effect 操作が CPS で組まれている。`work()` を呼ぶ側で `force_if_non_thunk_demand` が走らないと thunk のまま伝播する。

私が書8で入れた forcing は「ApplyClosure result」「DirectCall result」のみ。lower_root / lower_binding / lambda body return は手付かず。

ただし、(`each` 単独 / `each` を返すだけの helper) はこの forcing が無くても通っている。理由は以下の可能性:

1. `each` は外部関数だが、`.once` の lower 時に何らかの暗黙 force が入っているケース
2. `each` 単独だと `MakeThunk` の後すぐ `.once` の `loop` に流れ、root は handler frame だけ持つ thunk を返さない構造になっている
3. `guard` を入れると body 内で `if-else` (case) が増え、その分岐のせいで thunk が外側まで持ち上がる

仮説 3 が直感的には一番ありそう。`if cond: 0 else: ...` を含む body は CPS lowering で thunk を返す path が増え、helper の DirectCall result に thunk が来る。これを root が forcing しないので漏れる。

### D. recursive closure 単独 regression が `ResidualPolymorphicBinding` で落ちる

`my sum_down(n: int): int = if n == 0: 0 else: n + sum_down (n - 1)` で `ResidualPolymorphicBinding { vars: [TypeVar("t8124")] }` が出る。型注釈を入れても解消しない。direct recursion が `MakeRecursiveClosure` を踏むのか、踏むとしても monomorphizer が型変数を残すのか、どちらかが原因。

**これはそもそも write9.md の意図する単独 regression として機能していない。** `MakeRecursiveClosure` バグの再現には `with: our loop = ...` のようなローカル名前付き再帰関数の方が適しているかもしれない。

### E. `case ({ block }).once:` の surface error

```yulang
case ({
    my n = each [1, 2, 3]
    guard: n > 1
    n
}).once:
    ...
```

これは surface diagnostics で `undefined name 'n'` を出す（CLI `--infer` でも再現）。`my n = ...` の binding が `case (block)` 形では block 内に正しく見えていない。

ただし `case work().once:` で helper 関数を介すれば surface は通る。これは write9.md 直接の問題ではないが、**block syntax の name resolution に既存バグがある**。Phase F とは独立した issue。

## 質問・相談事項

1. **Phase F.5 step 5 を実装すべきか？** root / lambda return / binding return に return type ベースで forcing を入れる方針は write8.md ではっきり示されていた。今回の helper 関数経由 reject path failure はこれをやれば解消する見込みが高い。ただし、これを入れると既存 thunk-typed return がある箇所で over-forcing するリスクがある。どこまでガードすべきか？
2. **仮説 C (`guard` を入れると thunk が外に漏れる) の正否を確認すべきか？** 確認方法: helper 内で `if-else` だけ入れ、effect 操作は無いケース、effect 操作だけ入れ if-else 無いケースで切り分け。
3. **recursive closure regression をどう書くべきか？** `with: our loop` を使った local recursive closure 形 / `\rec f -> ...` 形（あれば）など、`MakeRecursiveClosure` を確実に踏む surface 構文の選び方。

## 触っていない（write9.md からの未消化分）

- write9.md 5 章: object / executable / native-run-cps-repr-exe での確認
- write9.md 6 章: `native-undet-plan.md` / `docs/native-backend.md` の更新
- write9.md 7 章: `std::undet.list` の scalar projection
- write9.md 8 章: `.once` を non-scalar (`opt int`) のまま返すパス

これらは A の root thunk leak が解消するまで保留。

## 変更ファイル

- `crates/yulang-native/src/cps_eval.rs` — debug eprintln 削除、`ListLen` / `ListIndex` / `ListIndexRangeRaw` の CPS domain 実装
- `crates/yulang-native/src/source.rs` — 4 本の `#[ignore]` 付き regression テスト + 1 本の layer-by-layer debug テスト
