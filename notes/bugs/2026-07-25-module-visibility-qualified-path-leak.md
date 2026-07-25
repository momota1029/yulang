# module 可視性: 修飾パス経由で `my` メンバーが読める

発見日: 2026-07-25
状態: 未修正
発見経緯: test facility 設計のための module system 調査中に副次的に発見

## 症状

module のメンバー可視性が、アクセス形式によって一貫しない。

`use` によるインポートは `my` を正しく拒否するが、`child::name` という直接の修飾パス参照は
同じ `my` メンバーを読めてしまう。

## 再現

```yu
mod child:
    my hidden = 41

child::hidden
```

```console
$ yulang --std-root lib --no-cache run --print-roots repro.yu
run roots [41]
```

`my` で宣言されたメンバーが、module 外から読めている。

### 対照 1: `use` 形式は正しく拒否する

```yu
mod child:
    my hidden = 41

use child::hidden
hidden
```

```console
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name in root expression: hidden
```

### 対照 2: `pub` メンバーは当然通る

```yu
mod child:
    pub visible = 41

child::visible
```

```console
run roots [41]
```

対照 1 と本体の再現は、同じ非公開メンバーに対して結果が食い違っている。

## 期待される挙動

`my` は「同一 band 内でも import 不可、cross-band export 不可」と定義されている。
そうであれば、外部 module からの直接修飾参照も拒否されるべきである。

## 原因の所在

`ModuleTable::value_path_at`（`crates/infer/src/module_table/mod.rs`）が、
prefix を持つ修飾パスの解決で、可視性フィルタを持たない `value_at` を先に引いている。

```rust
let target = self.module_path_with_imports_from(module, prefix, site)?;
self.value_at(target, last, module_path_site())
    .or_else(|| self.exported_value_at(target, last))
```

フィルタ付きの `exported_value_at` はフォールバック側にあるため、非公開メンバーが先に一致すると
そのまま返る。

同じ関数が prefix を持たない場合に使う `lexical_value_at` も `value_at` を使うが、そちらは
現在 module とその祖先を辿る経路であり、自分および親の非公開束縛が見えるのは意図された挙動である
（子 module が親の `my` を参照できることは別途確認済み）。問題は、他 module への修飾参照に
同じ無フィルタ経路を使っている点にある。

## 影響

`my` は、同一コンパイルグラフ内の呼び出し元に対して実効的なカプセル化を提供していない。
呼び出し元が module パスを綴れる限り、非公開メンバーを読める。

型健全性の穴ではなく、可視性契約の穴である。実行時エラーや誤った値は生じない。

ただし `my` / `our` / `pub` は言語の公開表面の一部であり、その意味が
アクセス形式によって変わる状態は、安定版として公開する前に解消しておきたい。

## 判断が必要な点

修正に着手する前に、次を確定する必要がある。

- `my` を「参照不可」と定義するのか、「import 不可だが綴れば読める」と定義するのか。
  前者なら本件はバグであり、後者なら `use` 側の拒否と合わせて仕様として明文化する必要がある。
- 現行の std / examples / tests に、この経路へ依存している箇所があるか。
  修正を活性化する前に測定すること。

## 関連

- 現行の可視性実装: `crates/infer/src/module_table/query.rs`
- 併せて確認された別の制約: `my mod child:` は現行の statement parser で module 宣言として
  解釈されない（`our mod` / `pub mod` は動作する）。完全に非公開な module を綴る手段が
  surface に存在しない。
