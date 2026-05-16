# notes/bugs

「本来ならばちゃんと実行できそうなのに動かない」例を集める。
ここは仕様議論・将来計画とは別で、**今の実装で素朴に書いたら詰まる** ことを
最小再現 snippet として残す場所。

## 使い方

各 snippet は `.yu` ファイルとして実行・確認できる形にしておく。

```bash
cargo run -q -p yulang -- --run notes/bugs/<file>.yu
# 型推論だけ見たい時
cargo run -q -p yulang -- --infer notes/bugs/<file>.yu
```

## ファイル一覧

- [`index.md`](index.md) — 現在の未解決 bug。
- [`solved/index.md`](solved/index.md) — 解決済み snippet の退避先 (回帰
  確認のための `.yu` ファイル付き)。

2026-05-16 時点では、解決済みを `solved/` 子フォルダに切り出して、本
ディレクトリ直下には今の build で再現する snippet だけを置く運用にした。
回帰したら `solved/` から元に戻す。

## 解決方針

- snippet が動くようになったら、まず `examples/` か `notes/diagnostics/` か
  parser/infer のテストに昇格できないか考える
- 修正後は該当 snippet をこのディレクトリから外す（または「解決済み」セクションへ移す）
