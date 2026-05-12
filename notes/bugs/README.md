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

カテゴリ別 index は [`index.md`](index.md) を参照する。

2026-05-13 時点では、`index.md` の項目は未解決 bug 一覧ではなく、
修正済み挙動や期待 diagnostic の回帰確認メモとして残している。

## 解決方針

- snippet が動くようになったら、まず `examples/` か `notes/diagnostics/` か
  parser/infer のテストに昇格できないか考える
- 修正後は該当 snippet をこのディレクトリから外す（または「解決済み」セクションへ移す）
