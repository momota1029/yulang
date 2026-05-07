# Native Backend TODO

目的: 現在の VM を参照実装とデバッグ対象として残しながら、Yulang プログラムを
CPS 風 lowering 経由で Cranelift にコンパイルする。

## 目標の形

```text
Core / runtime IR
  -> 明示的な control/effect 表現
  -> CPS または CPS 風 continuation lowering
  -> closure/environment 表現
  -> Cranelift IR
  -> native object / executable / JIT
```

## 最初の設計上の問い

- どの IR 境界から CPS lowering に入るか。
- 最初の control IR は direct-style ANF、CPS、小さな continuation graph のどれに近いか。
- algebraic effects、resumptions、`bind_here` を continuation にどう対応させるか。
- closure / environment layout はどうするか。
- runtime value representation をどうするか。
  - ints
  - floats
  - bools
  - unit
  - strings
  - lists
  - records
  - variants
  - closures
  - effect continuations
- native code を source example と照らしてデバッグできるようにするには、
  どの程度の metadata が必要か。

## 最初の slice

- `notes/design/native-backend-plan.md` を書く。
- pure first-order subset を選ぶ。
- primitive numeric/string operations をコンパイルする。
- direct call をコンパイルする。
- representation がすでに明確な場合だけ、simple records / variants をコンパイルする。
- 同じ小さな example を VM と native backend の両方で動かす。

## 後の slice

- closures と captured environments
- tail calls と continuation allocation policy
- algebraic effect operations
- handler / resumption representation
- host request boundary
- debug symbols または source-position metadata
- CLI 実験用の JIT mode

## 最初の slice でやらないこと

- VM を消さない。
- すべての runtime feature を一度にコンパイルしない。
- representation boundary が明確になる前に最適化しない。
- native backend design を playground 専用の挙動に依存させない。

## Benchmark

- 同じ example で VM と Cranelift を比較する benchmark path を追加する。
- compile time と execution time を分けて出す。
- startup latency 用の小さな benchmark と、generated code behavior 用の大きめの
  example を両方残す。
