# REPL（対話環境）TODO

状態: **未着手・要設計時間**。

## 現在わかっていること

- 累積 script を毎回 recompile すれば、effect row / nondet は現行モデルを流用できる。
- この形では、それまでの副作用も入力ごとに毎回再実行する。
- 未入力を effect handler と同様の continuation suspend/resume と見て、
  compile/run 境界を溶かす案は未検証である。

## 現在の扱い

公開準備 track 0〜8 の順序には含めず、将来の設計項目として保留する。
