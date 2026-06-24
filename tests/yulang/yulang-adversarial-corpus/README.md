# Yulang adversarial corpus

2026-06-24 の `momota1029/yulang` の仕様・hardening notes・regression tests をもとにした、破綻点探索用の小さな corpus。

これは確認済み不具合の一覧ではない。狙っているのは、型健全性、handler hygiene、solver 停止性、public projection、VM と interpreter の一致である。

## 期待する契約

| file | 期待 | 壊れ方の例 |
|---|---|---|
| `01_recursive_data_position_replay.yu` | `check` が短時間で終了し、`box.spin` の公開型に `AllExcept` や handled `tick` が漏れない | hang、replay 数の発散、private evidence leak |
| `02_repeated_callback_hygiene.yu` | 実行結果が `6`。内側 `strip_tick` は unannotated callback 由来の `tick` を奪わない | `0` などになり callback effect を誤捕捉 |
| `03_parameterized_effect_capture.yu` | `check` は短時間で終了してよいが、実行は拒否される。同じ effect path `ask.get` を `int` / `str` の別 operation として扱ってはいけない | effect family の型引数を見て同じ path を複数 operation のように扱う、誤捕捉、型衝突を実行まで見逃す |
| `04_computed_scc_cycle.yu` | `check` が有限時間で computed-binding SCC の診断を出す。現状の CLI exit は `0` | hang、`Any` / `Never` による循環隠し、誤った一般化 |
| `05_value_restriction_closure_ref.yu` | `check` は通りうるが、実行は拒否される。computed closure を作って同じ ref を多相利用できてはいけない | computed closure を use-site ごとに一般化し、同じ ref を `int` と `bool` で利用 |
| `06_multishot_ref_after_fork.yu` | VM と interpreter が一致し、各 branch が `(false, 1)` / `(true, 1)` | continuation clone 後に作る ref cell の共有、backend 差 |
| `07_polymorphic_recursion_termination.yu` | `check` は短時間で終了してよいが、実行は拒否される | recursive type の無限展開、specialization demand の発散 |
| `08_two_private_data_tails.yu` | `check` 成功。`box.handle_both` の公開型に `#...` / `AllExcept` / handled `tick` が漏れず、residual は落ちない | private tails の混同、片方の residual 消失、evidence leak |

`02` の `6` は、再帰深さ 3 で callback を 2 回ずつ呼ぶためである。`03` は同じ path の item を一つの operation として扱う仕様を確認する。型引数違いの operation が必要なら、別名の effect item を定義する。`05` は computed closure が use-site ごとに一般化されないことを見る。`06` は effect request の後で ref を作るので、各 resumed branch に fresh cell が必要になる。

## 実行

リポジトリ root で先に binary を作る。

```sh
cargo build -q -p yulang
YULANG=./target/debug/yulang ./path/to/yulang-adversarial-corpus/probe.sh
```

個別には次の形で確認できる。

```sh
timeout 20s ./target/debug/yulang check FILE.yu
timeout 20s ./target/debug/yulang run --no-cache --print-roots FILE.yu
timeout 20s ./target/debug/yulang run --no-cache --print-roots --interpreter FILE.yu
```

solver metrics を見る build では、`01` と生成した deep-apply family を比較する。

```sh
python3 gen_deep_apply.py 16  > /tmp/deep-16.yu
python3 gen_deep_apply.py 32  > /tmp/deep-32.yu
python3 gen_deep_apply.py 64  > /tmp/deep-64.yu
python3 gen_deep_apply.py 128 > /tmp/deep-128.yu

# repository 内部の hardening command
for f in /tmp/deep-{16,32,64,128}.yu; do
  timeout 60s cargo run -q -p yulang -- --std-root lib check-poly-std "$f"
done
```

`constraint.replay_generated`、`constraint.replay_accepted`、`constraint.max_replay_*` が深さに対して急激に跳ねるかを見る。`01` では、同じ static boundary を巡る weighted var-var alias が停止する一方、異なる residual を誤って同一視していないことも見る。
