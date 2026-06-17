# Yulang Examples

この directory には、現在の実装で動かせる小さな Yulang program を置いています。

English: [README.md](README.md)

まず広く眺めるなら `showcase.yu` が入口です。

```bash
yulang run examples/showcase.yu
```

個別の feature を見るなら、次の example が読みやすいです。

```bash
yulang run examples/13_console.yu
yulang run examples/01_struct_with.yu
yulang run examples/04_sub_return.yu
yulang run examples/06_undet_once.yu
yulang run examples/10_effect_handler.yu
yulang run examples/12_cast.yu
```

`examples/11_attached_impl.yu` は attached impl の意図を示す fixture として残しています。
role method の runtime specialization を詰めている間は、実行 example の一覧からは外しています。

型検査と public type の確認には `check` を使います。

```bash
yulang check examples/01_struct_with.yu
```

repository checkout から直接実行する場合は、同じ command を `cargo run` 経由で
呼べます。

```bash
cargo run -q -p yulang -- run examples/showcase.yu
cargo run -q -p yulang -- check examples/01_struct_with.yu
```
