# chasa-recover 0.2

`chasa-recover` は、回復を通常の構文値として扱う、小さな一回実行パーサの
実験的コアです。0.2 では `ParserOnce<I, R, S>` が
`Option<Output>` を返します。

- `None` は非一致であり、入力位置を保存します。
- `Some(output)` は通常の結果です。回復済み構文も `output` に含めます。
- `R` は非一致時に rollback する状態、`S` は Rowan builder などの非 rollback stateです。
- `R` と `S` は `reborrow-generic` の `Rb` target として `In` に格納されます。
- tuple parser は `S = ()` にだけ実装され、非一致時に tuple 全体を戻します。
- `In::map` は `S = ()` の文法を `check` し、成功時だけ parser output を
  `FnOnce` へ渡します。
- `In::then` は成功時だけ全関数へ `(output, In<I, R, S>)` を渡す
  committed procedural continuation です。
- parser の `then` は `In::then` へ委譲する state-lift wrapper です。
- `map_once` / `map_mut` / `map` は parser の通常出力だけを写します。
- `choice` は `S = ()` の候補を左から順に transactional に試します。

`FnOnce(In<I, R, ()>) -> Option<_>` はそのまま grammar parser であり、`None` を返した
ときに入力を消費していれば安価な opaque cursor identity だけを比較して panic します。
`None` なら `R` も marker へ rollback します。`&str` では現在の suffix pointer を使い、
入力内容や `R` の等値比較は行いません。`check` は読みやすい実行入口であり、input を
矯正しません。`S` を持つ stateful work は `then` の total callback で行います。

```rust
use chasa_recover::parser::item;
use chasa_recover::{In, ParserOnce};

let mut source = "ab!";
let recovery = ();
let mut sink = String::new();

let parser = (item('a'), item('b')).then(
    |(a, b), input: In<&str, (), &mut String>| {
        input.state.push(a);
        input.state.push(b);
    },
);

let output = parser.run_once(In::<_, (), &mut String>::new(
    &mut source,
    recovery,
    &mut sink,
));
assert_eq!(output, Some(()));
assert_eq!(source, "!");
assert_eq!(sink, "ab");
```

独自の recover state はデータ側へ `Recoverable` を実装し、parser の `R` には
`&mut State` を指定します。`In::rb()` で短い parser call を作れます。

```rust
use chasa_recover::{In, Recoverable};
use reborrow_generic::Reborrow as _;

#[derive(Default)]
struct Log(Vec<char>);

impl Recoverable for Log {
    type Mark = usize;

    fn mark(&self) -> usize {
        self.0.len()
    }

    fn rollback(&mut self, mark: usize) {
        self.0.truncate(mark);
    }
}

let mut source = "";
let mut log = Log::default();
let mut sink = String::new();
let expected_index = source.as_ptr();
let mut input = In::<_, &mut Log, &mut String>::new(
    &mut source,
    &mut log,
    &mut sink,
);

let short = input.rb();
assert_eq!(short.index(), expected_index);
```

通常の output mapping と grammar choice は state lift を行いません。

```rust
use chasa_recover::parser::{choice, item};
use chasa_recover::{In, ParserOnce};

let mut source = "b!";
let output = In::<_, (), ()>::new(&mut source, (), ()).map(
    choice((item('a'), item('b'))),
    |item| item.to_ascii_uppercase(),
);

assert_eq!(output, Some('B'));
assert_eq!(source, "!");
```

## 0.1 からの破壊的変更

0.2 は 0.1 の API と互換ではありません。`Result` / `Err` による回復出力、
複数回実行用の `Parser` / `ParserMut`、`many` / `recover` 系 combinator は
削除されました。`then` は全関数による committed state lift であり、monadic な
`bind` / `flat_map` / `and_then` は提供しません。
回復不能な非一致は `None`、回復された構文は `Some(output)` で表します。

この crate は分離された prototype です。Yulang production parser の移行は
この crate の追加では承認されません。

詳しい transaction と composition の規則は [DESIGN-0.2.md](DESIGN-0.2.md)
にあります。
