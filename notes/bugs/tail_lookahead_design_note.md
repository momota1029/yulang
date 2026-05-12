# tail.rs の先読みヒューリスティックは外したい (設計方針メモ)

ユーザからの要求: `crates/yulang-parser/src/expr/tail.rs` L49:62 の
`next_is_tail_continuation` で行っている lookahead は最終的に **やめる方針**。

```rust
fn next_is_tail_continuation<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> bool {
    i.lookahead(from_fn(|i| {
        let led = scan_expr_led(leading_info, i)?;
        match led.tag {
            ExprLedTag::Stop | ExprLedTag::MlNud(_) => None,
            _ => Some(()),
        }
    }))
    .is_some()
}
```

これは「次の token が led かどうかで継続を判断する」場当たり的な救済で、
副作用として indent ヒューリスティックが silent に挙動を変えるケースを生んでいる
(例: [`indent_neg_silent_drop.yu`](indent_neg_silent_drop.yu))。

将来的には:

- 行頭継続のルールを「先読み」ではなく構文側のもっと素直な規則に置き換える
- もしくは tail-continuation を許す位置を明示的にする

…という方向で取り外したい、という意図。本ファイルは bug 報告ではなく、
「この hack を恒久的なものとして扱わない」という申し送り。
