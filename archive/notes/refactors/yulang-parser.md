# yulang-parser クレートのコード臭い分析

yulang-parser クレートは、パーサー/スキャナー層としてよく構成されており、モジュール分割は適切です。しかし、数か月の開発を経るなかで、いくつかの繰り返しパターンやエラー処理の不一貫性、深いネストなどが蓄積しているようです。特に `parse_*` 関数群では、sink の start/finish のネストが深くなり、エラーハンドリングが場所ごとに異なる傾向が見られます。以下は、リファクタリングの候補として挙げられるスポットです。

## 1. 繰り返されるsink start/finish のネストパターン

- **場所**: `crates/yulang-parser/src/mark/parse.rs:257-327` 及び全体を通じて
- **匂い**: Sink操作のネスト管理が深く、複数の finish() 呼び出しが離れた場所に散在

```rust
fn parse_paragraph<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    i.env.inline = false;
    let first = scan_mark(i.rb())?;
    match first.nud.tag {
        MarkNudTag::Block(_) => {
            if first.text.is_empty() {
                emit_trivia_only(&mut i, &first);
            } else {
                i.env.state.sink.start(SyntaxKind::YmParagraph);
                emit_text_trivia(&mut i, &first);
                i.env.state.sink.finish();
            }
            return Some(first);
        }
        // ... さらに複数の分岐でも同じパターン
        MarkNudTag::Inline(InlineNudTag::Newline { .. }) => {
            i.env.state.sink.start(SyntaxKind::YmParagraph);
            let stop = parse_inline_impl(i.rb(), Some(first))?;
            // ... emit
            i.env.state.sink.finish();
            Some(stop)
        }
        MarkNudTag::Inline(_) => {
            i.env.state.sink.start(SyntaxKind::YmParagraph);
            let stop = parse_inline_impl(i.rb(), Some(first))?;
            i.env.state.sink.finish();
            Some(stop)
        }
    }
}
```

**所感**: Sink のスコープが match の各arm で異なり、finish() の位置が不規則です。RAII的なウラッパーを作るか、早期リターンの際に finish() を忘れるリスクを軽減するヘルパーメソッドがあるといいかもね。69個の finish() 呼び出しが src/mark/parse.rs にあるので、このパターンが全体で相当数存在しそう。

## 2. 複数の boolean フラグによる暗黙的な状態制御

- **場所**: `crates/yulang-parser/src/context.rs:9-50` と複数の parse 関数での use
- **匂い**: Boolean 状態フラグ `ml_arg`, `inline` が複数あり、その相互作用が明確でない

```rust
pub struct Env<'a, S: EventSink> {
    pub state: &'a mut State<S>,
    pub indent: usize,
    pub mark_quote_depth: usize,
    #[reborrow(clone)]
    pub yumark_option: YumarkOption,
    pub inline: bool,
    pub ml_arg: bool,
    #[reborrow(clone)]
    pub stop: HashSet<SyntaxKind>,
}
```

**所感**: inline と ml_arg の二つの bool が、複数の parse 関数で細かく設定/参照される。実は状態機械として扱ったほうが明確かもぇ。特に pat/parse.rs の parse_tail_bp 117-120 行のような条件を見ると、これらの flag の組み合わせの意味が不透明。

## 3. 深くネストされた match-if ピラミッド

- **場所**: `crates/yulang-parser/src/pat/parse.rs:110-243`
- **匂い**: parse_tail_bp で 3-4 段階の match-if が入れ子になっており、メインロジックの把握が難しい

```rust
fn parse_tail_bp<I: EventInput, S: EventSink>(
    min_prec: Prec,
    mut leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<PatLedTag>>> {
    let mut prev_led = None;
    loop {
        if i.env.ml_arg && leading_info != TriviaInfo::None
            || i.env.inline && matches!(leading_info, TriviaInfo::Newline { .. })
            || matches!(leading_info, TriviaInfo::Newline { .. })
                && i.env.state.line_indent <= i.env.indent
        {
            return Some(Ok(Either::Left(leading_info)));
        }
        let Some(led) = /* ... */ else { return /* ... */ };
        match led.tag {
            PatLedTag::Stop => return Some(Ok(Either::Right(led.lex))),
            PatLedTag::DotField => { /* ... */ },
            PatLedTag::PathSep => {
                // 3階層目: 内部で別の scan_pat_nud, ifs, match
                let rhs_leading = led.lex.trailing_trivia_info();
                let rhs = scan_pat_nud(rhs_leading, i.rb())?;
                leading_info = if matches!(rhs.tag, PatNudTag::Atom) && rhs.lex.kind == SyntaxKind::Ident {
                    // ...
                } else {
                    // ...
                };
            }
            // ... さらに PatLedTag::KwAs, PatLedTag::Colon, etc.
        }
    }
}
```

**所感**: loop 内の match で複数のarm が各々さらに複雑な処理を含んでいます。各 arm を独立した関数に抽出するか、match の結果を構造化して処理の流れを見やすくしたほうがいいかも。

## 4. エラー処理の不一貫性：emit_invalid 呼び出しのばらつき

- **場所**: `crates/yulang-parser/src/pat/parse.rs:145-173` 等複数
- **匂い**: エラー時に emit_invalid を呼ぶ場所と呼ばない場所の区別が不明確

```rust
// parse_tail_bp で PathSep の時:
let rhs = scan_pat_nud(rhs_leading, i.rb())?;
leading_info = if matches!(rhs.tag, PatNudTag::Atom) && rhs.lex.kind == SyntaxKind::Ident {
    i.env.state.sink.lex(&rhs.lex);
    rhs.lex.trailing_trivia_info()
} else {
    emit_invalid(i.rb(), rhs.lex.clone());  // emit_invalid
    rhs.lex.trailing_trivia_info()
};

// KwAs の時:
let rhs = scan_pat_nud(rhs_leading, i.rb())?;
match rhs.tag {
    PatNudTag::Atom if rhs.lex.kind == SyntaxKind::Ident => {
        i.env.state.sink.lex(&rhs.lex);
        // ...
    }
    _ => {
        emit_invalid(i.rb(), rhs.lex.clone());  // emit_invalid もここも
        // ...
    }
}
```

**所感**: エラー処理のパターンが似ているのに、細部がすこし異なる。「不正なトークンが来たらどう処理するか」という判断基準を共通化したほうが、後で修正するときのバグを減らせるかもねぇ。

## 5. ?.unwrap() パターンによる非自明な前提条件

- **場所**: `crates/yulang-parser/src/pat/parse.rs:19,35`
- **匂い**: Option::unwrap() に頼った設計で、失敗条件が明示されていない

```rust
pub fn parse_pattern<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    Some(parse_pattern_bp(Prec::Lowest, leading_info, i)?.unwrap())
}

pub fn parse_pattern_from_nud<I: EventInput, S: EventSink>(
    i: In<I, S>,
    nud: Token<PatNudTag>,
) -> Option<Either<TriviaInfo, Lex>> {
    Some(parse_pattern_from_nud_bp(Prec::Lowest, i, nud)?.unwrap())
}
```

**所感**: parse_pattern_bp は Option<Result<...>> を返すのに、呼び出し側で ?.unwrap() しています。このパターンは、内部的には Err() が発生しないという前提条件が隠れているが、後任者にはわかりづらい。Result 型か、コメントで「内部的には成功するはず」という説明が欲しいかも。

## 6. 長い parse 関数と複数の責務

- **場所**: `crates/yulang-parser/src/mark/parse.rs:99-247` (parse_inline_impl) 
- **匂い**: 150行以上で多数の inline tag ごとの処理を含む monolithic function

```rust
/// インラインコンテンツを parse する。Block nud または closing nud で停止し、
/// その Mark を返す。env.inline = true のとき改行で InputEnd になる。
fn parse_inline_impl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    initial: Option<Mark>,
) -> Option<Mark> {
    let mut pending = initial;
    loop {
        let mark = match pending.take() { /* ... */ };
        match mark.nud.tag {
            MarkNudTag::Block(_) => { /* ... */ },
            MarkNudTag::Inline(inline_tag) => match inline_tag {
                InlineNudTag::Newline { .. } => { /* ... */ },
                InlineNudTag::Emphasis => { /* ... */ },
                InlineNudTag::Strong => { /* ... */ },
                InlineNudTag::OpenBracket => { /* ... */ },
                // ... さらに 6+ ブランチ
            }
        }
    }
}
```

**所感**: 150行近い関数で、InlineNudTag のバリアント数分の処理を持ってる。各ブランチをヘルパー関数に分割すると、各処理の flow がより明確になるかも。現状では「Emphasis の処理全体」を把握するのに関数全体を読む必要があります。

## 7. 同じ検証ロジックの繰り返し

- **場所**: `crates/yulang-parser/src/stmt/op_def.rs:64-102` and similar in enum_decl.rs
- **匂い**: `is_valid_kind()` 的なヘルパーなく、毎回 match で kind をチェック

```rust
// op_def.rs でのパターン:
let Some(paren_l) = scan_stmt_lex(after_fixity, i.rb()) else { /* ... */ };
if paren_l.kind != SyntaxKind::ParenL {
    let next = paren_l.trailing_trivia_info();
    emit_invalid(i.rb(), paren_l);
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    return Some(Either::Left(next));
}
i.env.state.sink.lex(&paren_l);

// ... その後 paren_r でも同じパターン:
let Some(paren_r) = scan_stmt_lex(after_op, i.rb()) else { /* ... */ };
if paren_r.kind != SyntaxKind::ParenR {
    let next = paren_r.trailing_trivia_info();
    emit_invalid(i.rb(), paren_r);
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    return Some(Either::Left(next));
}
```

**所感**: 「スキャン → kind チェック → エラーorlex」のパターンが何度も出てくる。ヘルパー関数 `expect_kind(kind: SyntaxKind) -> Result<...>` みたいなのを作って、コピペを削減できそう。

## 8. finish() 呼び出しの不規則な重複

- **場所**: `crates/yulang-parser/src/stmt/op_def.rs:66-102` に複数箇所
- **匂い**: エラーパスで finish() を 2回呼ぶことが頻繁、正常系との差がわかりにくい

```rust
if paren_l.kind != SyntaxKind::ParenL {
    let next = paren_l.trailing_trivia_info();
    emit_invalid(i.rb(), paren_l);
    i.env.state.sink.finish();      // 1回目
    i.env.state.sink.finish();      // 2回目
    return Some(Either::Left(next));
}
```

**所感**: 二重の finish() は、おそらく OpDefHeader と OpDef の二階層を閉じる意図だと思われますが、ドキュメント/コメント なしではエラーパス固有か shared なのか不明確。コード上で「OpDefHeader を先に finish」と順序をコメント化したほうがいいかも。

## 9. Option/Either パターンマッチの冗長性

- **場所**: `crates/yulang-parser/src/expr/control.rs:86-144`
- **匂い**: 複数の Either<TriviaInfo, Lex> のマッチで、似たようなロジックが繰り返される

```rust
pub(super) fn parse_if_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    if_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(SyntaxKind::IfExpr);
    let base_indent = i.env.indent;
    let mut arm_result = parse_if_arm(i.rb(), if_lex)?;

    loop {
        match arm_result {
            Either::Right(stop) if stop.kind == SyntaxKind::Elsif => {
                arm_result = parse_if_arm(i.rb(), stop)?;
            }
            Either::Right(stop) if stop.kind == SyntaxKind::Else => {
                let result = parse_else_arm(i.rb(), stop)?;
                i.env.state.sink.finish();
                return Some(Ok(result));
            }
            Either::Right(stop) => {
                i.env.state.sink.finish();
                return Some(Ok(Either::Right(stop)));
            }
            Either::Left(info) => {
                let can_continue = matches!(info, TriviaInfo::Space)
                    || matches!(info, TriviaInfo::Newline { indent,.. } if indent >= base_indent);
                if !can_continue { /* ... */ }
                // さらに複数の nested check
            }
        }
    }
}
```

**所感**: Either のマッチが多く、「Right で stop がある」という共通パターンが何度も出てくる。Either<A, B> に対して「OK(Right(stop)) を返す」という処理が何度も。パターンをもっと abstract できるなら、共通のヘルパーを導入してもいいかも。

## 10. 複数の similar struct でインターフェースが異なる

- **場所**: `crates/yulang-parser/src/stmt/enum_decl.rs`, struct_decl.rs など
- **匂い**: EnumVariantsBraceMachine, StructNamedFieldsBraceMachine など複数の Machine が同じ pattern だが個別実装

```rust
pub(super) fn parse_enum_variants_after_open<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    let mut machine = EnumVariantsBraceMachine;
    machine.parse_delimited_list(i, open)
}

// 同じパターンが struct_decl.rs でも:
pub(super) fn parse_struct_named_fields_after_open<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    let mut machine = StructNamedFieldsBraceMachine;
    machine.parse_delimited_list(i, open)
}
```

**所感**: これらはどちらも DelimitedListMachine を実装してる似たようなマシン。もし仕様がほぼ同じなら、ジェネリック化やテンプレート化で重複削減ができそう。差分（separator や item parsing）だけをパラメータ化する design も検討の価値あり。

## 11. scan/parse の役割分担が unclear な部分

- **場所**: `crates/yulang-parser/src/expr/scan.rs` の read_expr_nud_punct() と parse_expr_from_nud()
- **匂い**: scan が一部の tag 判定をして、parse がまた同じような判定をしている

```rust
fn read_expr_nud_punct(kind: SyntaxKind, stop: im::HashSet<SyntaxKind>) -> ExprNudTag {
    match kind {
        kind if stop.contains(&kind) => ExprNudTag::Stop,
        SyntaxKind::ParenL => ExprNudTag::OpenParen,
        SyntaxKind::BracketL => ExprNudTag::OpenBracket,
        SyntaxKind::BraceL => ExprNudTag::OpenBrace,
        SyntaxKind::Backslash => ExprNudTag::Backslash,
        SyntaxKind::Apostrophe => ExprNudTag::Apostrophe,
        _ => ExprNudTag::Stop,
    }
}

// そして parse_expr_from_nud で:
match nud.tag {
    ExprNudTag::OpenParen => {
        i.env.state.sink.start(SyntaxKind::Expr);
        delimited(i.rb(), SyntaxKind::Paren, SyntaxKind::ParenR, nud.lex)?
    }
    // ...
}
```

**所感**: scan で既に tag 判定してるのに、parse でも kind による分岐をしてる。もし scan の tag が十分な情報を持ってるなら、parse では単純に tag の match で十分なはず。逆に parse でも kind 情報が必要なら、scan の tag 設計を見直すほうがいいかも。

## 12. 未実装の TODO コメント

- **場所**: `crates/yulang-parser/src/mark/parse.rs:241, 511`
- **匂い**: TODO コメントが残されており、仕様が incomplete の可能性

```rust
// line 241:
InlineNudTag::Backslash => {
    // TODO: escape sequence / inline command
    emit_text_trivia(&mut i, &mark);
    emit_nud_lex(&mut i, &mark);
}

// line 511:
fn parse_list<I: EventInput, S: EventSink>(mut i: In<I, S>, first_mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmList);
    let mut stop = parse_list_item(i.rb(), first_mark)?;
    loop {
        match stop.nud.tag {
            MarkNudTag::Block(BlockNudTag::ListMinus | BlockNudTag::ListNum) => {
                // TODO: indent チェックで同一リストか確認
```

**所感**: Escape sequence や indent check の仕様が未実装。これらが後で追加されるときに、既存のコード構造では対応しにくくなる可能性がある。設計上の open question として、notes に記録しておくといいかも。
