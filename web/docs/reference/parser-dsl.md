# Parser DSL

Yulang's parser DSL builds parser values with `~"..."` and `rule { ... }`.
In a `case` arm, a parser pattern must consume the entire input string and may bind named captures.
This page covers the DSL surface and the `std::text::parse` combinators that it uses directly.
The low-level `parse` effect, custom error types, and the search and edit helpers are outside this page's scope.

## Matching in `case`

A parser pattern runs only against a string.
The arm is selected when parsing succeeds, no input remains, and its `guard`, if present, is true.
If any condition fails, `case` continues with the next arm.

```yulang
use std::text::parse::*

my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"

(request "GET users").say
(request "GET users now").say
```

The calls print `users` and `no match`.
The first `:resource` consumes `users`; the second leaves ` now`, so the parser pattern does not match the whole string.

## Compact `~"..."` form

A rule literal mixes exact text, word captures, and embedded parsers.

| Form | Result |
| --- | --- |
| `text` | Matches `text` exactly and does not bind a value. |
| `:name` | Runs `word` and binds its `str` result as `name`. |
| `{parser}` | Runs `parser` and discards its value. |
| `{name = parser}` | Runs `parser` and binds its returned value as `name`. |
| `{name = ..}` | Binds all remaining input as a `str`. |

### Word captures

`:name` is called a lazy capture in the compiler surface, but it is not a reluctant regular-expression match.
It runs `word`, which consumes one or more alphanumeric characters or underscores.
It stops before any other character and does not give characters back when a later item fails.
Adjacent word captures therefore need a literal delimiter.

### Embedded parsers and rest capture

`{name = parser}` captures the parser's returned value, not the text that it happened to consume.
The special parser `..` returns the entire remaining substring, including whitespace and punctuation.
It may return an empty string and must be the final item in its branch.

```yulang
use std::text::parse::*

my route(source: str): str = case source:
    ~":method /:resource/{tail = ..}" ->
        method + "|" + resource + "|" + tail
    _ -> "no match"

(route "GET /users/42/edit").say
(route "GET /users/").say
```

The calls print `GET|users|42/edit` and `GET|users|`.
The slash ends the `resource` word capture, and `tail` receives everything after the final slash.

## Expanded `rule { ... }` form

`rule { ... }` exposes sequences, parser values, captures, grouping, quantifiers, and alternation.
Items in one branch form a sequence.
A string literal is an exact token, while an identifier such as `word` refers to a parser value and is run by the DSL.

### Sequences and captures

Write `name = parser` to bind the value returned by one parser item.
Multiple captures produce one record whose fields become bindings in a parser-pattern arm.

```yulang
use std::text::parse::*

my pair(source: str): str = case source:
    rule { left = word ":" right = word } -> left + "/" + right
    _ -> "no match"

(pair "alpha:beta").say
```

This prints `alpha/beta`.
Both `word` parsers return strings; the literal `":"` only checks and consumes the separator.

### Quantifiers and capture values

Quantifiers attach directly to one item or parenthesized group.
Their capture types follow the combinator result.

| Form | Matches | Captured value |
| --- | --- | --- |
| `parser*` | Zero or more repetitions | `list` |
| `parser+` | One or more repetitions | Nonempty `list` |
| `parser?` | Zero or one occurrence | `opt`, with `nil` for no occurrence |

```yulang
use std::text::parse::*

my repeats(source: str): str = case source:
    rule { pieces = "ha"* } -> pieces.len.show
    _ -> "no match"

my optional_piece(source: str): str = case source:
    rule { piece = "ha"? } -> case piece:
        nil -> "nil"
        just _ -> "just"
    _ -> "no match"

(repeats "").say
(repeats "hahaha").say
(optional_piece "").say
(optional_piece "ha").say
```

The calls print `0`, `3`, `nil`, and `just`.
Even though the repeated token returns `unit`, capturing the quantified item preserves the `list unit` or `opt unit` produced by the combinator.

Repetition is greedy and does not revisit a completed match when a later item fails.
For example, `"a"*` consumes all three characters in `"aaa"` below, so the final `"a"` cannot match.

```yulang
use std::text::parse::*

my needs_final_a(source: str): str = case source:
    rule { "a"* "a" } -> "matched"
    _ -> "no match"

(needs_final_a "aaa").say
```

This prints `no match`.

### Alternation and backtracking

`left | right` is ordered alternation.
The left branch is tried first.
If it fails, the parser restores the input position from before that branch and tries the right branch, even when the left branch consumed input before failing.

```yulang
use std::text::parse::*

my alternative(source: str): str = case source:
    rule { "ab" "x" | "ab" "y" } -> "matched"
    _ -> "no match"

(alternative "aby").say
```

This prints `matched`.
The left branch consumes `"ab"` and then fails on `"x"`; the right branch restarts at the beginning and consumes `"aby"`.

Once a branch succeeds, later branches are not tried.
Full-input checking happens after that choice, so `rule { "a" | "ab" }` does not match `"ab"`: the first branch succeeds with `"a"`, then the remaining `"b"` makes the parser-pattern arm fail.

## Parser values and prefix runs

Both DSL forms produce parser values that can be passed to functions such as `read_prefix`.
The example stores a capturing `rule { ... }` value in a binding.
Unlike a parser pattern in `case`, `read_prefix` permits unconsumed input and returns it in `prefix_result.rest`.

```yulang
use std::text::parse::*

my assignment = rule { key = word "=" value = word }

case read_prefix "name=alice;rest" assignment:
    result::ok found ->
        (found.value.key + "/" + found.value.value + "/" + found.rest).say
    result::err _ -> "no match".say
```

This prints `name/alice/;rest`.
`assignment` returns a capture record, while `read_prefix` keeps the suffix that the parser did not consume.

The main combinators behind the DSL are `token`, `word`, `rest`, `choice`, `many`, `some`, and `optional`.
The lower-level effect, error, search, and rewrite APIs in `std::text::parse` are not exhaustively listed here.

## Current limits

Reluctant quantifiers `*?` and `+?` are tokenized, but lowering rejects them with `yulang.unsupported-rule-lazy-quantifier`.
Use the greedy `*` or `+` forms and structure the following parser explicitly.

The rest parser `..` is likewise accepted by the parser in a non-final position, but lowering rejects it with `yulang.rule-rest-position`.
Move `..` to the end of its branch.

A `rule` sequence may contain at most one uncaptured parser that returns a value.
`rule { word word }` parses, but lowering rejects the two returned values as an unsupported rule expression.
Capture value-producing items with `name = parser` when a sequence needs more than one.

A `{...}` interpolation in a rule literal accepts exactly one parser item at lowering.
For example, `~"{word word}"` parses but is rejected as unsupported rule-literal interpolation.
Use separate interpolations, or write the sequence in `rule { ... }` and capture its value-producing items.

## Related pages

- [Pattern Matching](./patterns) covers `case`, guards, and non-parser patterns.
- [Tour → Parser patterns](../guide/tour#parser-patterns) gives a shorter feature example.
- [Standard Library Catalogue → `std::text::parse`](./std/) locates the module among the other text APIs.
