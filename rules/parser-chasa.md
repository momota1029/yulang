# `chasa` parser conventions

These rules apply to `crates/yu-syntax` code using `chasa`.

## Parser composition

- When a function already returns a `chasa::Parser`, do not wrap it again as `from_fn(|i| f(i).map(...))`. Use `f.map(...)`.
- Do not write `i.run(from_fn(some_fn))` when `some_fn` can already be called as a parser function. Use `some_fn(i)`.
- Name a `chasa::In<...>` state parameter or binding `i`, not `input`, following the library's idiom.

## `SynIn` lifetime alias

Do not spell out:

```rust
In<'_, SourceInput<...>, (), &mut ParseLocal, E>
```

in function signatures. Use `SynIn<'a, 'source, 'b, E>` from `crates/yu-syntax/src/session.rs`.

`'a`, the reborrow lifetime of `In`, and `'b`, the lifetime of `&mut ParseLocal`, are distinct and must not be collapsed. `#[derive(Reborrow)]` requires the right-hand `In<...>` to map the first slot correctly; the alias parameter names/order are otherwise only naming.

Where no lifetime must be propagated into the return type, write:

```rust
SynIn<E>
```

Where one lifetime, such as source lifetime, must be named, identify only that slot:

```rust
SynIn<'_, 'source, '_, E>
```

## Grammar design and recovery

Parser behavior, CST/AST ownership, recovery roles, byte ranges, ambient newline ownership, and dispatch promotion are design decisions. Follow the relevant `Authoritative` grammar/addendum and its gate order. Do not infer a new recovery rule locally from one failing fixture.

A parser change that affects grammar, recovery, CST/AST, diagnostics, or public dispatch requires the routing and reviews defined in `rules/agent-orchestration.md` once that policy is active.
