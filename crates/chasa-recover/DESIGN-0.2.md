# chasa-recover 0.2 core

## Scope

This is a deliberately small, breaking redesign of the experimental 0.1
crate. Its job is to make the two parser outcomes explicit:

1. `None` is a non-match and preserves the input position.
2. `Some(output)` is a normal parser result. Recovery is represented inside
   `output`; it is not a second error channel.

The prototype only establishes the core transaction and composition rules. It
does not migrate Yulang's production parser, define its boundary model, or
replace Yulang's authoritative flat `OperatorChain` expression representation.

## Core API

```rust
trait ParserOnce<I, R, S> {
    type Output;
    fn run_once(self, input: In<I, R, S>) -> Option<Self::Output>;
}
```

`I` is input, `R` is recoverable parser-local state, and `S` is non-recoverable
simple state. `R` and `S` implement `reborrow_generic::short::Rb`; `In<'a, I, R, S>`
stores `R::Target<'a>` and `S::Target<'a>` and derives `Reborrow`. Its
constructor accepts those targets directly, and `In::rb()` creates short
parser calls. `S` is intended for a sink such as a Rowan builder. The ordinary
parser grammar operates at `S = ()`.

`In<I, R, S>::map(parser, mapping)` is an ordinary output-only mapping. It
runs a unit-state parser through `check`, then calls
`FnOnce(O1) -> O2` only on success. The mapping never receives `In`.

`In<I, R, S>::then(parser, continuation)` is the central owned procedural
primitive. It also runs a unit-state parser through `check`; on success its
total callback has the exact shape
`FnOnce(O1, In<I, R, S>) -> O2`: it receives a successful parsed value and the
owned input with its requested state, then returns an output directly.
`ParserOnce::then` is a thin state-lifting wrapper which delegates to this
primitive. For `S != ()`, the grammar methods are absent. `S = ()` is an
intentional committed procedural escape hatch: the callback may inspect or
consume grammar input, but its direct `O2` return cannot propagate a `None`
through `In::then` or `ParserOnce::then` (an `Option<T>` chosen as
`O2` is wrapped as `Some(Option<T>)`). It therefore cannot cause grammar
backtracking. There is intentionally no `bind`, `flat_map`, or `and_then`.

`ParserOnce::map_once`, `map_mut`, and `map` are ordinary output-only mapping
operations using `FnOnce`, `FnMut`, and `Fn`, respectively. They preserve the
parser state type and do not receive `In`.

Tuple parsers are implemented only for `S = ()`. A tuple is transactional: if
any member non-matches, the whole tuple restores its initial input and
recoverable-state marks before returning `None`. A grammar parser that has
crossed its local commit frontier must recover into `Some(...)`, rather than
returning `None`.

`choice((p, q, ...))` is likewise available only for `S = ()`, with tuple
arities one through eight. Each alternative is run through `check`. The first
success commits; when every alternative returns `None`, choice restores its
outer input and recover-state checkpoint before returning `None`.

## Recover state and reborrowing

`Recover` is the static capability used by generic parser code:

```rust
trait Recover: Rb {
    type Mark;
    fn mark<'a>(this: Self::Target<'a>) -> Self::Mark;
    fn rollback<'a>(this: Self::Target<'a>, mark: Self::Mark);
}
```

Concrete mutable state normally implements the ergonomic `Recoverable` trait,
which is bridged to `Recover` for `&mut T`. Consequently a parser spells its
recover state as `In<I, &mut State, S>`. Calls use `R::shorten(_mut)` and
`S::shorten(_mut)` when the corresponding target must be moved into a shorter
scope; `In::rb()` reborrows the complete handle for a short parser invocation.

`Recover::Mark` is a passive snapshot. Taking a mark acquires no active
resource, nested marks remain valid, and success commits by dropping the mark.

## `None` contract and `check`

Arbitrary Rust procedures can still consume input and return `None`, so the
type system cannot prove the contract. A `FnOnce(In<I, R, ()>) -> Option<O>`
is itself a `ParserOnce`; that direct unit-state function implementation is the
runtime boundary for the input contract. It is intentionally unavailable for a
non-unit `S`, because `S` is not rollbackable and must not be mutated by a
fallible parser:

1. it records the input's current `Index`;
2. it records an `R` marker, then runs the function through a short `In::rb()`;
3. `Some(output)` commits normally;
4. on `None`, it rolls `R` back, compares `Input::Index`, and panics if it
   changed.

`In<I, R, ()>::check(parser)` preserves the readable procedural grammar
spelling. It delegates to the parser; direct unit-state functions and
structural combinators own their transactions. `check` neither marks nor
compares input and never corrects input after a contract violation. `R`
rollback is semantic, not a debug equality check; an `R` implementation is
expected to use an inexpensive marker such as a log length when it needs
transactional effects.

A caught contract panic poisons the wider parser invocation. It leaves the
violating cursor advanced and does not promise tuple-wide unwind restoration
for successful work performed before that scope. Parsing must not resume from
the wider invocation after catching such a panic.

For `&str`, `Index` is the current suffix pointer (`*const u8`). This is an
O(1) cursor identity, not a text comparison or a source-offset API. A caller
that needs source ranges owns the source-relative offset policy separately.
For every `Input`, `Index` equality must mean the same reachable cursor
position during a transaction. That opaque cursor identity is the sole
equality requirement; neither input contents nor `R` are compared.

## Minimal input trait

```rust
trait Input {
    type Item;
    type Mark;
    type Index: Eq;

    fn next(&mut self) -> Option<Self::Item>;
    fn mark(&self) -> Self::Mark;
    fn rollback(&mut self, mark: Self::Mark);
    fn index(&self) -> Self::Index;
}
```

No clone, equality, ordering, general backtracking combinator, or multi-pass
parser trait is part of the 0.2 core. The initial input implementation is
`&str`; general input abstractions must earn their complexity through a later
use case.

## Acceptance checks for this prototype

- a successful tuple consumes normally;
- a non-matching tuple restores both input and `R`;
- a choice rolls back each failed alternative and its all-`None` outer scope;
- a direct unit-state function parser rolls `R` back and panics for a buggy
  consume-then-`None` procedure using only pointer identity for `&str`,
  without correcting the cursor;
- `In::map` maps only successful grammar output and does not expose `In`;
- `In::then` runs its total continuation only after grammar success and can
  write an output sink;
- parser `then` delegates to `In::then`, so a consume-then-`None` grammar procedure
  rolls back `R`, leaves its cursor advanced, and panics;
- ordinary `map_once`, `map_mut`, and `map` transform parser output without
  becoming state-lifting or monadic composition;
- `In::rb()` witnesses short repeated access to reborrowed `R` and `S`;
- no `bind`, `flat_map`, or `and_then` API is exposed.

These checks certify only the isolated prototype. They do not authorize or
verify a Yulang parser migration.
