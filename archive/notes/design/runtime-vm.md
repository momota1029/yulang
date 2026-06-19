# Runtime VM Notes

## Current Direction

- Runtime IR is the VM input.
- Monomorphization should remove remaining polymorphic use sites before execution.
- Effects are represented as thunks plus handlers in runtime IR.
- The VM interpreter is the reference execution engine for now.

## Recent Fixes

- Pattern defaults are runtime expressions, not type-only metadata.
- Default expressions must participate in reachability and monomorphization.
- Pattern binding needs access to the interpreter when it evaluates defaults.

## Things To Watch

- `&record.field = ...` still has fragile spots around runtime lowering.
- Effectful defaults may expose gaps in pattern-binding continuation handling.
- Reachability needs to include every expression stored inside patterns and handlers.
- Nondeterministic search currently clones continuations that own `Expr`, handler
  arms, and `Env` data.  Wide `.once` searches such as three independent
  `each 1..` ranges can be fine on native builds but overflow browser Wasm
  stacks.  Until the VM is replaced or refactored, examples should constrain
  infinite choices early (`b = each a<..`, `c = each b<..`).  A deeper fix is to
  make continuation frames share expression and handler data by reference.
