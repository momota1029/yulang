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
