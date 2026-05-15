# Native Direct-Style Islands

This note records the planned route from optimized CPS representation to
Cranelift-friendly direct style / SSA regions.

The goal is not to abandon CPS. CPS remains the semantic representation for
handlers, resumptions, thunk hygiene, local returns, and loop control. The goal
is to identify regions where those control features are not dynamically active,
then lower those regions as ordinary direct-style SSA instead of paying the
runtime cost of closure / thunk / continuation calls.

## Core idea

The optimizer should split a CPS repr ABI function into two kinds of regions:

- **control regions** that still need CPS control frames, dynamic handler search,
  thunk boundary evidence, or resumption capture;
- **direct-style islands** where every jump target, call target, and value lane
  is concrete enough to map to Cranelift blocks, block parameters, and ordinary
  calls.

The safe first target is an island made only of:

- `Literal`
- pure structural value construction and projection
- `Primitive`
- `DirectCall` whose target is known and whose result is not effectful at the
  call site
- `Continue`
- `Branch`
- `Return`

These nodes already look close to SSA. `Continue` becomes a block jump, `Branch`
becomes a conditional branch, continuation parameters become block parameters,
and statement destinations become SSA values in the current block.

The island must stop at:

- `Perform`
- `EffectfulCall`
- `EffectfulApply`
- `EffectfulForce`
- `InstallHandler` / `UninstallHandler`
- `Resume` / `ResumeWithHandler`
- `ForceThunk` unless the thunk target is proven local, non-escaping, and pure
- `ApplyClosure` unless the closure target has been reified to a known direct
  call
- escaping `MakeThunk` / `MakeClosure` / `MakeRecursiveClosure`

This boundary keeps the semantics simple: effectful control stays in CPS,
effect-free local computation becomes SSA.

## Why this should be fast

Today, even simple code can carry administrative CPS shape:

```text
make closure
apply closure
continue k
return param
```

The current optimizer already removes some of this:

- forwarding continuations
- empty return continuations
- primitive wrappers
- local partial-application closure calls
- small one-shot continuation calls
- dead pure statements

Direct-style islands are the next generalization. Instead of rewriting one
statement at a time, the optimizer can recognize that a whole connected
subgraph has no dynamic control effect, then codegen it as a normal SSA CFG.

That should make common code approach the value backend path:

- no heap closure allocation for non-escaping partial applications
- no indirect closure call for known callees
- no continuation function call for local `Continue`
- no runtime handler search in pure regions
- no thunk object when the thunk is a local, single-force adapter and its
  hygiene frame is irrelevant to the island

Cranelift can then do the usual work: instruction selection, register
allocation, constant folding, and local scalar optimization.

## Eligibility analysis

Add a CPS optimization analysis that computes, per continuation:

```text
ContinuationClass =
  DirectIslandCandidate
  ControlBoundary(reason)
```

A continuation is a candidate when:

- it has no handler install/uninstall statements;
- it has no effectful terminator;
- all called continuations through `Continue` / `Branch` are in the same
  candidate SCC or are an island exit;
- all `DirectCall` targets have a known direct ABI and do not require effectful
  resume frames at that call site;
- any `MakeClosure` / `MakeThunk` result is either dead or consumed by an
  already-recognized local reification pass;
- all values crossing the island boundary have known ABI lanes.

The analysis should be structural. It must not depend on std module paths,
function names, or fixture names.

## Island shape

An island is a connected continuation subgraph:

```text
entry continuation
  -> local continuation blocks
  -> exits
```

Inside the island:

- continuation ids become block ids;
- continuation params become block params;
- statement destinations become SSA values;
- `Continue(target, args)` becomes `jump target(args)`;
- `Branch(cond, then, else)` becomes `brif cond, then(), else()`;
- `Return(value)` returns to the surrounding CPS function or direct native
  function result.

An island can have one of these exit kinds:

- ordinary return;
- call into a remaining CPS control boundary;
- fallback to existing CPS repr Cranelift lowering for an unsupported edge.

The first implementation can support only ordinary return and internal
`Continue` / `Branch`. That is enough to make many pure helper functions and
post-reification partial applications cheap.

## Partial application and ordinary functions

The current local pass rewrites this shape:

```text
MakeClosure c, wrapper
ApplyClosure r, c, x
```

when `wrapper` is:

```text
wrapper(param):
  y = DirectCall target(captured..., param)
  return y
```

or the same shape after primitive-wrapper reification:

```text
wrapper(param):
  y = Primitive op(captured..., param)
  return y
```

Direct-style islands make this stronger:

- if the closure value is non-escaping within an island, represent it as
  `(known target, captured SSA values)` rather than a heap object;
- when the final argument arrives, emit a direct call or primitive statement;
- if a closure crosses an island boundary, materialize the ordinary CPS closure
  object there and stop optimizing through it.

This gives a principled version of "partial application is not a thunk". It is
a known callable value while it stays local, and it becomes a runtime closure
only when it actually escapes.

## Thunks

Thunks need a stricter rule than closures because thunk boundary hygiene is
observable.

A thunk can be lowered inside an island only when all of these hold:

- it is non-escaping;
- it is forced in the same island;
- the force is single-use or one-shot;
- its body does not perform or cross a handler/delimiter boundary that matters;
- removing the object does not remove required hidden-effect evidence.

Otherwise the thunk must remain a CPS thunk pointer, even if its body is small.

This preserves the earlier decision: no source-level `lazy` keyword is needed.
The optimizer sees typed/lowered thunk adapters and removes only the cases that
are semantically ordinary computation.

## Suggested implementation order

1. **Island classifier**
   - Walk each CPS repr ABI function.
   - Mark direct-compatible continuations.
   - Record boundary reasons for trace output.

2. **CFG island builder**
   - Group candidate continuations into direct islands.
   - Start with single-entry, ordinary-return islands.
   - Keep multi-entry or control-boundary exits unsupported at first.

3. **Cranelift block codegen path**
   - Add a codegen helper that emits an island as Cranelift blocks.
   - Reuse the existing ABI lane and statement lowering for literals,
     primitives, structural values, direct calls, branches, and returns.

4. **Closure scalar replacement inside islands**
   - Track non-escaping `MakeClosure` as `(entry, captured values)`.
   - Reify `ApplyClosure` to direct calls across local block boundaries, not
     only within one continuation.

5. **Thunk scalar replacement inside islands**
   - Only for non-escaping, single-force, hygiene-neutral thunks.
   - Leave all boundary-bearing or effectful thunks in CPS form.

6. **Profile and regression**
   - Add optimizer counters:
     - `direct_style_islands`
     - `direct_style_continuations`
     - `scalar_replaced_closures`
     - `scalar_replaced_thunks`
   - Add source regressions for ordinary arithmetic, `map` / `fold`-like
     higher-order helpers, and partial applications that do not escape.

## Safety invariants

- Direct-style lowering is an optimization, not a new semantics.
- If an island cannot be proven safe, leave it in CPS form.
- Handler / delimiter / hidden-effect evidence is never erased by the island
  classifier.
- Multi-shot resumptions stay in CPS unless a later proof shows a region has no
  capture point.
- Closure and thunk scalar replacement requires non-escape evidence.
- The optimizer must be driven by IR shape, lanes, effect/control evidence, and
  escape information, not by std paths or names.

## Open questions

- Whether the island IR should be an explicit intermediate structure or a
  codegen-side view over CPS continuations.
  The safer first version is a view, because it keeps existing CPS fallback
  intact.
- How much alias analysis is needed before closure scalar replacement can cross
  records/lists.
  The first version should not cross structural storage.
- Whether island calls to direct functions should inline small callees before or
  after island construction.
  The first version should keep calls explicit and let Cranelift handle normal
  call lowering.
