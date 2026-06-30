# ChatGPT Pro consultation: local mutable ref and loop runtime plan

Paste the answer here:

- `notes/research/consultation/2026-06-30-local-ref-loop-runtime-answer.md`

## Question

I am working on Yulang, a language with algebraic effects, effect rows, handlers, and a current interpreter called Evidence VM. I need an architecture-level review, not a small benchmark-specific trick.

Please answer in Japanese. Please be concrete and engineering-oriented. I want a plan that can be implemented safely in stages.

## Current measurements

All numbers below are from warm source-key release runs using:

```sh
target/release/yulang run --runtime-phase-timings --print-roots <file>
```

Representative runtime_execute values:

- `bench/nondet_20_discard.yu`
  - `(each 1..20 + each 1..20).list`
  - about `9.4ms / 10.1ms / 10.3ms / 10.1ms / 9.9ms`
- `bench/loop_recursive_20_discard.yu`
  - handwritten recursive nested loop building a list by append
  - about `1.9ms / 1.8ms / 1.7ms / 1.9ms / 1.8ms`
- `bench/loop_recursive_sum_20_discard.yu`
  - handwritten recursive nested loop computing a sum
  - about `1.6ms / 1.6ms / 1.4ms / 1.5ms`
- `bench/loop_for_no_ref_20_discard.yu`
  - std `for` nested loop, no local mutable ref
  - about `6.1ms / 6.2ms / 6.4ms / 6.9ms / 6.0ms`
- `bench/loop_for_sum_ref_20_discard.yu`
  - std `for` nested loop with `my $total = 0` and `&total = $total + i + j`
  - about `1.994s / 1.847s / 2.042s`
- `bench/loop_for_20_discard.yu`
  - std `for` nested loop with `my $xs = []` and `&xs.push(i + j)`
  - about `2.043s / 1.875s / 2.065s`

The conclusion so far:

- Pure recursive loops are not catastrophically slow.
- `for` itself is slower than recursive code, but not the 2-second problem.
- The catastrophic case is `for` plus local mutable ref updates.

## Current local mutable ref lowering

Yulang source:

```yu
{
    my $total = 0
    for i in 1..20:
        for j in 1..20:
            &total = $total + i + j
    ()
}
```

lowers roughly to:

```text
let #total = 0
let &total = &total#...::var_ref()
&total#...::run #total {
    for_in 1..20 (\i ->
        for_in 1..20 (\j ->
            &total := &total.get() + i + j))
    ()
}
```

The generated local var act follows the std shape:

```yu
pub act ref_update 'a:
    pub update: 'a -> 'a

pub type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
    pub r.update(f: 'a -> 'a): ['e] () =
        my loop(x: [_] _) = catch x:
            ref_update::update v, k -> loop:k:f v
        loop:r.update_effect()

pub act var 't:
    pub get: () -> 't
    pub set: 't -> ()

    my var_ref(): ref '[var 't] 't = ref {
        get: \() -> get(),
        update_effect: \() -> set:ref_update::update:get()
    }

    my run(v: 't, x: [_] 'r): 'r = catch x:
        get(), k -> run v: k v
        set v, k -> run v: k()
```

The VM has `RefSet` frames. Assignment evaluates the reference, forces the assigned value, projects `update_effect`, calls it, and then handles `ref_update::update` by resuming with the assigned value. For local refs, this means every update goes through:

- record field selection,
- `update_effect()` call,
- `ref_update::update` request,
- local `get` request,
- local `set` request,
- catch/resume machinery.

That seems to explain the 2-second loop.

## Important semantic constraints

Please do not suggest any plan that relies on benchmark names, file paths, source names, or special casing `for` bodies by string matching.

Yulang must preserve these properties:

- `std.control.var.ref` is a normal public reference abstraction.
- A local ref like `&total` can escape into closures or records and still work.
- Some refs are not local cells:
  - file refs,
  - record/list/string projected refs,
  - refs implemented by user code through `get` / `update_effect`.
- `ref.update` intentionally uses the `ref_update` effect so nested projections can update a focused subvalue.
- Algebraic effects and handlers are real language features, not just implementation details.
- Multi-shot or captured continuations may interact with state. If direct mutable cells change semantics here, the plan must say what restriction, snapshot, or representation is needed.
- The implementation should not weaken handler hygiene / marker / provider semantics.
- Runtime optimizations should be cause-side fixes, not downstream patching of observed output.

## Existing candidate idea

One tempting idea is to add a runtime value such as `LocalRefCell` and make local `my $x` allocate a VM-local cell. Then:

- `$x` / `ref.get` can read the cell directly,
- `&x = value` can write the cell directly,
- `&x.update(f)` can apply `f` to the current cell value and write back,
- escaped `&x` remains a value pointing to the cell.

But this has risks:

- current lowering models local vars as algebraic effects with `run`;
- captured continuations might need state snapshots, rollback, or shared-cell semantics;
- local refs must remain compatible with public `std.control.var.ref`;
- direct cell operations might need to coexist with generic `update_effect`.

## What I need from you

Please propose a concrete plan.

Questions to answer:

1. Is a VM-level `LocalRefCell` representation the right direction for this performance issue, or is it semantically dangerous?
2. If it is viable, what exact semantics should it have under captured continuations and multi-shot resume?
3. Should this be implemented by changing lowering, by adding a runtime-recognized intrinsic representation, by specializing the existing `var_ref/run` pattern, or by introducing a new control IR node?
4. How should escaped refs be represented so that `&x` passed into a function remains fast and correct?
5. How should projected refs such as list/string/record element refs interact with local cells and `ref_update`?
6. What are the stages of implementation, with rollback points?
7. What invariants and tests should be added before changing runtime behavior?
8. Is there a smaller near-term optimization that is safe and likely to reduce the 2-second case substantially, or should we avoid short-term patches?
9. Separately, should std `for` be optimized after local refs, and if so, what is the safest route?

Please rank options by:

- semantic risk,
- expected performance gain,
- implementation size,
- fit with algebraic-effect semantics.

Please also call out any option that looks attractive but should be avoided.
