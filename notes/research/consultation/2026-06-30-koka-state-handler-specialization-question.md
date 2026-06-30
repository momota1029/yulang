# ChatGPT Pro consultation: Koka-style state handler specialization

Paste the answer here:

- `notes/research/consultation/2026-06-30-koka-state-handler-specialization-answer.md`

## Question

Please answer in Japanese.

I am working on Yulang, a language with algebraic effects, effect rows, handlers, and an interpreter called Evidence VM. I need an architecture-level review.

The previous consultation suggested a VM-level `LocalRefCell` representation for local mutable refs. That may be practical, but it feels too close to specializing one implementation detail of local variables. I want you to reconsider the problem from a Koka-style direction: evidence passing, known-handler optimization, and compiling state-like handlers so effect operations do not allocate generic requests or walk continuation trees on the hot path.

Please do not just repeat the `LocalRefCell` plan unless you can explain why the Koka-style approach cannot work for Yulang.

## Current performance problem

Warm release `run.runtime_execute`:

- pure recursive nested loop computing a sum: about `1.5ms` to `1.6ms`
- std `for` nested loop with no mutable ref: about `6ms`
- std `for` nested loop with `my $total = 0` and `&total = $total + i + j`: about `1.8s` to `2.0s`
- nondet `(each 1..20 + each 1..20).list`: about `10ms`

So pure recursion is not catastrophically slow. The catastrophic case is local mutable refs implemented through algebraic effects inside std `for`.

## Current local mutable var semantics

Surface:

```yu
{
    my $total = 0
    for i in 1..20:
        for j in 1..20:
            &total = $total + i + j
    ()
}
```

Current lowering is roughly:

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

The generated local var act follows this std shape:

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

This is clean semantically but slow. Every `&total = ...` currently goes through record selection, `update_effect()`, `ref_update`, `get`, `set`, catch, and resume machinery.

## Concern with the previous `LocalRefCell` idea

The previous answer proposed:

- compiler-generated local mutable var only becomes a VM `LocalRefCell`,
- escaped `&x` points to that cell,
- continuation capture snapshots/forks local cells,
- generic refs keep the existing `get/update_effect/ref_update` protocol.

This is plausible, but it still seems like a special representation for one compiler-generated implementation pattern. Even if it is keyed by synthetic metadata rather than names, it is close to "local variable implementation is special".

I want to know whether we can instead treat this as a general known-handler compilation problem:

```text
state-like handler:
  run state body =
    catch body:
      get(), k -> run state (k state)
      set new, k -> run new (k ())
```

and compile it into a state slot in the handler frame or evidence frame.

## Koka-style direction I want evaluated

Please evaluate a design like this:

1. Use typed evidence / control evidence to know that an operation call is handled by a particular handler.
2. Classify a handler as a state handler if its operation arms are tail-resumptive and thread a state parameter in a recognizable semantic form.
3. Compile that handler into a runtime `StateHandlerFrame` with a state slot.
4. Compile handled `get` / `set` operations into direct operations against that frame:
   - `get`: read state slot and continue with it
   - `set`: update state slot and continue with `()`
5. On captured continuation / multi-shot resume, snapshot/fork handler-frame state, because the original handler recursion carried state in the continuation path.
6. Keep generic fallback for operations whose handler is not statically known or whose handler shape is not recognized.

This would optimize the same local var case, but the optimization target would be "known state-like handler" rather than "local ref cell".

## Questions

1. Is this Koka-style state-handler compilation a viable direction for Yulang, given the current semantics?
2. Is it more semantically principled than `LocalRefCell`, or is it just a different kind of implementation-specific special case?
3. What exact handler shape should be recognized first?
   - only `get/set` state handlers?
   - any operation family whose arms tail-resume with updated state?
   - only compiler-generated handlers annotated by lowering?
   - can this be generalized without solving full program equivalence?
4. Can this be implemented using type/evidence information instead of std function names or source-shape string matching?
5. What should the control IR look like?
   - `StateHandlerScope`
   - `StateOperationGet/Set`
   - route-specific operation opcodes
   - or a more general `KnownHandlerPlan`
6. How should continuation capture and multi-shot resume work?
   - snapshot active state-handler frames?
   - remap handler-state handles inside captured continuations?
   - preserve old handler-recursion semantics exactly?
7. How should escaped refs fit?
   - `&x` may be a public `std.control.var.ref`
   - a ref can be passed to generic code that calls `r.get()` or `r.update(f)`
   - file/user/projected refs must not accidentally become state-handler refs
8. How should `ref_update` and projected refs interact with this?
   - `ref_update` is not just local assignment; it is the protocol for focused updates through projections
   - can known projection handlers/lenses be compiled separately, or should projection remain generic until later?
9. What are the implementation stages and rollback points?
10. What canaries should be added before behavior changes?
11. Would Koka-style handler compilation also help nondet, or is nondet a separate continuation/multi-shot issue?
12. Should std `for` be handled by the same known-handler/evidence mechanism later, or by a separate iterator IR?

Please rank these options:

- pure `LocalRefCell`
- Koka-style `StateHandlerFrame`
- metadata-annotated compiler-generated `var.run` only
- general known-handler plan derived from evidence routes
- direct iterator IR for `for`
- doing nothing short-term except counters/canaries

Rank by:

- semantic risk
- expected performance gain
- implementation size
- fit with algebraic-effect semantics
- likelihood of avoiding future special-case accumulation

Please also list attractive-looking approaches that should be avoided.

## Important constraints

- Do not rely on benchmark names, file paths, source names, or string matching on std function paths.
- `Any`, `Never`, and `Unknown` are distinct in Yulang; do not suggest using `Any` as an inference fallback.
- Public `std.control.var.ref` must remain a normal abstraction.
- User-defined refs and file refs must keep working through the generic protocol.
- Handler hygiene / marker / provider semantics must not be weakened.
- If a plan changes multi-shot state semantics, say so explicitly and explain why it is acceptable or unacceptable.
- Prefer cause-side runtime/IR changes over downstream output patching.
