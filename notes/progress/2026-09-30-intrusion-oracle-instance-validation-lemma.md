# Oracle reachable definition-instance validation lemma

Date: 2026-09-30
Oracle: frozen Yulang2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: code-level necessary-condition lemma; no intrusion correspondence proof

## Claim

For each body-bearing definition instance reached by the frozen Oracle's
specializer from its selected roots, successful completion of the mono
specialization worklist implies that the instance body passed the solver's
definition-body validation under that instance's inference signature.

## Source derivation

The path is `crates/specialize/src/specialize2/emit.rs`:

1. `emit_root_definitions` / root emission calls `ensure_def_instance` for
   selected definitions.
2. A local body-bearing reference in `emit_var` takes
   `solved.ref_signature(expr)` and calls `ensure_def_instance` with that
   per-use type.
3. `ensure_def_instance` uses `(def, runtime_signature_ty)` as its key and,
   for a new key, appends a `PendingInstance` carrying the corresponding
   `inference_signature_ty`.
4. `drain_pending_instances` pops each pending instance and calls
   `TaskSolver::solve_def_body` before emitting/storing its specialized body.
   An error propagates from the worklist; it cannot store that body as a
   completed instance.

In `crates/specialize/src/specialize2/task_solver.rs`,
`solve_def_body(def, body, signature)` constructs a fresh solver, infers the
body, consumes the body against `signature`, materializes the actual and
definition predicate occurrences, adds `actual <: signature`, and calls
`finish`. `infer_expr` recursively dispatches applications to `apply_type`,
which derives callee Function shape and argument/result constraints. Thus a
successful mono worklist entails satisfaction of the body constraints
reconstructed for each reached `(definition, instance signature)` pair.

## Relation to the q fixture

For `pub f x = x f; pub main = f 1`, the exact traced instance is
`f : int -> unit`; its reconstructed body constraints fail at
`int <: Function`. For `pub id x = x; pub use id = f id`, the `f` instance is
`(unit -> unit) -> unit`; its body constraints fail at
`(unit -> unit) <: unit`. The two traces witness the lemma's rejection path
for these instances.

## Limits

This code-level implication is not an equivalence between Oracle inference
constraints and specialization constraints. It does not establish that every
recursive SCC edge, effect/handler obligation, role constraint, or provenance
fact is reconstructed by `solve_def_body`; nor does it prove that the intrusion
candidate produces the same set of reached instance signatures. The q source
therefore still requires an explicit stage-indexed relation, at least:

```text
Infer(P) -> (inference observation, specialization roots)
Specialize(roots) -> reached (definition, signature) instances
SpecValid(def, signature) -> body constraints solve
Public(P) = ordered combination of the selected phase observations
```

The observed successful `dump-poly` and failing `dump-mono` for `f 1` confirm
that these phase observations cannot be collapsed. The source-level checker
and runtime entrypoint remain uncharacterized for this fixture.
