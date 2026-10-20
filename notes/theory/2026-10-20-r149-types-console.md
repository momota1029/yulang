# R149 proof map: tuple inference, library display, and module output

Status: Reviewed
Scope: Constructive source-to-native evidence required for the exact pinned
Yulang2 `Types` and `Console` examples proposed in
`notes/design/2026-10-20-r149-types-console.md`.
Drafted-by: Luna primary
Reviewed-by: compiler/source reviewer, spec reviewer

## Fixed source obligations

The source templates are the 142-byte and 92-byte strings pinned by SHA-256 in
the design proposal. Their defining Yulang2 library sources are `lib/std/core/fmt.yu`,
`lib/std/io/console.yu`, `lib/std/io.yu`, and `lib/std/prelude.yu` at oracle
commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`, with exact blobs listed in
the design proposal. The source chain also includes `core/ops.yu` and `int.yu`:
resolve integer display and integer/string addition through their library
wrappers to the authentic primitive leaves, retaining the source identity and
the primitive operation identity at each boundary.

## Proof chain to construct

For each exact module, establish a single identity-preserving chain:

1. The parser and HIR retain every tuple construction, library reference,
   method/application, module item, mixed computation/expression schedule
   position, and source order position from the pinned bytes. Unsupported
   syntax must reject the exact source before any type or output is published.
2. Tuple inference emits the product type from its element constraints. Each
   element occurrence maps to the corresponding product component, preserving
   order and independent polymorphic instantiation of `id` at `int` and `str`.
3. The accepted inference artifact is tied to this exact HIR/module identity.
   Public type rendering reads that artifact and reports the polymorphic `id`
   scheme plus `answer: int`, `name: str`, and `pair: (int, str)`. Execution
   values and host writes do not appear in the Types pane.
4. Library `Display` resolution identifies the actual `Display` role instance
   and its prerequisites. Evaluation of `pair.say` follows those resolved
   source/library calls and yields the observed pair text. A spelling-based
   evaluator branch is a counterexample, not a proof.
5. The module evaluator consumes the original mixed source schedule. It keeps
   computation definitions in source order, preserves lazy value
   materialization, cached successful values, and forward demands, and
   completes with unit after the schedule is exhausted. Each executed schedule
   item remains tied to its original source identity.
6. For Console, source/library resolution follows prelude and IO re-exports to
   the actual `println`, `say`, `Display`, and `out::write` declarations. The
   host capability is authorized by the resolved `out::write` declaration
   identity and its checked `str -> ()` type, not by spelling. At each request,
   the host checks the operation identity and string payload, records exactly
   one write, supplies unit, and resumes the exact saved continuation exactly
   once. Other unhandled requests remain unavailable.
7. Each write event is tied to the corresponding source call, exact payload,
   and mixed-schedule order position. The Types payload is `(42, Yulang)\n`;
   Console payloads are `hello from Yulang\n` and `3\n`.
8. Publication is atomic: a type error, unresolved library binding,
   unsupported runtime node, step exhaustion, or unhandled write rejects the
   run without exposing a partial type list or output sequence. Each published
   type and output event is tied to the same accepted module/HIR identity.

## Falsifiers

- A tuple component is reordered, collapsed, or inferred from a shared type
  variable where Y2 permits independent types.
- A source spelling triggers an intrinsic path without the matching resolved
  standard-library definition.
- Runtime execution uses a different HIR or library environment from the
  accepted inference result.
- Module expressions execute in a different order from source, output writes
  are reordered/dropped/duplicated, or `println` is treated as a pure string
  operation.
- Any failed or resource-exhausted run publishes partial output or public
  types.

## Gate status

This is a proof plan, not a proof. Tuple typing, standard-library loading,
effect handling, module execution, and publication correspondence remain open
until exact implementation owners and constructive derivations are reviewed.
No parent theorem or production gate is discharged here.
