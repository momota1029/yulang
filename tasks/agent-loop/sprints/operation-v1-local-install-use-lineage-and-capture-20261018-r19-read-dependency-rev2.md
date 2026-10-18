# R19 revision 2 — bounded native-drain read dependency

Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, unchanged and
OPEN/closure0. Base contract: `operation-v1-local-install-use-lineage-and-capture-20261018-r19.md`, revision 1, SHA-256
`75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.

## Reason

The constructive lane needs the actual session-level typed-drain return path to
determine whether an authentic `FreshUse`'s physical edge is acknowledged by
that same use. R19 revision 1 already permits read-only inspection of the
candidate effect/context owners, but not the session-level caller and drain
return path in `lib.rs`.

## Added read-only dependencies

Pin `crates/yu-solver/src/lib.rs` at SHA-256
`2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`.
This digest was recorded before inspecting the file contents. It is a read-only
source dependency for the constructive proof lane; no writer lease is granted.

Also pin `crates/yu-solver/src/candidate_extrusion.rs` at SHA-256
`fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`. The
independent source falsifier had already inspected this existing physical
consumer owner while following the R19 FreshUse route. Its unchanged baseline
bytes and precise scope are now recorded for independent review; this grants no
write lease and does not turn its result into a sibling-use counterexample.

Permitted inspection is limited to the implementations and direct caller/return
edges needed to establish typed-drain ownership and completion:

- `constrain_live_effect`;
- `run_candidate_typed_drain`, `start_typed_drain`, `step_typed_drain`, and
  `candidate_step_typed_drain_terminal`;
- `dispatch_live_item` only where required to follow the current drain item;
- the exact caller and return path from `candidate_effect.rs` /
  `candidate_extrusion.rs` into those functions and their completion receipt.
- in `candidate_extrusion.rs`, only `candidate_begin_bound_restoration`,
  `candidate_drive_bound_restoration`, `candidate_step_bound_restoration`, and
  the exact emission/return path needed to identify the bound/use owner.

No unrelated `lib.rs` behavior, tests, or other source files may be added as
dependencies without a further Luna adjudication. Existing immutable pins and
all write leases remain unchanged.

## Unchanged limits

The revision adds no implementation authority, semantic rule, theorem premise,
worker, test/build permission, review change, or resource allowance. The proof
lane remains within its original 720-second allocation; total R19 remains
2400 seconds fully charged; Astra remains 0. Runtime implementation and source
falsification continue unchanged. The original theorem and all quantifiers
remain intact. A generic drain call, enqueue, or later `consumed` flag is not
by itself evidence that the target `FreshUse` consumed its own field edge.

Success requires tracing
`capture -> authentic FreshUse -> physical edge emission -> drain completion /
acknowledgement` with the same use identity. The falsifier remains acceptance
when the capture lacks the field evidence or when the drained edge belongs to a
sibling use/template. The parent remains OPEN/closure0 absent independent proof.
