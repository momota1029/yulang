# R286 — caller-reference closure and conditional model preservation

## Unchanged parent and boundary adjudication

Preserve original `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, its source domain,
quantifiers and semantics. R285 remains INCOMPLETE: its arbitrary-caller
initialization theorem and omitted caller endpoint checks are both preserved.
The R285 review establishes a genuine model boundary: caller endpoints are
copied into a bound request and saved Parents without local dereference, but
they remain references requiring justification before external consumption.
R286 will make that obligation explicit as a conditional model premise; it
will **not** claim every computed input or accepted production entry satisfies
it. Parent/A/B remains 0->0; R70, source/native correspondence and production
remain OPEN.

## Exact caller invariant

Use R285's `CallerRowsValid` for both `State.operation.caller` Value endpoints.
Add a predicate requiring both Value endpoints in every saved
`Parent.operation.caller` to be valid against the current Value store and
kind-separated `qv` map. Define `CallerClosure` as the conjunction of:

1. R285 `StorageClosed`;
2. the current operation caller endpoint validity; and
3. caller endpoint validity for every stored Parent.

Do not treat copying or opaque payload status as proof of bounds. State the
exact endpoint conditions in the theorem types, including raw index and
canonical representative bounds. Prove `CallerClosure` implies R285
`StorageClosed` and preserves both R283/R284 gap exclusions.

## Required initialization and frame results

- Prove computed initialization under the explicit premise that the input
  Request's lower and upper Value endpoints satisfy the exact raw/canonical
  conditions. Prove the converse/equivalence where the model definitions make
  it exact. Keep R285's checked arbitrary-caller impossibility theorem; do not
  replace it with assumption-free computed initialization.
- Prove a caller-frame lemma through actual store extension and canonical-map
  updates: existing caller references remain valid when rows are appended and
  the old `qv` representatives are retained.
- Prove that operation replacement/preservation and `State.retain` preserve
  the current caller conditions and that newly retained Parents inherit a
  valid caller. Cover Parent append followed by partial failure.
- For an external bound result, prove the emitted request retains valid caller
  endpoints against the returned state. This is a model equation, not proof
  that a source/native consumer receives or preserves them.

## Preservation target

Attack R285's exact open `select = some (task, popped)` → `perform` branch.
Prove or falsify `CallerClosure` transfer through queue removal and every
`perform` constructor, every Funding outcome, all `.next`/`.external`/`.failed`
projections and partial publication before failure. Then prove:

```lean
step_preserves_caller_closure :
  ∀ (funds : Funding) (s : State), CallerClosure s →
    CallerClosure (resultState (step funds s))
runPrefix_preserves_caller_closure :
  ∀ (funds : Funding) (fuel : Nat) (s : State), CallerClosure s →
    CallerClosure (resultState (runPrefix funds fuel s))
```

Retain arbitrary Funding, satisfying State and fuel quantifiers. Apply the
finite-prefix theorem to the computed row prefix only under the exact
initial-caller validity premise. If a branch fails, freeze a kernel-checked
counterexample or the exact unclosed constructor obligation. Do not assume
preservation, hide caller validity, narrow to reachable states, omit failures,
or strengthen hypotheses silently. A conditional model lemma is not evidence
that production entries satisfy its caller premise.

## Frozen inputs and exact leases

Reuse the explicit 33-input manifest
`tasks/agent-loop/sprints/extrusion-caller-closure-r286-inputs.json`, SHA-256
`d61df1fdbb3ea46e34cc680a70bd4fdc8d6f26129680cc2b0423e86077efa814`. It reuses R285's authenticated 32-input review
manifest and adds its independent review receipt. Keep R283–R285 files
unchanged. Preserve R70 authority and pinned Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no dependency/config update.

Producer `/root/sol_r286_caller_closure`, registered `lean_prover`, requested
Sol/high, maximum 2,400s, no descendants. Exact write leases:

- `notes/theory/lean/YulangClosure/OriginalExtrusionCallerClosureR286.lean`
- `tasks/agent-loop/inbox/extrusion-caller-closure-r286.md`
- `notes/theory/lean/.lake/build`, exclusively after stopped-owner
  reconciliation.

Run focused pinned Lake build, direct Lean check and bundled per-theorem type/
axiom checker for all delivered declarations. Report the complete theorem
types, exact caller premise, per-theorem axiom results, all result/failure
cases, exact open obligations, checks and parent application. No broad suite.

## Review, resources and non-goals

After producer STOP, reserve 900s for a fresh independent Sol Lean reviewer.
Transfer only cache ownership after live-roster/stopped-owner reconciliation.
Reviewer checks caller/Parent coverage, initialization premise/equivalence,
all `perform` branches, external bound result, failure publication, exact
quantifiers and complete axiom audits, with a focused independent checker run.
Luna owns the review receipt and adjudication.

Fresh R286 envelope is 3,600s: Sol producer 2,400s, reviewer 900s, Luna 300s.
All prior charges remain consumed; no refund, renewal or budget reset. No
Rust/source/Cargo/tests/probes, external-body inspection, implementation,
semantic changes, source-domain change, Git or production authority. The
missing production constructor/session and `candidate_source` /
`candidate_intrusion` initialization and mutation bridge remain OPEN. A
conditional theorem here cannot close R70, A/B, Parent or production.
