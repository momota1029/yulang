# R75 Rust implementation — frozen handoff

Sprint / contract: `EFFECT-PERMISSION-SOURCE-ROOT/20261031-R75`, contract
`tasks/agent-loop/sprints/effect-permission-source-root-20261031-r75.md`,
SHA-256 `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb`.
Frozen input manifest:
`tasks/agent-loop/sprints/effect-permission-source-root-20261031-r75-inputs-r1.json`,
SHA-256 `6bca174a95365afbf71a4919ec82f15b6ef7f5493880d9c6772a5d52bd116a9a`.
Baseline `6cd31c3043f142a8500eb9ea8d8095a1296f4f8d`.

Assignment: `/root/r75_rust`; requested model / effort `gpt-6-luna` / high;
observed model / effort UNKNOWN / UNKNOWN (runtime telemetry unavailable).
Budget: 1200 seconds. No descendants.

## Exact lease and result

Wrote only:

- `crates/yu-solver/src/candidate_receiver.rs`
- `tasks/agent-loop/inbox/effect-permission-source-root-r75-rust.md` (this file)

The source-root relation and entry-emission relation now remain distinct from
the owner-checked `CheckedBoundEmission` through `InventoryEntryRequest` and
`InventoryInternalRootView`. `CurrentInternalEmission` also retains the exact
Value pair passed to `checked_emission_for_internal_use`. Inventory validation
looks up the source-root relation at its own indexed row and checks that row's
pair against this retained source Value pair. Separately, it looks up the
admission relation at its indexed row and checks that row against the Effect
pair derived from the indexed admission's bound. The old equality between the
admission relation and source-root relation is removed.

The existing `checked_emission_for_internal_use` call remains the authority
for physical-slot readback, source-use root ownership, and ancestry in the
direction `emission/admission relation` descendant to `source use-root`
ancestor. This patch retains both relation IDs and the checked emission and
admission references. It does not edit or weaken `candidate_context.rs`, and
does not change inference, propagation, or execution behavior. The repaired
code is in a private `shadow-apply-candidate` inventory path with no ordinary
inference caller identified, so this is a source-evidence construction fix,
not a demonstrated runtime change.

## Correspondence and limits

The retained source Value pair is computed from the exact Internal semantic
fact's endpoints at the existing check call and accompanies the returned
owner-checked root ID. The emission pair is derived from the indexed
admission's bound; the same admission is joined to the physical emission by
the existing index and bound checks. The inventory's relation-table index must
equal each relation ID, and each indexed row must carry its respective pair.
Thus a Value source root and an Effect emission are not substituted for each
other.

This establishes correspondence only within the private Rust inventory's
borrowed native owner tables. It does not connect actual source syntax through
constraints and propagation to executed output, establish that the observer
is called, construct a genuine R66 `Root`, or close original A/B, whole-language
soundness, or production. Rust type checking and runtime behavior remain
UNVERIFIED.

## Prior evidence and review targets

Reused the R75 frozen source pins, R74's repair to the owner-derived Internal
view, the existing R73/R74 receiver implementation, and the `CheckedBoundEmission`
source in `candidate_context.rs`. The relevant R47/R65/R66 proof sources remain
the exact versions pinned by the R75 manifest. Rejected treating the finite
R73 model, an assumed successful `Root`, or source inspection as proof of
physical source/native extraction or parent-theorem closure.

Search of the solver source/tests found no dedicated test for
`internal_root_view_from`, `InventoryInternalRootView`, or the former
`root_relation` join. Tests were not run because this packet prohibits them.
The independent reviewer should verify the two relation constructors, their
indexed table rows and typed pairs, unchanged ancestry direction, and error
propagation against these frozen bytes and the proof-lane artifact.

## Checks, paths, and state

`git diff --check -- crates/yu-solver/src/candidate_receiver.rs` passed.
Static inspection only; no compiler, Cargo, tests, formatter, Lean/Lake,
build, environment, worktree, dependency, configuration, cache, target, or
scratch output was created. No Git mutation was performed.

New path: this handoff. Disposable scratch paths: none.

Worker state / writes: STOPPED / WRITES STOPPED. The source file and this
handoff are frozen for independent review and Luna adjudication. This author
does not self-certify the change.
