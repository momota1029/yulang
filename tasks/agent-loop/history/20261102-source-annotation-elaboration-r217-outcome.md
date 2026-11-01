# R217 outcome — source annotation elaboration

Session R217 ended at a reviewed source-model correspondence boundary. The
original parent theorem, quantifiers, supported-source domain and approved
effect-hygiene policy were not changed.

## Result

The primary constructed a fixed-signature candidate containing original
annotation ID, owner, type scope, selected entry and a complete recursive tree
matching current `SourceAnnotationType`. Its resolver is independent of a
solver assignment. Two Lean theorems establish candidate lookup stability and
owner/type-scope identity. This table is not present in the original Lean
source model, which retains only `Annotation := Nat`.

The candidate formal constructor rejects a Tuple when an immediate child has
an effect row. The parser retains that row. Frozen Oracle
`a58eefc31e22141574b6f20c6a5748151c6d79f1` recursively builds tuple child
annotations and strips `Effectful` wrappers in `lower_value_bounds`. R217
formalized the local root-wrapper erasure and tuple value recursion, without
claiming end-to-end Oracle correspondence.

The inspection found a separate Function row-position mismatch: frozen Oracle
gets argument effects from the arrow's `TypeRow`, but the current carrier
places a prefix row on the argument node and the candidate treats that as the
argument-effect port. The explicit fixture equation is:

```text
([E] int) -> int
Oracle:   param = Effectful(E, Int), arg_eff = None
value:    Effectful wrapper erased from param
candidate: argument-effect port = Some(E)
```

The candidate's local Function-view theorem states only its own definition.
It does not close this mismatch, establish hygiene, or prove source coverage.

## Parent and effect-hygiene accounting

`Contracts.SourceProblem.InferenceSoundness` remains open. The annotation
declaration cannot be instantiated at `sourceFormalRole`, and
`Kernel.atom` remains an independent parameter. The candidate definitions do
not imply the original Lambda premise.

```text
roots closed:       0 / 4
packages closed:    0 / 5
parent delta:       0
effect hygiene:     no theorem delta; approved policy preserved
```

The next exact evidence owner is the original source annotation equation that
preserves Oracle's distinction between an arrow `TypeRow` and an
`Effectful` value wrapper, then supplies that same resolved declaration to
generation and declarative source typing while retaining the unchanged
source-domain quantifier.

## Independent review and verification

Reviewer: `/root/r217_candidate_review`, compiler_referee, fresh read-only
delta review. Initial Major was corrected: the first version asserted a new
semantic choice before reading frozen Oracle. Final delta **PASS**, scoped to
the corrected incomplete candidate; reviewer also identified and verified
the Function row-position mismatch.

Pinned Lean command passed in the existing project/cache. Axiom audits for
the four named candidate theorems report only `propext` and `Quot.sound`.
`python3 tools/agent_sprint.py check` passed as static workflow evidence.
No tests, Rust builds, Cargo, environment/dependency changes, or changes to
the original parent source model occurred. User explicitly authorized Lean
cache creation.

Frozen artifacts and hashes are in
`tasks/agent-loop/inbox/source-annotation-elaboration-r217.md`.

## Primary closeout correction and R218 continuation

The primary acknowledged handoff revision 1 at SHA-256
`be4a32b1699320d1aa6e0491a396425b717d9d914c40262f13166d2c687891d8` and
preserved its exact bytes at
`tasks/agent-loop/history/20261102-source-annotation-elaboration-r217-handoff-r1.md`.
Revision 1 listed stale model digest
`0462b51e301b0f21d764106f9f1f83a87a8e9f7533be5c14ae1820d813ab395b`; the
actual frozen model digest is
`7f70d0cf755c291f6dff8fb0d7cf26fa2e17e0135a65a3f0bbd9e08a91ea6b63`. The
handoff was advanced sequentially to revision 2; the candidate, Lean module,
contract, and reviewed claim bytes did not change.

The completed R217 `next_action_selector` recommended R218 to determine whether
the original annotation meaning can be reconstructed from the actual source
inputs, with a discriminator preserving the distinction between an
`Effectful` parameter wrapper and an arrow `TypeRow`. The primary accepts this
as the next in-scope step without changing `InferenceSoundness`, `supported`,
or the approved effect-hygiene policy. R217's selector disposition and
resolved artifact leases are archived in
`tasks/agent-loop/history/20261102-r217-selector-and-resolved-leases.md`.
