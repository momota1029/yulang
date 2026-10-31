# R75 — keep source root and entry emission relations distinct

Status: CANDIDATE until Luna freezes this contract and the input manifest.
Sprint ID: `EFFECT-PERMISSION-SOURCE-ROOT/20261031-R75`.
Branch / baseline: `yulang3`; baseline `6cd31c3043f142a8500eb9ea8d8095a1296f4f8d`.
Authority: continuing `research/simple-sub-intrusion` goal. This repairs a private
evidence-construction mismatch and proves its typed relation distinction. It
does not change language semantics or production authority.

## Fixed outcome

In the private feature-gated Internal root inventory path,
`InventoryEntryRequest.root_relation` currently conflates two records:

* the completed source-use root relation, selected as `CheckedBoundEmission.use_root`
  and checked by `checked_internal_use_root` against a Value pair; and
* the entry emission's admission relation, checked against the fresh Effect bound.

`InventoryPackage::internal_root_view_from` currently requires the admission
relation to equal the source root relation. Since the relation table is a
function and `TypedPairKey::Value` and `TypedPairKey::Effect` are disjoint, this
equality rejects every source/native-success case with these two checked roles.
The existing native helper already preserves the intended ancestry direction:
emission relation descendant to source root ancestor.

**Rust fixed outcome:** in `crates/yu-solver/src/candidate_receiver.rs`, retain
the source-root and emission relation IDs as separate fields from request
through returned view. Trace the source-root pair to the existing owner-checked
`use_root` record and the emission pair to the indexed admission/current-bound
record. Validate each against its own retained relation row and typed pair;
remove only the erroneous cross-role equality. Preserve the already checked
ancestry direction and all physical-slot, source-use, identity, and error
distinctions. Do not edit `candidate_context.rs` or change its native helper.
If an exact source pair cannot be revalidated from leased owner data, record the
first missing owner datum rather than substituting the Effect pair or weakening
the check. Preserve `SearchLimit` as distinct from evidence mismatch.

**Lean fixed outcome:** add
`notes/theory/lean/YulangClosure/DistinctSourceEmissionRootR75.lean` and prove:

1. for a functional R47 relation-pair reader, a source relation whose endpoints
   are both Value endpoints and an emission relation whose endpoints are both
   Effect endpoints have distinct IDs;
2. the old admission-relation-equals-source-root check rejects this typed case;
3. a two-ID record keeps the R47 query root and probe/emission relation separate
   while retaining the original ancestry check from root to emission; and
4. a finite mixed Value/Effect relation example satisfies the corrected role
   and ancestry checks while failing the old equality check.

Use R47's `Endpoint`, `Inputs.relationPair`, and `ancestryCheck` semantics in the
checked artifact or provide a byte-pinned flattened stdin audit of those exact
definitions. Include theorem types and complete transitive axiom reports. A
finite model or an assumed successful `Root` does not construct a genuine R66
`Root`; actual source/native construction remains OPEN unless all incidence,
readback, unique source-drain, and physical ownership fields are derived from
the pinned owner records without assuming `Root`, `readRoot = .ok`, or policy
success.

## Exact assignments and review gate

Rust writer `/root/r75_rust`, Luna/high, 1200 seconds: write only
`crates/yu-solver/src/candidate_receiver.rs` and
`tasks/agent-loop/inbox/effect-permission-source-root-r75-rust.md`.

Proof writer `/root/r75_proof`, lean_prover, 2400 seconds: write only the new
Lean module and `tasks/agent-loop/inbox/effect-permission-source-root-r75-proof.md`.
At most one direct Lean `--stdin` audit is assigned to this lane; a second is
allowed only if Luna records its exact input and 120-second / M1024 envelope
before execution. No Lake or ordinary project build.

Fresh independent reviewer `/root/r75_review`, compiler_referee, 1200 seconds:
write only `tasks/agent-loop/inbox/effect-permission-source-root-r75-review.md`.
Start after both authors report STOPPED / WRITES STOPPED and their artifacts
are frozen. Trace both relation constructors, typed-pair checks, ancestry
direction, ID substitution, and failure propagation; audit the Lean theorem
types and axiom receipts against the frozen source/module bytes.

Primary Luna: 1200 seconds including at least 500 seconds closeout; owns the
contract, manifest, current state, review adjudication, archive, exact staging,
commit, and push. No other writer may edit those paths.

## Resource and authority boundary

Use the existing checkout and existing installed Lean toolchain only. No new
environment, worktree, dependency, configuration, cache, build target, scratch
directory, or generated output. No Cargo, compiler, tests, formatter, Lake, or
build. Static source tracing and `git diff --check` are permitted. The single
bounded direct Lean stdin audit above may run only against the already installed
Lean 4.35.0 executable and must not emit `.olean`, `.ilean`, or other files.
If the pinned executable or import artifacts are unavailable without creating
outputs, leave executable proof status UNCHECKED; do not build them.

Preserve all 32 pending items, all UNKNOWN worker observations and quarantined
path leases, unrelated dirty/untracked files, and the released R24 capacity
record. No path lease is released by capacity accounting. No semantic claim,
production gate, or original A/B obligation is changed.

## Closure boundary

This packet can close only the private relation-role source mismatch and the
conditional typed-relation theorem. It does not establish that the private
observer is called, that an actual source/native package produces the finite
model, that a genuine R66 `Root` is constructible, or that original A/B,
whole-language soundness, or production is closed. Rust compilation/runtime
remain UNVERIFIED because builds and tests are outside this packet.
