# TABLES-LIFETIME-READBACK — r4 producer handoff

Status: constructed, pinned-kernel checked, ready for fresh independent review.
Original complete inference soundness remains OPEN at the concrete runtime and
semantic owners below. No Git operation, shared import edit, production edit,
configuration change, dependency change or child agent was used by this leaf.

## Lease, inputs and outputs

Budget start: `2026-10-26 12:08:47 UTC`; hard deadline:
`2026-10-26 13:08:47 UTC`. Limit: 3,600 wall seconds, 24 focused checks, each
at most 120 seconds, one Lean thread and `-M1024`. Actual checks: 19 (one additional check for the review repair).

Initial accepted source revision:
`82b8fb669c5b51c6c99771cd2208c9730ebc85c3`.
The accepted Readback dependency was added only after the primary published
`ee61ba0b68789e2dea9eac024130f21c5a4e6453` and authorized its exact SHA.
All 18 dependency/native/config hashes are in the frozen `inputs.json`.

Exact repository outputs:

- `notes/theory/lean/YulangClosure/NativeContextTables.lean`
- `notes/theory/2026-10-26-native-context-tables.md`
- this handoff

Owned scratch/cache: `/workspace/scratch/f98087c7ac1a/context-tables-r4/`.
No other repository path or sibling scratch input was changed. Final output
hashes and writes-stopped time are in `freeze.json`; no self-referential hash
is placed in this handoff.

## Constructed result and actual parent application

The original owner is §7 of the accepted
`2026-10-26-native-context-readback.md`: replace one unversioned, arbitrary
`Tables` parameter by the actual native five-lane constructor/lifetime history.

The new module constructs Context interning, native cache insertion/removal,
weight allocation, the reserved-View/weight/publication/sample sequence,
complete View-copy validation, contribution allocation, native frontier
rollback, retry births and versioned missing observations. All six Context
constructors and all optional View/weight branches remain represented.

The successful-read transport proof covers the existing parser, every
installed check, operands and child admission, complete prepare/finish, Value
Context and original construction-directed prefix/body recipes. It permits
fresh allocation, including `none → some`; a successful closed-weight operand
is protected by the native availability check. `VersionedChecks` constructs
the complete ordered prefix when allocation occurs between individual checks.

`Reindex.step` migrates every accepted Readback event, preserving original
issued work, actual processing relation, previous checked prefix, complete
keys, early publication, active-owner memo, Derived edges and completed body.
The dependent `Joint` then contains the Store and that driver indexed by the
same Store's tables. `JointHistory` commits actual combined runs or performs
the proved native table rollback and restores the same driver checkpoint.

Principal roots in `YulangClosure.NativeContextTables`:

- `committed_tables_context_readback`: from a constructed `JointHistory`, an
  empty queue and empty frame stack, every original issued work has its actual
  resolved receipt and valid source/Derived route.
- `committed_tables_original_body`: at the original `NoCurrent` cut, an actual
  Effect receipt has its owner's stored original `BodyRecipe`, previous fresh
  nonempty prefix, Derived edges, full sources/transformer and absent Effect
  demand, interpreted at the resulting native table version.
- `committed_tables_whole_child`: all generated children keep the complete
  source-derived Context/provenance/admission payload.
- `cancellation_all_five_tables`, `native_cache_rollback`,
  `native_prefix_rollback`: native vector truncation and removal of exactly the
  drained expression keys derive restoration of all five lanes.
- `retry_context_birth`, `retry_all_lanes_birth`: numeric reuse does not reuse
  a cancelled allocation birth.
- `versioned_prepare_readback`, `versioned_finish_readback`: complete prefix
  and body construction across actual intermediate allocation cuts.
- `committed_observation_readback`: retained positive and missing observations
  have their actual source-constructed version/cut witnesses.

None of these principal committed roots takes table equality, full Context
coverage or a finished body as an opaque premise. The remaining premise is
the constructed native event interpretation, not generic pending coverage.
The complete exact types of all 145 named source theorems and every generated
constant are in `origin-inventory.json` and the census log.

## Native source correspondence

The paper gives the complete owner/readset/mutation map. Key owners are
`State::context` (candidate_context 2630–2655), `source_weight` (2734–2758),
signature/copy/remapped View constructors (candidate_effect 859–909,
1155–1211), contribution append (1213–1236), Context-source prefix interning
(candidate_context 3361–3372), both native checkpoint/truncation owners, and
the captured rename frontier (1556–1689).

The module retains owner/position, actual allowed member order, both source
and closed weights, attachment source/scope/ordinals/unit push, operation
origin/occurrence/retained bytes, contribution origin/instance, and raw index
plus birth/version. Native Context cache removal is proved from actual
insertions and no-duplicate expression history; it is not presumed coherent
after a generic snapshot restore.

The weight-before-View and Context-rollback-before-View-rollback windows are
both explicit. There is no global well-formedness assertion at these
transient cuts. Optional `source_drain_completions` storage is never required
by the readback: its native reservation can fail without changing inference
success.

## Verification receipts

Pinned toolchain:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean reports 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Each focused check copied an immutable `sourceNN.lean` to the owned project.
The ordinary checks invoke the repository skill's `check_lean.py` with that
project, exact Lake, module, named roots and a 120-second timeout. The final
audit command is `python3 audit_check.py 19`; it verifies every frozen input
hash, builds `+YulangClosure.NativeContextTables`, then runs
`lake --no-cache env lean -j1 -M1024 AuditNativeContextTables.lean`.
`PYTHONDONTWRITEBYTECODE=1`, `LEAN_NUM_THREADS=1`, and the owned `TMPDIR` were
set. Execution used the already-authorized isolated native checker path;
there was no install or shared cache write.

Final source SHA-256:
`eaf2b037af40af01ad116e1ae413a6c7d5a0023d49c8b9f1b92d29c319d2df81`.

Full origin census: **1,125 declarations; 521 theorem constants; 145 named
source roots; 65 private declarations; 43 private theorem constants**.
Theorems by actual axiom set: none 260; `propext` 118;
`propext, Quot.sound` 113; `propext, Quot.sound, Classical.choice` 30.
Every originating axiom declaration and every dependency outside the three
standard axioms is rejected by the audit. No holes/native bypass remain.
Census SHA-256:
`ec9858b8f1f923d47fddf1e627227e060ff96bdcfdcbfde9331474420b8db32d`.

19 checks used 261.166 measured wall seconds in total; maximum 55.687 seconds.
Final audit 19: build and census exit 0, no warnings, 14.749 seconds, maximum
child RSS 1,022,980 KiB. Checks 02, 14, 17, 18 and 19 pass.
Failures 01, 03–13, 15 and 16 are retained with
their exact source snapshots and logs. They concern notation/elaboration,
record/function commutation, and proof normalization; the fixed-table
counterexample was repaired through construction rather than deleted.

The final source examples construct every lane, cancel, retry raw Context ID
1 with a new birth, and compute both differing successful parser results.
They also construct the actual complete prefix/body and preserve it through
fresh allocation. They use ordinary kernel-checked computation.

## Batched independent-review repair

The assigned reviewer reconciled the original 18 inputs, 190 artifact hashes
and 1,125 complete census entries and reported no semantic finding. The sole
requested repair was 21 warnings in the new module. Exactly those 21 lines
were changed: unnecessary `simpa` becomes `simp`, unused simp arguments are
removed, unused `needed` becomes `_needed`, and `Reindex.map_put` loses its
global simp registration. All internal uses already name it explicitly. No
global linter suppression or semantic/statement change was made.

The original frozen scratch tree and repository source/note/handoff are
preserved in `pre-review-20261026T125109Z/`; its manifest SHA-256 is
`ceded2ab2448689e96e2dd4fba00d369d1785f0dbe94a928a5f5b41b42c2472b`.
The original final check and all failures remain untouched. The new check 19
verifies the same 18 inputs, builds the repaired module and prints the complete
origin census. `review-delta-census.json` verifies all 145 named root types and
axiom lists are identical. Of all 1,125 entries, 1,123 are byte-identical;
`step_fresh._simp_1_6` moves to `_simp_1_5` and `_simp_1_7` moves to
`_simp_1_6`, with their complete types and axiom lists unchanged after that
renaming. The initial strict generated-name comparison and its failure are
retained in `review-delta-first-comparison.json`.

Final inventory SHA-256:
`f48c9d108b76d3a4a5c388500e03ae6a503c227e2774955dac45bd7ed05162e3`.
Delta census receipt SHA-256:
`fac981aae24eb7e69e896ec97ca4e4c118fd23fa00d5b09becb90f3d6af0f87f`.
The repair consumed one of the intended at-most-four additional focused
checks; 19 of the original 24 checks are used. Final hashes and the renewed
writes-stopped time are in `freeze.json`. Independent delta review remains
required; this producer does not self-certify acceptance.

## Exact residual owners and review boundary

The fixed-table premise is eliminated for the represented combined history.
The original parent remains open until the actual runtime supplies that
history and the semantic owners below are joined:

- Native callback/completion interpretation must construct each actual
  Context/control step and place the storage events at its real source cut,
  keeping all raw task/relation lookups and success guards. Root's separate
  Context callback/completion packet owns this mapping.
- Actual representative forests and physical bound/body carrier readback
  must instantiate the unchanged canonical/Derived transport data.
- Native Value dispatch and generated-child-to-issued-work supply remain
  with the root's disjoint Value drain/Value structure/Context completion
  work. Full ScopedDemand and source fields are preserved here.
- Effect semantics, conflict-free acceptance and full Value typing remain
  prerequisites for original inference soundness. A conflict-recording local
  return is still not source subtyping success.

No live unaccepted sibling file was imported. Native remap cache hits are
table stutters; their external substitution-map validity is not invented by
this packet. The authoritative supported-language scope and inference
behavior are unchanged. Fresh independent review is required; only the
primary can accept, integrate, commit and push this packet.
