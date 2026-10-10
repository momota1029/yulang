# Canonical bound fibers: exact restoration witness reachability

Status: research characterization; static source bridge; unreviewed.
Baseline: `1007224e2e7e6efab1590bd88c54bcb0a1fe8ff6`.
Scope: the two-Value-parent-pair, representative-changing restoration trace in
`2026-10-10-canonical-bound-fiber-prover-audit.md`. No soundness, lifecycle
closure, source counterexample, implementation, or semantic change is claimed.

## Objective, authority, and method

Determine whether the exact pending physical state in that trace is generated
by candidate constraints or reconstructed by candidate scheme capture and
freshening. The authority is contextual attachment/admission design §§4–5,
particularly bound insertion, opposite replay, capture/freshening, SCC intrusion,
and rollback. The selected row equality and attachment meanings are unchanged.
This complementary audit reads the real constructors and consumers; it does
not duplicate the prover's canonical-storage derivation.

The result is an exact static characterization: the supplied trace is an
unexecuted API/injected-state witness. Direct ordinary constraints and normal
Value scheme reconstruction do not supply its stated setup. This does not
establish global source nonreachability of other representative-changing drains
or prove restoration correct.

The primary confirmed that relevant dependency bytes match the pinned baseline
despite unrelated HEAD movement. Filesystem hashes below also match the prover
audit's recorded dependencies. Initial read-only `git status --short` and
`git rev-parse HEAD` queries preceded application of the packet's no-Git rule;
this was a workflow deviation. No Git mutation occurred; subsequent work used
filesystem reads only.

## Exact pending state and physical orientation

Write `r + x` for a physical lower of owner r, and `r - x` for an upper.
The proposed setup has parents B, O at level 2 and positive extrusion copies
b, o at level 0, with retained parent records `(b,B)` then `(o,O)`.

| Operation | Physical result relevant to the witness | Source status |
| --- | --- | --- |
| Positive extrusion B to 0 | `B - b`; actual `(b,B)` record | Actual constructor, `candidate_extrusion.rs:112–123` |
| Positive extrusion O to 0 | `O - o`; actual `(o,O)` record | Same constructor |
| Direct insertion `b - B` | `b.direct_upper_rows = [B]` | API insertion; ordinary `b <: B` chooses `B + b` instead |
| Direct insertion `o - O` | `o.direct_upper_rows = [O]` | API insertion; ordinary `o <: O` chooses `O + o` instead |
| Direct insertion `o - TopNegative` | `o.exact_non_variable_uppers = [TopNegative]` | API insertion; ordinary Top comparison is omitted before application |
| Restore `o + b` | `o.direct_lower_rows = [b]`; initial opposite count 2 | Requires this owner-side restoration to be selected |

Insertion canonicalizes both endpoints and physically appends the chosen side
(`candidate_extrusion.rs:422–469`); it does not choose that side from levels.
Ordinary Value application does choose: if upper-row level is no greater than
lower-row level, it stores an upper on the lower; otherwise it stores a lower
on the upper (`candidate_extrusion.rs:698–717`). Thus both of the witness's
reverse low-owner-to-high-parent upper insertions differ from application of
their corresponding ordinary comparisons. The equal-level comparison b <: o
also ordinarily stores `b - o`, rather than the witness's restored `o + b`.
This is a physical-owner distinction even though the intended inequalities can
be spelled with the same endpoints.

`lib.rs:11924–11935` records a TopNegative comparison and continues before
ordinary `apply_value_task`; this route does not create its exact upper slot.
The candidate application dispatch is `lib.rs:13014–13016`. These are narrow
constructor facts, not a proof that no different source construction can ever
retain such an exact upper.

## Capture and freshening cannot directly recreate the stated Value owner

The exact static bridge uses these hypotheses:

1. Graph capture and its immediate freshening use the inspected normal route,
   with a `u32` boundary and no external mutation between them.
2. Physical owner bounds come from `Capture::expand_row`; no injected `Graph`
   or direct mutation adds extra bound records.
3. Row allocation is fresh and parent provenance is created by the inspected
   extrusion constructor; no external code supplies forged parent records.

These hypotheses describe the inspected top-level and local capture/use seam,
not every initializer or legacy mutation in the compiler.

`Capture::row` canonicalizes the source row and sets `local` precisely when
`level > boundary && !non_generic` (`candidate_scheme.rs:189–214`).
`expand_row` returns immediately for nonlocal rows (`440–442`). Its four Value
vector loops (`446–484`) emit only bounds owned by that local Value row: upper
endpoint for a positive side, lower endpoint for a negative side. Therefore
the preexisting level-0 o is nonlocal at every `u32` boundary and contributes
no owned Value bound to `graph.bounds`. It can occur as a shared endpoint in a
different local owner's bound; that does not make o the restoration owner.

For a local Value owner in an immediately captured graph, freshening allocates
a fresh row at `use_level` (`candidate_scheme.rs:841–852`).
`fresh_value_at_level` pushes empty bounds and level/metadata, with no
parent/copy record (`lib.rs:10061–10085`). The row can numerically have level 0,
but it is a new identity, not the old extrusion copy o. Freshening preserves
bound owner sides (`candidate_scheme.rs:996–1032`); it does not copy the
captured parent records to these new identities.

The only `retain_extrusion_parent` call in the inspected constructors is after
extrusion allocates its own fresh copy (`candidate_extrusion.rs:112–123`). A
freshening row does not become that newly allocated copy merely because it is
an extrusion parent or because a child later merges into it. Existing parent
records refer to older identities. Consequently reconstruction of a generic
owner does not supply the witness's actual `(o,O)` copy provenance. No global
forest preservation theorem is asserted here.

Actual callers preserve this distinction:

- Top-level incoming use: `lib.rs:15890–15897` →
  `route_candidate_graph` (`candidate_scheme.rs:786–802`) → live capture →
  `instantiate_candidate_graph` (`1039–1048`) → freshening → bound restore.
- Local use: `route_candidate_local` (`1117–1133`) captures and freshens in a
  route transaction, then admits its occurrence link.
- In both, the occurrence/use comparison is applied after reconstruction
  (`1068–1075`, `1133`), so that later comparison cannot retroactively create
  the witness's pending reverse slots before the earlier restore call.

Graph Bound records are per physical side and retained relation, not an
arbitrary mirrored inequality list (`candidate_scheme.rs:408–434`). Capturing
`B + b` therefore does not silently emit `b - B`. If a parent/copy pair already
merged before capture, endpoint interning and row lookup canonicalize it
(`177–178`, `190`), preventing reconstruction of its old distinct pair from
the aliased rollback storage alone.

## The nested drain itself is real

Restoration appends first, freezes owner, bound and opposite count, then reads
an opposite slot for each index (`candidate_extrusion.rs:611–616`). Fresh
context transport before it attaches relation metadata, not physical opposite
bounds (`candidate_scheme.rs:1019–1032`).

| Restore iteration condition | Can this iteration drain and settle SCCs? |
| --- | --- |
| No physical opposite bounds (`count == 0`) | No iteration; no nested drain |
| Opposite slot but either input relation fiber absent | Replay produces no Cartesian pair; publish invokes no constraint drain |
| Both fibers have at least one relation | Each published relation invokes `constrain_live_item`, which drains and settles |
| Freshen starts with empty fresh rows | The first incident bound can have no opposite; later restored bounds or earlier induced constraints can supply opposites |

`candidate_context_replay_impl` reads literal keys at
`candidate_context.rs:1943`, constructs the Cartesian pairs at `1952–1983`,
then calls publish. Restore's publish callback invokes `constrain_live_item`
for every relation (`candidate_extrusion.rs:635–639`). That function calls SCC
settlement at an empty-worklist boundary (`lib.rs:11838–11845`). Normal
`candidate_replay_bound` instead enqueues inside its callback (`684–687`);
its loop has no synchronous settlement callback.

SCC adjacency uses physical owner-to-bound edges from both sides; storing
`B + b` gives B→b, not b→B (`candidate_intrusion.rs:390–413`). Only actual
recorded parent/copy pairs in the same SCC are selected, in parent-record
order (`477–506`). `TopNegative` does not prevent this calculation:
`Dependencies::intern` excludes it (`626–635`), and `edge` skips excluded
endpoints (`655–658`). It remains a physical opposite slot for restoration.

If the injected setup and successful allocation/drain hypotheses are supplied,
its first published b <: O comparison can settle both already-qualified
pairs. Subsequent merge appends/transports both sides, changes representatives,
canonicalizes contextual keys, and replays parent lowers
(`candidate_intrusion.rs:559–603`). The outer restore still has saved b and
count 2; its next key can mix the new owner O with stale b
(`candidate_extrusion.rs:632`). The replay consumer canonicalizes the task pair
but reads the supplied keys literally (`candidate_context.rs:1938–1943`). This
establishes the dynamic key/vector transition only. The alleged first miss of
`BoundKey(O,+,b)` is refuted: the preceding b <: O comparison inserts that
exact key before the merge. The missing bridge for any stronger defect claim
is therefore not merely generation of the setup; one must show an omitted
incoming-use obligation while accounting for this historical fiber and the
merge's own replay. The old exact slot can also move beyond the saved index
range when direct bounds are appended, but that observation alone establishes
no lost diagnostic or unsound publication.

## Coverage, independence, and next action

No source program witness was found. The failed direct paths are orientation
of reverse constraints, ordinary omission of TopNegative, nonlocal capture of
the level-0 owner, and fresh generic owners lacking the required copy record.
This is not an exhaustive source search. Effects' capture-incidence expansion
(`candidate_scheme.rs:488–495`), different levels, structural Functions,
indirect creation of pending cycles during earlier reconstruction, changes to
shared bound endpoints, and opposite-vector growth are unverified.

No executable oracle, seeds, ranges, mutation campaign, or solver execution was
used. Oracle independence is therefore inapplicable. The evidence comes from
actual source ownership rather than a model assuming transitions, but shares
the compiler implementation and frozen baseline with the prover audit.
Success of allocation and route handling is conditional; static inspection
does not establish execution, termination, or publication conformance. This
producer does not independently review its own output or certify the prover.

Checks actually run: bounded `cat`, `rg`, numbered `sed` slices, dependency
`sha256sum`, and the initial read-only Git queries disclosed above. No tests,
builds, compiler edits, shared-record edits, descendants, or Git mutations.
Only this note was written. Shell reads were short lived; zero Cargo processes,
zero measurement samples. CPU/RAM and wall-time totals were not measured.
Writing stops at handoff for frozen review.

Recommended next action: retain this exact trace as API-only evidence and
assign one different, bounded source construction targeting a shared copied
bound endpoint or opposite-vector growth during normal freshening, rather
than replaying the same directly injected Value owner setup.

## Commit packet

- Exact lease: `notes/progress/2026-10-10-canonical-bound-fiber-reachability-audit.md`.
- Baseline: `1007224e2e7e6efab1590bd88c54bcb0a1fe8ff6`; primary confirmed frozen
  dependency identity despite unrelated HEAD movement.
- Dependency changes: none by this producer; no changed dependency hashes.
  Observed SHA-256: `candidate_scheme.rs`
  `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11`;
  `candidate_extrusion.rs`
  `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a`;
  `candidate_intrusion.rs`
  `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0`;
  `candidate_context.rs`
  `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337`;
  `candidate_effect.rs`
  `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e`;
  solver `lib.rs`
  `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1`;
  contextual attachment design
  `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
- Review status: unreviewed characterization, no closure; frozen on handoff.
- Checks: static source/rule/skill reads and hashes only; no executable check.
- Proposed message: `research: characterize source reachability of restore-bound SCC witness`.
- Shared deltas left for primary/curator: mark exact two-pair trace API/injected,
  retain nested-drain and literal-key seam, record failed direct Value source
  bridges, keep alternative source witnesses and lifecycle closure open.
