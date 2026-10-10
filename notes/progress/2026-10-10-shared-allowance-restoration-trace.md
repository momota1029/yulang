# Shared Allowance restoration: the mixed-root fixture

Date: 2026-10-10
Status: frozen unreviewed bounded static derivation; no execution, source counterexample, R closure, or production-conformance claim
Assigned baseline: `26b89d7b4d587ad8fac09c72c35c6343f2326554`
Producer: `/root/shared_allowance_restoration_trace`, source-correspondence leaf; no descendants
Exclusive lease: this note only

## Objective and result

Trace the second body of
`crates/yu-solver/tests/candidate_effect_annotation.rs:346–355`,
`concrete_root_member_stays_local_when_the_row_also_has_a_shared_tail`:

```yulang
act tick:
    our next: () -> int

my maker f = {
    my local:[tick, 'e] (int -> ['e] int) = {
        my ignored = f ();
        my ident x = x;
        ident
    };
    local
};
my late = maker tick::next;
my checked:int -> [] int = late
```

**Result:** the final `local` lookup inside `maker` realizes the shared-owner
incidence premise, including real extrusion provenance. Its shared owner has
zero positive lowers, so restoring its negative Allowance cannot enter the
first callback required by witness condition 2. Later restoration callbacks
can drain the worklist and inspect SCCs, but do not add a positive lower to
that shared owner or connect it back to its parent. This fixture therefore
does not realize all four witness preconditions for R at this lookup.

This is a source-directed derivation under the normal successful candidate
schedule, not an observed solver trace. Coordinates below are source roles
with level suffixes, not observed numeric row IDs. The result does not exclude
a witness at another lookup or after a different source construction.

## Authority, claim class, and hypotheses

The governing contract is contextual attachment/admission design §§3–4:
§3.1 distinguishes exact annotation occurrences, while §4 requires retained
contexts/origins, ordered opposite replay, joint graph capture/freshening,
actual parent/copy SCC intrusion, and route rollback. The existing approved
covariant annotation meaning and Simple-sub row-level orientation are retained.
No new language meaning or source restriction is proposed.

The four witness conditions are those in
`2026-10-10-canonical-bound-fiber-source-witness.md`, “Exact missing witness
and next action”: shared incoming incidence with actual parent provenance;
a first callback that changes the opposite vector/SCC before another index;
an exact obligation outside the remaining index range; and no insertion,
merge, or diagnostic rescue for that use.

Claim class: **bounded characterization with a conditional static exclusion**.
Hypotheses are that the displayed source has its ordinary supported HIR
projection, the candidate source schedule is used, indices and representative
forests are valid, allocations and invoked operations succeed, and no external
mutation interleaves the synchronous calls. No unrelated constraint supplies
a lower to `f` during its own definition's body schedule. The fixture's actual
parsed HIR and numeric fiber/row inventory were not obtained by execution.

## Coordinates and authentic extrusion

| Coordinate | Meaning before the final `local` lookup |
| --- | --- |
| `f1` | `maker`'s Value parameter, level 1 |
| `I3` | fresh invocation Effect row for `f ()`, level 3 |
| `C1` | negative Effect copy of `I3` carried by the Function demand installed on older `f1`, level 1 |
| `A3` | application computation Effect row of `f ()`, level 3 |
| `Effect2` | initializer block's computation Effect row, level 2 |
| `Outer1` | outer block computation Effect row, level 1 |
| `T2` | the annotation-local `'e` Effect row, level 2 |
| `F` | Function result annotation view: allowed set empty, tail `T2` |
| `P_F+2`, `P_F-2` | paired positive/negative Function result Effect ports |
| `R` | root computation annotation view: allowed set `{tick}`, tail `T2` |
| `P_R-2` | root computation's negative Effect port |

Source scheduling starts at level 1 (`candidate_source.rs:229`). A Lambda's
parameter and body retain that level (`246–261`); each block initializer adds
one level (`263–280`). Thus `f1` is level 1, `local`'s initializer/annotation
is level 2 with boundary 1, and `ignored`'s call is level 3. Parameter names
use the actual Parameter endpoint (`184–191,1283–1298` in `shadow_apply.rs`
for endpoint interpretation), rather than a separately fresh local scheme.

The call allocates `I3` before checking its Function demand against `f1`
(`shadow_apply.rs:1340–1385`). A structured negative upper is extruded to the
receiving Value row's level (`lib.rs:11958–11973`). In that extrusion the
result Effect port is visited negatively. Since `I3` is fresh, its negative
bound snapshot is empty. The copy constructor allocates `C1`, retains the
actual record `(copy=C1,parent=I3,polarity=Negative,target=1)`, and inserts

```text
BoundKey(EffectRow(I3), Positive, EffectRow(C1)).
```

These are `candidate_extrusion.rs:88–121` and
`candidate_intrusion.rs:171–222`. In particular, the constructor does **not**
insert `BoundKey(C1,Positive,I3)`. Parent provenance itself is absent from SCC
adjacency; it is not an executable reverse edge.

The call's later `I3 <: A3` effect link is owned negatively by `I3` because
both rows are level 3. Replay propagates `C1 <: A3`; this is owned positively
by the younger `A3`. Installing `ignored` links `A3 <: Effect2` and replay
propagates `C1 <: Effect2`, owned positively by `Effect2`. Installing `local`
also links its one-shot `Effect2 <: Outer1` before annotation admission
(`candidate_source.rs:283–299`); propagation can retain
`BoundKey(C1,Negative,Outer1)`, because both are level 1.

Every one of those uses the level orientation in
`candidate_extrusion.rs:736–749`. None inserts a positive lower on `C1`.
The parameter `f1` has no positive Function provider in this prefix; the
later `maker tick::next` source action has not run. `ident` and the literal/
Name evaluation rows are pure. They can supply Bottom to computation rows,
but cannot supply a concrete member or Function provider to `f1`/`C1`.

## Annotation incidence: the actual three keys

The local annotation constructs its negative Function pair first, then its
positive pair; it checks the initializer, checks the explicit root computation
row, links the positive pair to a new local scheme root, and installs that
root (`candidate_effect.rs:1005–1037`). Both occurrences use the same scoped
Effect-variable constructor for `'e`, so they share `T2`. Their view IDs differ
because `views` is keyed by each exact `SourceEffectRow.position`
(`1380–1424`). This is shared tail identity, not shared attachment authority.

The Function result ports contain

```text
BoundKey(P_F-2, Negative, Allowance(F[T2]))
BoundKey(P_F+2, Positive, Support(F[T2])).
```

The explicit root row creates a separate negative port, with

```text
BoundKey(P_R-2, Negative, Allowance(R[{tick};T2])).
```

`candidate_annotation_computation_effect` compares `Effect2` with that port
(`1172–1207`). With both at level 2, the immediate stored row bound is
`BoundKey(Effect2,Negative,P_R-2)`. Existing lower `C1` reaches `P_R-2`,
is stored there positively, and meets its Allowance, producing

```text
BoundKey(C1, Negative, Allowance(R[{tick};T2])).
```

Consequently the `T2` incoming-incidence bucket contains, in first-registration
order, exactly these physical-key families:

1. `BoundKey(P_F-2,Negative,Allowance(F[T2]))`;
2. `BoundKey(P_R-2,Negative,Allowance(R[{tick};T2]))`;
3. `BoundKey(C1,Negative,Allowance(R[{tick};T2]))`.

Capture registration deduplicates `(source,view)` and appends bucket links
(`candidate_effect.rs:372–399,426–432`). Multiple contextual fibers of a key
are captured separately; this list does not invent a numerical fiber count.
Neither `I3` nor `Effect2` is itself one of these incoming-incidence owners:
their pertinent stored uppers are row endpoints. A root Allowance is not
positive root Support (`1172–1184`), so the concrete root member supplies no
positive `tick` seed to `T2` or the local Function scheme.

## Final lookup: capture, freshening, and restoring order

The block executes the `local` install before the final local Name action.
`route_candidate_local` then captures the live scheme at boundary 1, freshens
at use level 1, restores all captured bounds, and only afterward links the
fresh value into the receiving occurrence (`candidate_scheme.rs:1115–1148`).
This is a transactional use-time observation, not the installation of a
closed immutable authority.

The scheme root's positive annotated Function reaches `P_F+2`; its Support
reaches `T2` (`candidate_scheme.rs:333–344`). The local `T2` expansion visits
incoming incidence *before* its own bound vectors (`488–500`). It emits all
fibers of the three keys above. The newly reached negative ports' own row
expansions occur later: `capture_candidate_graph_inner` expands pending nodes,
then advances its row cursor monotonically (`598–605`). Duplicate key/fiber
emissions from their own upper vectors are suppressed (`408–434`). Thus the
three incidence negative-bound groups precede the captured positive lowers of
`P_R-2` and `P_F-2`, independent of their later row visitation order.

Freshening maps `T2`, both captured Function ports, `P_R-2`, and the local
scheme root to new level-1 rows. It maps `C1` to itself: level 1 is not above
boundary 1 (`841–853`). All row maps are chosen before restoring any bound.
The map canonicalizes coordinates, but no qualifying `C1/I3` merge occurred
in the preceding source prefix. `C1` therefore remains the genuine shared
owner. Each original view is copied once per `(old_view,mapped_tail)` within
the use (`879–897, candidate_effect.rs:671–711`): write these copies as
`F_u[T_u]` and `R_u[{tick};T_u]`. They retain shared `T_u` inside this use and
fresh view identity across uses. `canonical_effect` only renames rows
(`lib.rs:11334–11339`); an Allowance view ID is stable under row equality.

For each captured relation, reconstruction transports it to its exact mapped
BoundKey and then calls `candidate_restore_bound` in captured-bound order
(`candidate_scheme.rs:998–1032`). In the incidence prefix:

| Restored key | Opposite positive bounds at that point | Callback |
| --- | --- | --- |
| `P_F-_u - Allowance(F_u)` | none: its positive template bounds restore later | none |
| `P_R-_u - Allowance(R_u)` | none: its positive template bounds restore later | none |
| `C1 - Allowance(R_u)` | none: shared `C1` has never received a positive lower | none |

The final row is the decisive falsifier for condition 2. Inserting an upper
can journal state, attach fibers, register incidence, and mark intrusion dirty;
those operations do not synchronously drain a queue. Restoration takes
`count=0`, so there is no outer index, Cartesian replay callback, or nested
SCC settlement before a “next” opposite bound (`candidate_extrusion.rs:607–641`).
This remains true if that captured key has multiple fibers.

Later, the local negative root port's copied positive `C1` lower restores.
Its already restored `Allowance(R_u)` is an opposite upper. Each Cartesian
callback can call `constrain_live_item(C1,Allowance(R_u))`, draining the
worklist and settling SCCs before the next relation/bound. This may append
another physical negative Allowance on `C1`; it cannot create a positive
lower on `C1`. A copied Bottom lower on either negative annotation port also
invokes a callback whose Bottom comparison has no downstream effect. No
positive Support on the root computation port is captured or replayed.

The original `I3` and `Effect2` are outside this value-scheme graph: older
`C1` is reached through incidence and its mutable bounds are not expanded
(`440–442`); parent provenance and relation dependency endpoint IDs are not
additional capture edges. Their source relations still live in the session.

## SCC and replay rescue analysis

The relevant original Effect paths go forward from `I3` to `C1`/`A3`, from
`A3` to `Effect2`/`C1`, and from `Effect2` to the root port/outer computation.
`C1` has outgoing upper paths to root Allowance/tail and outer computation;
`T2` has no body-generated positive contribution or return path to `I3`.
The displayed initializer has no recursion and no Function provider into
`f1` that could supply the opposite invocation flow. The separately recorded
parent link does not close that path.

Freshening adds new ports/tail and their inherited outgoing graph, including
new root-port-to-`C1` dependency through its positive lower. Shared `C1` obtains
an upper path to the fresh tail, which has no bound back to that root port or
`I3`. Support/Allowance operands contribute only an edge *to* their tail in
the dependency builder (`candidate_intrusion.rs:382–448`). Restoring the
scheme root's positive Function creates outgoing edges to its own ports,
not an edge from `T_u` to `I3`. Thus the later callbacks have no qualifying
`C1/I3` SCC to merge (`477–493`), and create no direct opposite lower at `C1`.
The real parent record remains stored: successful settlement does not delete
it; `parents.truncate` belongs to rollback (`103–115`).

If a different route did make a parent/copy SCC qualify, the present source
consumer appends both sides, transfers origins and contextual fibers,
canonicalizes bound keys, then replays each canonical parent lower against
its uppers (`candidate_intrusion.rs:548–603`). Ordinary effect insertion also
replays opposites (`candidate_extrusion.rs:746–749`). These rescues cannot be
ignored in a proposed counterexample. Here no omitted obligation is produced,
so conditions 3–4 never acquire an exact target; no rescue-failure claim is
made.

For a nonempty restoration, the saved physical opposite count and saved owner/
item surround calls that enumerate the two current literal bound-fiber heads.
`candidate_context_restore_replay` bypasses ordinary replay frontiers and
dependency deduplication for the incoming use (`candidate_context.rs:1938–1977`).
Its relation list is built before callbacks; each callback drains the live
solver and can settle dirty intrusion (`lib.rs:11838–11846`). This derivation
does not prove that those snapshots cover every subsequent mutation for R.

## Effect and Value diagnostic paths

All callback comparisons use the incoming local occurrence/cause. At return,
Effect conflicts are traversed from the original initial pair and its current
canonical pair through `context.children` (`candidate_effect.rs:524–580`).
That traversal includes all relation contexts retained for an endpoint pair,
not only the restored fiber (`candidate_context.rs:1515–1521`). Derived and
FunctionPort dependencies connect parent to child; Replay connects both bound
parents to the replay child (`1445–1477`). Ordinary FreshUse transport alone
is not an executable diagnostic edge upstream. Equality canonicalization
retains additional derived paths (`1994` onward).

A Value initial comparison follows its diagnostic edges/replayed witness.
An Effect initial comparison also reports any Value diagnostic delta induced
by mixed SCC work under the same incoming cause (`lib.rs:12089–12099`). A
Value-root merge can reopen that root and attach ordinary replay edges.
These are separate potential rescue routes for a future witness.

At this lookup, the directly replayed concrete operands are Bottom; root
`tick` is an allowance member, not a supplied contribution. `C1` has no
lower to test. There is no exact hidden Effect mismatch whose absence must
be inferred from an unvisited vector index. This does not certify all later
`late`/`checked` diagnostics or the fixture's test assertion by execution.

Failure returns through `?`, rather than resuming the successful restore loop.
`route_candidate_local` owns the route transaction; rollback restores algebra,
forests and vectors. Failure/rollback publication correctness remains outside
this successful-prefix exclusion.

## Checks, resources, omissions, and next action

Commands used: bounded `cat`, `sed`, `rg`, `sha256sum`, and one read-only
`git rev-parse HEAD` in the initial shell call. **That Git command violated
the assigned packet's no-Git restriction.** No further Git command and no Git
mutation occurred. No Cargo/test/build/probe, mutation campaign, formatting,
model-policy change, interactive question, or descendant was used. Only this
leased note was written. Several broad locator captures truncated; subsequent
narrow source slices supplied the owning constructors/consumers quoted here.

Compute: zero heavyweight processes, zero executable samples, no seed/range
enumeration. CPU/RAM and exact wall time were not measured. Shell calls only
performed static reads and the note write. No independent executable oracle
exists here: this derivation shares implementation and authority assumptions
with the constructive lane and is not independent review of that lane.

Unverified: actual parsed HIR, numeric row/relation/fiber inventories, execution
of either test body, top-level later uses, other source shapes, nonidentity
mixed contextual SCC admission, arbitrary R, full Call, hygiene, termination,
soundness and principality. The fixture is not claimed minimal.

Recommended next action: target one authentic source schedule that places a
positive lower on the shared incidence owner *before* capture and independently
closes its recorded parent/copy SCC during restoration; keep this fixture as
a static exclusion instead of rerunning an equivalent empty-lower probe.

## Frozen direct dependency hashes

Hashes were read before note construction and must be rechecked at handoff.
The baseline was supplied by the primary and observed by the single forbidden
read-only Git query; current-file equality with baseline blobs was not checked.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-solver/tests/candidate_effect_annotation.rs` | `46207880936209875117a48aba44fb19ed2736afcd827e8d6d5bab5ee41109a2` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-10-canonical-bound-fiber-source-witness.md` | `715143ea458825c88d41aa0ce7cb57be8290dd5586c1bd7cc0f86e1537721c77` |

## Commit packet

- Exact lease: `notes/progress/2026-10-10-shared-allowance-restoration-trace.md`.
- Baseline: `26b89d7b4d587ad8fac09c72c35c6343f2326554`.
- Dependency changes: none observed during construction; final recheck belongs
  to the handoff report, and primary integration must verify baseline equality.
- Review: frozen unreviewed research characterization; no independent review.
- Checks: static source slices and dependency hashes only; no execution. The
  single read-only Git packet violation is recorded above.
- Proposed commit: `research: exclude empty-lower shared allowance restoration fixture`.
- Shared deltas left for primary/curator: record condition 1 as source-realized
  here and condition 2 as excluded at this final local lookup; leave R open;
  direct the next witness lane to a shared owner with an existing lower and a
  newly qualifying real parent/copy SCC. No shared record was modified.
