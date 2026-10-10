# Restoration replay: source producers and remaining witness

Date: 2026-10-10
Status: unreviewed research characterization; conditional local exclusions; no source counterexample, R closure, or production-conformance claim
Assigned baseline: `e25608d5881123438c57bcba354571611fd98283`
Branch supplied by primary: `research/simple-sub-intrusion`
Producer: `/root/restore_replay_source_witness`, leaf; no descendants
Exclusive lease: this file only; frozen on handoff

## Objective, authority, and method

Find an authentic source construction in which a nested restoration drain grows
or replaces the opposite-bound vector and skips an incoming-use obligation
after accounting for ordinary insertion replay, SCC merge replay, and diagnostic
origins. This is a source-constructor/falsification audit, complementary to the
constructive R lane. No finite model, solver execution, or theorem about all
source programs is supplied.

Authority is `tasks/current.md:8170–8205` and contextual attachment/admission
design §4 (Bound insertion, Opposite replay, Capture/freshening, SCC intrusion,
Rollback), with §3.1 retaining the selected attachment grouping. The accepted
correction is that the old allegedly absent `BoundKey(O,+,b)` already exists
because the preceding nested comparison inserts it. That trace is not reused.
The earlier prover and reachability audits are dependencies, not authority for
an omitted-pair conclusion. Language meaning, source support, and implementation
gates are unchanged.

Result: **no authentic source witness found**. The distinct Effect incidence
route can restore onto a shared owner; the earlier Value fresh-owner exclusion
does not cover it. Two tempting shortcuts on that route are excluded below:
its restored allowance is a fresh, stable view ID, and a successful owner merge
schedules canonical lower/upper replay. Complete within-use replay and diagnostic
coverage remain open.

## Production owners inspected

The call-site search for `candidate_restore_bound`, `candidate_insert_bound`,
and `candidate_insert_bound_without_capture` found these production owners;
calls below `candidate_effect.rs:1437` belong to its `cfg(test)` module and are
not evidence of ordinary source generation.

| Producer | Physical insertion and synchronous behavior |
| --- | --- |
| Ordinary Value application | `candidate_extrusion.rs:694–723`; chooses side by row levels, inserts, then queues opposite replay |
| Ordinary Effect application | `candidate_extrusion.rs:726–750`; analogous level orientation, with nonrow operand handling in `candidate_effect.rs:753–820` |
| Extrusion | `candidate_extrusion.rs:112–175,293–324`; fresh copies, actual parent records, one-sided links, selected bound copies, and incoming allowances |
| Source Effect signature construction | `candidate_effect.rs:1304–1433`; fresh ports with Support/Allowance bounds |
| Scheme restoration | `candidate_scheme.rs:998–1032`; the only production caller of `candidate_restore_bound` found in this search |
| Parent/copy merge | `candidate_intrusion.rs:548–603`; append both sides, transfer fibers/origins, update representative, canonicalize fibers, then replay every canonical parent lower |

Context filter execution at `candidate_context.rs:1807–1868` invokes the same
Effect application/replay routes. It is not a separate direct vector writer.
Direct vector writes in the inspected legacy `lib.rs` application branches are
bypassed when the candidate graph is present (`lib.rs:11581–11584`, Value
candidate dispatch at `13014–13016`). This is a bounded owner audit, not a claim
that all compiler mutation sites have been exhaustively classified.

## Exact Effect incidence chain

Use `s - Allowance(v)` for an upper bound physically owned by Effect row s.
The following derivation has explicit hypotheses:

1. A valid, successful candidate route has retained a physical negative
   allowance bound `s - Allowance(v)` whose view has tail t.
2. Capture reaches t and classifies t local: `level(t) > boundary` and
   `!non_generic(t)`. The source row s is nonlocal and remains nonlocal until
   its freshening row mapping is chosen.
3. Capture/freshening use the inspected normal route, valid graph indices,
   and successful allocations; no external mutation injects Graph records.

These are conditional state hypotheses. In particular, hypothesis 1 together
with a nonlocal *copied* s and a local t has not been reconstructed from a
complete source program here.

The production chain is:

1. Bound insertion registers capture incidence after physical insertion
   (`candidate_extrusion.rs:529`; `candidate_effect.rs:426–432`). Registration
   canonicalizes the tail, then retains `(source=s, view=v)` in the tail bucket
   (`372–399`). This is capture metadata, not an additional SCC graph edge.
2. `Capture::expand_row(t)` skips nonlocal rows at `candidate_scheme.rs:440–442`,
   but for local Effect t enumerates its incoming incidence at `488–495`.
   It emits a **negative** bound with lower `EffectRow(s)` and upper
   `Allowance(v)`. It does not require s itself to be local. `Capture::bound`
   records the actual owner side and each retained fiber (`408–434`).
3. Freshening allocates rows only for still-local, eligible generic coordinates
   (`841–852`). Thus s maps to its shared representative, while t can receive
   a fresh use-level row. The Allowance operand is remapped at `879–889`.
4. Reconstruction extracts the remapped endpoints, chooses the lower endpoint
   as owner for a negative bound, transports the captured relation, and invokes
   restoration (`998–1032`). The physical restore owner is therefore shared s,
   not necessarily a newly allocated generic row.

The source schedule reaches these constructors through
`candidate_source.rs:552–570` (formal/whole annotations and local uses),
`candidate_formal_effect_port` (`candidate_effect.rs:919–935`), and the signature
constructor. A covariant mixed row can create a paired Support/Allowance view
with a symbolic tail (`1304–1433`). Ordinary Effect comparison can install an
Allowance on a row receiver (`candidate_extrusion.rs:736–749`). These establish
actual producer seams. They do **not** establish the exact levels, prior parent
record, captured-root reachability, bound order, or pending SCC needed for a
failure witness. An API-created s/t/parent state is still injected evidence.

For Value, normal row expansion emits only the local owner's own four vectors
(`candidate_scheme.rs:446–484`); it has no analogous incoming-incidence loop.
A shared Value endpoint can still occur as a bound item or Function port.
Those cases are outside the earlier exclusion and remain unverified here.

## Discriminating exclusions for the Effect route

**Fresh allowance identity.** On successful normal freshening, its operation
local view map starts empty (`candidate_scheme.rs:870–873`). A first remap calls
`candidate_copy_effect_view`; that calls `candidate_signature_view`, which
allocates `id = views.len()` and appends a view (`candidate_effect.rs:671–711,
598–635`). This occurs even when the tail is unchanged. Later remaps of the same
`(old_view, mapped_tail)` within the use share that new ID.

Consequently `Allowance(v_use)` did not exist before this freshening use.
No pre-use replay frontier can already name a pair containing that exact view
ID. This rules out an **earlier-use frontier** as the immediate explanation for
suppression of this restored incidence pair. It does not rule out frontiers
already established earlier in the *same* freshening loop, or repeated fibers
whose relation identity is unchanged within that use.

`canonical_effect` changes only EffectRow endpoints (`lib.rs:11334–11339`).
Thus the restored negative bound item `Allowance(v_use)` is stable through row
intrusion. Unlike the rejected Value trace's saved row item, this saved item
cannot become a stale row representative. The owner and opposite row endpoints
can still change, and the view's tail can name an aliased row.

**Physical omission is insufficient.** Restoration freezes the count and uses
the current direct-vector length to interpret each index
(`candidate_extrusion.rs:534–590,611–616`). Appending a direct row can shift an
old exact entry beyond the saved range. Replacing the canonical owner can also
change which slots appear there. Neither observation supplies a missed
incoming-use obligation.

If the shared owner receives new bounds through ordinary application, that
application invokes opposite replay (`716–717,748–749`). If an actual parent/copy
merge replaces or grows its canonical owner, the merge appends both sides,
transports contexts, updates the forest, canonicalizes keys, and enumerates every
current parent lower against its current uppers (`candidate_intrusion.rs:548–603`).
The restored allowance participates in this canonical upper storage.
The nested work is drained before returning to the restore loop
(`lib.rs:11838–11846`). This is actual scheduling evidence, not a proof that all
required incoming-use comparisons execute: ordinary contextual replay uses
frontiers and dependency deduplication, whereas restoration explicitly bypasses
them (`candidate_context.rs:1938–1977`).

**Length shrink is not the source seam.** In the inspected successful
insert/merge envelope, insertions append, and a merge appends the entire copy
side to the parent before changing the representative. Therefore replacement
does not reduce that side's total direct-plus-exact count. The fixed count can
select different entries, but this envelope does not itself make an old valid
index out of range. This local exclusion assumes valid row kinds, successful
calls, and no external clearing/deduplication. It says nothing about complete
pair or fiber coverage.

## Incoming diagnostics and rollback ordering

Every direct restore callback uses the incoming occurrence/cause
(`candidate_extrusion.rs:635–637`). A Value-root nested merge receives that
root, records diagnostic edges via ordinary replay, and reopens it
(`candidate_intrusion.rs:596–603`; `candidate_extrusion.rs:664–666`). An Effect
root also replays any Value diagnostic delta under the same occurrence/cause
(`lib.rs:12093–12098`).

Effect conflicts are replayed from the actual initial pair and its canonical
pair, traversing contextual children (`candidate_effect.rs:524–580`). Replay
dependencies create edges from both bound inputs; Derived dependencies create
parent-to-child edges. FreshUse transport itself creates no executable edge
(`candidate_context.rs:1445–1477`). The search uses endpoint-pair children across
all retained relation contexts (`1515–1521`). A complete witness therefore must
show absence of the relevant conflict path, not merely absence of a second
direct call to `constrain_live_item` for that outer index. This audit did not
establish all such paths.

Failure cannot ordinarily shrink the vector and then resume that outer loop:
its nested calls return through `?`. The route transaction restores on Err
(`lib.rs:9155–9176`). Rollback first restores context/algebra and forests
(`lib.rs:9311–9314`; `candidate_intrusion.rs:103–115`), then truncates physical
row vectors/restores levels (`lib.rs:9359–9411`). Context restores replay heads
from its log (`candidate_context.rs:1098–1100`); algebra restores incidence
links/buckets and truncates views (`candidate_effect.rs:178–205`). Intermediate
rollback state is not a replay boundary. This ordering audit excludes a
successfully resumed-loop explanation based solely on matching rollback;
it is not a complete transaction/publication theorem.

## Exact missing witness and next action

The missing bridge is one ordinary source/use schedule that simultaneously:

1. Captures a local Effect tail whose incoming allowance is owned by a shared
   row with actual extrusion provenance, or by a shared parent receiving a copy.
2. Restores that negative allowance while at least one opposite lower exists;
   its first Cartesian callback closes a previously unqualified recorded SCC
   or otherwise adds direct opposite bounds before the next outer index.
3. Identifies one exact lower relation/upper relation obligation outside the
   remaining outer index range.
4. Shows that ordinary insertion/merge replay fails to activate that obligation
   for this use, and that Value diagnostic edges/Effect contextual children do
   not report its result through another nested initial pair.

There is no claim of minimality for this envelope and no enumerated program
domain. Source program syntax or a complete action trace satisfying all four
conditions is still needed. Ordinary shared owner availability alone supplies
only condition 1's constructor seam. A larger toy transition count would leave
the same source/order and diagnostic premise untouched.

Recommended next action: obtain **one source-generated, within-use Effect
incidence trace** containing the actual row levels, parent records, restore
order, before/after vectors, replay frontier heads and diagnostic reachability;
use it to discriminate conditions 2–4. Production/test instrumentation requires
a separate lease. Keep R open pending that evidence or the constructive lane's
reviewed coverage argument.

## Checks, resources, and dependencies

Checks run: sequential bounded `cat`, `sed`, numbered `nl` slices, `rg` searches,
and `sha256sum` reads; no Git commands, Cargo, builds, tests, benchmark, mutation
campaign, executable solver probe, or descendants. Only this note was written.
No independent oracle, seeds, or enumeration ranges apply. Source evidence
shares the candidate implementation and authority baseline with the proof lane;
it is not independent execution or independent review of that lane.

Budget: at most one active shell command at a time; zero heavyweight processes
and zero measurement samples. CPU/RAM totals and exact task wall time were not
measured. The finite static search ended without a program witness. No timeout
or incomplete executable shard is concealed. Requested/observed runtime
model/effort metadata is unavailable to this leaf.

The following direct dependency hashes were observed and rechecked unchanged
before writing. The primary supplied the commit identity; this producer did not
query Git or compare committed blobs. Unrelated task/index movement is not
certified by these hashes.

| Dependency | SHA-256 |
| --- | --- |
| `candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| solver `lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| contextual attachment/admission design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

Historical input note hashes: prover audit
`5ca7f98a0e3ef53f83e869f9b6cbf21301ec861ffd5bef6c24d064eafe9df15f`;
reachability audit
`dc1ff5e26d5cf2568af3b23f54de4b9776f6ea65eccf6679f7f55ff6b63dca5c`.
Authored intrusion tests were read, not run; they are not execution evidence.
All-program source reachability, nonidentity fiber growth, Effect zero-word
filter behavior, all diagnostics/publication and lifecycle completion remain
unverified.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-canonical-bound-fiber-source-witness.md`.
- Baseline: `e25608d5881123438c57bcba354571611fd98283`.
- Changed dependency hashes: none observed; no dependencies changed by producer;
  hashes above identify the inspected snapshot.
- Review status: unreviewed research characterization; frozen at submission;
  no independent certification or R closure.
- Checks already run: static source/rule/skill searches and dependency hashes
  only; no executable verification.
- Proposed message: `research: audit Effect incidence restoration and replay witness gaps`.
- Shared-record deltas left for primary/curator: record the Effect shared-owner
  incidence seam, fresh stable Allowance discriminator, mandatory accounting for
  nested replay/diagnostics, and the exact four-condition source witness gap;
  retain R and lifecycle closure as open. No task/index/theory/question file was
  edited.
