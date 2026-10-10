# Positive tail extrusion: constructor invariant and selective-owner seam

Date: 2026-10-10
Status: unreviewed bounded derivation and reduced source premise; restoration R remains open
Assigned baseline: `4e5e60c81d834aafd736d45f28a1f197d012254a`
Producer: `/root/prover_equivalent_source_bridge`, prover-equivalent generic leaf
Requested routing: GPT-6.1 Sol/high; observed model/effort: unknown
Exclusive lease: this note; frozen at handoff

## Statement and scope

The question is whether one admitted ordinary HIR schedule can compose an
existing positive physical lower on an incoming-Allowance owner, positive
extrusion of its shared tail to a lower boundary, and a later local use that
restores an Allowance on the same nongeneric canonical owner with that lower
already present. A defect claim additionally requires a within-loop mutation,
an exact omitted obligation, and failure of subsequent ordinary replay and
Value/Effect diagnostic rescue.

Authority is contextual attachment/admission design §§3.1–5. Annotation
occurrences, member ordinals, nominal families, contextual derivations, and
parent/copy identities retain their existing meanings. This note adds no
semantics, rejection, carrier, invariant required of source programs, or gate
closure. The result is a constructor-local derivation and a minimized missing
source premise, not an ordinary-source witness or an impossibility theorem.

Quantification is over successful calls in a valid candidate session, valid
representative forests and endpoint/fiber indices, no external interleaving,
and no rollback removing the prefix under discussion. A local use captures
the live scheme before freshening. Original scoped rows and exact annotation
view identities are fixed. Representative changes are stated explicitly;
current-file hashes below pin the inspected implementation. The primary
supplied the baseline SHA; this producer did not inspect Git blobs.

## Constructor-local facts

The source scheduler starts at level 1, preserves a lambda's current level,
and visits each block initializer at its block level plus one
(`candidate_source.rs:229–280`). Local annotations receive level `boundary+1`
(`:283–300`). A signature Effect port is freshly allocated at that annotation
level; the scoped tail is allocated at the level of its **first** occurrence
(`candidate_effect.rs:844–864,1369–1381,1420–1433`). A later occurrence in the
same `(AnnotationScope,name)` reuses the earlier tail without changing its
level. Therefore “port and tail have equal levels” holds for a freshly scoped
row occurrence, not for every reused scoped variable.

For a composed-positive occurrence the negative port owns
`S - Allowance(v[T])`, and the separate positive port owns
`P + Support(v[T])`. The two ports use one occurrence view, while another
occurrence has its own view. The constructors create no reverse tail-to-owner
edge merely from the Allowance. The root computation annotation checks its
actual computation row once; it supplies no positive Support to that
computation (`candidate_effect.rs:1172–1207`).

A structured positive Function lower inserted into an older Value row invokes
positive extrusion at that destination's level (`lib.rs:11940–11956`). This
is an actual caller; a stored row-to-row relation alone does not invoke this
operation. Function arguments reverse polarity and results preserve it
(`candidate_extrusion.rs:209–244`). An invocation demand checked against an
older Value row instead invokes negative extrusion. Its negative result
Effect copy is a separate source route (`shadow_apply.rs:1340–1385`,
`lib.rs:11958–11973`), not evidence that positive tail extrusion happened.

Fix one positive extrusion at target t. Suppose the original canonical tail T
and its incoming canonical owner S both have levels strictly above t. The
operation maps them to fresh copies T' and C, both allocated at t. It records
actual parent pairs `(T',T)` and `(C,S)`, and inserts the one-sided source links
`T - T'` and `S - C`. It snapshots S's positive physical bounds and schedules
those bounds for positive insertion onto C. Its `IncomingAllowance` inserts
`C - Allowance(v'[T'])` and transports the original bound's fibers/origins
(`candidate_extrusion.rs:88–179,293–322`). These are physical insertions;
they do not synchronously replay opposites.

Thus an existing positive lower on S becomes a positive lower on C by successful
extrusion completion. When S is first visited by this incoming record, the
LIFO pending work visits S and finishes its queued bounds before popping that
record; a lower can therefore precede C's remapped negative Allowance insertion.
If S was mapped earlier with pending bounds, this insertion order is not a
universal guarantee (`candidate_extrusion.rs:77,163–179`). Neither fact supplies
the later capture/restoration. If S was already at or below t, it is reused;
if T was already at or below t, its row visit returns before traversing incoming
incidence. Those cases are outside the fresh-pair colevel statement.

## Why the isolated copied-tail route does not restore a shared copy

Capture classifies a canonical row as local exactly when its level is above
the scheme boundary b and its metadata is generic
(`candidate_scheme.rs:189–215`). It returns immediately from expansion of an
older/nongeneric row **before** traversing its incoming-Allowance incidence
(`:440–442,488–500`). Merely interning an Allowance/Support node also interns
its tail node; it does not bypass that row-expansion guard (`:321–344`).
Context payload views likewise intern their tail nodes without overriding the
guard (`:615–626`).

For the fresh pair C,T' at t, assume no intervening representative or metadata
change and capture obtains C's Allowance solely through T' incidence:

* If b >= t, T' is shared and capture stops before that incidence. C's live
  bounds remain in the session, but this route captures no negative key to
  restore on C.
* If b < t, both rows are local and both freshen. All row maps are selected
  before reconstruction restores bounds (`candidate_scheme.rs:841–853,
  998–1032`). The captured lower on C restores later on a new owner; it is not
  an already surviving lower on unchanged C at its first incidence restore.

This excludes the **isolated fresh copied-tail route under these stability
hypotheses**. It does not exclude another captured bound exposing C, an older
original S, reused scoped tails, metadata changes, or an intervening merge.
In particular it must not be promoted to a global level invariant.

## Selective parent/copy intrusion breaks the colevel argument

The actual SCC graph follows every physical bound from owner to item, follows
Allowance/Support to their tail, and follows Function constructors to their
ports. Creation provenance is not an SCC edge. Eligibility checks each recorded
parent/copy pair independently (`candidate_intrusion.rs:382–493`). There is
no condition requiring the owner pair `(C,S)` and tail pair `(T',T)` to merge
together.

If an actual extra path C -> ... -> S closes the owner pair, merging C into S
appends both C bound sides to S, transfers all fibers/origins, changes S's
level to `min(L(S),L(C))`, and leaves unmerged T and its view unchanged
(`candidate_intrusion.rs:549–603`). Original `S - Allowance(v[T])` remains.
For L(T)>b>=t, S is now shared at t while T remains local above b. Capture
through the original generic T can emit that original Allowance on S;
freshening leaves S unchanged and restores the mapped view with a fresh T_use.
Original S lowers and transferred C lowers survive on S before that restore.

This is an exact conditional escape from the colevel exclusion. It does not
claim the extra path is source-reachable. A schematic dependency graph makes
the uncoupled condition independently checkable:

```text
S_d -> C_t                       actual positive-extrusion source link
S_d -> Allowance(v[T_d]) -> T_d  original incoming incidence
T_d -> T'_t                    actual positive-extrusion source link
C_t -> Allowance(v'[T'_t]) -> T'_t
C_t -> ... -> S_d               REQUIRED extra path
```

The first four lines alone have no return from C to S. A return can put C and S
in one SCC while T and T' remain outside it. If instead the added path puts T'
and T in the same SCC, tail intrusion lowers T too; capture through that tail
again stops. Both membership tests must be checked on the same actual graph.
View ID equality is unnecessary for owner merge and is not implied by it.

### Actual constructors to inspect for the extra path

These are concrete producer/consumer seams, not an inventory or a proposed
source program:

1. `candidate_annotation_computation_effect` admits the actual computation row
   against its negative annotation port (source slot 42 for local bindings,
   slot 47 for expression ascription). With a preexisting older C lower on
   that computation/port, opposite replay can admit
   `C <: Allowance(w[X_d])`; `candidate_apply_effect` stores that exact upper
   on C and capture registration adds incidence at X
   (`candidate_effect.rs:1193–1207`, `candidate_extrusion.rs:736–749`). This
   supplies a possible C -> X_d seam without Value structural extrusion of
   that Allowance. The missing premise is the source producer that put this
   **same C** on that computation path, at the required time.
2. Ordinary Apply owns invocation-to-application and callee-evaluation links;
   Group owns child-computation-to-facade links; a block install owns its
   one-shot initializer-computation-to-block link
   (`shadow_apply.rs:1421–1462`, `candidate_source.rs:283–290`). At equal
   levels the relevant direct row comparison stores an upper on its lower
   row; at unequal levels ownership is selected by canonical levels. A
   path from X through these **identified actual rows** can reach S only if
   S is the true annotation negative port of the terminating computation
   check. Choosing an arbitrary intermediate row named X does not prove it
   is a scoped annotation tail.
3. A symbolic formal result port can supply the real scoped X row to a call:
   singleton symbolic formal rows return the same row pair
   (`candidate_effect.rs:918–935`), and Apply's Function result comparison
   links that row to its invocation row. Scoped row reuse can couple this X
   to the tail of an actual annotation at the same binding scope. A covariant
   Support's tail is enqueued only when the operand checker expands that
   Support (`candidate_effect.rs:753–776`); Support merely stored on a row
   does not independently emit a tail-to-that-row comparison.

These seams identify a finite, checkable missing premise: one actual HIR
action prefix whose admitted tasks connect the previously extruded C through
a genuine generic scoped tail/call computation back to its **recorded original
owner S**, while leaving the original tail pair outside a qualifying SCC.
Parameter Names use their Parameter endpoint; ordinary Names/literals are
pure. They cannot be treated as unconstrained contributions or as arbitrary
providers of this path (`candidate_source.rs:184–191,310–348`). A new local
annotation scope is not equal to an old scope merely because both spell `'e`.
No such complete prefix was established by this static assignment.

## Exact later restoration condition

Let a captured negative Allowance restore on canonical owner O, and let A be
its remapped Allowance endpoint. After insertion the consumer saves physical
opposite count N once. On iteration n<N it reads the **current canonical
owner's current concatenated direct/exact lower vector** and constructs the
two literal bound keys from that owner, that current lower, and saved A
(`candidate_extrusion.rs:599–641`). A has a stable view ID: `canonical_effect`
renames row endpoints only (`lib.rs:11334–11339`). Hence this particular
Allowance restoration does not have the saved-row-item/historical-mixed-key
failure mode of a restored row bound.

For state s_n immediately before contextual list construction, let l_n be the
actual read lower, o_n the current representative, and F_s(K) its literal
bound fiber. That iteration emits exactly the ordered product

```text
F_s_n(BoundKey(o_n,Positive,l_n))
    × F_s_n(BoundKey(o_n,Negative,A)).
```

The list is complete for those heads, bypasses ordinary frontier suppression,
and is frozen before its first callback. Each callback drains the worklist and
settles dirty parent/copy SCCs before the next callback/index
(`candidate_context.rs:1938–1994`, `lib.rs:11838–11846`).

The required dynamic seam is therefore a first nonempty callback whose drain
changes O's representative, direct/exact vector arrangement, or relevant
fibers **before a later obligation would be selected**. An appended direct
lower shifts the combined indices of old exact lowers. A copy-to-parent merge
places the destination's old prefix before appended source entries, while N
still addresses the old total. Fiber growth after a product list is built is
also outside that product. A mutation elsewhere is insufficient. For an exact
target ordered fiber pair omega, the necessary omitted-enumeration condition
is that omega is required for this admitted use and absent from every product
actually emitted during this restoration. N>0 or a qualifying merge alone
does not imply that condition.

The full use can still rescue it. Multiple captured fibers of the same key
cause further restore calls with newly saved counts; later positive bound
restorations can invoke the same Allowance again; and the final Value link
occurs only after all restoration (`candidate_scheme.rs:998–1032,1127–1135`).
A source witness must trace all of these before asserting loss.

## Ordinary replay and diagnostic rescue remain mandatory

A successful owner merge enumerates every merged-owner lower against every
current upper after transferring fibers and canonicalizing retained keys
(`candidate_intrusion.rs:593–603`). Ordinary insertion also replays its
opposites. Their contextual replay uses frontier/dependency suppression; a
suppressed callback is not by itself evidence that its semantic obligation or
incoming diagnostic was lost.

Value replay records a root-to-child diagnostic edge before contextual
suppression (`candidate_extrusion.rs:666–675`). Effect reporting traverses the
initial and current canonical pairs through all retained relation children;
Derived/FunctionPort dependencies and both Replay parents contribute edges
(`candidate_effect.rs:524–580`, `candidate_context.rs:1445–1477,1515–1521`).
An Effect initial drain also replays Value diagnostic deltas produced by mixed
SCC work (`lib.rs:12083–12099`). Equality transport adds Derived lineage;
FreshUse transport alone adds no ordinary diagnostic edge upstream.

Accordingly, a defect needs a named omega with its exact derivation, incoming
occurrence/cause and observable consequence, absent both from subsequent
replay coverage and from all applicable retained diagnostic paths. This note
has no source-authentic omega and establishes neither missed checking nor
missed reporting. R remains open.

## Economy, checks, and handoff

The invariant question was reduced at the owner of levels, capture, and SCC
merging. Another isolated copied-tail fixture would repeat the failed premise.
No new reconstruction layer or semantic clause is warranted by this result.
Restoration correctness remains safety/natural-inference work; existence of a
counterexample is research characterization until an actual missed obligation
is demonstrated. The reduced next action is one finite HIR prefix realizing
the selective owner return path above, with actual row identities/scopes and
both parent-pair SCC tests, or a source-construction proof excluding it.

Checks performed: static `cat`, `sed`, `rg`, and `sha256sum` reads; source
branch and constructor derivation. No Git command, test, build, executable
probe, external contact, delegation, compiler edit, or shared-record write.
Zero heavyweight processes and zero executable samples; CPU/RAM and elapsed
time unmeasured. Several early broad captures truncated; subsequent narrow
slices supplied the owning code used here. Parsed HIR, concrete row IDs,
actual successful scheduling, rollback/retry and all-source coverage remain
unverified. The yulang-proofs skill was read; its old nested-CLI fallback is
superseded for this packet by the explicit primary assignment and active
proof-dispatch liveness rule. No custom prover execution is claimed.

| Frozen direct dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11` |
| `crates/yu-solver/src/candidate_context.rs` | `2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| governing contextual attachment design | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

Commit packet: exact lease `notes/progress/2026-10-10-positive-tail-source-composition-proof.md`;
baseline `4e5e60c81d834aafd736d45f28a1f197d012254a`; direct dependency changes
none observed, all nine hashes unchanged on the final recheck; primary must
compare hashes to baseline blobs; unreviewed
research-only bounded derivation; static checks only. Proposed checkpoint:
`research: reduce positive tail restoration to selective owner intrusion`.
Shared deltas left for primary/curator: record the isolated colevel exclusion,
its selective-owner merge escape, stable Allowance-item distinction, and exact
remaining source-prefix/whole-use rescue premises. Do not promote R or any
semantic/production gate.
