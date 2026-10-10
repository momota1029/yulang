# Ordinary HIR positive-lower / incoming-Allowance composition search

Status: unreviewed research-only bounded source characterization; no source
counterexample, universal exclusion, theorem closure, or implementation authority.
Baseline: `4e5e60c81d834aafd736d45f28a1f197d012254a`, supplied by the primary.
Owner/lease: `ordinary_hir_composition`; this note only. Frozen on submission.

## Objective, method, and authority

Trace ordinary HIR constructors that could compose: an incoming source row
already has a positive physical lower; positive extrusion carries its shared
tail to a lower annotated boundary; later capture/use shares the same canonical
owner before restoring its negative Allowance. If reachable, distinguish this
prefix from a genuine omission witness by tracing within-loop mutation, missed
obligation, ordinary replay, and Value/Effect diagnostic rescue.

Method: bounded static inspection of actual source projection, sequential
actions, effect constructors, extrusion, capture/freshening, qualifying
parent/copy intrusion, and the restore/diagnostic consumers. No fixture inventory
was repeated. This is complementary source evidence; main constructive proof
work remains with the primary's prover lane.

Governing source is Authoritative
`notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3.1–5:
attachment identity grouping stays occurrence-local; source-owned contextual
obligations survive extrusion, capture, and intrusion; bound/replay order and
rollback remain required. The accepted two-cycle acceleration does not admit
arbitrary concrete negative formal rows or decide general mixed components.
No source meaning or admission policy is selected here. Research-lab,
design-authority, git-concurrency, agent-orchestration, and the `yulang-proofs`
skill were read. The assignment prohibits tests, builds, probes, and Git.

## Result and exact hypotheses

No complete ordinary source witness was established. The positive-extrusion
seam is real and can transport an existing physical positive lower before
installing its remapped negative Allowance. However, the direct fresh-constructor
composition has a precise level obstruction.

Let `C` be the negative port carrying `Allowance(V)`, and let `T` be `V.tail`.
For the inspected annotation constructor instance, assume:

1. `C` is freshly allocated at constructor level `L`; `T` is allocated in that
   instance at `L`, or is a scoped tail reused at a level `l <= L`.
2. Both have ordinary `non_generic = false` metadata. No independent canonical
   merge, metadata change, or rollback changes these levels/identities between
   construction, extrusion, capture, and row mapping.
3. Positive extrusion visits this incidence using one target level `t`, mapping
   both its source and tail positively; the later capture boundary is `b`.
4. The proposed negative restore is obtained through this mapped tail's
   incidence. No different already split incidence supplies the restore.

The inspected implementation gives

```text
level(T') = min(l, t) <= min(L, t) = level(C').
```

If `T'` is nongeneric at boundary `b`, capture's `expand_row` returns before
enumerating its incidence. If `T'` is generic, then `level(C') > b` too, and
freshening allocates a new incoming `C'_use`, rather than sharing `C'`. Thus
this one incidence path does not supply the requested conjunction of generic
captured tail, nongeneric preserved owner, and that owner's old positive lower
at the negative restore snapshot. Other captured paths and earlier restores
can supply new lowers to fresh owners; they are outside this identity-preserving
claim.

This is a conditional constructor calculation, not an invariant over every
ordinary source program. In particular, scoped reuse at a greater level than
the port, preexisting split incidences, qualifying intrusion, and intervening
mutation are excluded hypotheses, not proved impossible source events.

Smallest level obstruction for the proposed copy route: `C2,T2` at level 2,
positive copies `C1,T1` at target 1, capture boundary 1. Even if `C1` has a
positive lower, `T1` stops capture. Moving capture to boundary 0 makes both
copies generic. This is a minimized level calculation, not a runnable program
or counterexample.

## Source constructors and sequential consumers

`crates/yu-hir/src/module/local_source.rs:107` defines the supported local forms:
Unit, Operation, Integer, Name, Apply, Group, Ascription, Lambda, and Block.
`expression` retains each annotation tail and occurrence in source order
(`:477`); `block` creates local IDs, parameter owners, initializer occurrences,
and an expression scope for the final expression (`:698`). Catch is not a
local-form constructor in this inspected route.

The exact relevant sequential action owners are:

| Constructor/consumer | Schedule and identity consequence |
| --- | --- |
| Lambda/formal | `candidate_source.rs:246`: parameter/body retain the current level; FormalAnnotation precedes body actions. Local parameter annotations use their owning local's AnnotationScope, otherwise Definition scope. |
| Block binding | `:263`: initializer runs at `boundary + 1`; source bindings run in order, each initializer before its Install/LocalAnnotation; final expression follows installations. |
| LocalAnnotation | `:283`: initializer computation first flows once to block computation. `candidate_local_annotation` constructs negative and positive interfaces, checks initializer at slot 40, checks computation at slot 42, exposes at slot 41, then installs `(root,boundary)`. |
| Ascription | `:403`: aliases the child's endpoint after peeling nested annotations/groups; scope follows Definition, LocalInitializer, Parameter's owner, or Expression. `candidate_annotation_pair` checks at slot 45, computation at 47, exposes at 46. |
| Operation/Apply | Operation constructors produce actual family Support; sequential Apply can propagate it to a checking port. A name's own evaluation is pure. Source-local initialization effects are not reproduced by later lookups. |
| Local use | `candidate_scheme.rs:1117`: capture the live installed root at its recorded boundary, freshen/restore the captured graph, then link the fresh interface to the lookup Value row. The lookup's later provider link cannot create an earlier snapshot lower retroactively. |

`candidate_signature_effect` (`candidate_effect.rs:1304`) constructs a scoped
tail before allocating the new port. For a fresh scoped tail both allocations
use the same constructor level. Reused scoped variables use the existing
identity (`:844`). Covariant negative ports physically receive Allowance;
covariant positive ports receive Support of the paired view. Contravariant
symbolic ports return the tail directly. Explicit concrete negative positions
remain rejected. `candidate_formal_effect_port` (`:919`) uses the same paired
constructor for admitted covariant rows; symbolic-only/omitted formal ports
are shared directly.

`candidate_apply_effect` (`candidate_extrusion.rs:726`) can populate `C` with a
positive physical lower when its canonical lower is non-row, or when its lower
row is older than canonical `C`. Equal/younger row lowers orient the other way.
An allowed family is not itself such an insertion. This identifies the actual
producer but does not establish a full source prefix activating the needed
lower on a preserved owner.

## Positive extrusion: real provenance and insertion order

Ordinary structural Value-to-row admission invokes positive extrusion to the
receiver's level (`lib.rs:11944`); structural row-to-Value admission invokes
negative extrusion. Function arguments reverse polarity, results preserve it.
Installation alone does not extrude every scheme coordinate to its
generalization boundary (`candidate_scheme.rs:1087`); it stores a live root and
boundary. A claimed lower-boundary copy therefore needs this actual structural
admission, rather than an assumed effect of Install.

For a younger positively visited Effect row, `candidate_extrude` snapshots
selected lower lengths, allocates a copy at `t`, retains the actual
`(copy,parent,Positive,t)` record, and inserts the one-sided negative copy bound
on the original (`candidate_extrusion.rs:88`). Parent provenance alone is not
an SCC adjacency edge (`candidate_intrusion.rs:171`).

When positively visiting the tail, extrusion schedules `IncomingAllowance`
with a *positive* source key and the original negative BoundKey (`:165`). LIFO
pending work visits the source before processing that IncomingAllowance.
Visiting a younger source schedules its selected lower visits/Bound actions
above the pending IncomingAllowance; those actions populate the source copy
before IncomingAllowance installs its remapped Allowance (`:293`). Nested
selected-bound work also completes above that pending action. No synchronous
solver drain occurs in these copying insertions. This confirms the required
physical lower can survive copying; it does not establish the later shared
owner restore.

The remapped view uses the mapped tail. Capture marks rows local exactly when
`level > boundary && !non_generic` (`candidate_scheme.rs:189`), and `expand_row`
stops at every nonlocal coordinate (`:437`). Incoming incidences are enumerated
only after that guard (`:488`). Freshening rechecks the current representative,
level, and metadata and uses one canonical row map (`:839`). Fresh row metadata
defaults to nongeneric=false (`lib.rs:10092`). These are the actual consumers
behind the conditional calculation above.

## Reduced remaining SCC/source premise

A route beyond that calculation must establish a split at the actual capture:

```text
level(rep(C)) <= b < level(rep(T)),
or equivalent nongeneric metadata on rep(C) alone;
T's incidence still yields C <: Allowance(V),
and a positive physical lower survives on rep(C).
```

A concrete candidate mechanism is an *actual recorded* C-parent/copy pair
becoming one SCC, lowering canonical C to the minimum level while an original
T/view remains generic and unmerged. This is a candidate assumption, not an
established ordinary sequence. A second copy or two numerically equal rows
does not establish it.

`settle_candidate_intrusion` (`candidate_intrusion.rs:354`) builds adjacency
from both physical row-bound sides, structural Function ports, and
Allowance/Support-to-tail links (`:390–477`). It merges only recorded
parent/copy pairs whose canonical endpoints belong to the same computed SCC
(`:482`). Capture incidence and parent provenance alone do not provide the
return path. `merge_candidate_rows` (`:513`) appends both bound sides onto the
parent, splices incidence buckets when merging tails, takes minimum levels and
ORs nongeneric metadata, canonicalizes contexts, and replays each retained
positive lower against the parent uppers (`:551–607`).

Consequently the next source constructor must supply a real return path for
the C pair and show why the tail pair does not also qualify. The inspected
sequential constructors, active recursive-initializer links, Function-port
projection, and effect-view adjacency did not establish such a complete
source-generated SCC prefix. The search stops here rather than treating an
arbitrary manually supplied SCC as source evidence. It is incomplete over all
recursive source compositions and does not exclude this mechanism.

## Restore mutation and rescue obligations still required

Even a nonempty shared-owner restore would establish only the prefix.
`candidate_restore_bound` (`candidate_extrusion.rs:599`) inserts the bound,
canonicalizes owner/item once, saves the physical opposite count, and fetches
each subsequent bound from that saved owner. Each context replay callback calls
`constrain_live_item`, which drains the typed worklist and can settle dirty
intrusion (`lib.rs:11814`). `candidate_context_restore_replay` enumerates saved
fiber heads before invoking callbacks and bypasses ordinary replay frontiers
for incoming uses (`candidate_context.rs:1938`).

A failure witness must therefore name a callback mutation and an exact later
comparison/fiber lost because of that mutation. Neither a vector-size change
nor canonical-owner change alone proves loss: ordinary insertion calls
`candidate_replay_bound` (`candidate_extrusion.rs:645`), and qualifying merging
replays all parent positive lowers. Those may admit the missing comparison.

Effect diagnostic replay starts at both original and current canonical initial
pairs, traversing children for *all* retained relation contexts of a pair
(`candidate_effect.rs:524`, `candidate_context.rs:1515`). Derived/FunctionPort
dependencies and Replay dependencies provide diagnostic edges; FreshUse
transport alone does not (`candidate_context.rs:1445`). Value roots replay
witnesses after diagnostic completion; an Effect callback also reports Value
diagnostic deltas induced by mixed SCC work (`lib.rs:12086`). A proposed hidden
conflict must survive these rescues and route rollback. This search found no
exact hidden obligation or failure condition to test. No diagnosis of a solver
bug or rescue completeness is claimed.

## Evidence, coverage, resources, and omissions

Commands: bounded `cat`, `rg` (some location output capped with `head`), `sed`,
and `sha256sum`; one leased-note creation through apply_patch. No parser run,
checker, mutation experiment, test, Cargo build, benchmark, seed enumeration,
or formatting run. No independent executable oracle exists in this lane;
source and argument share the exact compiler rules inspected. This is not
independent validation of the selected language semantics. Ranges/seeds and
mutation coverage: none, because no executable search was authorized.

Source coverage is the supported local-form constructor inventory and the
exact called paths above, not an enumeration of source programs or fixtures.
General recursive compositions, module-provider schedules, Catch/Call semantic
completion, negative-concrete admission, all possible SCCs, and a within-loop
loss with failed diagnostic rescue remain unverified.

Resource use: one lightweight read process at a time except small independent
read batches; zero heavyweight processes and zero builds/probes. Shell reads
completed immediately. Aggregate CPU, peak RSS, and wall time were not measured;
no numeric resource budget was supplied beyond the no-compute prohibition and
bounded source-search stop condition. No children were spawned. Requested and
observed model/effort metadata are not available in this lane.

Process deviation: the initial combined context command inadvertently executed
read-only `git rev-parse HEAD` and `git status --short`, contrary to the packet's
no-Git instruction. Output was truncated; primary supplied the exact baseline
after disclosure. No Git mutation occurred and no later Git command ran.

Recommended next action: assign the exact source-owned C-parent/copy SCC return
path that preserves a generic unmerged tail as the next discriminating source
bridge, rather than another fixture inventory or checker assuming that SCC.
Keep the restoration gate open pending that bridge and an actual missed
obligation with ordinary replay/diagnostic rescue accounted for.

## Dependency snapshot and commit packet

Frozen inspected dependency SHA-256 values:

```text
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
2897c168c02640443a2f1280286a648853afe08324294c53f1c95d373ac3a337  crates/yu-solver/src/candidate_context.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
```

- Exact leased/changed path:
  `notes/progress/2026-10-10-ordinary-hir-successor-composition-search.md`.
- Baseline SHA: `4e5e60c81d834aafd736d45f28a1f197d012254a`.
- Changed dependency hashes: none intentionally changed by this worker; primary
  must match the frozen hashes to the pinned commit before integration because
  this worker did not issue Git comparisons after the disclosed initial error.
- Claim/review status: bounded source characterization and explicit conditional
  level calculation; independent review pending; no gate promotion.
- Checks already run: static constructor/call-path inspection and dependency
  hashing only; no executable checks requested or run.
- Proposed checkpoint message:
  `research: isolate HIR positive-extrusion restore level obstruction`.
- Shared deltas left for primary/curator: retain the restoration gate as open;
  record the level-split/SCC source premise and the replay/diagnostic rescue
  obligations. No shared task/index/authority/theory/question record was edited.
