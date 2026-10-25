# R59 complementary source lane — immutable heap identification falsifier

Status: frozen research-only source characterization; independent review PENDING.
Parent: PAPER-HEAP-OBSERVATION-20261026/r59. Baseline supplied by primary:
`4eb348f7ebf53509ae701c6b0434041a90f8f573`. No Git command was used to resolve it.
Contract SHA-256: `fd8913816e2ab6c6f3316f2be50125b148dab192aefc1de3b529644547604e21`.

## Objective, authority and method

Read-only constructor/consumer trace in the pinned `program.rs` and `machine.rs`,
compared with the manuscript §§3/3.8, lines 252–326, 488–500 and 981–990, and
R29's accepted finite allocation boundary. This complements the separate Lean
constructive lane; it does not construct or review its theorem. The supplied
language meaning is unchanged: manuscript `H` is immutable, finite and guarded;
references observe an underlying node, type application normalizes at the outer
elimination boundary, and Force/Delay is separate. R29 established payload
allocation without guardedness or source/native correspondence. R58 established
represented type beta only. No candidate runtime meaning is adopted here.

Applied the assigned R59 contract and read root operating maps,
`rules/research-lab.md` and its preserved baseline, `rules/design-authority.md`,
`rules/git-concurrency.md`, current state/README, sprint skill and active sprint
rules. No scheduling, semantic, code or shared-record changes were made.

## Owner-specific trace

| Owner | Constructor / retained data | Consumer / distinction from paper |
| --- | --- | --- |
| `program.rs:17–32,214–225,605–645,749–763` | Immutable **code** arena; `LocalBinding` retains an initializer label and recursive flag. The ownership walk marks active self references; initializer activation is conditional on nonempty local parameters. | This is code and binder information, not an immutable value heap. It does not build R29's typed `(id,type,RHS)` block, simultaneous substitution or `Xi`. |
| `program.rs:779–804,815–817,858–879` | Names retain source resolution and Observe/Execute consumption; ascription/group forward to the inner label; blocks retain ordered binding ordinals or statements. | The two owners expose no graph-reference/type-application observation constructor or R29 allocation call. Runtime dictionary/dispatch metadata is not an established implementation of paper type beta. |
| `machine.rs:29–38,175–196,441–454` | Separate value arena, executable map, environment arena and `Vec<Option<ReceivedValue>>` cells. All global definition slots start `None`. Closures/delays retain code labels plus environment indices. | A cell is neither a paper `Value.graphReference` nor a total typed immutable heap payload. Environment lookup and executable lookup are separate operations. |
| `machine.rs:2500–2539,1498–1559` | Each local initializer allocates one `None` cell. A recursive local extends its environment with that cell **before** initializer execution. | `Frame::Local` later writes `Some(received)` into the already allocated slot, then continues the next statement. A recursive closure can retain an environment whose binder points to the slot subsequently filled with that closure. This is a mutable knot construction, not direct R29 simultaneous immutable allocation. |
| `machine.rs:781–862,1738–1763,2377–2445` | A name resolves to a global index or nearest environment binder cell. Scheduled roots or demanded globals evaluate an initializer while retaining a publication frame. | Initialized names dispatch/consume a cached value. A missing global starts computation unless already initializing, in which case it yields `RecursiveDefinitionInitialization`; a missing local yields `UninitializedBinding`. `Frame::Root` / `GlobalRead` publish into existing slots. Paper `lookupHeap` instead returns an already stored payload without starting an initializer. |
| `machine.rs:1181–1198,1285–1329,2469–2495,2548–2582` | Application allocates an inert argument delay `(code, environment)` and receiving view. Value parameters execute it; computation parameters bind its carrier. | `consume Execute` checks computation interface/view receipts and calls `execute_with_substitution`; its Delay branch enters stored code after environment substitution. The same consumer also accepts Request carriers. It is not by itself the paper Force rule or a graph/type-beta observation theorem. |
| `machine.rs:2585–2638,2701–2715` | `extend` / `bind` append environment entries and cells; `allocate` appends concrete runtime values plus an optional executable. | Lexical lookup chooses the nearest binder along parent links, then reads an indexed Option cell. This differs from R29's first-match `(reference,payload)` association list. Append-only value handles alone do not establish a whole heap interpretation, typed closure environments or guard preservation. |

## Smallest direct-identification falsifier

Claim attacked: identify Rust `cells` (same numeric IDs, every allocated slot)
with R29's `Heap`, and treat local/global initialization as R29 `allocate` plus
heap lookup, with no extra abstraction or simulation premise.

A single scheduled global whose initializer returns one integer is sufficient
(e.g. the candidate source `my main = 1`; no source compilation was run):

1. `Machine::start` creates `cells = [None]` (`machine.rs:452`).
2. `begin_root` records initialization and evaluates that definition body with a
   retained `Frame::Root { cell: 0, ... }` (`:2391–2405`).
3. On its return, `Frame::Root` assigns `cells[0] = Some(received)` (`:1738–1745`).

This is a source-reading derivation conditional only on the ordinary initializer
return; it is not an executed trace. There is one slot and one publication, no
recursion, handlers, dispatch dictionaries or type-beta assumptions. If slot 0
belongs to the alleged heap at step 1, it lacks a paper Value payload and later
changes. If it enters the abstraction only at step 3, the abstraction is instead
a projection of **published** cells with a separate pending-cell simulation
invariant. That alternative is not refuted, but it is an unproved bridge, and
cannot be obtained by equating the two containers.

The recursive-specific discriminator is equally explicit: condition on a
recursive local whose initializer produces a closure. `begin_local` allocates
`None`, installs the binder before evaluation, lambda evaluation captures that
environment (`:864–886`), and `Frame::Local` fills the slot. No source acceptance
claim for an arbitrary recursive RHS is needed. A direct read before publication
would fail locally or detect a global initialization cycle, whereas R29's
one-entry self-alias heap `[(r,graphReference r)]` already has a successful lookup
and can repeatedly observe itself. R29 `self_alias_payload` / `self_alias_block`
(`PaperFreshHeapAllocation.lean:285–305`) deliberately allow this without proving
the paper guard. This does not establish that the manuscript admits the alias;
it distinguishes the weaker R29 relation from both a guarded heap and native
pending initialization.

## Claim class, independence and omitted cases

Established by inspected source: allocation/publication sites, name failure
branches and Delay consumer separation above. Bounded negative conclusion:
**direct container identification is false; no source-to-paper observation bridge
was found in these two exact owners**. This is not a repository-wide absence
proof or a disproof of an eventual suitable abstraction.

Oracle independence: no executable oracle/model/checker was run. The evidence
comes from actual Rust constructors/consumers and independently pinned paper/R29
text, rather than a checker that assumes Rust transitions. Both sides still
require a representation relation to compare observable behavior. Source
acceptance, complete receiving/dispatch laws, closure reification, metadata,
continuation replay/publication, all constructor eliminators and source-formal
order were not proved. No seeds, numeric search ranges or mutation runs apply;
coverage is the named static owner paths. No external proof artifact arrived
through this lane. A changed pin, unauthorized write requirement, unknown writer
on the sole lease or the time cap would stop work; none was used to expand scope.

## Safe implementation slice and next action

**NO_SAFE_CODE_SLICE for this R59 packet.** `program.rs` needs a correspondence
from its binder/initializer representation to paper values and simultaneous
allocation; `machine.rs` needs a relation covering pending versus published
cells, captured environments, dispatch/receiving views and execution. R29/R59
finite typing results alone do not supply either premise. Both actual owners
were inspected; no code change is authorized or justified by this evidence.

Recommended next action: keep source realization OPEN and assign a separate
bounded proof/source packet for a published-cell plus pending-initializer
simulation invariant at `begin_local`/`Frame::Local` and global publication,
with this one-slot trace as its first discriminator. Review R59's finite Lean
result on its own represented-paper scope.

## Commands, pins and resource receipt

Commands were only bounded `cat`, `rg`, `nl`/`sed`, `head`/`tail`, `sha256sum`,
a UTC clock read and the single leased note write. No build, test, runtime probe,
Lean/Lake/checker, network, Git or descendants. Zero checker budget consumed.
All 18 hashes in the R59 frozen-input block matched at initial inspection.
Immediate pre-write recheck also matched contract, manuscript and both Rust
owners. Direct dependency hashes:

```text
a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b  docs/yulang-operational-type-safety-ja.tex
6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907  tools/inference-playground/src/runtime/program.rs
b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e  tools/inference-playground/src/runtime/machine.rs
7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925  notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean
d6523cba7a7b68871f56d359168f37d83bef27fa8ae2081777094e794b3cbea7  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-adjudication.md
2611315d23588db8b02f8644bc9d8c495e388566659037e59f3b3501b49e25b1  tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-review.md
```

Exact active-work origin was not sampled. First sampled clock was
`2026-10-25 22:56:15 UTC`; startup reads preceded it. Process CPU/RAM peak and
exact active seconds UNKNOWN; no compute-heavy process was launched. Primary
must conservatively charge the full 240-second lane reservation. Requested
model/effort: registered role defaults; observed model/effort and session ID:
UNKNOWN. Sole author: `/root/r59_heap_observation_source`.

Writer cessation: this note is the final write; no descendants or generated
outputs exist. Bytes are frozen for primary intake/review after the write and
final read-only dependency/artifact hash receipt. No independent review claimed.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/paper-heap-observation-r59-source.md`.
- Baseline SHA: `4eb348f7ebf53509ae701c6b0434041a90f8f573` (primary supplied).
- Changed dependency hashes: none observed; all contract pins initially match.
- Review: PENDING; source characterization and direct-identification falsifier only.
- Checks already run: static owner trace and hash comparisons; zero executable verification.
- Proposed message: `research: record R59 native cell and immutable heap boundary`.
- Shared deltas left for primary/curator: source realization stays OPEN;
  NO_SAFE_CODE_SLICE; record frozen source receipt/hash and writer cessation;
  retain pending/publication simulation as the exact missing owner premise.
