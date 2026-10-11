# Mutual module recursion with a nested extrusion demand

Date: 2026-10-11
Status: frozen, independently reviewed bounded static research; no parent-gate closure.
Baseline supplied by primary: `670d1572eedd2bf5ee839ff5f889a2222f6c36b2`.
Exclusive lease: this file. No compiler edits, tests, builds, Oracle, executable
probe, Git mutation, or child delegation.

## Objective, method, and authority

Search one extension of the reviewed two-root module witness for an actual
retained Value extrusion pair and source-owned paths placing that pair in one
SCC. Method: inspect the HIR ownership, source schedule, open module-use
records, native Apply replay, and extrusion creation. Stop at the first missing
constructor bridge. This is complementary source-construction research, not
the main constructive theorem or independent review.

Exact authority: `notes/design/2026-10-10-parent-copy-scc-intrusion.md`,
“Direct decision”, “Selected operation and compiler responsibility”,
“Value-reference SCC clarification”, and “Retained boundary”; top-level
inference principles §§1–3 and “Evaluation”. Actual references in Value values
are the user-selected edges. Comparisons, parent metadata, and the definition
`SccPlan` do not supply those edges. Preserve ordinary native inference and the
selected parent/copy operation.

The independently reviewed
`notes/theory/2026-10-11-mutual-recursive-value-scc-proof.md` establishes actual
root identities and source references for `my f x = g; my g y = f` only.
The untracked `2026-10-11-source-qualified-value-parent-copy-scc.md` is reused
only as operational constructor evidence; its payload trace does not establish
the semantic graph for this module or for copied identities.

## Single discriminator and explicit hypotheses

The primary suggested:

```yulang
my f x = { my inner y = f; inner g }; my g y = f
```

The nested initializer only places an older module root behind a level-2 Name.
Its later local use captures and reconstructs local rows at level 1 while
sharing the older root (`candidate_scheme.rs:566–621,1008–1021,1363–1377`).
That fresh allocation is not `retain_extrusion_parent`. It therefore supplies
no direct higher-level Function demand at a module root.

The primary accepted the smallest additional application discriminator:

```yulang
my f x = { my inner y = f y; inner g }; my g y = f
```

One argument occurrence added to the nested body exposes level-2 argument and
result ports to level-1 `f`. This is not a minimized counterexample or a claim
that the whole source solves. No parse, lowering, or inference execution was
performed. Existing exact mutual-module test sources and the local recursive
Block fixture at `candidate_source.rs:695` corroborate the component syntax;
acceptance of this exact combined program remains unexecuted.

The following prefix derivation is conditional on successful ordinary parsing,
LocalSource lowering and collection of this exact source, successful checked
allocation, and completion of the first Name/Apply replay through native Value
dispatch, before any identification of its rows. It substitutes no test-created
bound, `close_cycle`, externally mutated session, or resumed failed state.
These execution hypotheses are not proved by a static trace.

## Actual ownership, levels, and use records

Let `F,G` be the actual distinct allocated Value rows for module definition
roots, `H` the inner Lambda's expression row, `Y` its parameter row, `N` the
Name `f` in `f y`, and `P` the Apply-result row of that occurrence. Every
identity comes from the same HIR, collection artifact, and session; numerical
ordinals are neither guessed nor used to identify copies.

LocalSource owns one top-level Lambda for each module binding and a distinct
local binding/initializer for `inner`. Its lexical table resolves `y` to the
inner parameter, `inner` to the published local, and `f,g` to the two unique
module definitions (`module/local_source.rs:269–373,396–437,636–647,790–829`).
No parameter or local has spelling `f` or `g`.

Collection keeps the containing module definition in its `parent` field even
while traversing the local initializer. This field is collection/orchestration
ownership, not proof that the module root owns every nested source reference.
The nested `f` occurrence belongs to `inner`'s local initializer. The three
module Name records are:

| Occurrence | Parent definition | Target definition | Use level |
| --- | --- | --- | --- |
| `f` in `inner`'s `f y` | `f` | `f` | 2 |
| `g` in `inner g` | `f` | `g` | 1 |
| `f` in `g`'s body | `g` | `f` | 1 |

The pending records are emitted at `candidate_source.rs:376–378`; final
endpoint resolution retains `target_root_component` and `use_value_component`
at `lib.rs:1275–1327`. The root map and dense allocation are the same owners as
the reviewed original-root proof (`lib.rs:1676,1897,10047`).

All collected roots initially have level 1 (`lib.rs:10047–10061`). Source
traversal starts at 1, preserves Lambda/Apply levels, adds one only for a Block
initializer, and preserves the level for the Block final expression
(`candidate_source.rs:253–305,532–541`). Thus
`L(F)=L(G)=1`, `L(H)=L(Y)=L(N)=L(P)=2`. The parameter Name endpoint is exactly
`Y`, rather than its separately allocated expression facade (`:210–216`).

The prior reviewed `F → G` and `G → F` result applies only to the original
source `my f x = g; my g y = f` and its jointly constructed root identities.
It is not transferred to this extension by reusing the root names. This note
does not establish a semantic source cycle for the extension, or project the
local initializer's `f` reference onto the module root `F`. Deriving paths
through local ownership, the local use and the enclosing Block requires its
own bridge. The collection records above still determine native open-use
routing without supplying that semantic adjacency.

## Genuine extrusion constructor prefix, conditional on native replay

The definition SCC orchestration activates both original roots and all their
internal uses before executing either source schedule
(`candidate_scheme.rs:869–889`). `Action::Module` therefore routes the nested
`f` through `route_candidate_open_use` and `route_internal`; the latter selects
the actual pair `F <: N` (`candidate_source.rs:672–676`,
`candidate_scheme.rs:938–945`, `lib.rs:15765–15792`). This is open monomorphic
use, not a published module scheme instance.

The native owners then give this finite prefix:

1. `F <: N` selects higher-level `N` and installs `F` in its direct lower
   bounds (`candidate_extrusion.rs:815–830`). This yields physical payload
   reference `N → F`; the comparison itself supplies no semantic edge.
2. The nested Apply creates `Function⁻(Y, effects, P)` and compares `N` with
   that demand (`shadow_apply.rs:1331–1410`). At receiver level 2 its Value
   ports need no copy; `N` physically owns the demand's `Y,P` references.
3. The owning lower/upper replay requests
   `F <: Function⁻(Y, effects, P)` (`candidate_extrusion.rs:763–802`).
   Context replay combines the retained admission origins and drives or queues
   the child at `candidate_context.rs:2930–2987,3058–3105`. Arrival at its
   native Value dispatch is part of the explicit prefix hypothesis.
4. Structural admission extrudes the demand at receiver `L(F)=1`
   (`lib.rs:12412–12454`). Function argument polarity flips, while result
   polarity stays negative (`candidate_extrusion.rs:211–245`). This allocates
   **actual retained Value pairs** `(Yc,Y,Positive,1)` and
   `(C,P,Negative,1)`. Both original ports have level 2, hence are copied.
5. At creation `candidate_extrusion.rs:83–124` allocates each fresh level-1
   row, retains its actual parent, and inserts the one-sided link on the
   original: `Y.upper` contains `Yc`, `P.lower` contains `C`. The parent
   registry records identities/polarity/target only
   (`candidate_intrusion.rs:24–29,171–220`). Function reconstruction produces
   a demand with `Yc,C` as its Value ports
   (`candidate_extrusion.rs:325–355`). Rewritten dispatch queues the comparison
   against `F` and returns (`lib.rs:12441–12454`); it has not yet installed that
   demand on `F` at this stopping point. Subsequent admission is not traced.

At this prefix `Y` has no earlier Value lower and `P` has no earlier Value
upper. Positive extrusion snapshots `Y`'s lowers; negative extrusion snapshots
`P`'s uppers. Both selected snapshots are empty, so no Value bound is copied
onto `Yc` or `C` by that operation. This inspection establishes the actual
allocation/retention mechanism, conditional on the stated source/replay
prefix; it does not establish whole-program acceptance or termination.

Projected physical references here include `N → F,Y,P`, `Y → Yc`, and
`P → C`. No `F → Yc,C` payload incidence is established at this stopping
point: the rewritten demand is queued, not admitted on `F`. The new copies
have no outgoing Value payload in this prefix. These are owning native
payloads, not a declaration of the complete user-semantic graph.

## First exact missing premise and stopping point

The prior original-program source-root cycle and this extension's guarded
extrusion allocations are different results in different constructed artifacts.
Neither establishes a source-owned path from **C back to P** or from **Yc back
to Y**, using this extension's actual retained identities before equality.
Even treating the constructor's one-sided bound references as graph witnesses
leaves both return paths absent at this prefix.

The first missing source-construction bridge is the value/reference ownership
of an extrusion-created row. `ApplySourceInput` retains the original expression,
callee, argument, and original result component
(`candidate_source.rs:393–409`). Extrusion retains no LocalSource expression
or source-reference ownership map for `C`; it copies the selected bound
snapshot and records a parent. Parent identity cannot be promoted to the
missing reference or identify `C` with the original Apply row. The reviewed
root proof deliberately excludes exactly this occurrence/copy transport.

To complete this witness, the next lane must derive the actual source value
owned by `C` (or `Yc`) from the selected extrusion operation, and trace a
reference from that copied value through actual Value identities back to its
original parent. For example, asserting `C → F → P` would still require both
the copy's `C → F` reference and the original-root-to-original-Apply-row
reference `F → P`; neither follows from the prior original-program root cycle
or this extension's demand comparison.
No such edges are asserted here. No scanner conformance conclusion is drawn.

Stop here: no later source continuation, additional variant, rank argument,
generic mutation, or forced consumer cycle was investigated. A missing retained
source certificate is not proof that no semantic value exists; implementation
absence is not an authorized change to the user-selected graph or inference.
The earlier local-self audit and this mutual-module discriminator leave the
same copy/source-ownership premise untouched. A third equivalent demand probe
would repeat that blocker.

Recommended next action: give the exact pair-creation prefix to the constructive
lane and derive the copy's source-value/reference transport at the owning
extrusion operation before another source variant or scanner argument.

## Checks, coverage, and dependency snapshot

Commands: bounded `cat`, `rg`, `sed`, `sha256sum`, and leased-file patches.
Startup also used read-only `git status --short` and `git rev-parse HEAD`,
contrary to the packet's no-Git instruction; HEAD matched the supplied baseline.
No Git mutation or subsequent Git command ran. No test/build/Oracle/compiler
process ran. No independent oracle, seeds/ranges, enumeration, or mutations
apply: these are inspected native owners sharing their level/polarity and
admission assumptions. Executed acceptance, replay completion and failure
behavior remain unverified. The exact final source is one discriminator;
its suggested precursor was inspected only to identify the missing demand.

At most three lightweight read processes were concurrent, with no heavyweight
processes or measurements. CPU/RAM and total reasoning wall time were not
measured. Requested/observed model and effort metadata are unavailable to this
leaf; no routing change or escalation occurred. No numerical compute budget
was supplied; the single bounded static-search/stop condition was used.

Dependency SHA-256 snapshot (no dependency edited by this worker). Rechecking
the listed authority/proof/source hashes immediately before freezing found
no change since their first snapshot; context was hashed at the final check.

```text
parent-copy-scc-intrusion.md             2f08967e8f0477a1dacda62a211c620cd9cc3b80d476412b4c1e3d60506040c0
yulang-inference-top-level-principles.md edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389
mutual-recursive-value-scc-proof.md      332f757481af278e533f0e5d7eda2b3aa004e75d54f1d3e48c77b8f76d5a786d
source-qualified-value-parent-copy-scc.md d73496fc376a9970d3a72e49208c3857e885b18b5ab2de074bc2cceae81a8a76
yu-hir/module.rs                       943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5
yu-hir/module/local_source.rs          906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed
yu-solver/lib.rs                       c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94
candidate_source.rs                    13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49
candidate_scheme.rs                    9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1
candidate_extrusion.rs                 fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0
candidate_intrusion.rs                 aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0
candidate_context.rs                   4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987
shadow_apply.rs                        230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6
```

## Commit packet

Exact leased path: `notes/progress/2026-10-11-mutual-recursion-parent-copy-search.md`.
Baseline: `670d1572eedd2bf5ee839ff5f889a2222f6c36b2`.
Changed dependency hashes: none caused by this worker; primary-owned baseline
comparison/integration revalidation pending. Independent `compiler_referee`
review found two major overclaims in the initial version; both were corrected
and the delta review passed. This remains a conditional source/operation trace;
there is no genuine parent/copy SCC witness and no parent theorem, scanner,
source-adequacy or production certification.
Checks already run: bounded static reads and dependency hashes; no builds/tests.
Proposed message: `research: trace nested mutual-module extrusion construction`.
Shared-record delta intentionally left to primary/curator: record this
discriminator and the exact copy/source-value transport premise; preserve
parent/copy semantic SCC, source/consumer correspondence and inference gates
OPEN. No shared record changed.
