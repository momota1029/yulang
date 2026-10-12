# Fixed-term H explicit-state replay evidence

Date: 2026-10-12
Status: independently reviewed bounded research-only executable evidence; no production or authority promotion
Assigned baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this note and `tools/research_fixed_term_h_machine.py` only

Independent review and integration scope: [fixed-term H review](2026-10-12-fixed-term-h-review.md).
The checker is evidence; the concrete refinement proof is in
[H state construction](../theory/2026-10-12-fixed-term-h-state-construction.md), section 8.

## Claim and scope

The checker implements a finite candidate H as a traversal of explicit type cells and both row-bound lists, then resumes native-style inference for exactly this resolved term from an empty context at level 0:

```text
let rec odd = lambda n_outer.
  let rec even = lambda n_inner. odd n_inner
  in even n_outer
in odd
```

The four runs are stock without H, low-anchor H, bounds-only H without live-cell transport, and low-anchor H with canonicalization of historical pending comparison keys. H produces the conditional note's continuation: live B/R become existing C/D, even publishes at boundary 1, its one use copies only e, odd publishes at boundary 0, and final use copies five rows. Both named mutations discriminate actual transport/cache duties. All four compact interfaces still simplify to Top -> Bot; this final interface is expressly not the mutation discriminator. No mutation is asserted to refute source soundness or principality.

This is executable evidence for one chosen research representation and fixed finite continuation. The stock and H runs share translated source transition assumptions, so they are not independent source-semantics oracles. The earlier conditional note's source principality theorem is not proved by this checker. Arbitrary clients, all sources, Call/effects, Yulang admission, exception paths, general equality preservation, normal termination and F5 cutover remain OPEN.

## Representation and executable H owner

The machine is a LIFO explicit stack. Lam, App and Let frames carry integer cell indices; environment schemes carry a body-cell index and optional lexical generalization limit. Type descriptions are immutable variable/Function tuples inside cells or row-bound lists. Copy-bounds-return frames also carry raw parent/target row IDs as creation-parent and active-copy ordinals. For the exact two H calls, no pending later frame targets a rewritten B/R row; the concrete refinement proof must establish this precise frame census. Host locals are used within one transition only: H runs in the copy-bounds-return transition after all its copy children have returned, and that transition uses no pre-H typed operand afterward. No suspended Python generator or recursive host-stack inference call carries an unvisited type. Retaining already consumed cells is a finite conservative superset of live slots, not a hidden continuation.

Variable allocation levels are an append-only tuple. H does not allocate, lower a level or alter this tuple. Bounds are mutable; original B/R allocation records survive with levels 2 and retired-to C/D metadata. Original rows' bounds are moved into the existing anchor rows and cleared, then every bound is rewritten structurally. This retirement is an explicit research encoding of class ownership, not a claimed native Scala union implementation. Historical allocation identity remains available.

For each actual qualified pair, H concatenates both lower lists and both upper lists into the copy anchor, rewrites both bound sides on every row, then rewrites every type cell by q(parent)=anchor. All other variable IDs are unchanged. Environments and suspended frames automatically observe transported operands through their existing cell indices; Function tuples are re-embedded, and their levels are recomputed from immutable child levels. This is an implemented finite action, not an abstract H call, supplied target store or hardcoded final answer. The exact two unions have no lower/upper cross product; an assertion rejects use outside that bounded premise. No generic bound-union solver or downward dependency closure is claimed.

Comparison caches are separate sets of literal tuple keys. Polar extrusion memos retain raw (parent ID, polarity) keys and raw copy IDs. Event records retain resolved source origin/receiver and original parent/copy IDs; freshening frames use a separate unsigned map. H traverses neither historical key space nor these identities. The cache-canonicalization mutation explicitly changes only comparison keys in addition to otherwise complete H. The bounds-only mutation moves and rewrites bound lists but leaves all typed cells untouched. This makes its stale suspended formal/result visible to the real Lam return, publication and freshener.

Each run checks every row-bound level after every transition, preserves levels and raw memo identities through every H action, and checks actual transport/insertion/map consequences. It stops after at most 1,000 transitions. The machine accepts only the fixed constructor subset; it is not an installable compiler or reference replacement.

## Source resolution and early eligibility certificate

The checker resolves lexical Names to separately allocated binder IDs before type inference. Its source-only prepass walks each declaration's initializer under that declaration root; a nested initializer is walked under its own root. Let bodies resume the surrounding owner. Apply fragment membership traverses only Name/App subtrees in this exact syntax, rejecting unsettled fragment constructors. The final Name has no enclosing definition owner. No type constraint, bound adjacency or type-parent relation is used to build this graph.

Computed edges:

| Source Value | Resolved reference targets |
| --- | --- |
| odd | even, n_outer |
| n_outer | empty |
| even | n_inner, odd |
| n_inner | empty |
| apply4 | n_inner, odd |
| apply5 | even, n_outer |

The computed root SCC is {odd, even}; neither formal nor Apply-result row is identified with a root. The first App records origin even and resolved receiver odd and qualifies its two actual produced polar pairs. Freshening creates no Value incidences and no extrusion event. Precomputing these approved source-only facts before constraint propagation is a candidate phase ordering for this term, not an approved or implemented general compiler scheduling policy. The reference has no such prepass.

## Exact source correspondence

Reference revision: `LPTK/simple-sub` `9bae772624c23b52a93c1b226157e16898b4d9db`.
Sources: [Typer.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala) and [TypeSimplifier.scala](https://github.com/LPTK/simple-sub/blob/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/TypeSimplifier.scala).

| Python owner | Reference owner and retained behavior |
| --- | --- |
| `step`: eval / let_rhs_done / let_publish | Typer 48–55, 59–83: recursive root at lvl+1; constrain actual initializer; publish unchanged boundary; monomorphic Name inside initializer |
| `step`: lam_return / app_compare / app_return | Typer 63–72: actual captured formal and body/result; lazy App result allocated after arguments; demand Function(arg,res) |
| `constrain` | Typer 88–126: variable raw cache before insertion; Function contravariant argument/covariant result; left-variable case priority; newest-first bounds and replay; native re-entry after returned extrusion |
| `copy` with extrusion map | Typer 134–156: early level test, Function polarity reversal, memo before recursive copying, selected bound side and native direct parent link |
| `copy` with freshening map | Typer 166–188, 199–202: independent unsigned map per Name, memo before both lists, oldest-first allocation while preserving newest-first output order |
| append-only `levels`, `level`, `check_levels` | Typer 209–227: immutable Variable level; maximum-child Function level; bound-level invariant |
| tuple cache keys | Typer 223–233 and Function case class: Variable raw allocation identity; Function key uses actual child IDs |
| `compact_interface` | TypeSimplifier 102–157: polar variable closure and structural-bound expansion; 185–239: single-polarity nonrecursive removal; 286–319: empty negative Top / positive Bot |

The compact routine covers the variable/Function subset reached by these four runs. It rejects repeated recursive compact layers or variables with both polarities, rather than pretending to implement the complete simplifier. Its computed output is not supplied to the store machine. The raw tuple key representation reproduces the relevant source equality law; the identity shortcut checks the only relevant identity cases here (same variable). Function object-reference identity outside this trace is not modeled. Source graph and H are proposed additions, explicitly distinct from reference owners.

## Discriminating cut and continuation

Initial allocation order is o=0, A=1, e=2, B=3, R=4, C=5, D=6. Levels are 1,1,2,2,2,1,1. The first cache initially contains literal o <: F(B,R). Extrusion produces (B,+)->C and (R,-)->D with native direct B upper C and R lower D. H moves these to C upper C and D lower D and transports suspended formal/result cells. Original parent IDs 3/4 remain in event/memo and the initial cache key.

At the first-App cut H has U(o)=[F(C,D)], U(C)=[C], L(D)=[D], empty other bounds. Its owning cache contains both o <: F(B,R) and o <: F(C,D). The transformed native re-entry was not cached and therefore inserted U(o). In the canonical-cache mutation the old pending key has become o <: F(C,D); the same native re-entry returns cached before the sole insertion, so U(o)=[] at this cut. Nothing resets or discharges the pending key specially.

In H the actual inner Lam returns F(C,D); even publishes PolymorphicType(1,e); the freshener copies e only and retains the whole level-1 Function bound. In bounds-only H the actual Lam still returns F(B,R), so even's publication has that actual high-level initializer and its use copies e,B,R. This is a violated H transport postcondition, despite the same final displayed interface.

Native H continuation emits A <: C and D <: S, plus the D <: S cache-stopped self-lower replay, then C <: A and S <: D from outer completion. The code checks levels on each transition. No additional extrusion event occurs. Root o publishes at boundary 0; the final memo traverses both lists and copies o,A,C,S,D, preserving self-bounds and cycles.

## Counts and final compact results

| Execution | Steps | Allocated rows | Comparisons | Upper insertions | Lower insertions | Cache returns | H actions | E-use copies | O-use copies |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| stock | 72 | 17 | 12 | 7 | 2 | 0 | 0 | 3 | 6 |
| H | 65 | 14 | 12 | 6 | 2 | 1 | 2 | 1 | 5 |
| bounds_only | 69 | 17 | 11 | 6 | 2 | 0 | 2 | 3 | 6 |
| canonical_cache | 53 | 13 | 9 | 3 | 2 | 2 | 2 | 1 | 4 |

Comparison counts include Function comparisons and cache-stopped repetitions; direct extrusion bound links are not constrain calls. Allocations include all historical and final fresh-use rows. Compact H result is root vars {9}, Function argument vars {10,11}, result vars {12}, no recursive compact vars. All are single polarity; simplification computes Top -> Bot. Stock and mutations also compute Top -> Bot, making the state/memo discriminators necessary.

## Every final store and map frame

Row IDs and labels below come directly from the completed executions. Empty retired rows retain original levels. Bounds list order is newest first. Map entries are shown in actual insertion order; `+`/`-` are polar extrusion keys, `unsigned` denotes freshening.

### stock

| ID / label | Level | Retired to | Lower | Upper |
| --- | ---: | --- | --- | --- |
| 0 / odd | 1 | active | F(n_outer#1,result@apply5#10) | F(n_inner+copy#5,result@apply4-copy#6) |
| 1 / n_outer | 1 | active | empty | n_inner@use1#8 |
| 2 / even | 2 | active | F(n_inner#3,result@apply4#4) | empty |
| 3 / n_inner | 2 | active | empty | n_inner+copy#5 |
| 4 / result@apply4 | 2 | active | result@apply4-copy#6 | empty |
| 5 / n_inner+copy | 1 | active | empty | n_outer#1 |
| 6 / result@apply4-copy | 1 | active | empty | result@apply5#10 |
| 7 / even@use1 | 1 | active | F(n_inner@use1#8,result@apply4@use1#9) | F(n_outer#1,result@apply5#10) |
| 8 / n_inner@use1 | 1 | active | empty | n_inner+copy#5 |
| 9 / result@apply4@use1 | 1 | active | result@apply4-copy#6 | result@apply5#10 |
| 10 / result@apply5 | 1 | active | empty | result@apply4-copy#6 |
| 11 / odd@use2 | 0 | active | F(n_outer@use2#12,result@apply5@use2#15) | F(n_inner+copy@use2#14,result@apply4-copy@use2#16) |
| 12 / n_outer@use2 | 0 | active | empty | n_inner@use1@use2#13 |
| 13 / n_inner@use1@use2 | 0 | active | empty | n_inner+copy@use2#14 |
| 14 / n_inner+copy@use2 | 0 | active | empty | n_outer@use2#12 |
| 15 / result@apply5@use2 | 0 | active | empty | result@apply4-copy@use2#16 |
| 16 / result@apply4-copy@use2 | 0 | active | empty | result@apply5@use2#15 |

| Frame | Kind / level or boundary | Actual raw map entries |
| --- | --- | --- |
| 0 | extrude target 1 | 3+ -> 5, 4- -> 6 |
| 1 | freshen boundary 1, use level 1 | 2 unsigned -> 7, 3 unsigned -> 8, 4 unsigned -> 9 |
| 2 | freshen boundary 0, use level 0 | 0 unsigned -> 11, 1 unsigned -> 12, 8 unsigned -> 13, 5 unsigned -> 14, 10 unsigned -> 15, 6 unsigned -> 16 |

Computed compact: `{"vars":[11],"fun":[{"vars":[12,13,14],"fun":null},{"vars":[15],"fun":null}]}`; simplified `(Top -> Bot)`.

### H

| ID / label | Level | Retired to | Lower | Upper |
| --- | ---: | --- | --- | --- |
| 0 / odd | 1 | active | F(n_outer#1,result@apply5#8) | F(n_inner+copy#5,result@apply4-copy#6) |
| 1 / n_outer | 1 | active | empty | n_inner+copy#5 |
| 2 / even | 2 | active | F(n_inner+copy#5,result@apply4-copy#6) | empty |
| 3 / n_inner | 2 | 5 | empty | empty |
| 4 / result@apply4 | 2 | 6 | empty | empty |
| 5 / n_inner+copy | 1 | active | empty | n_outer#1, n_inner+copy#5 |
| 6 / result@apply4-copy | 1 | active | result@apply4-copy#6 | result@apply5#8 |
| 7 / even@use1 | 1 | active | F(n_inner+copy#5,result@apply4-copy#6) | F(n_outer#1,result@apply5#8) |
| 8 / result@apply5 | 1 | active | empty | result@apply4-copy#6 |
| 9 / odd@use2 | 0 | active | F(n_outer@use2#10,result@apply5@use2#12) | F(n_inner+copy@use2#11,result@apply4-copy@use2#13) |
| 10 / n_outer@use2 | 0 | active | empty | n_inner+copy@use2#11 |
| 11 / n_inner+copy@use2 | 0 | active | empty | n_outer@use2#10, n_inner+copy@use2#11 |
| 12 / result@apply5@use2 | 0 | active | empty | result@apply4-copy@use2#13 |
| 13 / result@apply4-copy@use2 | 0 | active | result@apply4-copy@use2#13 | result@apply5@use2#12 |

| Frame | Kind / level or boundary | Actual raw map entries |
| --- | --- | --- |
| 0 | extrude target 1 | 3+ -> 5, 4- -> 6 |
| 1 | freshen boundary 1, use level 1 | 2 unsigned -> 7 |
| 2 | freshen boundary 0, use level 0 | 0 unsigned -> 9, 1 unsigned -> 10, 5 unsigned -> 11, 8 unsigned -> 12, 6 unsigned -> 13 |

Computed compact: `{"vars":[9],"fun":[{"vars":[10,11],"fun":null},{"vars":[12],"fun":null}]}`; simplified `(Top -> Bot)`.

### bounds_only

| ID / label | Level | Retired to | Lower | Upper |
| --- | ---: | --- | --- | --- |
| 0 / odd | 1 | active | F(n_outer#1,result@apply5#10) | F(n_inner+copy#5,result@apply4-copy#6) |
| 1 / n_outer | 1 | active | empty | n_inner@use1#8 |
| 2 / even | 2 | active | F(n_inner#3,result@apply4#4) | empty |
| 3 / n_inner | 2 | 5 | empty | empty |
| 4 / result@apply4 | 2 | 6 | empty | empty |
| 5 / n_inner+copy | 1 | active | empty | n_outer#1, n_inner+copy#5 |
| 6 / result@apply4-copy | 1 | active | result@apply4-copy#6 | empty |
| 7 / even@use1 | 1 | active | F(n_inner@use1#8,result@apply4@use1#9) | F(n_outer#1,result@apply5#10) |
| 8 / n_inner@use1 | 1 | active | empty | empty |
| 9 / result@apply4@use1 | 1 | active | empty | result@apply5#10 |
| 10 / result@apply5 | 1 | active | empty | result@apply4-copy#6 |
| 11 / odd@use2 | 0 | active | F(n_outer@use2#12,result@apply5@use2#14) | F(n_inner+copy@use2#16,result@apply4-copy@use2#15) |
| 12 / n_outer@use2 | 0 | active | empty | n_inner@use1@use2#13 |
| 13 / n_inner@use1@use2 | 0 | active | empty | empty |
| 14 / result@apply5@use2 | 0 | active | empty | result@apply4-copy@use2#15 |
| 15 / result@apply4-copy@use2 | 0 | active | result@apply4-copy@use2#15 | empty |
| 16 / n_inner+copy@use2 | 0 | active | empty | n_outer@use2#12, n_inner+copy@use2#16 |

| Frame | Kind / level or boundary | Actual raw map entries |
| --- | --- | --- |
| 0 | extrude target 1 | 3+ -> 5, 4- -> 6 |
| 1 | freshen boundary 1, use level 1 | 2 unsigned -> 7, 3 unsigned -> 8, 4 unsigned -> 9 |
| 2 | freshen boundary 0, use level 0 | 0 unsigned -> 11, 1 unsigned -> 12, 8 unsigned -> 13, 10 unsigned -> 14, 6 unsigned -> 15, 5 unsigned -> 16 |

Computed compact: `{"vars":[11],"fun":[{"vars":[12,13],"fun":null},{"vars":[14],"fun":null}]}`; simplified `(Top -> Bot)`.

### canonical_cache

| ID / label | Level | Retired to | Lower | Upper |
| --- | ---: | --- | --- | --- |
| 0 / odd | 1 | active | F(n_outer#1,result@apply5#8) | empty |
| 1 / n_outer | 1 | active | empty | n_inner+copy#5 |
| 2 / even | 2 | active | F(n_inner+copy#5,result@apply4-copy#6) | empty |
| 3 / n_inner | 2 | 5 | empty | empty |
| 4 / result@apply4 | 2 | 6 | empty | empty |
| 5 / n_inner+copy | 1 | active | empty | n_inner+copy#5 |
| 6 / result@apply4-copy | 1 | active | result@apply4-copy#6 | result@apply5#8 |
| 7 / even@use1 | 1 | active | F(n_inner+copy#5,result@apply4-copy#6) | F(n_outer#1,result@apply5#8) |
| 8 / result@apply5 | 1 | active | empty | empty |
| 9 / odd@use2 | 0 | active | F(n_outer@use2#10,result@apply5@use2#12) | empty |
| 10 / n_outer@use2 | 0 | active | empty | n_inner+copy@use2#11 |
| 11 / n_inner+copy@use2 | 0 | active | empty | n_inner+copy@use2#11 |
| 12 / result@apply5@use2 | 0 | active | empty | empty |

| Frame | Kind / level or boundary | Actual raw map entries |
| --- | --- | --- |
| 0 | extrude target 1 | 3+ -> 5, 4- -> 6 |
| 1 | freshen boundary 1, use level 1 | 2 unsigned -> 7 |
| 2 | freshen boundary 0, use level 0 | 0 unsigned -> 9, 1 unsigned -> 10, 5 unsigned -> 11, 8 unsigned -> 12 |

Computed compact: `{"vars":[9],"fun":[{"vars":[10,11],"fun":null},{"vars":[12],"fun":null}]}`; simplified `(Top -> Bot)`.

## Reproduction, dependency snapshots and omissions

Exact successful final command, from the repository root:

```sh
python3 tools/research_fixed_term_h_machine.py --json /workspace/scratch/08aefbd4a01c/h-machine-work/replay.json > /workspace/scratch/08aefbd4a01c/h-machine-work/stdout.json
```

Exit 0; all bounded discriminators passed, four executions. Optional scratch JSON contains every comparison, final store, cut, raw cache, event and map. Each H action records selected formal/result/demand cell values before and after H, all changed cell indices, suspended frame metadata, environment metadata and allocation levels. These selected values are not full-cell snapshots; H itself traverses all type cells. stdout includes complete final stores/maps. The checker also runs without retrieval-only reference files; when present it verifies both exact reference hashes. Other dependencies are reported when available.

Development ran four Python execution processes, each replaying exactly these four modes: the first exited 1 because an initially guessed stock O-use cardinality was 5; a diagnostic execution derived the actual six-row stock reachability; the assertion was corrected to 6, and the two subsequent executions (including the frozen code) exited 0. This corrects a new research check, not any compiler test expectation. No random search, unbounded enumeration, heavyweight process, dependency installation, Scala/Rust/Cargo build, benchmark or Git operation ran. Elapsed CPU/RSS were not measured; the final maximum is 72 transitions per run and 17 allocated rows. One failed check is retained honestly here. The diagnostic import's generated bytecode was removed before freeze; no generated output remains in the repository. No optional parent-representative mutation was implemented.

Read policy: root AGENTS and research-lab, design-authority, compiler-engineering, git-concurrency, testing rules; governing top-level principles and three authority notes; full conditional proof; exact reference owners. `tasks/current.md` was unavailable in the supplied snapshot; `tasks/research-lab.md` was read. No unfinished/new transition proof was read or used as an oracle. Primary reported unrelated branch advance during the lane; integration revision validation belongs to primary.

| Direct input | SHA-256 |
| --- | --- |
| `reference/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `reference/TypeSimplifier.scala` | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| `notes/theory/2026-10-12-fixed-term-intrusion-quotient-proof.md` | `6d2e79c2113562422d06e8250e6830b60fe8b9006b18746b4f23362ac044e6c1` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `notes/design/2026-10-12-value-reference-copied-row-ownership.md` | `7c170c346eeeabca50afe254425eba0c83995cb5e61bf257290ce2757c78bfbd` |

## Frozen commit packet and next owner

- Exact changed paths: `tools/research_fixed_term_h_machine.py` and `notes/progress/2026-10-12-fixed-term-h-machine-evidence.md`.
- Claim class: independently reviewed research-only explicit-state evidence for one finite term; the separate refinement note owns the proof. No producer self-certification or parent-gate closure.
- Assignment baseline: `5e7ffb735fc1a829d03890ebfd353e17ad7ca342`; direct frozen hashes above. Source inputs were not edited by this leaf.
- Verification: four fixed final runs, all state/cache/map discriminators and per-transition bound-level checks; optional reference-hash verification. Broad suites deliberately omitted because no compiler code changed.
- Suggested checkpoint message: `research: replay fixed-term intrusion with explicit live-state transport`.
- Shared-record deltas deferred to primary/curator: record this explicit finite candidate H and the two distinct omissions; preserve general scheduling/transport adoption, actual compiler owner, all-source soundness/principality, effects/Call, Yulang correspondence and cutover OPEN.
- Required next gate: independent source-conformance review and proof of this concrete machine's state inventory/H refinement before using the executable evidence to discharge any theorem. A producer's successful run does not supply that proof.
- Writes stop at handoff; primary owns all integration, commits, pushes and shared records.
