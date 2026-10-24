# Retained graph extraction and concrete SCC/provenance queries

RETAINED-GRAPH-REPLAY-20261024/r1. Baseline `14860b9ba4792c74bfb4d8610cc3ff10b5d0578f`. [Contract](retained-graph-replay-20261024.md) SHA-256 `e91b05d5274ea45d43a5c1cb3034665f876dd8eb9495a12a348e749f9d2366bb`.

## User correction and resulting method

> そこはグラフを持ってきてSCCとりだすしかないですよ

This corrects the method used at the concrete replay obstruction. Carry the existing graph and extract SCCs; do not treat the next step as a new ownership-policy question. The selected immutable birth-level induced Value-SCC rule and actual occurrence/pair identities remain. Type-bound and replay-provenance edges are not additional Value-reference edges. Original Simple-sub A/B, full source/Call/effect scope and publication/use obligations remain unchanged. Implementation and tests are excluded.

## Constructed evidence and parent application

The [graph extraction](../../../notes/theory/2026-10-24-retained-value-graph-replay-attribution.md) enumerates the fixed example's source vertices and constructor-produced adjacency, separating fragment helpers. It contracts helper-only paths before filtering semantic vertices by birth. All relevant SCCs are singletons. F/F qualifies; F/H and F/wrapper do not. External closed builtins cannot create return paths, so their unrecorded birth values do not affect these concrete verdicts.

The actual contextual graph retains ordered Replay parents/input BoundKeys, FunctionPort and Derived/Transport edges, source Origin records and physical bound emission/admission evidence. From the fresh B≤T extrusion link, the actual processing relation Record(B)≤C is recovered; its upper R≤C link leads to the original h-call boundary F/H. The lower recursive-return path independently leads to F/F. This refutes an explanation that the retained data consist only of a flattened source set or cannot recover the h boundary at this fixed cut.

The two concrete queries are now evaluated: the receiving-boundary backtrace yields nonqualifying F/H; current support-`any` consumer yields qualifying F/F. Their distinction is visible in the retained graph. The [primary companion](../../../notes/theory/2026-10-24-retained-graph-publication-consequence.md) proves exact finite selection from graph/association/occurrence/pair records and applies these results to prior PR1–PR3. No fresh policy is chosen to obtain a preferred acceptance result.

**Remaining source theorem RG-OWNER:** derive that the selected operation's actual receiving occurrence is represented by the reconstructed boundary path, or derive a different authentic association from the same original source/transport rules. The SCC computation is complete for the stated graph. The faithful occurrence interpretation and full source-to-contextual path remain proof work, not a pending user decision. Actual equality-consumption time and full source membership are still required before applying the conditional rejection as a source counterexample. Whole-source safety/principality/combined termination are not closed.

## Concrete implementation correspondence findings

- The frozen `candidate_value_graph` owner walk omits FieldTail.receiver although `candidate_source` visits it. In the declared top-RHS representation, the graph misses P→F and, when resolved as a Name, P→T_bool. The semantic definition-root rule requires these incidences. The proof includes the source-required edges separately; both graphs have the same singleton result in this example. Other root representations can also change the default association owner for unvisited outer Apply expressions.
- The frozen Graph stores no immutable birth map. The proof supplies the concrete creation-level derivation from source constructors. Current all-graph SCC code is not certified as a general implementation of the new birth-level rule.

These are owner-specific correspondence findings, not permission to change compiler code and not a refutation of the user-selected mathematical operation.

## Independent review

Independent reviewer `/root/astra_semantics_review` authored neither target, verified the five frozen hashes (contract and four targets below), and found **no BLOCKING or MAJOR issue within the stated conditional scope**. It accepted the constructor adjacency/singleton calculation, FieldTail finding, source-derived birth annotations, fresh-cut admission/Replay backtrace, both concrete query results and finite qualification theorem. It preserved the rooted LocalSource correspondence premise, reuse/rollback exclusions and PR1–PR3 timing premises.

Primary accepts its boundary adjudication: recovering the upper boundary alone does not prove exclusive ownership of the new pair by that boundary. Neither all-ancestor ownership nor a general upper-boundary ownership rule is independently established. The retained ordered graph is present, and RG-OWNER is proof work under the current authority. No new user decision is required. The reviewer recommends deriving the exact receiving-occurrence judgment from original Call/transport rules with these retained witnesses, separately constructing the full source path and consumption timing.

After producer/reviewer STOP, primary transferred the exact stopped note lease and made only editorial review-header/status annotations in both proofs. The mathematical text and guides remain unchanged. Final proof hashes are recorded below; this receipt supplies no whole-language or implementation certification.

| Target | Frozen reviewed SHA-256 |
| --- | --- |
| `notes/theory/2026-10-24-retained-value-graph-replay-attribution.md` | `37d4a398f9c867d0b3996495ad34dcd590596ae23b8aed3c61c21073f72de16f` |
| `notes/theory/2026-10-24-retained-graph-publication-consequence.md` | `e8f05c9f615797439614e0ff50630843369400973e33dfccee55dc7bac4ba8e3` |
| `docs/yulang-whole-proof-closure-ja.md` | `591a97623bb2dc92e9bfa5d090db08f22a2f2447258cece329d2a2e5df5acf77` |
| `docs/yulang-proof-index-ja.md` | `8fee9696aff67bea304f2525c116a585374f8be599d46c8ee541acc5c0cbf465` |

Integrated proof hashes: graph extraction `8adfe10dda01a223c2b289cec81692cd6c92cca66f3170501b96fe894ff5c1c6`; primary companion `5ea7d91ece760262af4f1ddd9da6496c25a9a555e4f7d9a7c9279adf782b3574`. Both guides retain their reviewed hashes.

## Runtime and integration boundary

Prior4590s + direction30/producer190/review80 = **4890s charged**. The new envelope follows explicit user correction and a materially different graph-extraction method. Requested Astra/medium; observed model/effort/duration UNKNOWN. One child at a time, no descendants, no automatic renewal or unobserved refund. Current STOP receipts and final live reconciliation govern worker status; old recorded rows never establish a live process.

Actual direction, producer and reviewer STOP receipts were received; final live listing shows all five existing children completed, without descendants. Primary proof/document construction ends at this checkpoint; only final static/Git integration and reporting remain.

No implementation changes, tests, builds, compiler execution/probes, scratch, manifests, nested CLI or child Git/network. Static document checks cover19 frozen inputs, final leases, local links/fences, compact current JSON below16KiB and explicit seven-path whitespace/scope. These are document-integrity checks, not mathematical certification.

Exactly seven paths are intended: two new proofs, two guides, this contract/outcome pair and current state. Original `/home/momota1029/rust/yulang` and its unknown external reservations remain quarantined. Protected untracked question files are excluded. Primary inspects the entire outbound range and normally pushes the dedicated `research/semantics-proof-20261024` branch. The containing commit identifies the integrated bytes.

**Disposition:** graph/SCC and exact boundary-query construction advances the concrete obligation; occurrence/source transport and the original whole proof remain OPEN. No user decision or post-session worker activity is claimed.
