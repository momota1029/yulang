# F5c ordinary Function-ring complexity proof

Date: 2026-09-28
Scope: source-level accounting for the productive Function SCC ring in the
no-cap addendum
Reviews: architect, compiler referee, and performance auditor; source proof
closed for the exact successful recipe
Targeted output-cardinality delta review: performance auditor; replay and
substitution output gap closed for this recipe, with descriptor wording refined

## Result

The source supports the addendum's ordinary-ring target `O(N² log N)`, where
`N` is the number of definitions and compressed source bytes
`B = Θ(N log N)`. The bound is for the exact successful source recipe below,
under expected constant-time hash-table operations. It does not cover other
path-sensitive contexts or establish a global polynomial bound for all F5c
inputs. Production cutover remains closed on its separate acceptance gate.

## Source and constraint inventory

For each member `i`, the recipe is `my n_i x = n_(i+1 mod N)`. Collection
creates one Lambda recipe, four effect facts, and one resolved internal use.
Lambda admission adds one positive Function lower `F_i <= R_i`; SCC routing
adds `R_(i+1) <= B_i` and transmits exactly one copied Function lower
`F_(i+1) <= B_i`. The parameter row `P_i` has no value bounds, `R_i` has one
Function lower, and `B_i` has one direct lower plus that one transmitted exact
Function lower. The walker's single-direct-target equality check skips the
copied Function lower. No other value fact is produced by this recipe.

The collector and route therefore process `O(N)` facts and uses, plus `O(B)`
source-byte parsing and identifier hashing. SCC discovery is linear in the
`N` definitions and `N` internal-use edges. The expected-time qualification
applies to the existing hash-backed maps and sets.

## Generalization, replay, and normalization

Each member has one guarded candidate owner. The predicate walk and that
owner's lower-bound walk each traverse one Function spine of `O(N)` rows and
may each record a guarded trace of `Θ(N)` hops. The negative upper walk is
constant size. Thus the two trace copies and scans cost `O(N)` per member,
`O(N²)` overall.

The component memo persists between member drafts, but remains logically empty
for this recipe. The no-bound parameter and body rows finish as non-cacheable
variables; the cycle reentry taints every active positive R/B frame; and
`ExitRow` leaves active state before summary promotion. Consequently no exact
ring row is promoted into the component memo, and its incidence,
reverse-parent, and root-edge lists remain empty. The flat sink still creates
root-local raw nodes; this fact only bounds the separate component-expansion
memo. Every active row event therefore scans zero memo adjacency and performs
constant work. Each of the `N` drafts has `O(N)` active row events, giving
`O(N²)` cumulative active propagation.

For one initial R candidate, `r_candidates` removes candidates and has at most
two rounds. In each round it replays and checks at most one bound, scans at
most two traces, and analyzes the predicate once, costing `O(N)`. Post-R
selection, retained-occurrence traversal, replay, and binder substitution each
visit the one predicate spine and at most one lower/upper pair once; they
preserve its topology and do not multiply the spine by `N`. Boxed replay copies
each Function child once; substitution replaces variable leaves with scalar
leaves without multiplying the one-spine topology. The flat path may retain
unreachable copies from its bounded replay calls, but one candidate permits at
most two R rounds and one post-R pass; each call appends only one copy of the
predicate and at most one lower/upper pair. Its total staged raw nodes are
therefore `O(N)` per member, and selected-root traversal prunes unreachable
nodes before normalization. Each member thus contributes `O(N)` selected
nodes; across `N` members the batch has `D = O(N²)` nodes.

The ring produces Function and atomic Bottom/Top/Recursive/Quantified
descriptors of bounded width (at most five words: Function descriptors use
five, Recursive and Quantified leaves use two, and constants use one).
Descriptor words total `W = O(D)`. The prescribed height-group mergesort
performs at most `O(D log D) = O(N² log N)` comparisons over all groups, with
`O(1)` word work per comparison. The total is therefore `O(B + N² log N)`,
which is `O(N² log N)` and `O(B²)` coarsely for `B = Θ(N log N)`.

## Evidence boundary

The earlier `N=2/4/8/16` source captures corroborate this derivation but do not
establish its asymptotic order. The proof covers only the exact recipe and
successful path; failure cleanup, arbitrary source shapes, and F5e remain
outside it. The completed §15 source-ring capture budget is exhausted; any
new measurement requires a fresh reviewed plan and budget. No code, tests,
builds, or measurements were run for this proof.

## Source-owner phase-cost audit

Date: 2026-09-28. Read-only architecture audit of the current
`r_candidates`, `build_inner_work`, and `rank_all` implementations; no code or
test changes.

For `r_candidates`, let `r` be the initial eligible owner count. Candidate
masks only shrink, so the loop runs for at most `r+1` rounds. In round `j`,
write `c_j` for surviving candidates, `a_j` for the capacity scanned by the
candidate hash sets, `B_j` for bound replay and guard visits, `H_j` for
examined trace hops, `P_j` for predicate replay/analysis visits, and `E_j` for
reachable-owner/bound/reference traversal. The expected hash-time ledger is

`O(r + Σ_j(c_j + a_j + B_j + H_j + P_j + E_j))`.

Keep each term per mask and round. In particular, the two `retain` operations
scan hash-set capacity, not only length, and mask-dependent replay cannot be
collapsed into one pass over the compact graph. Trace survival examines each
visited hop once.

`build_inner_work` adds predicate expansion; positive and negative expansion,
materialization, and incidence visits for each distinct reentry owner; trace
indexing; raw-root/order scans; the full `r_candidates` ledger; post-R replay
and retained-occurrence traversal; and substitution over each selected
predicate and recursive bound. The `non_generic_closure_work` rebuilds
session adjacency per member, costing `O(V + E + T)` for session-bound rows,
visited endpoints/adjacency, and term-row visits, followed by linear
reachability. This is an `O(N²)` contribution over an `N`-member ring.

For `D` selected DAG nodes, `W` descriptor words, and `C_norm` actual
descriptor-word comparisons, batch `rank_all` groups by height and radix
preorders in `O(D+W)`, while prescribed child/height-group merges and adjacent
equality checks cost `O(C_norm)`. Its source-level bound is `O(D+W+C_norm)`;
the comparator scans descriptor words, so comparison count alone needs a
descriptor-width bound. The exact ordinary ring has one R candidate, at most
two rounds, at most two `Θ(N)` traces, fixed-width selected descriptors and
`D=O(N²)`, yielding `O(N² log N)` under expected constant-time hashing. No
concrete asymptotic blocker was found for that exact successful recipe.

The proof does not extend to arbitrary path-sensitive contexts. Their trace
multiplicity and repeated mask-dependent replay remain explicit work terms,
and the no-cap addendum makes no universal compressed-source polynomial
claim.
