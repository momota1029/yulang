# Formal annotation filter: directed transition candidate

Date: 2026-10-10
Status: frozen research candidate; bounded checker passed; independent review pending
Claim class: source-inspected algebra correspondence and conditional finite transition characterization
Production authority: none; no semantic adoption, proof closure, or compiler change
Baseline: `7bb417ea45a651071ff87da7f7d38d81a2a93879`
Branch assigned by primary: `research/simple-sub-intrusion`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note and `tools/research_formal_filter_transition_contract.py` only
Verification owner: primary; producer may perform syntax inspection only

Primary verification: `timeout 30 python3 -B tools/research_formal_filter_transition_contract.py`
passed: 341 words, 3,087 replay pairs, 30 event orders and three detected
mutations; maximum 11 facts and four pending tasks. One bounded checker process
ran, with no timing samples or benchmark processes. This is consistency of the
shared source-derived transition assumptions, not support-projection, source
formation, hygiene or compiler conformance evidence. Shared task/index status
synchronization is deferred to integration after the independent review.

## Objective, authority and source anchors

Specify the missing row-bound and Function-port transitions for a private
annotation-owned endpoint candidate, including late Function discovery at an
unknown returned value. This assignment does not repeat the already known
attachment/support subtraction example and does not define new language meaning.

The governing selected meaning is
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §1:
contravariant concrete `[E]` permits function-local subtraction at that position;
covariant `[E]` permits concrete E, with symbolic variables still connected.
Sections 2–4 identify the Oracle construction and forbid canonical row identity
from creating annotation authority. Section 5 leaves the coupled implementation
open. The applicable process boundaries are `rules/research-lab.md` “One semantic
baseline”, “Writes, artifacts and review snapshots”, and “Evidence quality”;
`rules/design-authority.md` “Authority order” and “Natural compiler behavior”;
`rules/git-concurrency.md` “Disjoint-file mode”. No question bundle is consumed.

The stable Oracle source inspected in this assignment supplies these rules:

| Frozen source | Rule actually observed |
| --- | --- |
| `annotation/constraints.rs:657–691` | A concrete atom set receives a fresh subtraction ID and a push; variable-only tails do not supply a concrete set. Empty/wildcard branches are distinct. |
| `annotation/constraints.rs:424–470,921–926` | Negative return-effect construction preserves its inner variable, push and filter; output predicates pop the same IDs with the specified filter. |
| `annotation/constraints.rs:363–389,848–851` | Nested return values carry `NonSubtract` weights. |
| `lowering/expr/tail.rs:1058–1114` | Defined-lambda output predicates accumulate frame/latent predicates and wrap **both** body effect and body value. |
| `constraints/machine/propagate.rs:11–38` | `Pos::Stack` and `Pos::NonSubtract` prepend the weight to the left constraint context; they are not merely effect-row decorations. |
| `constraints/mod.rs:3566–3612` | Ordinary variance swaps directed sides, replay concatenates left weights in path order and right weights in reverse path order, then applies directed mix. |
| `constraints/directed_weight.rs:12–39,137–176,399–420` | Per-ID count composition, equal-family requirement for one ID, and directed mix. |
| `constraints/machine/propagate.rs:207–271` | Four Function ports; ordinary argument ports swap weights, result ports retain weights. Pure argument-effect passthrough is a separate branch using `both_from_right()`. |
| `constraints/machine/bounds.rs:3285–3360` | Filters check registered variable lowers, including future lowers; filtering a Value Function does not immediately recurse through its ports. |

At the successor baseline, `lib.rs:753–778` has kind-qualified endpoint pairs but
no directed context in `TypedPairKey`. `candidate_extrusion.rs:358–637` inserts
unweighted bounds and replays opposite bounds; `:641–695` chooses the row owner
by levels. `lib.rs:11879–11937` generates the four ordinary Function children.
`candidate_extrusion.rs:1–325` transports rows by `(endpoint,polarity,target)`;
`candidate_intrusion.rs:493–604` merges parent/copy row identities, transfers
origins, minimizes levels, increments generation and replays bounds.

## Exact hypotheses and representation candidate

This is a candidate representation of inspected transitions, conditional on:

1. Source formation supplies one authentic tuple
   `A=(formal, annotation occurrence, lexical frame, fresh attachment ID,
   resolved concrete set, connected symbolic rows)` for each selected position.
   Family/type-argument equality is already resolved. The checker substitutes
   two immutable IDs with the same singleton set and does not prove formation.
2. Every weighted endpoint/bound carries the actual ordered weight and the
   attachment records it references. No source occurrence/frame is reconstructed
   from a row representative, Function shape, level, or successful comparison.
3. Every emitted lower/upper bound is replayed against the opposite side,
   including later bounds, within one typed worklist and its one semantic memo.
4. Checked support is finite, normal row comparison is used, and Function
   argument-effect passthrough, wildcard/empty annotation rules, generalized ID
   rebinding, and output support projection are outside the experiment.

Use a weighted **value or effect** endpoint `View(K,endpoint,W,Arefs)`, where K
is kind and endpoint rows are subject to canonicalization. `Arefs` contains
immutable source records, not permissions unioned at a row. A pop predicate is
a distinct operation tied to its original attachment ID. Its set/filter does
not choose an attachment by effect-family equality.

For ID i, the normalized left word has `p_i` leading pops then `n_i` pushes.
An active push has immutable set `S_i`. Composing counts `(p,n)` then `(q,m)`
gives `(p,n-q+m)` if `q<=n`, otherwise `(p+q-n,m)`. Thus push then same-ID pop
cancels, but pop then push retains both counts. Different IDs never cancel,
even if their concrete sets coincide. The left filter F intersects on composition.
Right context contains only per-ID pop counts.

Write context `W=(L,F,R)`. The source-exact operations in the checked fragment are:

```text
prefix(B,W) = (B.left ; L, B.filter ∩ F, R)
swap(W)     = (pops(R), All, pops(L.leading_pops))
replay(W1,W2) = mix(L1 ; L2, F1 ∩ F2, R2 ; R1)
```

`swap` drops active left pushes and the left filter. Copying an entire unordered
profile onto the contravariant ports is incompatible with the inspected Oracle
rule. `mix` first leaves either single-sided context unchanged. Otherwise it
appends each right-ID pop to that ID's left word; an active left push keeps the
residual on the left, pure residual pops move to the right, and exact cancellation
removes that entry. The checker uses the finite alphabet `{E,F}` for `All`.

`Arefs` must follow the referenced operations; dropping an inactive reference
requires a separately justified lifetime/evidence rule. These equations do not
permit unioning distinct A records into a new source grant.

## Row lifting, Function lifting and late discovery

Store a lower bound as `(b,W_b→r,Arefs)` and an upper bound as
`(u,W_r→u,Arefs)`. Joining them enqueues `(b,u,replay(W_b→r,W_r→u))`.
For a new lower, join every retained upper; for a new upper, join every retained
lower. A direct row edge is a weighted edge, not a permission on either row.
The baseline's one-sided level-selected storage can remain only if its existing
replay invariant is extended to these contexts. A row alias cannot reduce the
bound key to `(representative,side,endpoint)` while omitting W/Arefs.

For `Function(a,ae,re,r) <: Function(A,AE,RE,R)` under W, enqueue:

| Port | Child constraint | Context |
| --- | --- | --- |
| Argument value | `A <: a` | `swap(W)` |
| Argument effect | `AE <: ae` | `swap(W)` for the ordinary branch |
| Result effect | `re <: RE` | `W` |
| Result value | `r <: R` | `W` |

The Function fields retain their value/effect kinds. Repeated nested return
descent retains W until an actual Function comparison reaches a port. Repeated
argument descent applies the source swap each time, rather than treating the
original source polarity as a universal grant. Pure argument-effect passthrough
is **not** covered: Oracle uses `both_from_right(W)` and a specially constructed
return-effect target. Applying the ordinary table to that branch is a failure.

A lambda output must construct `View(Value,body_value,pop_i[S_i],A_i)` and
`View(Effect,body_effect,pop_i[S_i],A_i)` together. When the value is initially a
row v, retain its weighted upper use. A later lower Function f replays through v,
obtains the weighted Function comparison, and carries its return context to
latent effects. No initial Function shape or solved provider is required.
The checker has this exact delayed topology. Wrapping only the immediate body
effect loses the context at the future latent return-effect port.

Provider no-backflow here means that an upper comparison generates demand
children without mutating the existing lower provider's stored endpoint/A record.
The finite checker verifies the original provider fact remains present and no
reverse edge to its contribution is created. This is directed transition
evidence, not a theorem for all effect/protection descriptors.

## Levels, frames, memo identity and rollback boundary

Transport separates row coordinates from source authority. A polarity copy uses
the existing row rule: rows older than/equal to target remain anchors; younger
rows receive a copy at target, an opposite-side parent link, and copied selected
bounds. Function children flip traversal polarity on a/ae and retain it on re/r.
Map every row mentioned inside a weighted view, including symbolic tails, using
the operation-local mapping. Preserve immutable A identities/sets while remapping
coordinates; do not use canonical row equality to map one attachment ID to another.

The extrusion key must distinguish context-bearing structures:
`(kind,canonical endpoint,polarity,target,normalized W,authority references)`.
The semantic task identity must similarly distinguish
`(kind,canonical lower,canonical upper,normalized W,authority references)`.
These extend the existing operation-local copy maps and **one** typed memo;
they do not introduce a second semantic memo. Diagnostic origins/cause replay
remain evidence attached to these tasks, not an alternate authority relation.
Equivalent keys may share work only when the retained authority dependencies and
their expiry behavior are demonstrably equivalent.

On SCC parent/copy equality, reindex row coordinates, union distinct retained
bound records, and requeue affected contextual comparisons under the existing
generation discipline. A contextual `(r,r,W)` is not automatically a no-op:
the baseline unconditional same-row short circuit needs separate validation.
The checker aliases rows with distinct contexts but does not execute the actual
SCC finder, generation invalidation, or self-cycle behavior.

Owner level is the source lexical formation level, distinct from the mutable
minimum level of canonical rows. The inspected output boundary is operational:
`lambda_predicate_subtracts` collects the defined frame's local/latent predicates;
`lambda_output_predicate_vars` emits both wrappers. Closing the lexical frame
must not erase the exported wrappers needed by later Function discovery. A live
frame cannot grant unrelated source uses authority merely because their rows
merge. No extra dynamic “frame active” guard is proposed.

The exact relation between frame closure, retained A records, exported wrapper
lifetime, capture/freshening and subtraction-ID rebinding is **unproved input**.
The stable successor source has no negative formal constructor establishing it.
This contract does not invent an expiry policy. Its immutable frame locator
identifies the owning construction point; it is not itself an expiry theorem.
Any coupled implementation must define journal rollback for new records, bounds,
memo entries, dependency edges, generation changes and remapped structures before
publication. This checker does not validate that transaction implementation.

## Executable envelope, independence and evidence limits

The checker has two implementations: count arithmetic/incremental worklist and
literal per-ID word cancellation/batch saturation. Both use the same **supplied**
source transition schema, concrete identity dictionary, Function table and
row-join rule. Algorithmic independence covers reduction/scheduling only. Neither
invokes Oracle, source lowering, current Rust propagation, support projection or
the retained full hygiene theorems. Agreement cannot prove those input rules or
their source formation. This is not a full `[E]` removal oracle.

Planned deterministic domain, no random seed:

- All words over `(ID0/ID1) × (push/pop)` of length 0–4: 341.
- Replay inputs: both left words length 0–2, right-pop words length 0–2 over
  IDs 0/1: `21 × 21 × 7 = 3087` pairs. Filters are `{E}` then `{E,F}`;
  arbitrary filter pairs and arbitrary concrete/type-argument sets are omitted.
- Two finite graph fixtures: unknown returned value then Function (four events,
  all 24 orders), and two source IDs sharing a canonical row (three events,
  all six orders). No weighted cycles or arbitrary nested Function graphs.
- Mutations: `context-erasure` suppresses a distinct W at the same endpoint
  pair; `global-family-cancel` identifies distinct IDs with equal sets;
  `effect-only-wrap` discards the body Value wrapper. Each must differ from the
  literal reference. These attack shortcuts in transition retention, not the
  already known whole-support subtraction example.

The model retains an unattached E contribution as a distinct output task with a
residual pop, while an attached E route has cancellation of its matching push.
This does **not** establish whether either task contributes concrete E after full
Oracle output projection. The missing concrete projection consumer is a precise
boundary; claiming whole effect subtraction from these weights would be false.

For N fixed endpoints and C normalized contexts, memo cardinality is at most
`N² C`; the two stored orientations of row bounds remain context-qualified.
Each Function comparison adds four children; row joins can create quadratic
products of lower/upper bound records. With A IDs, per-ID counts bounded by D,
and B possible filters, a loose context bound is `B (D+1)^(3A)` before authority
reference variants. This bound is conditional on a finite count/context envelope;
it gives no termination guarantee for weighted cycles producing new contexts.
Never silently cap counts to change an accepted result. The checker fails at
4096 retained facts/pending tasks or its 29-second deadline; the primary command
also has a 30-second process cap. Actual Python memory and wall usage are unknown.
No CPU timing measurements are requested; one lightweight process, no builds.

Producer verification at handoff: syntax inspection only. Primary execution,
mutation detection and observed maxima are recorded in the verification paragraph above.
No compiler tests, Cargo, formatting, Git mutations, or child agents were used.

## Conditional derivation and precise remaining cut

Under hypotheses 1–4, source wrapper normalization gives a weighted body row
use. Lower/upper replay composes its context with a later Function lower.
The ordinary Function rule carries that context to both result ports, including
the latent effect row. A concrete contribution arriving before or after the use
is joined by the same ordered composition, because both insertion sides replay
retained opposite bounds. Per-ID normalization preserves independent IDs at
equal sets; canonicalization changes only row coordinates. These are conditional
local transition statements; no reviewed theorem is asserted.

The smallest discriminating topology is one unknown Value row between a Function
lower and a pop-wrapped Function upper, plus one latent effect row receiving a
push-bearing concrete lower. Dropping the Value wrapper changes the latent task's
directed context. The separate two-route fixture uses one canonical row and two
distinct IDs with equal sets; pair-only memoization loses one contextual task.
These are executable witnesses of candidate transition loss, not source-language
counterexamples.

Recommended next action: independently review the row/Function contract and run
the bounded checker, then require the source owner to supply the negative formal
constructor and exact frame/output-lifetime/ID-freshening bridge before the coupled
filter implementation. Do not claim that increasing this finite domain would
resolve that missing construction premise. Full support projection and the
Oracle pure argument-effect passthrough need distinct source correspondence work.

## Commit packet

- Exact paths: `notes/progress/2026-10-10-formal-filter-transition-contract.md`;
  `tools/research_formal_filter_transition_contract.py`.
- Baseline: `7bb417ea45a651071ff87da7f7d38d81a2a93879`; Oracle:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Pinned dependency Git blobs: authority `e38db742e7fec97fc6215b60addcf1b80b904f2e`;
  successor lib `5c5cbf30c4b52f1ed5eb40a69f1f72192401e9e7`, extrusion
  `0e10d00fc9db845c03d14537a4ae4bcd5fd81a5f`, intrusion
  `ed363d7f0fea060eb19ce188294934e48589d591`, scheme
  `404ff4ae75f99d1854e1dff23bbe42db565012b9`.
- Oracle blobs: annotation `d2cf0e18266233c1e3c2943448244ee2a3499529`,
  directed weights `a5998519c74f89a8bd65b22defd8f0a1e4fd59d9`, propagation
  `d558e7b9c17d33e91c5bb39c4cd85ebbfa4a8b09`, constraints module
  `14860e3664a7ac05f7493f1d51fe69a6f34216e5`, tail
  `8289bfdc6a17b2469ae168ac7939d34813fda474`.
- Changed dependency hashes: none intentionally; only pinned Git source read.
  Primary must revalidate the live negative-formal producer separately.
- Claim/review: unreviewed conditional research candidate, frozen at producer
  handoff; no independent review or runtime conformance claim.
- Check: primary command
  `timeout 30s python3 -B tools/research_formal_filter_transition_contract.py`;
  primary execution passed as recorded above. Independent review remains pending.
- Proposed commit message: `research: specify formal filter row and Function transitions`.
- Shared deltas left to primary/curator: record this as a candidate transition
  contract in `tasks/current.md`/`tasks/research-lab.md`; retain the open negative
  source constructor, lifetime/freshening, passthrough and support-projection
  obligations. No theory status or design index promotion is requested.
