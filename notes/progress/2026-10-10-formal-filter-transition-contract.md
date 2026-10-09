# Formal annotation filter: directed transition candidate

Date: 2026-10-10
Status: repaired conditional research candidate; bounded checker and independent delta review passed
Claim class: source-inspected algebra correspondence and conditional finite transition characterization
Production authority: none; no semantic adoption, proof closure, or compiler change
Repair baseline: `9d7967c3a6c1db0304963e21681c770d0080be44`
Original candidate baseline: `7bb417ea45a651071ff87da7f7d38d81a2a93879`
Branch assigned by primary: `research/simple-sub-intrusion`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note and `tools/research_formal_filter_transition_contract.py` only
Verification owner: primary; producer may perform syntax inspection only

Primary repair verification: `timeout 30 python3 -B tools/research_formal_filter_transition_contract.py`
passed: 341 words, 3,087 replay inputs, 68 event orders and seven detected
mutations; maximum 11 facts/four pending tasks. One lightweight checker process
ran; zero timing samples, benchmark processes or compiler builds. Independent
source-semantic delta review found no findings and closed the insertion mismatch
within this finite supplied model. This is not source formation, support
projection, full hygiene or production conformance evidence.

Historical verification at `9d7967c3a`: 341 words, 3,087 replay inputs, 30 event
orders and three mutations passed, maximum 11 facts/four pending tasks. That
revision incorrectly retained the left filter on stored bounds, including
`v:return <: fun:U` carrying `POP=(pop0,{E},empty)`, then replayed `{E}` into
latent result ports. The accepted source mismatch invalidates that revision's
insertion/filter correspondence. Its passing checker was consistency evidence
for the wrong shared schema. It is not verification of this repair. Shared
status synchronization remains the primary's responsibility after adjudication.

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
| `constraints/machine/bounds.rs:630–646,714,3174–3191` | Lower insertion checks the weighted positive lower with its left filter, erases that filter before storage, then applies filters already registered on the target to the stored lower. |
| `constraints/machine/bounds.rs:815–831,3193–3210` | Upper insertion checks active left stacks, registers the left filter on the source row, then erases it before storage. |
| `constraints/machine/bounds.rs:3213–3255,3285–3360` | Registered filters check current/future variable lowers. Filtering a Value Function is a no-op, without port traversal. |
| `constraints/row_effect.rs:834–848,875–932` | Active stack families and concrete effect families are checked against a filter; the checker covers only finite zero-argument E/F families. |

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
3. Every emitted row bound follows the insertion check/register/erasure rule
   below before replay against retained opposite bounds, including later bounds,
   within one typed worklist and its one semantic memo. Registered filters persist
   for the finite run and are applied to future lowers; this is not a source
   lifetime theorem.
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

Let `erase(W)=(L,All,R)`. The insertion operations precede row joining:

```text
weighted_check(b,W,F):
  check every active family in W.left against F
  check positive shape b against (W.filter ∩ F)
lower_insert(r,b,W):
  weighted_check(b,W,W.filter)
  store (b,erase(W)) at r
  weighted_check(b,erase(W),G) for each G registered at r
upper_insert(r,u,W):
  check every active family in W.left against W.filter
  register W.filter on r; check every current stored lower at r
  store (u,erase(W)) at r
```

`All` checks/registration are no-ops. Positive shape checking registers a filter
on a variable and checks concrete effect families; `Pos::Fun` is a no-op and
never traverses Function fields. Future lower insertion applies the registered
filter to that lower's active stacks and positive shape. For row-row input,
Oracle inserts both orientations; each consumes the supplied filter and stores
its erased context. The checker includes one acyclic row-row fixture. It omits
Oracle extrusion, subsumption, provenance and same-row short circuits.

Joining retained `(b,W_b→r)` and `(u,W_r→u)` enqueues
`(b,u,replay(W_b→r,W_r→u))`. These **stored** contexts already have `All` left
filters. Pop/push IDs and counts remain intact: erasure removes only F, not the
ordered directed word. A direct row edge is a weighted edge, not a permission
on either row. The baseline's one-sided level-selected storage can remain only
if its replay invariant accommodates this separation between checked row filters
and retained directed contexts. A row alias cannot reduce the bound key to
`(representative,side,endpoint)` while omitting W/Arefs. No successor data layout
or new semantics is selected here.

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
obtains a Function comparison carrying the retained pop word **without** its
consumed left filter, and carries that directed word to latent effects. The
registered filter on v checks f as a positive Function, with no port traversal. No initial Function shape or solved provider is required.
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
row-join rule, insertion erasure rule and positive-shape filter-checking rule.
Algorithmic independence covers reduction/scheduling only. The repair grounds
those rules by the pinned source sections above; model agreement adds no further
source validation. Neither
invokes Oracle, source lowering, current Rust propagation, support projection or
the retained full hygiene theorems. Agreement cannot prove those input rules or
their source formation. This is not a full `[E]` removal oracle.

Planned deterministic domain, no random seed:

- All words over `(ID0/ID1) × (push/pop)` of length 0–4: 341.
- Replay inputs: both left words length 0–2, right-pop words length 0–2 over
  IDs 0/1: `21 × 21 × 7 = 3087` pairs. Filters are `{E}` then `{E,F}`;
  arbitrary filter pairs and arbitrary concrete/type-argument sets are omitted.
- Eight graph fixtures, all event permutations: late Function through an upper
  wrapper (four events, 24 orders); through a lower wrapper (four, 24); equal-set
  IDs at one canonical row (three, six); future forbidden concrete lower (two,
  two); immediately checked lower insertion (two, two); upper active-stack check
  (two, two); lower active-stack check (two, two); acyclic row-row filter bridge
  (three, six). Total 68 orders. These expose both insertion orientations,
  current/future registered checks and absence of Function port traversal.
- Seven mutations: the original `context-erasure`, `global-family-cancel` and
  `effect-only-wrap`; plus `retain-upper-filter`, `retain-lower-filter`,
  `skip-future-filter` and `recurse-function-filter`. Each must differ from the
  literal/batch reference snapshot, which now compares retained facts,
  registered filters, checks and violations. The retain-filter mutations must
  specifically change non-row output contexts, skip-future must omit the named
  forbidden F check, and Function recursion must register E on the latent row.
  These detect representation/checking shortcuts, not whole-support removal.
- Filter checking covers only finite sets over zero-argument concrete E/F,
  active stacks and row variables. Row items, Stack/NonSubtract positive shape
  recursion, unions, other shape branches, type-argument unification, wildcard,
  Empty/AllExcept filters and arbitrary filter pairs are omitted. `All` is the
  finite surrogate `{E,F}`, never an assertion that Oracle wildcard is finite.
  No weighted cycles, arbitrary nested Function graphs or source programs run.

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
4096 candidate memo entries, candidate retained facts plus filters/checks/
violations, reference tasks plus filters/checks/violations, or pending tasks,
or its 29-second deadline; the primary command
also has a 30-second process cap. Actual Python memory and wall usage are unknown.
No CPU timing measurements are requested; one lightweight process, no builds.

Producer verification at repair handoff: syntax inspection only. Primary revised
execution, mutation detection, maxima and independent review are recorded above;
historical counts refer only to the superseded schema.
No compiler tests, Cargo, formatting, Git mutations, or child agents were used.

## Conditional derivation and precise remaining cut

Under hypotheses 1–4, source wrapper normalization produces the body row use
`v:return <: fun:U` with `W=(pop0,{E},empty)`. Upper insertion registers `{E}`
on v, checks the active stack (there is none), and retains
`(v,fun:U,(pop0,All,empty))`. A later lower `fun:L <: v` checks the registered
filter on `Pos::Fun`, with no recursive work. Replay therefore produces
`fun:L <: fun:U` under `(pop0,All,empty)`. Ordinary Function result ports retain
that context. On the latent effect row, joining the attached `push0` route gives
`(empty,All,empty)` while the unattached route retains `(pop0,All,empty)`.
The old model instead delivered `{E}` on both results. This four-event fixture
adds the two concrete routes to the minimized two-event insertion discriminator:
`v <: fun:U` under POP; `fun:L <: v` under EMPTY. No concrete source program or
support-projection claim follows from either witness.

The opposite-orientation discriminator inserts `fun:L <: v` under POP, then
`v <: fun:U` under EMPTY. Lower insertion checks the Function without traversing
it, retains POP_ERASED, and creates no filter on v. Replay again carries the pop
word with All into the result ports. An immediately forbidden concrete F lower
with left filter E records a violation before storage erases E. Separately,
registering E on a row before a later concrete F lower must record that violation;
all permutations verify the analogous current-lower check. Active-stack fixtures
use an E push with filter F and must record a stack violation in each orientation.

These are source-inspected local operational correspondences and conditional
finite characterization, not reviewed theorems. They preserve provider bounds,
independent same-set IDs and row-coordinate aliases within the stated fixtures.
Source formation of authentic annotation records, frame/output lifetime,
ID-freshening, support projection, pure argument-effect passthrough, actual SCC
reindexing/generation, transaction rollback and weighted-cycle termination stay
unproved. The new filter registry is a finite supplied operational input, not a
new successor ownership or expiry policy.

Recommended next action: primary runs the bounded repaired checker and requests
one independent delta review against the exact insertion/filter source anchors;
then keep the source constructor/lifetime/projection gate open rather than
increasing finite counts to claim it closed.

## Commit packet

- Exact paths: `notes/progress/2026-10-10-formal-filter-transition-contract.md`;
  `tools/research_formal_filter_transition_contract.py`.
- Repair baseline: `9d7967c3a6c1db0304963e21681c770d0080be44`; Oracle:
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
  `8289bfdc6a17b2469ae168ac7939d34813fda474`; newly inspected bounds
  `365ed25a8b3b7e468a7a4e57159125be53209708`, row-effect checking
  `d33c8d34f14dd5acc3b995050f4e9f7fa07ade25`.
- Changed dependency hashes: none intentionally; only pinned Git source read.
  Primary must revalidate the live negative-formal producer separately.
- Claim/review: conditional research candidate; accepted insertion mismatch
  repaired and independent source-semantic delta review passed. No runtime
  conformance or full hygiene claim.
- Check: primary command
  `timeout 30s python3 -B tools/research_formal_filter_transition_contract.py`;
  revised execution passed as recorded above. Producer syntax inspection only;
  historical passing execution is superseded for insertion correspondence.
- Proposed commit message: `research: correct formal filter insertion and erasure witnesses`.
- Shared deltas left to primary/curator: record this as a candidate transition
  contract in `tasks/current.md`/`tasks/research-lab.md` as repaired, with
  `9d7967c3a` insertion evidence superseded and revised verification passed;
  retain the open negative
  source constructor, lifetime/freshening, passthrough and support-projection
  obligations. No theory status or design index promotion is requested.
