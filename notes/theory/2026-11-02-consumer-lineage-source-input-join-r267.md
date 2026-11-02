# R267-r6: ordered Function inputs and the remaining source join

Revision 1. **Candidate source-native evidence; source-input join and parent OPEN.**
Author: `/root/sol_r267_source_input_join`; no descendants or coauthors.
Contract: `tasks/agent-loop/sprints/consumer-lineage-closure-r267-r6.md`,
SHA-256 `000e0d4d4297026ab8b4c634b7d7e36f186070d04236f852d9f6ae189e7277c9`.
Baseline supplied by Luna: `8d646ac2ed171e13a529e25e035fc75f91678b0b`.

## Parent and achieved boundary

The unchanged parent edge is inference soundness -> R70 copy correspondence ->
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`. The full accepted source domain, original
Simple-sub A/B, independent satisfying assignments and shared witnesses,
F1/FK1 and foreign continuations are unchanged. Parent/A/B delta: **0 -> 0**.
No complete source occurrence/canonical-candidate/consumer join or accepted-source
counterexample was constructed. This is not a claim of an actually executed
source fixture: no execution was authorized. The statements below concern actual
constructor behavior for any reached instance satisfying their stated local
conditions; they do not assert those conditions for every source occurrence.

The source read establishes two precise local facts. First, a Function Replay
consumer's immediate input keys contain structural Function items, not row items.
Second, at a selected exact Function slot, canonicalization creates no stale-item
lookup discrepancy. Applied to R71, this discharges the raw-key availability
subcase for that selected exact slot within R70's successful stable local call.
It does not establish which source occurrence independently requires a particular
canonical lineage, nor that an arbitrary later Function Replay came from that
subcase. The first missing join is stated below rather than assumed.

Lean declarations, theorem types and axiom dependencies: NOT APPLICABLE. No Lean
proof/checker was assigned or run. No new semantics or production authority.

## 1. Backward reconstruction from the consumer

At `lib.rs:14411-14485`, typed-drain Transport retains the canonical-task
relation; Context executes that relation; Dispatch records Function children;
FunctionAdmission calls `candidate_function_port_admit` with the current processing
RelationId (`lib.rs:15060-15090`). The Function dispatch children are derived
from the actual positive/negative Function terms (`lib.rs:14905-14967`), with
Argument and ArgumentEffect contravariant and ResultEffect and Result covariant.

For an ordinary Replay generated at `candidate_replay_bound`
(`candidate_extrusion.rs:1070-1111`), let o be its canonical owner and let the
actual emitted task have positive Function L and negative Function U. Reading
that constructor in both insertion polarities gives exactly

```text
lower_input = (o, Positive, PositiveFunction(L))
upper_input = (o, Negative, NegativeFunction(U)).             (INPUT267)
```

If insertion polarity is Positive, the lower key is inserted and the upper key
is existing; if Negative, their roles as inserted/existing reverse, while the
ordered lower/upper keys above do not reverse. The incoming restoration owner
uses the same ordered keys, with incoming_use=true (`:1034-1066`). This is a
constructor equation for these routes, not exhaustive coverage of all source
histories or an assertion that a particular source term reaches this task.

`candidate_context_begin_replay:4411-4497` takes exact heads on those keys and
enumerates new-lower x all-upper, then old-lower x new-upper. Incoming-use resets
the prior heads. For each retained pair l,h it constructs

```text
Replay { child:q, lower:l, upper:h, lower_input, upper_input }
K(q) = J(K(l),K(h))
S(q) = union(S(l),S(h))
F(q).transformer = compose(F(l).transformer,F(h).transformer)
F(l).demand = None; F(q).demand = F(h).demand.
```

Here K is the immutable relation-key context, S its source set, F its scoped
flow, and J(I,I)=I, otherwise ordered ContextExpr::Replay. Exact dependency
novelty may suppress another ordinary queue admission, but does not turn an
unselected input into a Replay parent. Equal q IDs do not identify distinct
Replay recipes. INPUT267 therefore fixes which side carries an authentic
source demand: h, never an arbitrarily chosen lower or same-pair relation.

At the Function port (`candidate_context.rs:3924-3988`), a present demand must
match the processing relation's actual upper NegativeFunction root. It retains
original_call/use_instance/output_scope/input; then removes demand on the child
and creates the field-specific stamp_input or protect_body transformer on Effect
ports. Value ports retain transformer zero. The inherited scalar context is
P_v(processing), with Swap for Argument/ArgumentEffect and Preserve for the two
result fields, followed by the child-local prefix. A successful authentic-root
check proves this local root equation; it does not prove source necessity of all
fibers in upper_input's bucket.

## 2. Exact Function slots have no stale-item discrepancy

Local statement, in R70's existing successful local operation envelope: fix a
selected physical Value slot s whose stored item is PositiveFunction(L) or
NegativeFunction(U). Let k=(visited_owner,p,stored_item) be its exact saved raw
source, and let C canonicalize row endpoints in the forest at this local cut.
Then

```text
k = C(k).
For every c attached at C(k) at the transfer cut, Work::Bound
transports that exact c, with its own dependency and FiberTransform. (SLOT267)
```

Derivation: `canonical_value:11925-11931` rewrites only ValueRow endpoints;
Function terms are returned unchanged. `canonical_extrusion`
(`candidate_intrusion.rs:293-298`) preserves that distinction. R70's Visit keys
already have canonical owners; its stable local call does not perform intrusion
representative writes. The selected exact-lane item is read verbatim and the raw
BoundKey is saved separately from the canonical child Visit key
(`candidate_extrusion.rs:110-180`). Thus neither owner nor Function item changes
under C at the transfer cut. This uses the reviewed local stability premise,
not an all-source ENTRY-WF theorem.

`Work::Bound:399-417` installs the mapped physical Function item and passes k
unchanged to `candidate_transfer_bound_origins`. That helper
(`candidate_effect.rs:1045-1089`) captures the full exact-key head, saves next,
and transports each retained relation. Since k=C(k), a canonical candidate on
that particular key is an actual loop parent. All such candidates are covered;
there is no need to choose one preferred fiber or infer necessity from bucket
membership to establish this local availability result. Empty lists remain
legitimate. No claim is made about a candidate attached only after that captured
prefix or a different selected slot/owner.

The transported flow retains exact source/scoped identities and only remaps a
matching NegativeFunction demand root through the actual from/to witness
(`candidate_context.rs:3286-3298,4737-4751`). Distinct dependencies, antecedent
snapshots, coverage gaps and transforms remain distinct even if child IDs intern
together. SLOT267 neither erases evidence nor substitutes metadata for executable
fibers. Structural Function copying can change U to a copied U'; that is the
operation-local structural map and witnessed root remap, not row canonicalization
of U.

Application at unchanged R71: for this selected exact Function-slot subcase,
every independently required candidate already on the canonical key is available
to R70's actual raw lookup and gets an actual Extrusion transport. The remaining
stale-item branch of this particular comparison is a selected direct-row slot,
where the stored row can differ from its representative. This is a local case
reduction, not source-wide R71 coverage. INPUT267 does not prove that an earlier
copying occurrence selected an exact Function slot: later propagation may have
materialized its Function endpoint through direct-row ancestry, a later merge,
FreshUse or another Replay.

## 3. Source constructors meet only part of that backward requirement

The forward source spine retains an Apply association keyed by its checking
occurrence, origin definition owner and resolved callee
(`candidate_value_graph.rs:329-344`). The Apply record separately retains callee,
argument, application result, effects, checking/cause, recipe and source call
index (`candidate_source.rs:1872-1924`). Native demand construction uses those
actual endpoints, stores the native interface before constraint admission, and
constrains callee against that demand (`shadow_apply.rs:4302-4399`). Apply result
is not thereby its Lambda body or definition root; Action::Link still admits a
constraint (`candidate_source.rs:2482-2486`).

At `candidate_context_seed:3793-3838`, source events and an eligible local-slot-0
introduction seed the exact original_call, use_instance=0, demand root,
output_scope and input route. Eligibility is conditional on retained introduction;
no every-Apply scoped-demand theorem follows. `retain_extrusion_parent`
(`candidate_intrusion.rs:305-365`) retains actual parent/copy/polarity/target,
occurrence, comparison and source set; qualification checks the approved source
Value event. This does not select a canonical candidate needed at a later copied
slot or identify its opposite Replay input.

The first missing constructor-to-consumer equation is the joined existence and
coverage assertion for one actual accepted source occurrence omega:

```text
its actual source checking event / origin and receiver Values
 + its retained Parent indices / selected physical slots and raw prefixes
 + its independently required canonical candidate c
     -> the exact ordered (lower_input,l,upper_input,h,q) of INPUT267,
        with all actual intervening transports, scope/use/root remaps,
        pair/source/scoped payloads and processing consumer retained.
```

No total mapping of that tuple was derived. In particular INPUT267's authentic
upper demand does not establish which earlier selected direct-row slot carried
its required c or why a proposed h_c is its actual opposite input. The owners
that must meet are `candidate_apply_value`/`candidate_replay_bound`
(`candidate_extrusion.rs:1070-1144`) and source qualification/Work::Bound, with
`candidate_context_begin_replay` retaining the ordered relation incidence.

Existing fail-closed diagnostic authentication is not the missing existence
proof: `authenticate_replay_ancestry:3338-3449` requires supplied source and
FreshUse relation IDs/from/to, a matching retained Replay, exact current key
attachments and four FunctionPort dependencies. It rejects absent incidence;
it does not construct an accepted source omega, cover ordinary paths, or cover
a rewritten consumer (its documented consumer is the direct q identity case).
FreshUse scoped remapping separately preserves local scope/input/root/use
mapping (`candidate_scheme.rs:4859-4883`). Neither successful authentication nor
a shared source-set membership proves arbitrary ordinary canonical necessity.

No absence assertion is made. A falsifier still needs all same-class selected
slots, all raw prefixes, unscoped bootstrap, incoming Allowances, both pre-merge
copy sides and earlier completed canonicalization paths. The current merge
copies before representative mutation and its later sweep (`intrusion:599-710`)
cannot justify its earlier lookup. Full accounting was not constructed here.

## 4. TEMP265/Z265 and the parent remain open

Preserve R265's definitions and equations unchanged:

```text
P_t(r) = discharge_residuals_t[r] (or I) if r is discharged at t;
         K(r) otherwise.
J(P_t(r), K(h))  ?~  J(P_t(c), K(h_c))                 (TEMP265)
Z_A(J(P_t(r), K(h))) = Z_A(J(P_t(c), K(h_c))),          (Z265)
```

Z_A is the same live arena's validated filters/residual before callbacks under
successful reservations/sampling; ?~ remains unresolved. Reviewed VD267 gives
P_t(r)=K(r) for retained Value relations and makes their ordinary transport K
constant along actual edges. SLOT267 supplies an actual edge for every candidate
at the selected exact Function key; it does not supply the missing c/h_c paths
for direct-row ancestors. Effect temporal simulation, actual receiver callbacks
and all later Effect relation-local cuts remain open. At a retained reached Value
q, VD267 gives P_v(q)=K(q); that cannot manufacture q or its source ancestry.

Thus the R70 raw-prefix fact applies directly to the SLOT267 subcase. Its
source-wide application at R71 still lacks the joined accepted-source tuple
above. ENTRY-WF, drain/eventual Diagnostics, Q262-EPISODE, permitted-history and
whole-solver rollback, diagnostic adequacy, successful-helper coverage, full
soundness, A/B, F1/FK1 and foreign continuations remain OPEN.

Mutual TODO `R267-R6-SOURCE-ORDERED-INCIDENCE-1` to Luna: preserve the original
R70/R71 parent. Obtain the exact source/Parent/slot-to-ordered-input tuple above,
including why c is required and every competing path. Distinguish the locally
covered exact Function-slot case from direct-row ancestry. Falsifier: a named
accepted-source reached consumer requires a lineage absent after all competing
slots/history paths, not unequal ContextIds or a failed diagnostic helper. This
TODO grants no dependency, code, observer or resource extension.

`NO_SAFE_CODE_SLICE`: Work::Bound/raw-prefix transfer and Replay/Function-port
owners expose no established violation of an approved clause. The missing join
is evidence, not a justified production repair. A later separately authorized
observer would minimally need the exact tuple above and retained evidence gaps;
this packet adds no observer or production edits.

## 5. Provenance and checks

Reused only within actual premises: R70's reviewed successful local worklist
invariant (author `/root/r70_ordinary_extrusion_proof`, complementary author
`/root/r70_extrusion_countertrace`); R71's reviewed one-way retention/forwarding
(author `/root/r71_raw_canonical_proof`); R265's accepted conditional consumer
formulas (author `/root/sol_r265_consumer_lineage_51dd6af`); R267-r5 reviewed
VD267 (author `/root/sol_r267_consumer_lineage_r5`). No R261/R262 result assumed;
R255's excluded theory and all excluded/quarantined paths remained unread.
Historical contract links were not followed as new dependencies.

Initial gate: all 47 pin occurrences extracted from R6 matched (the R4 stop
receipt occurs twice; 46 distinct immutable files), and all 36 R255 manifest
entries matched before source-body reads. Only the 14 enumerated Rust/HIR paths
were eligible for body reads. Some bulk operational output was truncated; no
claim of exhaustive comprehension of truncated text is made. Subsequent exact
operational reads supplied the active process/role/authority rules used here.
Direct technical hashes are exactly those in the frozen R6 contract and R255
manifest `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
Final revalidation and theory/handoff hashes appear in the terminal freeze.

Runtime identity matched before GO; session supplied by Luna:
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested producer model/effort per
Luna/current state: gpt-6-sol/high (contract says Sol/high); observed UNKNOWN.
The initial report's gpt-6.1-sol/high request wording was corrected by Luna;
no model switch is claimed. Three substantive stages: consumer reconstruction;
source/slot join and local case application; remaining-premise/freeze. Grant
540 seconds, no reset/extension; full reservation charged. No descendants,
tests, builds, probes, Lean, Cargo, Git, source/expectation edits, external contact,
scratch/cache or generated outputs. Only the two leased R6 Markdown outputs
are new. Independent review and adjudication remain Luna's responsibility.
