# R263: exact Replay tokens and the first source-causal charge obstruction

Recovered provisional draft, revision 1 with provenance correction. Candidate
source/native correspondence and a proposed accepted-prefix falsifier of one
episode charge. Original author:
`/root/sol_r263_source_causal_episode`; no descendants or technical coauthors.
`/root/r263_repair` corrected the recovery/provenance statements only. The
technical argument below remains unreviewed and is not an accepted proof result
or a Lean theorem. The original worker stopped before a freeze check or inbox
handoff was completed; see
`tasks/agent-loop/history/20261102-r263-stop-reconciliation.md`. Contract SHA-256
`3d5b618dcfe388dc9ff935816d9b703e60f76f2226255567b0175c70c8ea5f98`;
admission SHA-256
`7834c24d6c14ed9e56ba89510a020c7e7755b55620086767198784e8ccf41da2`;
fixed pre-admission baseline HEAD/origin
`0ca717c7bca52105df447548fab00898d410ac0b`.

## Claim and disposition

The unchanged parent is inference soundness and its Rust implementation on the
original accepted source domain, with Simple-sub A/B, independent satisfying
assignments, shared witnesses, F1/FK1 and foreign continuations intact. The
immediate edge is `Q262-EPISODE(r,p,L)` to R251's distinct-pair birth charge,
then R70-DRAIN eventual Diagnostics. R70's all-source entry premise W remains
separate. The proposed source-local result here is **TOKEN263**, exact ordinary Replay
dependency non-reuse at a fixed key, and **MIX263**, a claimed accepted source prefix
that defeats a one-event/one-branch causal charge and an entry-fixed exact-token
inventory. Neither bounds the number of newly constructed tokens. The episode
bound, R251's branching charge, R70/R71, the full parent and A/B remain OPEN;
parent/A/B delta is 0 to 0. There is no divergence or production-defect claim.

The R255 source manifest SHA-256 is
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
The stop receipt records that all 36/36 direct source hashes matched before
source-body reads. No final freeze recheck was completed; the hashes and source
locators below are retained draft inputs, not newly authenticated dependencies.
Reviewed R262 theory/handoff/outcome/overlap hashes are respectively
`848cd42d99d5638060703a14b332f9e7cce4e4a7e7def56ee5565b37a68cb63b`,
`aac3790116c591c9666a529ae7da9966d37550e308ab0cadc2616759f3b321d9`,
`f057ef37b651c20a4668f006b26cfbb5bdd249d85b17a9dc094bf66e149f5a07`,
`bc0675bbc15362ffd7c38ea4e22bf5105936badff1c9c2617005fbe8b6ec9165`.
R257 accepted-prefix note SHA-256 is
`97d9c27dd9715d5e5dd9f9013f386bd86d1ac4f6260b503aed18566d5132ef9a`.
The R262 unreviewed stage-2 memo and quarantined R261 inbox were excluded.

## Constructor-to-consumer correspondence

`candidate_source.rs` plans a Lambda as its own fact and retains Fact actions;
an Apply records actual callee/argument/result endpoints, a checking
occurrence, and a `Candidate` action. Name planning uses a local/parameter/
module resolution, with local initialization or later slot use, and emits a
Link or Local action as appropriate (source:1780-1925,2080-2120,2428-2500;
lib:11546-11591,11620-11821). At Context seed, only a checking occurrence
found in `references.checking` receives that Apply event as a singleton source
set (context:3793-3830). The event is not a free label attachable to an
arbitrary later pair.

The source Graph stores `Association { origin: owners[index], receiver:
expression_value(callee) }` for each Apply. Owner traversal begins at the
source root, propagates through ordinary structural/Lambda children, and
changes to `Value::Local(binding.id)` for a binding initializer. A Name adds
an owner-to-resolved-Value edge; expression fragments add result-to-fragment
and fragment-to-structural-child edges (value_graph:110-345). For a direct
Name callee, the owner-to-receiver edge is present. A general expression
callee has no automatic owner-to-Apply-result edge merely because the event
record exists. `seal` rejects cross-level edges into helpers and performs
both SCC passes **only on equal-planning-level edges** (value_graph:350-394).
Semantic-Value edges may cross levels but are excluded from those SCC passes.
Component IDs are representative ordinals, not a rank or a DAG order across
level changes. `qualifies` tests component equality, without consuming or
orienting the event (value_graph:395-397).

Each retained relation key includes the complete pair, Context, source set,
and scoped flow (context:3470-3513). Direct/port/rewrite/bound derivations
retain the actual parent source set; Replay uses the union of *both* input
relation source sets, composes their scoped flows and records
`Dependency::Replay { child, lower, upper, lower_input, upper_input }`
(context:3527-3538,3910-3925,4314-4358,4411-4478). The input keys are the
ordered raw keys selected from the current canonical owner and bound at the
replay invocation. Relation ancestry keeps both antecedent RelationIds and
both keys. Source-set union alone erases which branch supplied a particular
event. A Value ExtrusionLink preserves the processing relation's source set
and bound derivation while resetting executable Value scoped flow to default
(context:3455-3472,4314-4358). `retain_extrusion_parent` qualifies the
*processing* source set, records the raw Parent and may put it in `pending`;
the Parent provenance is deliberately absent from dependency adjacency
(intrusion:305-355).

The deep Visit canonicalizes a row and checks its current level against the
target. At `h>L` it makes one fresh row per invocation-local `(row,sign,L)`
map key, retains its Parent and opposite-side source link, then follows
visit-time bound slots and structural selectors (extrusion:24-43,71-215,
295-347). Successful Function/Tuple/Record/Variant comparisons emit actual
ordered port children (lib:14900-15161). Ordinary bound insertion appends a
physical slot and authenticates readback, then invokes replay against the
current opposite slots (extrusion:700-875,1070-1145). Context `attach`
deduplicates `(BoundKey,RelationId)` fibers despite possible repeated physical
slots; `begin_replay` joins new lower fibers with all current uppers and old
lowers with new uppers, omitting old/old (context:3702-3715,4411-4497).
`drive_replay` queues children for later Transport/Context/Dispatch; it does
not run a child in that producer call (context:4517-4647). Dispatch checks
actual processing relation/generation, canonical representative, prior
whole-pair rewrite, and raw complete pair before an extrusion can repeat
(lib:13593-13606,14411-14485,14565-14615,14814-14866). Settlement is later,
at an empty typed queue; it merges pending Parents, transports bound fibers,
min-lowers levels, canonicalizes keys and replays merged lowers
(intrusion:568-710; context:4649-4678). Thus graph edges, source events,
relation dependencies, physical slots and successful pair dispatch are
separate objects.

## TOKEN263: what exact ordinary Replay novelty actually buys

Fix an ordinary `incoming_use=false` Replay call before equality-generation
change, its ordered input BoundKeys `b_l,b_u`, and attached antecedent
RelationIds `rho_l,rho_u`. These determine the child pair from the input
bounds, Context from their Contexts, union source set and composed scoped flow;
relation interning returns the same child RelationId if the complete key is
unchanged. Hence the exact dependency token

```text
T = (child, rho_l, rho_u, b_l, b_u)
```

is the same `Dependency::Replay` on repetition. Ordinary replay checks
`dependency_keys` and does not queue that child again when T is already
present (context:4411-4478); `dependency` also interns the exact edge
(context:3570-3615). Likewise a repeated physical slot with the same
`(BoundKey,RelationId)` does not add a fiber (`attach:3702-3715`). This is a
non-reuse fact at exact *current* identities, not an entry-only cardinality
bound. Fresh rows can make new BoundKeys; fresh relation pair/Context/source/
scoped identities can make new fibers and Replay tokens. Equality
canonicalization transports old fibers to new keys and relations
(context:4649-4678), then merged-lower replay can supply further tokens.
Scheme restoration uses `incoming_use=true`, deliberately resets old heads
and may queue a child even when a dependency was already interned
(context:4431-4475; extrusion:970-1066). TOKEN263 is not asserted for that
separate owner. No completed relation or pair memo is treated as a global
bound across changed representatives/generations.

## MIX263: proposed accepted-prefix failure of a one-branch episode charge

Consider the reviewed R256/R257 accepted source route:

```yu
my outer x = {
  my k a b = b;
  my g p y = { y 0 0; p y; g p k; g x k };
  g
}
```

The high second-Apply path places `J_h` on `y` with an attached lower fiber
`beta_yh` sourced by `{e_h1,e_h2}`. The earlier low `Visit(y,+,1)` creates
`c_y` and its actual negative source link `u=(y,-,c_y)`, with fiber `ell_y`
sourced by `{e_l1,e_p}`. `e_l1` is the qualifying low self-call event; the
first `(y,+,J_h)` ordinary replay against u has **new/new** product
`(beta_yh,ell_y)`, with both old/new quadrants empty. It creates new child
`delta_h` at task `(J_h,c_y)`, identity Context, default Value scoped flow,
union sources `{e_h1,e_h2,e_l1,e_p}`, and the exact fresh
`Dependency::Replay` with both RelationIds and BoundKeys (R257 §§1-3;
context:4411-4497). The new upper BoundKey contains `c_y`, born inside this
drain; this token was absent from any entry inventory of *exact* keys.

On the first successful `(J_h,c_y)` dispatch the raw pair is new, the
representatives are unchanged, Context is unconsumed, and no retained
whole-pair rewrite applies. Its positive extrusion uses receiver `c_y`'s
current level 1 and deep-Visits four distinct signed Value rows. The four
Parents all qualify because the *union* includes `e_l1`; the qualifying
event arrived on the **opposite link**, while `J_h` arrived on the high
lower fiber. The processing sources and resulting source links are retained
at their exact owners (R257 §§2-3; extrusion:96-204; intrusion:305-355).
This defeats the proposed one-branch charge:

> Each qualified pre-settlement productive reset can be charged to one
> qualifying event on its newly supplied lower/structural branch, or to a
> distinct event credit spent once at the reset.

Here the event is on the other Replay antecedent, and a single source-set
membership qualifies multiple Parents without consumption. This is a finite
accepted prefix, not a same-token repetition or infinite recurrence. Keeping
both antecedents repairs the branch attribution, but the exact token then
contains newly born `c_y` and cannot be drawn from a fixed entry list of
exact raw keys. A finite source-event set, equal-level SCC condensation,
structural selector depth, or TOKEN263 alone therefore cannot pay the
number of novel qualified Replay tokens in an episode.

For never-activated groups, `QUAL262` gives only that a relation lineage
with no qualifying event stays unqualified until a new actual union/seed
adds one. It does not establish strict SCC advance: a general Apply callee
may lack the proposed owner-to-result edge, and cross-level semantic edges
are outside the SCC order. Their Parents remain retained, potentially
recapturable; `SETTLED262` does not lower them before activation. For
qualified groups, `SETTLED262` applies **after** an actual settled Parent and
excludes later births of the same canonical `r,L`; it does not limit the
pre-settlement token series. Both cases still require an entry-bound
branch-sensitive multiplicity proof.

The first remaining equation, owned jointly by the source constructor
`candidate_value_graph::retain_source`/`candidate_source::collect`, relation
producer `candidate_context_begin_replay` and consumer
`dispatch_live_item`/`candidate_extrude`, is: inject every *new successful*
Replay token leading to a fresh exact original pair and deep `Visit(r,p,L)`
before the episode cut into finitely many entry-funded credits, while
retaining both input RelationIds/BoundKeys, source-event branch origin,
Context/scoped payload, physical slot/fiber, canonical representative,
memo/rewrite and qualification. R257 shows that a credit indexed solely by
the qualifying event, the current equal-level SCC, receiver level, or an
entry-exact Replay token is invalid. No replacement injection is proved.
R251's existing injection from births to successful original full pairs
therefore remains unfunded, and R70 eventual Diagnostics does not follow.

## Checks, resources and stop

The draft records requested Sol/high and an observed model instruction
`gpt-6-sol`; observed effort, worker UUID and exact active duration remain
UNKNOWN. The historical stop receipt records the pre-source 36/36 hash gate,
no descendants, and no Git, source edits, scratch, tests, builds or probes.
It records only this note as written: the R263 inbox handoff was never written,
and no freeze check or handoff was completed. Its post-interruption inventory
was 12,660 bytes at SHA-256
`99ec81fd39aad2d04ecac66c1474ec51edb7e913c4daeb162f4b6a61c92bfaac`.

The primary interrupted the exact live worker after its STOP acknowledgement.
That historical cessation receipt and the later user-reported WSL restart
permit recovery; neither independently validates TOKEN263 or MIX263. This
provenance-only edit preserves the partial technical text for fresh review.
No new source audit, build, test, probe or proof check was performed during
this recovery. Independent technical review and any accepted handoff remain
with the primary. Parent/A/B remains OPEN with delta 0 to 0.
