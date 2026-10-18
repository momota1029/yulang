# R73 owner map: helper Local suffix and consumer join

Date: 2026-10-19. Sprint `helper-suffix-history-20261019-r73`, revision 2.
Contract SHA-256 `25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f`; baseline `69ecc0dc3c796f9ddbc4c7d815b1816dd97c5ccd`.
Author `/root`, Luna/high. Static source/native correspondence only. This is a
frozen **partial** map: it does not claim a complete cut-state or A/B/C.

## Fixed source and inherited prefix

The source, ordinary-mode restriction, parent quantifiers and outcome contract
are exactly those in R73 contract §Original parent and fixed outcome. R72's
conditionally reviewed prefix supplies the first qualified helper extrusion:
`Y+`, `n_y+`, `C_h−`, `U_h−` at target 2; selected production copy
`(Y,+,Int+)`; and settlement redirects each copy to its original parent. At
the helper Local boundary, `Y`, `n_y`, `U_h`, and helper return effect `RE_h`
are at level 2, while the original helper computation entry `t_y` remains at
level 3. The exact initial third-owner slot is
`K_t=(t_y,−,n_y)` in `EffectUpperRow[0]`. Its raw item still represents `n_y`
at this prefix; the aliasing self-class extrusion link is owned by the merged
class. Nothing here transfers R53's callable-provider group.

This inherited endpoint table does **not** determine the next Local capture,
which bound relations it contains, or the live restoration endpoint indices.
Those require the complete cut-state ledger below. The numeric row IDs and
RelationIds are not available from static source declarations and remain
symbolic unless a frozen producer derivation supplies them.

One constructor detail sharpens the capture boundary: helper Lambda's positive
Function uses its registered `formal_domains[y]` (the annotated `Int−` term)
for the Argument port, while `Y` still determines the fresh return-effect
level (2) and remains in the helper call demand. Therefore the positive helper
Function does not reach `Y−` through its Argument child. Its structural capture
candidate is the helper root `H`; row `t_y` is reached through the argument
effect port; `n_y` is reached as the retained raw item of `K_t`; `U_h` and
`RE_h` are shared level-2 rows; the annotation value is the `Int` atom. This is
a constructor reachability description, not yet the full captured graph: each
relation/evidence fiber, any additional native structure, and exact owner IDs
still need the complete ledger.

## Source occurrence to native owners

| Fixed source occurrence | Source action owner | Candidate/native owner | Distinction required in the trace |
| --- | --- | --- | --- |
| `helper x` inside `loop` | `candidate_source.rs` Local action for installed helper, then FormalNameEffect for `x`, then Apply | `candidate_scheme.rs::route_candidate_local_run`, `capture_candidate_graph_owned`, `prepare_candidate_fresh_use`, `step_candidate_local_use`; `shadow_apply.rs` Apply admission | Local graph restoration emits FreshUse admissions. The later value comparison may invoke `candidate_extrude`; FreshUse itself is not `Work::Bound`. |
| helper Local bound restoration | Captured graph bound, preserving `source_bound`, relation and evidence snapshot | `candidate_scheme.rs::begin_candidate_fresh_bound`; `candidate_extrusion.rs::candidate_begin_bound_restoration` and `candidate_step_bound_restoration_child`; `candidate_effect.rs` bound insertion | Ordinary FreshUse admits the bound through `candidate_context_bound`; the separate `begin_candidate_fresh_bound` path maps and attaches its FreshUse relation transport. Keep these relation/evidence lineage edges separate. Restoration snapshots the initial opposite-side count, then re-reads the canonical owner and indexed opposite endpoint before every replay child. Earlier children can mutate representatives or append adjacency. |
| final helper Apply and its queued descendants | Apply slot and formal-Name effect constraints | `shadow_apply.rs` Apply comparison; `lib.rs::step_typed_drain`, `dispatch_live_item`, and `candidate_step_function_dispatch` | Track FIFO typed items, active drain stage/current item, relation, function child cursor/pending item, replay acknowledgements, diagnostics and memo generations. |
| loop Lambda | Loop's original Lambda constructor, after both body calls | `lib.rs::admit_lambda_fact`; `candidate_context` replay and normal typed drain | This replays the newly admitted Function against each retained earlier demand. Record each raw/canonical pair and its own RelationId; endpoint pair identity alone does not establish current evidence. |
| post-merge comparison recapture | Existing value-pair memo rewrite | `lib.rs::dispatch_live_item` and `recapture_candidate_extrusion` | A canonicalized/reopened pair can recapture the extrusion rewrite. Inventory the memo key, stored rewrite, relation/generation currentness, by-output groups, and exact triggering item before treating it as a new operation. |
| loop Local boundary 1 and outer Lambda | Published loop Name after installation; enclosing outer return | `candidate_scheme.rs` Local route, then `lib.rs::admit_lambda_fact` | Only after loop Lambda replay and memo work are drained can this yield the later production comparison. Track all selected physical slots at that occurrence. |
| independently justified consumer | Source-level consumer/provider occurrence demanded by the preservation question | `candidate_context.rs` relation-local `post_check_context`; source/call occurrence and provider evidence | Candidate Apply metadata or a transported fiber alone is not the consumer proof. Join the exact required residual/discharge to an authentic source occurrence and provider lineage. |

Ordinary mode excludes the scoped Local-callee authentication and scoped
consumer branches. The R50 path stays NOT_ADOPTED. Candidate mechanics remain
conditional research evidence and are not a source-language typing derivation.

## Frozen producer's two local cut boundaries

The frozen Astra proof (`notes/theory/2026-10-19-r73-helper-suffix-history.md`,
SHA-256 `38b46fa0ea2183ab5ebedb727979a8c343e1bdd0820c4941f22df4e503fda03d`)
distinguishes C0, before Local capture, from C1, after graph capture and FreshUse
preparation but before the first Local step. Both remain conditional on reaching
the successful constructors. Its C1 cursor is exactly
`(next_bound=0, restoration=None, complete=false)`. This identifies an empty
Local cursor only; it does not certify an idle/empty historical memo or a
complete zero-sized bound list.

For C0, the producer names `B` as the helper body's application effect, `R` as
helper Lambda return effect, `H` as helper root and `M` as final helper-callee
Name row. The provider is `Fh+ = Function+(Int−,t−,R+,U+)` and the retained
helper demand is `Function−(Y+,n+,C−,U−)`. The Lambda emits `B≤R`; prior Apply
slots emitted callee-effect≤B and `C≤B`. The first group lowers `Y,n,C,U` to
2, leaves `t` at 3, and `R` is allocated at 2. Thus shared `R/B/C` physical
adjacency is a required part of the pre-Local ledger, beyond endpoint levels.

The producer's C1 row classifies `H,t` as structural local-row candidates,
`U,R,n` as shared, and the annotation Argument as `Int−`. It confirms the
physical raw slot `EffectUpperRow(t)[0]=n`, but reports exact physical
multiplicity, `bound_cursor`/`bound_entry` fibers, evidence snapshots, exact
relation IDs, H's bound multiplicity, and preexisting memo/group/replay state
as **unknown**, not empty. `Capture::bound` emits one graph-bound record for
each attached relation or a single None record if absent; payload/demand capture
can grow the graph afterward. Consequently the hypothesized two-row/two-bound
projection is explicitly not an established cut. A full current/queued work,
physical slot, relation/fiber, representative/level, memo, restoration and
pending replay ledger is still missing. I preserve the producer's unknowns as
unknowns rather than completing them by endpoint projection.

## Required complete cut-state ledger

Before suffix claims, freeze one simultaneous ledger at helper Local entry and
one at the first Local-restoration boundary. The ledger must enumerate:

1. Current source action and all remaining/queued source actions.
2. Every typed work item in FIFO order, plus every active drain's initial and
   current task, stage, relation/processing value, function dispatch children,
   `next`, `pending`, replay acknowledgements, and destination.
3. All relevant physical value/effect bound lanes, owner and side, slot index,
   raw item, representative item, attached RelationIds, source `BoundKey`, and
   evidence/origin fiber including a legitimate empty fiber or association gap.
4. Representatives, levels and non-generic flags for every row in those bounds
   and Function child endpoints; all Parent/merge parent-copy pairs in order.
5. Every retained capture bound and its exact raw `source_bound`, relation,
   evidence snapshot, graph endpoints, FreshUse row/effect remaps, and capture
   boundary/locality decision.
6. Every restoration record: saved `opposite_count`, next index, current live
   canonical owner/bound, active replay ID, child lower/upper keys, child
   RelationId/dependencies, completion receipt, and cursor advancement.
7. Every typed-pair memo entry that can match a queued/current item, including
   original key, retained extrusion rewrite, diagnostic completion, relation
   and generation currentness. Recapture groups must be keyed by the exact
   `(memo key, rewritten endpoint)` output identity.

The helper positive Function's `Argument` port is the registered annotation
domain, not the original parameter row. This matters when joining a proposed
provider/call consumer: the annotation endpoint, `Y`, the invocation's `C_h`,
and the later consumer's Function port cannot be identified by shape alone.

The exact reuse join is `by_output[(TypedPairKey, ExtrusionEndpoint)]`, as
declared at `candidate_intrusion.rs:19` and read by
`recapture_candidate_extrusion` (`:388–400`). It does **not** key by comparison
`RelationId`. For a retained rewritten pair, recapture checks the original
typed-pair key against each actual reused output endpoint; for each matching
group/source-set pair it records a distinct reuse occurrence and can activate
the group's parents if the new source set qualifies. RelationId and generation
remain separate inputs to `pair_is_current` and context completion; do not use
them as `by_output` index coordinates. Two different contextual relations of
the same typed pair and output can therefore reach the same indexed group
lookup, while relation-local currentness still governs execution. An
endpoint/RelationId projection is not enough to reconstruct those recaptures.

HashMap iteration order is not a work order. Where the scheduler's order comes
from a vector, saved index, queue, or source action cursor, preserve that owner
order; otherwise report a set rather than inventing a sequence. The bounded
R72 endpoint/level table alone is not a complete cut-state. The complete
symbolic ledger was not reconstructed within the bounded owner lane; frozen
producer records and fresh review receipts remain the only later inputs.

## Consumer and implementation boundary

`candidate_context.rs` keeps `post_check_context` relation-local. A correct A
trace must identify the exact relation(s), selected raw physical slot(s),
canonicalized child relation, all same-class slots, and the authentic source
consumer/provider for the particular residual or discharge. It cannot substitute
endpoint equality, ancestry, a call record, or an origin tag for that join.

Static inspection adds a useful conditional restriction for this exact ordinary
source: `candidate_closed_allowance` recognizes a filter only when an Effect
pair's upper endpoint is an `Allowance` with a closed weight. A concrete
`[io] int` formal-entry registration emits no upper cap (`candidate_effect.rs`:
the formal-entry annotation path); value and ordinary effect sources therefore
start with `IDENTITY`. Function-port, ordinary-bound, extrusion, FreshUse and
replay transports preserve that identity context, and `candidate_context_execute`
returns before filter discharge for an identity relation. This means a
residual/discharge mismatch cannot, under the fixed-source successful-prefix
and no-external-input premises, distinguish the raw and canonical fibers here.
It does **not** settle whether the candidate's exact relation/provider lineage
is the independently required source consumer, nor does it establish complete
suffix or scheduled-occurrence coverage. This is not C and does not remove the
consumer/provider join from outcome A if some independently justified
obligation remains.

The frozen Sol counter-reading supplies a constructor-closure argument for that
restriction, conditional on the exact ordinary source route: only a comparison
whose upper Effect endpoint is a closed `Allowance` introduces a context
wrapper (`candidate_context.rs::candidate_context_source`). Root `[io] int`
maps to the Int leaf pair; the concrete formal-entry row emits no cap. No
handler, effect operation Name/Apply, annotation ascription or external graph
exists in the fixed source. Seed, Function-port, bound, replay, FreshUse,
equality/extrusion and memo-recapture constructors therefore preserve
`IDENTITY`; execution exits before discharge/residual mutation. Exact transport
and replay witnesses still differ even when their contexts are identity. This
cannot establish source/runtime correspondence or erase raw/canonical fiber,
source-set, provider and RelationId distinctions.

There is also a useful counterexample guard for the tempting local absence
claim: **if** C1 had exactly H and t as local rows, H's positive Function and
t's upper n bound as captured families, all captured fibers, no extra payload,
and the four Function ports at level 2, the new H'/t' owners would have no
opposite bounds at restoration entry. Those local restorations would have zero
opposite products, and the rebuilt root comparison would create no Parent or
production `Work::Bound`. These are explicit added completeness premises, not
facts established for the fixed source. `Capture::bound` is fiber-multiplicative;
the exact count/order of graph bounds and context payload closure is missing.
So this conditional discriminator rejects a shortcut to C, while leaving the
full suffix OPEN.

No proof-independent safe code slice has been established. The remaining
question is whether this fixed source admits the complete scheduled history and
required consumer, not whether an assumed alias schedule can be implemented.
No code, tests, builds, probes, parser/solver execution, measurements,
instrumentation, expected-output edits or semantic changes were performed.

Current result: **UNFINISHED/OPEN; neither A/B/C established**. The fixed
complete C1 cut-state remains unavailable: exact graph-bound order/count,
relation and evidence fibers, physical multiplicities, all live slot aliases,
prior memo rewrites and by-output groups, source sets/generations, pending
parents and replay heads/cursors are not fully reconstructed. The complete
suffix through both loop Lambda demand replays and boundary-1 Local remains
untraced. The Sol identity-context result removes only the residual/discharge
mismatch route under its source/successful-prefix assumptions; exact provider,
RelationId, dependency and witness lineage remain open. No safe code slice is
established. Parent, Simple-sub A/B and R70/R71 remain OPEN; R50 NOT_ADOPTED.

Review correction: the first frozen Luna-map SHA
`79d062879fc33f066d154179563eb5e34b0f155c20811f59ca212fe55dc65480` misstated
the `by_output` key as `(comparison RelationId, output endpoint)`. Fresh
compiler review identified the defect and the existing same-pair/different-
context recapture case. This corrected frozen note now uses the actual
`(TypedPairKey, output endpoint)` key and separates source qualification from
relation/generation currentness. The compiler review's targeted delta re-review
of this correction is pending; the original major finding remains in the
review receipt. The source-map outcome stays UNFINISHED/OPEN.

Owner cessation receipt: this source-map work began in the R73 activation
session, but no separate Luna launch timestamp was recorded. At 2026-10-18
23:02:31 UTC the original 500s owner-map allocation had elapsed or may have
elapsed; exact elapsed and overrun are UNKNOWN. I stop derivation here, claim no
extension or carryover, and leave the frozen gap as `R73-CUT-LEDGER-1` for a
separately authorized successor. The current 300s integration allocation is
reserved for intake, review adjudication and this checkpoint only; it does not
extend the 500s source-map lane. Fresh independent compiler/spec review and
final Luna adjudication remain pending.
