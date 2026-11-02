# R251: finite birth depth, persistent pair funding, and the unfunded branching edge

Revision 1. Candidate static source-native derivation; independent review pending.
Sole author `/root/sol_r251_birth_charge`; no descendants or coauthors.
Contract: `tasks/agent-loop/sprints/ordinary-birth-charge-r251.md`, current
SHA-256 `30aea41a739866e73b6220754e05a8eb96388720046f87482714d530623cda23`.
Initial contract SHA-256
`67863d85e0d81d97ba5757a5125e0bfb57d2f991a157b0a12448a280f5cac29b`.
Baseline `bd613e50662677872a9fe6c522f80b782c45268c` matched by reading HEAD/ref
files, without a Git command. All initial 16 pins matched before citation.
Luna subsequently admitted only the additional Graph owner in the appendix;
its hash and revised contract matched before its body was read.

## Parent, scope and actual result

The original parent remains Yulang inference soundness and its Rust
implementation, with the accepted source domain, Simple-sub A/B, independent
satisfying-assignment quantifiers, shared witnesses, F1/FK1 and foreign
continuations unchanged. Immediate edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`
/ `R70-DRAIN-1`, specifically `R250-BIRTH-CHARGE-1`.

This packet uses the R250 successful forward initialized-session domain,
including finite successful prefixes with diagnostics. It does not assume
eventual drain return. R70's entry well-formedness W remains a separate
unproved all-source premise. The claims below describe the admitted production
SCC with successful helpers and valid referenced inventories; they do not
establish W or certify an arbitrary installed graph as source-reachable.

**Result:** finite source-event support, finite birth-level alphabet/depth,
and persistent funding by an exact productive Value pair are derived below.
They do **not** establish finite branching. The first missing equation is an
injection of newly productive complete pairs into unused credits fixed at
drain entry (§4). No repeated credit on an accepted source execution, infinite
cycle, production defect or need for global copy sharing is demonstrated.
The global birth bound is NOT ESTABLISHED; parent and Simple-sub A/B delta
remain **0→0**. This is source evidence and a precise obstruction, not a
kernel-checked or independently reviewed theorem. Lean declaration/type/axiom
audit: NOT APPLICABLE; checker NOT RUN under the no-Lean contract.

## 1. Current production SCC and finite carriers at their owners

The production entry is not a direct test call. `admit_collected_fact`
(`lib.rs:11546–11591`) admits the occurrence/provenance and translates its
same-kind endpoints before calling constrain. `admit_lambda_fact`
(`11620–11821`) constructs the four-port positive Function, admits its
Function-to-root occurrence and calls the same typed drain. The source schedule
actually selects Fact/Lambda/Link/ValueConstraint actions at
`candidate_source.rs:2428–2493`; Lambda planning retains the recipe at
`:2092–2111`. `constrain_live_item_with_inferred_entry` (`lib.rs:14096–14109`)
selects `run_candidate_typed_drain`, whose loop uses `step_typed_drain`.
These are constructor/callsite provenance, not a new example program or a
claim that every symbolic state below is attained by a particular source.

| Producer → consumer | Credit-relevant transition on current bytes |
| --- | --- |
| Transport/Context → Dispatch (`lib.rs:14447–14474`; context:4186–4312) | Canonicalize the admitted relation; execute context before memoization. First filter discharge can install/replay Allowance bounds. Discharged exact relations retain residuals; unrestricted contexts are not silently erased. |
| `dispatch_live_item` → `candidate_extrude` (`lib.rs:14565–14600,14814–14866`) | Canonical aliases requeue first. Existing exact-pair rewrites are reused. Otherwise nonrow lower→row uses Positive at receiver level; row→nonrow upper uses Negative at receiver level. Both calls have Value roots. |
| `candidate_extrude` → fresh row/Parent/link (extrusion:34–43,96–185) | New invocation-local maps; first deep `(kind-qualified row,p,L)` visit allocates at L, retains Parent, maps the key, writes the opposite-side source link and schedules the selected visit-time slots. Effect Positive also follows actual high-tail capture incidence. |
| Local work → copied bounds/rebuilt output/replay (extrusion:225–595) | Function flips Argument/ArgumentEffect and preserves ResultEffect/Result. Tuple/Record/Variant preserve their ordered payloads. Bounds and incoming cuts transport actual fibers. Rebuild output, retain group, then replay initialized incoming Allowances into the existing queue. |
| Successful changed output → retained whole pair (lib:14842–14866,15380–15398) | Record memo, actual rewrite relation, persistent `original ↦ rewritten`, and enqueue rewritten task. Original includes the receiver identity. |
| Ordinary insertion → opposite replay (extrusion:702–875,1070–1175) | Physical slots append, even if their keys already exist. Captured opposite count is finite at that call; ordered input BoundKeys select fiber products. |
| `candidate_context_begin_replay` → queue (context:4411–4497,4598–4647) | Snapshot actual fiber heads and old heads; enumerate new-lower×all-upper plus old-lower×new-upper. Child includes complete pair/context/source/scoped identity and ordered dependency. Exact old dependencies suppress ordinary repetition; new fibers can add children. Transfer is not execution/acknowledgement. |
| Empty queue → Parent settlement (lib:14411–14446; intrusion:568–710) | Only then process the pending suffix. Genuine merges append both bound sides, transport fibers, redirect copy representative, lower parent level by min, canonicalize all captured fibers, advance equality generation and replay merged lowers. |
| Merge replay → Transport/Context/Dispatch | New queue items re-enter the same route before Diagnostics. Root reopening alone is diagnostic admission; replay adds typed work. Relation/generation completion and exact-pair rewrite retention are different mechanisms. |

The complete birth-producing feedback is therefore dispatch/rewrite → local
extrusion/bound construction → retained rewritten/initialized-replay tasks →
ordinary bound products → dispatch, with the additional empty-queue Parent
merge/canonicalization/replay → dispatch edge. Structural children and effect
Support/member/tail expansion (`candidate_effect.rs:1606–1673`) feed that graph;
they do not allocate rows. The inspected SCC's row allocation sites are the
two fresh-row calls in extrusion. Source action/annotation/scheme constructors
outside this drain are not silently included in its row budget.

Actual finite components, without assuming eventual trace finiteness:

- At drain entry the physical rows/levels, term nodes, bound slots, views,
  incidence and source plan are finite stored vectors/maps. Entry finiteness
  does not say their later extensions have a common finite bound.
- Source events E0 are the actual `Graph.events` vector. Collection appends an
  Apply association and checking identity (`candidate_value_graph.rs:332–345`);
  `seal:355–394` constructs components, and `qualifies:395–397` only reads the
  event's origin/receiver components. Neither qualification nor Parent
  retention consumes an event. The SCC does not call collection or resealing.
  Source unions (context:3514–3538) sort/deduplicate existing event indices;
  rewrite/port/transport preserve them or replay takes their union. Thus source
  sets in this SCC range over subsets of the finite entry support, subject to
  separate authenticity of the original indices. At most 2^|E0| labels is a
  finite label bound, not a bound on relations or uses of a label.
- A single extrusion uses visit-time selected bound lengths, not immutable
  entry snapshots. Its new rows are anchors at L; each existing deep row is
  expanded at most once per sign. Source links on an old high row can enter
  its later opposite-sign snapshot. New capture records have low mapped
  tails; high-tail capture chains are not extended by this call. This reuses
  R70's mutable-discovery argument with the current owners above, preserving
  physical duplicates and exact raw transport keys. No uniform cross-call
  bound on those mutable slot/fiber counts follows.
- Replay `attach` (context:3702–3715) deduplicates `(BoundKey,RelationId)`;
  relation interning (:3481–3513) includes complete pair, ContextId, sources
  and scoped flow. Context interning (:2784–2810) uses exact ContextExpr.
  Finite source labels, or R250's finite fixed-support scoped transformers,
  therefore do not bound complete keys, contexts or fiber multiplicity.

## 2. Birth ancestry has finite depth, but needs a branching charge

Fix one drain's entry level alphabet J0, the set of all current Value/Effect
row levels, and assign every entry raw row the ghost label equal to its entry
level. Every later fresh row receives its actual allocation level as its label.
This is an analysis label, not production metadata or a change to the solver.

Within the inspected SCC, (i) an existing row's level only stays fixed or is
lowered by merge's min (intrusion:665–687); (ii) a fresh row's target is the
current Value receiver level at dispatch; and (iii) min selects an existing
level. Consequently all current/allocation levels stay in J0, and each raw
row's current level is at most its ghost label. At every actual fresh Parent:

```text
current_level(parent) = h > L = label(copy)
label(parent) >= h
therefore label(copy) < label(parent), with both labels in J0.
```

This remains true if the canonical parent represents an earlier copy or
earlier merge: use the actual representative read by this Visit and its own
label, rather than relabeling an entire equality class. The retained raw Parent
history is not replaced by the representative forest. There is one actual
Parent per newly allocated row, while later recapture reuses its group.
Thus a raw birth lineage has at most `|J0|-1` birth edges. Both polarities and
both row kinds obey the strict inequality; negative variance does not change L.

This improves a numerical depth bound to an actual finite entry alphabet.
It does not make out-degree finite over an unbounded continuation. During
one call a raw parent has at most one child per sign at this fixed L; the maps
are recreated at the next call. Many finite local bounds do not give a common
bound on the number of such calls, receivers or siblings.

The actual raw-row equation at the first deep Visit is still:

```text
rows' = rows ++ [copy]                 label(copy)=L<label(parent)
ParentHistory' = ParentHistory ++ [Parent(copy,parent,p,L,S,comparison,occ)]
source events' = source events         source labels retained, not spent
local map'[(parent,p,L)] = copy         no such map persists into the next call
```

The source-link append mutates bounds, not the parent's birth label or any
global sibling budget. The finite-depth proof supplies no missing subtraction
in a source-indexed branching account.

## 3. Exact productive pairs fund at most one successful birth invocation

Call an invocation productive when its returned root differs from its supplied
root, and consider only successful production calls/dispatch boundaries, with
no failed-route continuation. On these bytes every birth-producing invocation
is productive, under R70's valid structural-entry premises:

1. Before the first deep row visit no selected Bound/IncomingAllowance work
   has been generated, since only the deep row arm generates that work. The
   first deep row is therefore reached through the root's structural child
   traversal. An anchored row would stop traversal and allocate nothing.
2. That structural child maps to a fresh same-kind ordinal. No merge runs in
   local extrusion, and the map retains this image through reconstruction.
3. Exact child handles occur in TermNode equality (`term.rs:230–256`), and
   `live_variable:1205–1216` includes kind, sign and ordinal. Function and
   Tuple/Record/Variant reconstruction preserve all ordered positions and
   replace the changed child; exact interning (`1166–1203,1295–1383`) cannot
   return the old node with a different child. Repeating along the structural
   path gives a changed Value root. Later births in selected bound discovery
   cannot undo that first fresh root-path image. Changed effect-view bounds
   do not require inventing a supported term reification: the claim concerns
   successful calls through the actual partial reifier (extrusion:597–633).

For that complete original canonical Value pair k, dispatch retains the
actual changed pair before its next successful return. On any later dispatch
of that same exact k, either `pair_is_current` suppresses processing, a
canonical alias requeues another key, or the retained rewrite branch precedes
both calls to extrusion. Memo replacement does **not** clear the stored
rewrite: `record_typed_pair_admission` (`lib.rs:15460–15478`) changes only
witness/completion fields of an existing Value memo. Its supplied `None` in
the reuse branch is not an assignment to retained_extrusion_rewrite.

Therefore each exact k has at most one successful birth-producing invocation.
This holds across new source relations and equality generations. Recapture
(`intrusion:386–420`) records source/group reuse and can activate old Parents;
it allocates no row and does not rerun extrusion. An initially unqualified
group activates at most once; group activation is not a new birth.

Application to the attempted charge: there is **no justified extra factor of
the number of equality generations** for birth-producing invocations of a
fixed pair. New generations do permit fresh relation completion/bound work;
they do not erase this exact-pair rewrite. Canonicalization after a merge can
produce a different full pair k', which needs its own funding. This result
does not identify k and k', or identify two different fresh receivers.

For each finite successful prefix ending at a dispatch boundary, let C_t be
the number of its distinct productive full original pairs, P0 the physical
row count at entry, and B_t its fresh rows. Before a productive call i, at
most `2*H_i <= 2*P_(i-1)` rows are born by R70's two-sign local bound; calls
with unchanged output have no births. No other SCC producer allocates rows.
Hence the finite-prefix accounting is:

```text
P_i <= 3*P_(i-1)
B_t <= P0*(3^C_t - 1).
```

This is a finite-prefix inequality, not an assumption that eventual C is
finite, and not the requested entry-only birth bound. An intermediate prefix
inside local construction still has that call's local R70 bound; the displayed
C_t counts completed dispatches. Mutable visit-time slot counts affect work
and replay products, but cannot allocate more than two copies per entry row
in that one call. They do affect which *later* productive keys are reached.

## 4. Frozen first failed credit-preservation equation

Method A gave a finite-depth branching tree (§2). Method B changed input to
the actual persistent pair rewrite (§3), removing generation-based duplicate
births for a fixed pair. Both leave one exact premise: fund new productive
full pairs, including fresh receivers and rebuilt structural identities.
No third renamed global-termination conditional is claimed.

Let U0 be a proposed finite set of source-indexed credits derived solely from
the actual drain-entry storage, not from the eventual pair/relation/fiber set.
Let Used be an injectively charged subset for productive original pairs
already completed. At the next productive dispatch of a new full pair k,
conservation requires:

```text
NEWPAIR251:
  choose credit(k) in U0 \ Used
  Used' = Used union {credit(k)}
  |U0 \ Used'| = |U0 \ Used| - 1.
```

No construction of `credit(k)` with that non-membership property has been
derived. Source event/polarity/target labels are finite, but neither
`qualifies` nor rewrite/transport/replay decrements their multiplicity.
Adding exact receiver/structural/copied-row identity to the label does match
the memo owner, but its carrier can grow at extrusion/reconstruction and
canonicalization. Adding invocation occurrence or RelationId is also not an
entry-only finite carrier. Dropping those identities to recover an entry
carrier loses the injectivity premise; it is **unproved**, not demonstrated
false by an accepted repeated-credit trace.

The owning constructor provenance is concrete:

```text
source Fact/Lambda action -> admitted occurrence/Function-to-root
 -> actual typed frame relation, Transport and Context
 -> canonical nonrow/ValueRow dispatch guard, target=current receiver level
 -> fresh deep-row constructor + retained Parent/opposite source link
 -> visit-time bound copies + exact structural reconstruction
 -> retained full pair rewrite and queue child / initialized-cut replay
 -> ordinary physical bound/fiber admission and ordered replay product
 -> another actual complete pair; or empty-queue merge/canonicalization/replay.
```

At the local birth transition, the source set S/comparison comes from the
same active processing relation (`context:3535–3538`, `intrusion:323–343`);
it is not fabricated by endpoint equality. At replay, sources are actual
unioned input labels and each lower/upper dependency remains distinct. The
new-key consumer applies the whole-pair memo check, not a source-label check.
These are production constructors and their guards from the accepted route,
not cfg(test) row installation. They show exactly where NEWPAIR251 must be
proved and where fresh identity can enter. They do **not** prove that an
arbitrary high-root/fresh-receiver configuration, a repeated credit or an
infinite sequence is source-reachable. No particular source program witnessing
repeated productive keys is supplied; no source-qualified counterexample is
claimed. The obstruction is absence of the required source construction law.

## 5. Application to R250 and remaining owners

R250's representative identity applies to every finite successful prefix:
`R_t = R0 + B_t - M_t`, where M_t counts genuine merges. Thus
`M_t <= max(0,R0+B_t-1)` (the combined-kind bound is deliberately coarse).
Each genuine merge advances equality generation once; repeated same-rep
pending entries do not. Applying §3 gives the prefix bound
`M_t <= max(0,R0+P0*(3^C_t-1)-1)`. This removes an unnecessary independent
generation factor from birth funding, but leaves C_t without an entry-only
bound. Consequently no global generation bound or eventual Diagnostics
entry follows. The finite local SETTLE250/SUFFIX250 results remain applicable
only at their actual phase entries; SCOPE250 still bounds one component.

Qualification is covered as a choice of pending scheduling, not a decrease:
qualified Parents enter pending at birth; unqualified Parents remain retained
and can later be activated by exact-group recapture. Settlement happens only
after queue emptiness. It cannot be bundled atomically with a birth to pay
for progress before that emptiness is proved. Merges lower levels and may
change canonical pair keys, transport fresh fibers and invalidate relation
completion. Existing pair rewrites persist throughout those changes. Neither
activation nor generation is an independent credit for new pairs.

Before/after parent edge: R250 lacked a global birth charge. After R251 that
charge still lacks NEWPAIR251; finite-depth and once-per-exact-pair facts
exclude two unjustified funding shortcuts and localize the needed branching
law to full-pair construction. Original semantic parent delta remains zero.
Full context/relation/fiber closure and diagnostic reference/report validity
remain separate even if NEWPAIR251 were later proved.

Reused only within premises: R70 reviewed conditional mutable-worklist result
(author `/root/r70_ordinary_extrusion_proof`, complementary contribution
`/root/r70_extrusion_countertrace`, closeout by Luna); R250 current SCC,
SETTLE250/SUFFIX250/SCOPE250 (author `/root/sol_r250_drain_progress`, reviewed
status supplied by this contract). Old pins/line numbers establish no current
source claim. No unread historical proof or R249 body is imported.

Retain separately: R70 entry W; R71 raw-slot/canonical-fiber coverage;
ordinary antecedent/seed/FreshUse/origin authenticity; report/reference
validity; F1/FK1; foreign continuations; full source/evaluator soundness;
hygiene, qualifying-intrusion adequacy and generalization. No provider,
residual or witness lineage is quotiented away. No resource/identity limit,
eventual-universe finiteness or withdrawn bypass is used.

Mutual TODO `R251-NEWPAIR-CREDIT-1`, owner Luna: establish NEWPAIR251 using
actual source-to-pair construction, or exhibit a particular accepted source
path repeating a proposed credit without its claimed resource decrease.
Required inputs are the exact dispatch/rewrite, extrusion/Parent, ordinary
bound/replay and merge/canonicalization owners above, plus an admitted finite
entry credit definition. Proposed output is one entry-indexed injection or
a source-qualified finite countertrace to that injection. Its falsifier is
two actual productive full-pair admissions assigned the same credit after
fresh receiver/canonical representative change; a synthetic row cycle, source
label equality alone or increasing ContextExpr syntax is insufficient.
New owners/leases/semantics require Luna admission before further work.

Mutual TODO `R251-REVIEW-1`, owner Luna: fresh compiler_referee review of the
frozen exact bytes, especially first-birth-to-root-change and rewrite retention
across generation changes. The producer cannot certify them independently.
Implementation **NO_SAFE_CODE_SLICE**: actual dispatch/extrusion and
Parent/merge/replay owners show no concrete accepted-source violation of an
approved clause. No production observation/repair is authorized or written.
Next useful step belongs to Luna intake/review and the concrete source-credit
law; this writer does not continue past freeze.

## Freeze and resources

Three substantive stages: fixed-source/SCC/carrier audit; two credit methods
and parent application; freeze and static validation. Checks are read-only
baseline observation, SHA-256 comparisons, bounded source reads/searches and
output whitespace/path checks. No build, test, Lean, probe, Cargo, benchmark,
Git, external contact, nested CLI, production/config/shared-state edit,
scratch/cache/generated file or quarantined/runtime path access. Only the
two leased outputs are new. Descendants and unresolved descendant leases NONE.

Requested `gpt-6.1-sol/high`; observed model/effort UNKNOWN. Worker
`/root/sol_r251_birth_charge`, session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`;
parent assignment/admission messages and active receipts are launch/work
evidence, not effective model metadata. Hard cap 2400 active seconds / three
stages, no expansion. First explicit clock 2026-11-02 04:54:20 UTC; final clock
and hashes are external to this file. Exact pre-clock/provider active time,
CPU/RSS UNKNOWN; conservatively retain the full 2400-second reservation as
charged, with no refund/carryover. Independent review reserve belongs to Luna.

The appendix records all direct pins. Artifact SHA is in the handoff; handoff
SHA is returned externally to avoid recursive hashing. Freeze ID
`R251-BIRTH-CHARGE`, revision 1. After final read-only verification:
**STOPPED / WRITES_STOPPED**, review/adjudication/integration pending.

## Direct dependency SHA-256 manifest

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
87e9af00bfc206fb22a29b776c634acc94e75e0283257f8bba9d513d23a90574  notes/theory/2026-11-02-ordinary-drain-progress-r250.md
8b52e40891096ca6086db636165b276a3f57630091e090e3e181f390cd178c65  tasks/agent-loop/inbox/ordinary-drain-progress-r250.md
```
