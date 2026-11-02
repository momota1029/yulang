# R244: constructor-derived ordinary-extrusion entry frontier

Status: **candidate source argument; R70-ENTRY-WF-1 OPEN**. Revision 1.
Author: `/root/sol_r244_entry_wf`; no contributing descendants.
Contract: `ordinary-extrusion-entry-construction-r244`, admitted frozen bytes,
SHA-256 `07815becba7a8f9e0584bdb289a49f3f81907c7b1d3394eb3dc35fca3aa6f3ec`.

## Parent and result

The unchanged parent is the full Yulang inference/evaluator goal, with the
original accepted source domain, shared witnesses and independent quantifiers,
including Simple-sub A/B. Its scope is inherited from R70 §1 and the R244
contract, not redefined by this note. No fully quantified full-inference Lean
declaration is supplied in the frozen dependencies; this packet invents none.
F1/FK1, foreign continuations, source/evaluator soundness, generalization,
principality and ordinary inference remain distinct obligations. Parent delta:
**zero**. No semantic or production gate closes.

The immediate edge is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`. The reviewed
historical claim has the informal type

```text
forall actual successful R70 production invocations (sigma, root, p, L),
  CallerEnvelope70(sigma, root, p, L) -> W70(sigma, root, p, L) ->
  SuccessfulCheckedHelpers70 -> EntryToReturn70(sigma, root, p, L).
```

This is a description of the frozen source argument, not a new Lean theorem.
There is no Lean declaration or axiom audit for R244; checker execution is
neither assigned nor authorized. The result here is an exact constructor
frontier and several source-derived preservation implications. It does **not**
derive the conjunction W for every current invocation.

The first missing constructor equation is in initialization, before graph
installation. `try_new_candidate` calls `try_new`, which calls
`initialize_candidate_source_levels`. After checking each formal's recipe
identity and absence of an earlier native root, the latter calls
`InferenceSession::candidate_endpoint(Parameter(recipe_position), Positive)`
at `candidate_source.rs:2316`. Its implementation is absent from the complete
eleven-file pinned Rust read domain. The exact required equation is:

```text
Given completed row initialization, p < parameter_recipes.len(),
and q = parameter_live_base + p,
candidate_endpoint(Parameter(p), Positive) = Ok(t)
  => t is visible in this branch, denotes a Value-positive endpoint,
     and value_endpoint(t, Positive) = canonical_value(ValueRow(q));
     q remains an allocated Value row and no previously valid row/term
     reference is invalidated by constructing t.
```

This is a missing constructor-to-native correspondence premise, not an assumed
interface and not a malformed-state counterexample. The owning symbol is
`InferenceSession::candidate_endpoint`; the exact defining file must be located
and hash-pinned by Luna in a successor packet. The inputs' validity does not
prove the output equation. The source read domain cannot be enlarged by this
leaf. Luna acknowledged this stop frontier before freezing.

## Actual construction order and derivations

Use `AllocatedV(i)` for `i < bounds.len()` and `AllocatedE(i)` for
`i < effect_bounds.len()`. These predicates do not assume W. Each implication
below is a source argument about the named constructor, with its premises
shown. It is not a complete induction over all source histories.

1. **Empty session, then dense collected rows.** In `lib.rs:10141–10148`, the
   live row/level/metadata vectors start empty. The component loop at
   `10410–10449` increments the counter of exactly the component's kind,
   appends an empty bound row and its level/metadata, and stores that kind and
   ordinal in `live_components`. Thus after each successful iteration the
   three Value lengths agree and the three Effect lengths agree. The stored
   endpoint is in range in its actual kind. Induction over the parameter loop
   `10451–10465` adds exactly `parameter_recipes.len()` Value rows, so
   `parameter_live_base + p` is allocated for every recipe position p. Checked
   counter increments precede publication. This establishes actual row
   allocation, not an arbitrary valid-row hypothesis.

2. **Level installation, then the first missing native constructor.**
   `initialize_candidate_source_levels:2292–2302` changes levels without
   changing lengths or row kinds. Its map keys require the prior collection
   index invariant. The pinned collection producers tie component levels to
   frozen `positions[index]` (`candidate_source.rs:1221–1227`) and parameter
   levels to positions obtained from the parameter map (`1280–1284`). A full
   HIR/collection index induction is not certified here. For each *completed*
   installation those writes preserve alignment. More locally, the formal
   loop `2303–2328` explicitly checks that `recipe_position` selects the
   registered parameter before calling `candidate_endpoint`. Hence its input
   row is allocated by item 1. No pinned definition supplies the displayed
   output equation. This is the first constructor frontier selected by the
   packet's stop condition; there is no claim that an invalid result is
   emitted or that it necessarily reaches an extrusion call.

3. **Successful graph installation is later.** Only after `try_new` returns
   does `try_new_candidate` install the graph (`lib.rs:10501–10505`).
   `start_candidate_graph` (`candidate_scheme.rs:2528–2552`) begins with
   `GraphState::default`, initializes effect-algebra identity, sets scoped
   mode and its inventory, and finally assigns `Some(state)`. This supplies
   an initial empty inventory for graph-owned records, conditional on success
   of the preceding native construction. Graph presence alone supplies no
   theorem about rows or terms accumulated later.

4. **Fresh row preservation is derived.** For either kind,
   `fresh_*_at_level` (`lib.rs:10521–10582`) computes the ordinal from that
   kind's current bound-vector length, reserves all lanes, and appends one
   empty row, requested level, Fresh metadata and extrusion mark. Starting
   from aligned lanes it returns an allocated row of that kind and preserves
   alignment. Failed reservations precede these pushes. This implication
   applies to source annotation/operation allocations, lambda effect rows,
   FreshUse row images and extrusion copies whenever their actual callers
   select these constructors. It proves neither validity of a supplied old
   row nor all-path validity of the caller's recipe indices.

5. **Forest preservation has a smaller independent induction.** The empty
   forests implement identity for unmaterialized rows: `representative`
   (`candidate_intrusion.rs:120–128`) returns the input when there is no stored
   entry. This must not be mistaken for validating an unallocated row.
   `retain_extrusion_parent:305–366` extends forests with singleton entries up
   to current row lengths. Under allocated parent/copy inputs, the returned
   representative stays allocated and kind separated. `merge_candidate_rows`
   (`599–733`) canonicalizes both same-kind inputs and returns if equal;
   otherwise its forest write connects two distinct roots. This cannot form
   a cycle: a path from the destination root to the source root would make
   their representatives equal. Compression (`507–566`) replaces a path by
   its own root and preserves that property. Reverse journal restoration and
   truncation (`195–223`) restore the earlier forest when the saved journal
   describes that actual earlier state. Thus the forest *shape* implication
   is derived; validity of every input row/history is still conditional.

6. **Term constructors separate visibility/sign from row allocation.**
   `term.rs:1205–1216` interns exactly the supplied kind, sign and ordinal for
   a live variable; it does not check `AllocatedV/E`. The Function
   constructors (`1230–1269`) look up all four children and require the
   Value/Effect/Effect/Value signs `(-,-,+,+)` for Positive and `(+,+,-,-)`
   for Negative (`1390–1404`). Therefore successful construction derives
   immediate child visibility/kind/sign. If the preexisting child DAG and
   component/live-row interpretation are valid, a new node whose children
   already exist preserves finite acyclicity; interning an existing node
   adds no edge. Branch lookup checks brand and page visibility (`831–855`).
   This proves no ordinal allocation from `live_variable` and cannot replace
   the missing translation equation. `component_endpoint` (`lib.rs:11830`)
   also requires the collection term-to-position association. The component
   constructors (`2075–2114`) append the component/term and its position
   together, providing the local association implication.

7. **FreshUse is downstream of those obligations.** In
   `prepare_candidate_fresh_use` (`candidate_scheme.rs:4581–4603`) each captured
   row is canonicalized. An already mapped representative reuses its image;
   a qualifying local row uses the appropriate fresh constructor; otherwise
   it reuses the old row. Thus, given valid captured rows and forests, every
   image is allocated and same kind. `4761–4782` reconstructs row/Function
   nodes from that image and completed children, so item 6 applies. The old
   graph row/node/child indices and its capture ownership remain named prior
   invariants; unchecked indexing is not their proof.

8. **Bounds retain their actual lane.**
   `candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:702–876`)
   canonicalizes owner/item, checks owner range and kind agreement, selects a
   lane by sign and row/nonrow form, and appends to that lane. Given a valid
   item of its selected sign this preserves bound validity. Its owner check
   does not prove item-row range, Function visibility, or atom polarity.
   Merge copies both actual sides before writing the forest link and then
   transports canonical-key evidence (`candidate_intrusion.rs:638–697`).
   Under the input invariant these operations preserve the same allocation
   and lane facts. Raw source-slot/canonical-fiber *coverage* is not used.

9. **Views and capture chains have explicit local preservation premises.**
   `candidate_signature_view` (`candidate_effect.rs:1219–1286`) returns its
   appended index; the supplied tail still needs `AllocatedE` and allowed
   members/payloads need their source-construction invariant.
   `candidate_copy_effect_view:1523–1547` checks old index and payload view,
   copies allowed members/provenance and uses the supplied tail. Therefore
   it preserves member ordinals, conditional on that old inventory and tail.
   `candidate_register_capture_bound:1035–1044` selects the actual Allowance
   view tail and canonicalizes it. `candidate_capture_incidence:959–1009`
   appends at the old vector length and links an old bucket tail to that new
   record. A finite valid bucket stays finite. Splicing (`1011–1033`) removes
   the source bucket and joins its chain to the distinct destination chain;
   disjoint old chains imply no cycle. This requires the prior disjoint-chain
   ownership invariant, not guessed membership from an allowed-effect set.
   The rollback inverse restores links/buckets before truncating records and
   views (`706–738`). No all-path source/member/payload induction closes.

10. **Evidence and replay shape do not establish all owners.**
    `attach` (`candidate_context.rs:3702–3716`) appends a new fiber whose next
    link is the old head for its exact key. Each next index is older than the
    appended index; the chain is finite, and duplicates are skipped. Relation
    ID validity remains an input premise. `relation_with_scoped:3481–3513`
    appends/reuses an actual relation ID and enforces the represented scoped
    lane restrictions; it does not derive valid source/context/transformer
    inputs merely by storing them. Canonicalization (`4649–4672`) transports
    existing actual fibers while retaining originals. Replay construction
    (`4411–4499`) snapshots actual heads and retains generated dependencies
    and children. With append-only fibers and earlier recorded heads, an old
    head is a suffix. Transfer (`2536–2548`) checks operation/index bounds
    and advances queued once. The missing complete source/import/rollback/
    retained-owner induction is not discharged by these local implications.
    In particular, no successful helper result proves later acknowledgement.

Row rollback (`lib.rs:9810–9863`), term rollback (`term.rs:803–829`) and context
rollback (`candidate_context.rs:2182–2280`) restore/truncate their own stored
state. Their composition needs the actual route checkpoint and no surviving
reference into a removed suffix. This note does not infer that cross-owner
property from the existence of three rollback functions, and does not impose
full recovery on abnormal paths allowed to stop/discard the private attempt.

## W classification and both actual applications

| R70 W conjunct | Constructor-derived portion | Exact remaining premise |
| --- | --- | --- |
| Row/level/metadata alignment, bound kinds/signs, valid forests | Successful initial/fresh row allocation; lazy identity forest extension and root-link/compression preservation; checked bound-owner/lane selection | Valid source/recipe and captured indices, native translation of every referenced row, valid item sign/row/term at each emission; first missing equation above |
| Visible, tagged, finite acyclic Function children and component translations | Successful checked Function immediate children; new-node DAG extension from valid children; component local association | Candidate endpoint output and retained child/component interpretation across all source/FreshUse/rollback histories |
| View/member/tail/payload/incidence validity | Appended view IDs, copy from validated old view, finite-chain append and disjoint-chain splice | All source tail/member/payload inputs, disjoint old buckets and coordinated rollback ownership |
| Evidence/replay/context/source/scoped and queued-owner validity | Exact-key decreasing fiber chain; retained replay construction and checked transfer | Valid input relation/context/source/scoped IDs and complete retained-owner/failure-resume induction |

Thus no full W conjunct is reported as independently closed at both calls.
Their displayed constructor-derived *parts* are not relabeled as W.

At `lib.rs:14822`, the actual call is

```text
candidate_extrude(Value(lower), Positive, value_levels[upper_row]).
```

At `lib.rs:14835`, it is

```text
candidate_extrude(Value(upper), Negative, value_levels[lower_row]).
```

The branches establish graph presence and a nonrow Value root with the shown
sign; `dispatch_live_item`'s canonical-task guard precedes both. The typed-drain
path retains the current item through Transport, Context and Dispatch
(`lib.rs:14399–14465`). Applying items 1, 4 and 5 says: **if** the actual task's
target row came from the allocated constructors through valid transports,
that row's level lookup is in range and the result remains a same-kind row.
Applying item 6 says: **if** a Function root and its child interpretation came
through the shown checked construction without a stale suffix reference, its
four ports satisfy the required visibility/kind/sign. Applying items 8–10
reduces traversed bounds/views/fibers to their exact emission and retained-owner
premises. None of these `if`s is removed by the caller. The missing
`candidate_endpoint` equation prevents the base-to-native induction needed
to instantiate these implications globally at either call.

The honest current application is therefore a proof obligation at **each**
call, not a theorem of its return:

```text
ReachCurrent(call+) -> [missing constructor/retention induction] -> WCurrent(call+)
ReachCurrent(call-) -> [missing constructor/retention induction] -> WCurrent(call-).
```

## Historical R70 application is a separate revision boundary

R70 froze `candidate_extrusion.rs` at `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`,
`term.rs` at `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60`,
and `lib.rs` at `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`.
They differ from this contract's current pins. Current `Work` adds Tuple,
Record and Variant (`candidate_extrusion.rs:8–13`). Current endpoint translation
handles their tags (`lib.rs:11874–11894`); current FreshUse reconstructs these
structures (`candidate_scheme.rs:4783` onward). Their constructor correspondence
and local worklist continuations were not covered by the R70 Function-only
argument. They are **current represented cases, historical correspondence
OPEN**, not atoms or excluded source forms.

Even if WCurrent were derived, applying the old reviewed implication requires
the explicit remaining edge

```text
Current constructor/continuation cases, including Tuple/Record/Variant,
and their observations refine the frozen R70 entry-to-return simulation,
with all current W premises justified; or a newly reviewed current result
establishes EntryToReturnCurrent directly.
```

No such equation/result is supplied by the old source hash or review. This
revision boundary and the earlier native-constructor frontier are independent.

R71 raw-slot/canonical-fiber coverage remains separate. R70-DRAIN-1 concerns
later execution/acknowledgement/settlement and remains separate. Neither follows
from decreasing chains, graph presence, queue transfer or an extrusion return.

## Checks, reuse, next owner and stop receipt

Reused: R70's reviewed conditional status, actual W decomposition, mutable
visit-time snapshots and separation of transferred/consumed replay. Rejected:
assuming W, testing hand-built states, proving row allocation from the live-term
constructor, treating a caller's unchecked level lookup as validation, or
porting old review coverage to additional structural cases by name.

Static source reads/searches and SHA-256 checks only; all 17 dependency pins
matched before source claims. Exact search for `candidate_endpoint` over all
eleven pinned Rust files found uses but no defining implementation. No Rust
writes, Cargo, tests, builds, probes, Lean checks, Git, external contact,
scratch/cache paths or descendants. Requested model/effort: Sol/high; observed
model/effort: UNKNOWN. Grant: at most 1,800 active seconds; exact active time,
CPU and RSS UNKNOWN. No renewal or returned unobserved budget is claimed.

Mutual TODO `R244-NATIVE-PARAMETER-1`: Luna may admit the exact defining source
of `InferenceSession::candidate_endpoint` and its required constructor inputs;
prove the displayed Parameter equation, then continue the current history
induction. Falsifier: an accepted production construction returns a wrong-kind,
wrong-sign, invisible or out-of-range endpoint that actually reaches a call.
No such prefix was established here. No repair is justified: **NO_SAFE_CODE_SLICE**.
TODO `R244-R70-REVISION-1`: independently establish the displayed current/R70
case correspondence or review a current replacement simulation. Neither TODO
authorizes new writes/dependencies. No self-certification.

Both assigned outputs freeze after final read-only hashing. Writer:
**STOPPED / WRITES_STOPPED**; no descendants or unresolved descendant leases.
New/scratch paths: only this note and the assigned R244 inbox; scratch NONE.
Independent review and integration remain with Luna.

## Frozen direct dependencies

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
```
