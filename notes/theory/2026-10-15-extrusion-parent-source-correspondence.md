# Extrusion Parent: bounded source-to-construction correspondence

Date: 2026-10-15
Status: provisional bounded proof evidence; construction derivation with a
conditional session-local bridge, not an established general theorem
Branch: `research/simple-sub-intrusion`
Frozen HEAD: `e2d913d6412bd332bea1860d495999d5717bc5ff`
Production source baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Lease: this new note only; leaf, no delegation or Git mutation
Method/checks: static constructor/queue/consumer tracing, dependency hashes,
baseline comparison and whitespace check; no Cargo, executable probe or measurement
Parent gates: original H1/H2/U OPEN; H3/P disabled; profile positions undecided
Review: one fresh compiler_referee found two minor record omissions; primary
integrated both, and final focused delta review passed

## 1. Frozen statement and exclusions

Fix the existing receiving-call fixture, without changing any binder or scope:

```yulang
my root = { my outer cb = { my inner x = cb x; inner }; my identity z = z; outer identity }
```

The two Apply occurrences are independently authenticated HIR occurrences:
the receiving `outer identity` and the inner `cb x`. Their distinct Local and
Parameter resolutions, Lambda/formal origins and checking occurrences remain
those of the frozen test. Name spelling selects fixture positions only.

Let S be one initialized live candidate State using the frozen production
constructors. Quantify over **every successful Parent append** reached from
`dispatch_live_item`'s structured Value-drain extrusion branches in this run,
including copying Visits reached through selected bounds. At such an append
t, let T be the current drain's `TypedWorkItem.task`, r its transported
`TypedWorkItem.relation`, and P the appended `candidate_intrusion::Parent`.
The code does not declare a type named `ExtrusionParent`; this note uses P for
the packet's extrusion Parent record.

Required bounded construction conclusion:

```text
r = Some(r_t)
P.comparison = Some(task_pair(T)) = Some(S.relations[r_t].key.pair)
P.sources = S.relations[r_t].key.sources
```

Both fields consequently project the **same active contextual task** at t,
although they are read from different processing slots. This is a construction
identity claim, not identity of all activations with that RelationId.

For the later join, additionally fix a final observation f in the **same live
State**, containing surviving P and the unchanged relation r_t. Define the
complete retained-table fiber

```text
J_f(P) = { r | Some(relations_f[r].key.pair) = P.comparison
                and relations_f[r].key.sources = P.sources }.
```

The conditional conclusion is: if `|J_f(P)| = 1`, its element is r_t. If that
element also equals the unique independently authenticated source `cb x`
Origin.relation, this P was appended while processing that source relation.
The existence/uniqueness of that source Origin and the observed fiber size
are **run inputs to be checked**, not conclusions supplied by this pass.

Hypotheses are the frozen code, successful entry into the inspected structured
candidate drain, ordinary constructor execution rather than manually forged
test records, and a same-State observation of surviving records. Successful
fixture admission is supplied by the primary's existing run record; this leaf
does not parse or execute it. The bounded domain does not replace the original
H1/H2/U source domains or quantifiers.

Excluded conclusions: direct Function field path of a copying Visit;
authentic origin/receiver Value association or SCC qualification of that
occurrence; unique activation history; cross-State/session identity; all-path
completeness or replay; dynamic Receive/Observe; profile formation, protection,
hygiene, residual U, complete Call, soundness, principality or F5 closure.

Authority is [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§1.1 and [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5. The original parent scope remains in
[effects-handler-next](../../tasks/effects-handler-next.md) §§1–3. This note
reuses the [consumer frontier](2026-10-15-omitted-formal-extrusion-consumer-frontier.md)
and [receiving-call observation](../progress/2026-10-15-omitted-formal-receiving-call-dispatch.md)
as bounded prior evidence; it does not extend their semantic claims.

## 2. Exact saved fields and RelationKey construction

Source locators below refer to the frozen production bytes in §6.

`candidate_intrusion.rs:31–39,229–289` defines and appends P. It converts the
actual copy/parent row endpoints into RowKeys, then reads:

```text
sources    := effect_algebra.context.extrusion_sources()
comparison := effect_algebra.processing
```

`candidate_context.rs:2447–2450` defines `extrusion_sources()` as
`context.processing.and_then(|r| relations[r].key.sources)`. Thus sources
comes from a **RelationId**, while comparison comes from an optional
**TypedPairKey**. The retain function alone supplies no equality between
those slots. Its `qualified` source-event test affects pending intrusion;
it neither creates a RelationId nor establishes a Function field incidence.

`candidate_context.rs:203–212,2403–2424` defines ordinary RelationKey identity
as the complete triple `(TypedPairKey, ContextId, Option<source-set-id>)`.
`relation_with_sources` interns this triple: an existing exact key returns
its existing RelationId; a fresh key appends at `relations.len()` and updates
`keys` and `pair_heads`. Different contexts may therefore share the same
pair and sources. Parent.comparison retains only the pair projection.

The source-set constructor (`:2425–2445`) sorts/deduplicates event IDs and
interns the resulting vector. `None` denotes an empty source set, not a
wildcard. IDs and their meaning are confined to this State's retained table.

The relevant construction/admission paths are:

| Owner | Pair, context and sources supplied to interning |
| --- | --- |
| `candidate_context_seed` (`:2696–2739`) | Canonical task pair; source-local context; singleton checking-event set if the exact occurrence is registered, otherwise None; retains Origin with the actual checking occurrence. |
| `candidate_context_admit` (`:2754–2776`), via `enqueue_item` (`lib.rs:12894–12923`) | Canonical queued task pair; source-local context; `relation()` inherits sources of current context.processing; retains a Derived parent when applicable. |
| `candidate_context_transport_task` (`:2931–2950`) | Asserts canonical(original relation pair) equals canonical(task pair); preserves existing relation when exact pair matches, otherwise interns canonical task pair with post-check parent context and unchanged sources, retaining Derived. |
| `candidate_context_begin_replay` (`:3131–3212`) | Canonical replay task pair; ordered lower/upper Replay context (identity for two identity inputs); union of their sources; exact Replay dependency; each child is queued with that RelationId (`:2001–2006,3281–3325`). |
| `candidate_function_port_admit` (`:2777–2835`) | Canonical child task pair; inherited post-check parent context with Swap for Argument/ArgumentEffect, Preserve for results, plus any local prefix; inherited sources; actual FunctionPort parent/field/operation dependency. |

The source entry is `execute_candidate_source_root` /
`execute_candidate_source_schedule` (`candidate_source.rs:780–794`), whose
Candidate action (`:889`) invokes `admit_candidate_fact`.
`shadow_apply.rs:1428–1529` validates the retained ApplySourceInput/recipe,
constructs and saves the four-port negative demand in NativeInterface,
admits its source occurrence, and calls `constrain_live_value`. This supplies
an actual native demand and queue seed. It does not supply complete semantic
Call meaning merely by retaining four ports.

## 3. Derivation of processing alignment at every inspected append

1. With a candidate graph, `constrain_live_item_with_inferred_entry`
   (`lib.rs:12007–12010`) selects `run_candidate_typed_drain`. Starting the
   drain (`:12191–12207`) saves enclosing processing, clears both slots,
   seeds the source relation, chooses an existing explicit relation or that
   seed, and enqueues the item. `enqueue_item` admits relation evidence if
   missing before queue insertion. This is the real queue, not a guessed
   correspondence from endpoint labels.

2. `step_typed_drain` (`:12260–12341`) retains the popped item as frame.current.
   Before a step with current work, it sets effect_algebra.processing to
   `task_key(item.task)` and context.processing to `item.relation`.
   Transport replaces the item's relation with
   `candidate_context_transport_task`'s result, and saves it in both frame
   and context.processing. Context execution asserts the transported key
   pair equals canonical(task pair) (`candidate_context.rs:2964–2972`);
   its temporary processing scope is restored (`:2953–2962`). Dispatch's
   next step restores the same task and transported relation from the frame.
   `task_key` (`candidate_effect.rs:368–373`) and `task_pair`
   (`candidate_context.rs:2631–2636`) are the same case-wise pair projection.

3. Value dispatch checks the raw task pair against its current canonical
   pair (`lib.rs:12412–12420`). If they differ it records/requeues the
   canonical task and **returns before extrusion**. Thus every actual
   structural Value extrusion call at `:12476` or `:12489` has
   `task_pair(T) = canonical(task_pair(T)) = relations[r_t].key.pair`.
   The structured admission paths above supply Some(r_t); there is no
   missing-relation enqueue on this initialized graph route.

4. Those two branches are the production callers of `candidate_extrude`
   located by the source search. `candidate_extrusion.rs:21–364` allocates
   an occurrence and runs a local Work stack. A high-level row Visit allocates
   its actual copy then calls retain (`:83–124`); bound Visits share the same
   invocation. The Function Work case schedules four polar child keys but
   does not store a field path in P.

5. This local traversal does not replace either processing slot. Its bound
   insertions (`:392–571`) append admissions/bounds and optional capture
   incidence; they do not call `candidate_replay_bound` or drive a nested
   drain. Origin transfer (`candidate_effect.rs:563–609`) appends contextual
   Transport/Derived evidence (`candidate_context.rs:3403–3428`) and
   admissions. Fresh row constructors (`lib.rs:10177–10242`), term
   construction (`:10287–10331`), view remapping
   (`candidate_effect.rs:733–784,871–912`) and scratch accounting (`:914–930`)
   likewise preserve processing. These are actual append/construct calls;
   the later replay method in the same file is a separate consumer.
   Induction over the finite successful local Work steps therefore preserves
   the same T and r_t through every retain call, including bound descendants.

6. Substituting steps 2–5 into §2's two reads gives the required equations.
   The comparison slot stores the task pair, and the sources slot reads
   that task's contextual relation. No source-set equality or endpoint
   equality was used to choose r_t. The conclusion does not equate
   Parent.comparison with the complete RelationKey or interpret a discharged
   key.context as the current post-check executable context.

This establishes the bounded code implication. Direct test-only extrusion
calls, manually assigned processing slots, forged Parent arrays and other
entry routes are outside this derivation, not counterexamples to it.

## 4. Survival and the exact finite join

At append t, r_t already exists. Relation keys and P's saved fields are
immutable on the inspected production route. Appending later contextual
relations may enlarge J, but cannot remove this member.

The production rollback owner also preserves that membership for surviving
P: `lib.rs:9152` takes `intrusion.begin()`; `candidate_intrusion.rs:113–138`
saves Parent length and the effect-algebra checkpoint, which includes the
context checkpoint (`candidate_effect.rs:228–248`). Rollback (`lib.rs:9409`)
uses this coupled Undo, truncating Parents (`candidate_intrusion.rs:148`) and
relations/source sets (`candidate_context.rs:1807–1818`). If P predates the
checkpoint, its already-existing r_t does too. If P follows the checkpoint,
that rollback removes P. Therefore the inspected coupled rollback cannot
leave surviving P with its original r_t removed. Source search found relation
removal only at this context rollback and Parent removal only at its owning
truncation in production; standalone test rollbacks are not this route.

The other production caller of `CandidateContext::rollback` is the local failure
path in `rename_contexts_impl` (`candidate_context.rs:1425–1536`), reached from
the incoming-route fresh-context reconstruction in `candidate_scheme.rs:1134`.
It checkpoints before its local traversal. That traversal reads and validates
`ContextExpr` nodes, interns renamed `Context` nodes, and updates only its
remap scratch state; it does not intern Relations, append Parents, or invoke a
typed drain. On its error path, the checkpoint rollback therefore has no new
Relation or Parent suffix to remove. It cannot remove a pre-existing r_t while
leaving its pre-existing P, and cannot orphan an earlier surviving pair.

The test session initializes its graph before source execution;
`start_candidate_graph` (`candidate_scheme.rs:703–717`) replaces the State,
so the claim explicitly does not cross a second initialization or retired
State. Commit/replay-operation retirement is not relation-key retirement.

It follows that r_t belongs to J_f(P). If complete enumeration reports a
singleton `{r}`, then r_t = r by set membership. This simple implication is
grounded by the source proof of membership above. It would be circular to
assume membership merely because the test found one equal pair.

The enumeration must scan `context.relations` in full, comparing the exact
saved TypedPairKey and exact Option<source-set-id>, without canonicalizing
them again. `pair_heads`, a selected CircuitEvidence subset, source-labeled
relations alone, or a search stopping at its first match cannot prove this
singleton. If there are multiple matches, Parent lacks the context coordinate
needed to select the owner. If there are zero, at least one bridge premise
(route, snapshot/lifetime or constructor fidelity) fails; that observation
alone establishes no semantic counterexample.

If the recovered singleton is the unique authenticated `cb x` source Origin,
it identifies the active source relation of this actual append. A subsequent
exact retained Derived/Transport path to a Replay **upper input**, then the
Replay child and its FunctionPort Argument edge, can place the append's owner
and the observed consumer in one recorded derivation chain. The Replay's
other lower input remains distinct and must be retained. This only proves
the displayed same-session operational chain; it does not prove that this
particular P was a direct Argument/Result Visit or that the consumer uses
that copy as its formal profile witness. Equal endpoints, pair equality and
arbitrary multi-input ancestry cannot replace these exact edges.

This leaf did not run the enumeration. The primary later executed the exact
same-State census twice: for each of the four retained Parents, the complete
pair/source fiber was a singleton equal to the uniquely authenticated `cb x`
checking-origin relation; the exact FunctionPort Argument parent's immediate
Replay upper input had explicit Transport/Derived ancestry to that relation.
Thus the conditional membership/singleton/source-origin premises hold for
those records in this one run. The separately authenticated receiving-call
Argument chain is also present. The run still does not identify any copied
row's direct Function field path or make the ancestry a per-copy consumer
proof; the full outputs and their limits are in the
[focused observation record](../progress/2026-10-15-omitted-formal-copy-relation-uniqueness.md).

## 5. Limits, economy audit and next action

The earlier pair-only observation and consumer-frontier pass left copy-time
contextual identity open. This pass uses its owning processing/transport/
append constructors, rather than another reconstruction relation. The parent
H1/H2 problem remains A/B; discarded direct field/profile/occurrence evidence
can create D reconstruction debt, which does not reclassify or close it.
No additional semantic clause or retained production field is authorized.

The assigned exact pair/source census is complete and independently reviewed.
The next discriminator is a test-only observation of retained Function field
substitutions: separate direct Function field copies from selected-bound
descendants, and check whether any retained witness connects an individual
Parent copy to the exact `cb x` Argument consumer. Stop at the first missing or
ambiguous field path. This does not select profile positions or authorize
production retention changes.

Unverified are fiber counts/consumer paths in other runs, direct copy-field
paths, complete lineage through all extrusion/capture/replay/merge routes,
Value occurrence qualification, source profile introduction, annotation
authority, protection/hygiene/U, full Call, soundness, principality and
production cutover.
No proof status is promoted and no source restriction is introduced.

## 6. Dependencies, checks and commit packet

Pinned SHA-256 dependencies (production bytes match both baseline revisions):

```text
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  crates/yu-solver/src/candidate_intrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
5424885f127469ed1148ede2d9aadecd06f88c35df6094854962c80ccaa233bd  crates/yu-solver/src/candidate_context_tests.rs at frozen HEAD only
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
9b137da3b91756ffc71ad5262113eb31ba8c7744a233524e7adaabb76e53998a  notes/theory/2026-10-15-omitted-formal-extrusion-consumer-frontier.md
30bc82644db46db8eb74886395309d93af9049104248e84694ef173e1d4ebeb7  notes/progress/2026-10-15-omitted-formal-receiving-call-dispatch.md at frozen HEAD
```

Checks: read-only branch/HEAD/status, narrow `rg`/`sed`, dependency
`sha256sum`, `git show e2d913d64:crates/yu-solver/src/candidate_context_tests.rs | sha256sum`
matches the assigned test hash; production baseline comparison reports only
the known test-file delta; `git diff --no-index --check /dev/null` against
the leased note emitted no whitespace diagnostics (exit 1 for the addition).
A preliminary live
test read encountered the independently owned new harness; it is excluded
from the derivation and re-read at the pinned revision. No worker output or
runtime result is assumed here.

Resource use: one bounded static pass, within the 20-minute allocation;
zero Cargo/build/test/probe/heavy processes, zero measurement samples, no
child launches. CPU/peak RAM and precise elapsed time were not measured.
Requested policy routing: ordinary Sol/high proof leaf under repository defaults;
actual launch arguments and observed effective model/effort metadata are
unavailable to this leaf (unknown). The prover
registration and absence of role-level model/effort pins were inspected;
configuration inspection alone establishes no runtime override or hot reload.

Commit packet:

- Exact leased path: `notes/theory/2026-10-15-extrusion-parent-source-correspondence.md`.
- Baseline SHA: `e2d913d6412bd332bea1860d495999d5717bc5ff`; production
  baseline `427d1ff5daab866fa7d89cb513a077063cc6454d`.
- Changed proof dependency hashes: none. The primary-owned exact census is now
  cited as runtime evidence for the conditional bridge; test and progress files
  remain separate artifacts, not frozen static proof dependencies.
- Review status: provisional bounded derivation/conditional bridge; the
  independent reviewer accepted the construction derivation and final delta
  corrections with no blocking or major finding. No theorem, parent-gate or
  production authority is promoted.
- Checks already run: static source/constructor tracing, baseline/hash checks
  and leased-note whitespace check; no executable verification.
- Proposed message: `research: derive extrusion Parent processing correspondence`.
- Shared-record synchronization: primary owns `tasks/current.md`,
  `tasks/research-lab.md`, `tasks/effects-handler-next.md`, theory maps and
  indexes; link this bounded same-task projection law and exact final-table
  census, and retain direct field/occurrence/profile gaps and H1/H2/U OPEN,
  H3/P disabled.
