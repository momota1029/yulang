# Native Context committed readback r4 — independent M3 review

**Verdict: ACCEPT the frozen constructive forward-history and joint-journal
supplier, with its stated native interpretation boundaries.** No BLOCKING,
major, or minor defect requires repair of these bytes. This verdict does not
close the actual `CONTEXT-COMMITTED-READBACK` application,
`MERGE-EXPANSION-COVER-1`, `SourceProblem.NativeCorrespondence`, or the original
`SourceProblem.InferenceSoundness`.

Assignment/handoff: `context-readback-review-r4`, revision 1. Reviewer:
`/root/context_expansion_review_r4`, independent nonauthor of this module;
no authorship, repair, descendant, Git, or shared-status authority. This reviewer
previously reviewed the frozen expansion component; that prior review did not
construct this readback result. Runtime/model/effort are inherited from the
actual supported launch; no custom role or unavailable runtime is claimed.
The producer baseline is `820ed79a8891e72c85280a5e0313e57fb05f3b73` on
`yulang3`. The primary's live packet grants the sole repository lease for
this receipt and the reviewer-owned scratch directory, a 900-second wall bound,
and at most two risk-driven 120-second, one-thread, `-M1024` Lean checks.

## 1. Frozen identity and evidence

The producer freeze is dated **2026-10-26 12:06:37 UTC**. I independently
verified **155 SHA-256 comparisons**, all matching: the manifest/freeze, three
repository outputs, all 14 inputs both live and frozen, all 120 scratch
artifacts (including 56 compiled artifacts), and the two installed executables
against their previously verified pinned digests. The final source is identical
in the repository, `source13.lean`, and the checked isolated project.

| Frozen object | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeContextReadback.lean` | `321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2` |
| `notes/theory/2026-10-26-native-context-readback.md` | `d3322e58a178d9939609518d986c467a5fdcadd6bad6a24399f42220865b636f` |
| `tasks/agent-loop/inbox/20261026-native-context-readback-r4.md` | `e3f316fe84bba313e42baafd91bd6438157cafc1651108b6ffb889f868b1d732` |
| Producer `freeze.json` | `9a6b9ed8d70b0d05734e51f2d851982cc956b5e2792ec1244d616e13066dfabd` |
| Producer `manifest.json` | `ddaf217b6771a6f5986838a76a34d4bda6a1f9e1ba60428fa43f902b1517e1ca` |
| Producer `origin-inventory.json` | `6c4dbbfa31dfa7e1ee7b04a2949f929b4abd9f9b63f6877db6c4ae8270128c3d` |
| Producer `check13-origin-census.log` | `acdc8afe9bf86415eb783adf9ce1ff7af0e39c326bf4eeb560381f134d9199c9` |

Producer evidence is under
`/workspace/scratch/f98087c7ac1a/context-readback-r4`. Reviewer evidence is under
`/workspace/scratch/f98087c7ac1a/context-readback-review-r4`:

- `reconciliation.json`, SHA-256
  `43108bc44c68997c17972974f6715e1168ee72140415e352d6c327257d4c5314`:
  all comparisons, complete type/axiom reconciliation, every check exit and
  material diagnostic, source search, and all choice-dependent names.
- `reconcile.py`, SHA-256
  `8d84901805bda112232a7acd751c77afedcc716d609db933f8157fefafe82fe1`:
  independent static verification procedure.
- `named-root-types.txt`, SHA-256
  `79a2fed4c5d40f679585174c96decb974cd62a92d1828ed650add4c7690e2bf0`:
  all 78 complete named-root types and actual axiom sets.
- `authority-check.json`, SHA-256
  `e59dec878dc7c4ed3373a55040a4a6310b99b2097b95bc82d91a01286831d588`:
  the 12 governing/source-contract files are unchanged from the versions
  already read for the preceding review.

The whole 1,509-line module, construction note and handoff were read, together
with the relevant imported drain/journal definitions and pinned native
constructors. The original proof-closure, authority, Lean skill, full-source
scope, fixed Value-birth-level qualification and shared-witness requirements
remain the same. No Git operation reconstructed or changed the supplied
baseline, and no historical scheduling row supplied authority.

## 2. Exact mathematical advance and premises

All new roots below are prefixed `YulangClosure.NativeContextReadback`.
The principal advance is a shared event history whose Context receipts are
forced to accompany the actual control model's clearing Dispatch events.
This removes the old possibility of leaving the original queued occurrence
at an unrelated pending vertex while only a canonical replacement receives
a body.

`prepareParsed` retains the complete ordered filter callbacks and their
consumed decision. `prepare` adds entry, canonical-key and parser guards.
`finishPrefix` computes the consumed branch or residual `applyEffect`.
`staged_decompose` and `staged_expand` prove their composition equals the
previous frozen computation when `a.publish = true`. The precise old-component
application is:

```text
∀ {t a levels q fuel key prefix body},
  prepare t a levels q fuel key = some prefix →
  finishPrefix t a levels q key prefix = some body →
  a.publish = true → NativeContextExpansion.Built t q key body.
```

The same `a`, `levels`, `q` and `t` occur in both computations. This theorem
must not be applied to independently chosen callback or representative
snapshots. Generic cached/completed receipts instead expose `BodyRecipe`,
whose prefix has an actual checked construction or explicit carrier transport
and whose residual has a computed completion. A recipe is not silently
identified with the stronger frozen `Built` predicate for every current map.

`Invariant` links owners, memo, receipts and processed occurrences. An owner
can enter only while its work is current; it remains live or acquires a seal.
Memo lookup returns that same owner and complete processing key. A duplicate
does not need a prior seal. The `Administrative` processed-count equation
excludes clearing Dispatch from the unrestricted control channel. Its
preservation proofs examine the imported control constructors, including
moving processed work from a popped frame into a return receipt. Finish,
duplicate and Value exit supply the missing receipt when the count increases.

The exact `quiescent_original_context_readback` quantification is:

```text
∀ {t : Tables} {s : State t},
  Run t (initial t) s → s.control.queue = [] → s.control.frames = [] →
  ∀ w ∈ s.control.issued, ∃ receipt ∈ s.receipts,
    receipt.work = w ∧ Resolved s receipt ∧ RouteValid s receipt.route.
```

For an Effect receipt, `Resolved` supplies a sealed body recipe for its
processing owner. For a Value receipt, it supplies the exact successful
Context forwarding result. `RouteValid` retains the actual Derived edge and
any earlier original nonempty checked prefix. Neither case supplies semantic
subtyping or a successful source judgment.

`committed_readback` derives one initial forward `Run` and a well-formed
journal from `Committed t journal`. `committed_quiescent_context` obtains the
same readback from that journal, its actual joint-cell lookup, empty queue and
empty stack; it takes no separate favorable forward run. These are theorems
of the constructed event/journal model. **Actual native execution has not yet
been shown to produce `Committed t journal`.** That is an explicit remaining
application, not an inferred consequence of the root's name.

## 3. Native order, ownership and coverage review

Native locators below are under the manifest-pinned `crates/yu-solver/src`.

| Obligation | Inspected source and assessment |
| --- | --- |
| Original occurrence and Transport | `candidate_context.rs:3767–3785` computes canonical endpoints, keeps the same relation for an unchanged pair, otherwise interns the post-check Context with whole sources/scoped flow and records Derived. `makeRoute`, `Route.target`, `Route.derived` and `Step.transport` preserve the immutable queued `Work` and compute these same branches. |
| Whole relation payload | `candidate_context.rs:265–292,3025–3073`: Effect retains endpoints, Context, optional sources and full transformer; a present Effect demand is rejected. Value retains the complete five-field optional demand and requires transformer zero. Both transport payload lemmas retain all these fields. |
| Full fresh and cached Context prefix | `candidate_context.rs:3670–3888`: `prepare` uses the reviewed parser and every filter callback. The cached branch looks up the same complete discharged owner and reparses. `actual_discharged_prefix` derives a fresh nonempty origin; `cached_parser_readback` proves successful parse equality without requiring identical fuel, under the same `t`. |
| Early publication and sampling | `candidate_context.rs:3870–3888` reserves retained state, publishes discharge/residual, then samples resources. `publish` and `sample` are distinct events. Neither supplies a body seal; `publication_is_early` preserves control and seals explicitly. A failed or unfinished sample/Dispatch cannot be promoted to completion from discharge alone. |
| Memo before residual | `candidate_intrusion.rs:423–455`, `lib.rs:13507–13518,14443–14456,15340ff`: `completed[processing]` is an admission memo, written before the residual callback. `admitOwner` records the actual live owner. Raw aliases mark it only when the raw task equals the canonical processing task. Memo currentness also requires raw typed-pair presence and the matching generation. |
| Duplicate ownership | `Step.duplicate` retains the memo's exact owner. `memo_has_actual_owner` proves live-or-sealed ownership, then `owned_body_at_cut` removes the live alternative only at `NoCurrent`. The concrete `Witness.active_memo_run` has source identity `some 9`, transformer `2`, a live memo owner and no seal; it is an abstract control witness, not an accepted source counterexample. |
| Clearing Dispatch | `lib.rs:14344–14420`: only actual completed local/structured dispatch clears the current task. The refined finish/duplicate/Value-exit events each add a receipt. `finishPrefix` retains every check and computes the residual or consumed branch before adding the Effect seal. |
| Inner synchronous settlement | `lib.rs:14308–14339`, `candidate_intrusion.rs:568–708`: the top current-none/empty-queue cut can coexist with a live outer frame. `settlement_owner_readback` returns a seal or that precise outer owner; it never substitutes abstract pending coverage. True no-current and empty-stack roots are kept separate. |
| Multiple merges in settlement | `beginSettlement` requires the empty queue at entry. `merge_session_has_actual_cut` preserves the entered working frame/current-none condition while allowing work queued by an earlier merge. It does not assume that the queue remains empty throughout the loop. |
| Every child payload | `recipe_prefix_children`, `recipe_body_children` and `resolved_body_whole_child_provenance` preserve every check/residual child, its child-local Context, complete sources/transformer and admission self-guard. These concern the constructed keys; they do not derive an issued `Work` occurrence from `Availability.enqueue = true`. |
| Diagnosed tickets and optional observations | The quiescent ticket theorem uses the same drain projection. `record_source_drain_completion` at `candidate_context.rs:2177–2184` can return when reservation fails. The new receipt lists are ghost history records and do not assert successful inference implies an entry in that optional native vector. |

In particular, the proof does not collapse “diagnostics ran” into “no conflict
exists.” Successful Effect callbacks may leave conflict leaves, and Value exit
proves only Context forwarding. Complete Value/record/Function dispatch and
semantic interpretation remain independent consumers.

## 4. Joint cancellation and lifetime boundary

`Transaction` obtains the actual prior joint cell and writes a `Step` result
into that cell. It cannot choose unrelated control, publication and memo
histories. `Attempt` allocates its journal birth before the transaction.
Cancellation uses the established exact table-unwind theorem to restore the
represented Context/control/owners/memo/seals/receipts together;
`committed_readback` then retains the earlier forward run.

The exact conclusion of `cancelled_attempt_birth_not_reused` is
`saved.clock < (NativeExecutionHistory.cancel saved current).clock`. It is
freshness of the **ghost attempt clock**. It does not, by itself, stamp every
native Context, relation, `Work`, Replay or frame slot with that lifetime.
The native identity/field interpretation must make that connection. The note
properly leaves the distributed journal erasure and table lifetimes open and
does not require Rust to store one physical whole-state snapshot or restore
irrelevant resource counters/capacities.

The frozen native source supports the lifetime boundary:

- `State::context` at `candidate_context.rs:2630–2655` interns all six
  constructors and allocates `contexts.len()+1`; Swap(Identity) is not folded
  away. Rollback removes interner keys and truncates the vector at 2141ff.
- `source_weight` at 2734–2758 allocates a weight with its exact allowed list,
  boundary, owner, position and attachment. `candidate_signature_view` at
  `candidate_effect.rs:859–909` determines the View index first, constructs
  the weight, then pushes the View. The intermediate weight is not already
  guaranteed to validate against a published View.
- Effect-algebra rollback at `candidate_effect.rs:313–389` truncates Views
  and contributions; Context rollback also removes relations/source sets.
  Replay numeric frontiers and old completion values are restored by their
  own owners. `lib.rs:9271ff,9489ff,9646ff` owns the common route boundary.

`LifetimeBoundary.two_successful_parses` computes two parser results for
different contents of raw Context slot 1; `no_single_raw_table` proves no
single lookup gives both. These are checked parser/interpretation facts,
corroborated by the legal native interner/truncation mechanisms. They are not
a constructed accepted-source execution or a refutation of inference
soundness. The paper states this boundary accurately.

The required **TABLES-LIFETIME-READBACK** supplier must cover all five table
components—Contexts, weights, Views, contributions, and actual PrefixLeft
interner results—plus their complete relation/source/scope references. It must
derive preservation on live allocation-stamped handles or the exact access
footprint from constructor/extension/cancel events. Whole-table equality is
not an acceptable substitute: new allocations and meaningful earlier `None`
observations must remain possible. The same trace must validate parser,
weight/View, child-local source and operand computations at each relevant cut.

Two further boundaries are substantive. First, the native emitter must join
every actual child-key callback to its issued immutable `Work` and Replay
transfer in this common history. Second, the module's merge event records maps
and generation, not complete physical-carrier transport. Historical sealed
recipes require the accepted `Body.transport`/`mergeGraph` construction to be
applied to that same native copy and frozen-prefix attachment history. Empty
queues or sealed recipes cannot supply either fact.

## 5. Complete census and actual checker evidence

I inspected the audit program, which selects by originating module index,
rejects originating axioms, enables full proof/deep-term printing and collects
transitive axioms for **every** declaration. Independent parsing reconciled
all **652 unique complete type/axiom blocks** with `origin-inventory.json`.
All 78 source-authored theorem names exactly match `named-roots.json`; there
are 13 private declarations, including 8 private theorem constants. No type
omission or unexpected axiom occurs.

| Complete transitive axiom set | Theorem constants | All declarations |
| --- | ---: | ---: |
| None | 48 | 154 |
| `propext` | 18 | 29 |
| `Quot.sound` | 1 | 1 |
| `propext`, `Quot.sound` | 135 | 442 |
| `propext`, `Classical.choice`, `Quot.sound` | 26 | 26 |
| Total | **228** | **652** |

Choice is present and explicitly reported. It propagates through the control
ownership proofs to roots including `memo_has_actual_owner`,
`quiescent_original_context_readback`, `effect_receipt_original_body` and
`committed_quiescent_context`. `fresh_body_is_frozen_built` and
`committed_readback` use only `propext, Quot.sound`. No choice-free or
axiom-free claim is accepted for the whole module. A source search across
the complete seven-module local import cone found no proof hole, project
axiom, native-evaluation assumption or kernel bypass. The `admit` matches name
the expansion function or readback event/cases.

Producer calls 01–13 have exits
`1,1,1,1,1,0,0,0,0,1,1,0,0`. Their source snapshots, complete logs and receipts
are retained and hash matched. The first failure is sandboxed Lake installation
detection. Calls 02–05 contain namespace/reserved-field, option-reduction,
elimination and record-invariant elaboration errors; the early failed
elaborations also report generated `sorry` placeholders. Those logs are not
accepted proof evidence. Calls 10 and 11 preserve the leaf-membership and
witness-frame normalization failures. Calls 06–09 are earlier successful
milestones with local warnings; final calls 12–13 have no errors or warnings.
The final census has no `sorryAx` dependency.

Call 13 uses the absolute provisioned Lake under
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake` for
`--version`, `--no-cache env lean --version`,
`--no-cache build +YulangClosure.NativeContextReadback`, and
`--no-cache env lean -j1 -M1024 AuditNativeContextReadback.lean`.
All four commands exit zero. The actual version is Lean **4.35.0**, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, with Lake `5.0.0-src+eb6cafb`.
The final call takes 17.345841534 seconds, with 15.350125 user + 1.920541
system child CPU seconds and 1,013,952 KiB observed child maximum RSS.
The producer used 13/20 checks and 127.127746060 recorded checker seconds.

**Reviewer Lean executions: 0/2.** No unresolved kernel/elaboration risk
justified another check. This is fresh independent proof/source-boundary
review and validation of recorded checker evidence, not a new independent
kernel run. Static verification used `PYTHONDONTWRITEBYTECODE=1` and the
owned `TMPDIR`; no Rust/native test, broad build, network, installation or
shared-cache operation ran.

## 6. Parent application, ownership and stop

The original `SourceProblem.InferenceSoundness` still quantifies over every
supported source, original scope, generated constraint set and successful
solution, and demands one original source witness shared by its judgment and
`sameScoped`. No source/world restriction, changed typing definition,
independent marginal witness, default scoped flow, or assumed `LocalLaws`
replaces that conclusion here.

The accepted advance is the derived original-occurrence/processing-owner
readback through actual modeled clearing cuts and one joint cancellation
history, with a precise table-lifetime obstruction. The native application
still needs the following concrete suppliers:

1. **TABLES-LIFETIME-READBACK:** the complete constructor/extension/cancel
   interpretation above, preserving live payload and dependent identities.
2. **Common native event and callback erasure:** actual control/Context/memo
   transitions, child issuance and Replay transfers, distributed journal
   restoration and actual identity births in one history.
3. **Current carriers and Effect/diagnostic interpretation:** apply the frozen
   copy/canonicalization/transport results and interpret all retained fibers,
   residuals and conflicts at the accepted native cuts.
4. **Complete Value dispatch:** preserve all indexed Function/tuple/record/
   variant, extrusion and source-record adaptation cases after exact Context
   forwarding; a successful Value-exit ghost event does not prove them.
5. **Original source semantics:** complete Call, hygiene, generation and the
   same scoped source witness, with principal coverage/progress/termination
   retained as their separate original obligations.

Only the exact leased review file and reviewer scratch evidence were written.
No producer file, import, shared status, Rust, configuration, dependency, Git
index or branch ref changed. The primary owns adjudication, status integration
and publication. Review began at 12:07:32 UTC and finished within the issued
900-second envelope; no extension was used.

**WRITES STOPPED.** No child, checker or background process remains. This is
the frozen final receipt; its digest is supplied in the submission message.
