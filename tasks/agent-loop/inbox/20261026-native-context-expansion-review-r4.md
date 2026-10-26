# Native Context expansion r4 — independent M3 review

**Verdict: ACCEPT the frozen local Context construction and its stated open
application boundaries.** No BLOCKING, major, or minor finding requires a
repair of these bytes. This accepts the executable parser, complete local
check/residual body, installed-body provenance, and algebraic graph transport.
It does **not** close `MERGE-EXPANSION-COVER-1`, committed native readback,
accepted return, `SourceProblem.NativeCorrespondence`, or the original
`SourceProblem.InferenceSoundness`.

Assignment/handoff revision: `context-expansion-review-r4`, revision 1.
Reviewer: `/root/context_expansion_review_r4`, fresh independent nonauthor;
no producer assistance, descendants, or Git authority. Model/effort inherited
from the actual launch; no custom role or unavailable runtime is claimed.
The primary supplied baseline `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`,
branch `yulang3`, a 900-second wall budget, and at most two focused
120-second/one-thread/`-M1024` checks for unresolved concrete risks. The live
assignment supplies the authority and exact lease; historical scheduling rows
were not treated as permission to reclaim any writer.

## 1. Frozen identity and review evidence

I independently recomputed **203 SHA-256 comparisons, all matching**: the
manifest and freeze receipt, three repository outputs, all 31 inputs both in
the repository and frozen snapshot, 32 compiled outputs, 102 scratch artifacts,
and both native executables. These checks establish byte identity with the
recorded evidence; no Git operation was used to reconstruct or change the
supplied baseline.

| Frozen object | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeContextExpansion.lean` | `9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8` |
| `notes/theory/2026-10-26-native-context-expansion-construction.md` | `0bddd394a8dc7d686b1708ef099808c8b24c1e217242eaa7d0df5c1f6e9bed95` |
| `tasks/agent-loop/inbox/20261026-native-context-expansion-r4.md` | `a0c99c1fa00537e6c4dc3bd50efa586a68cb4e07f8a8285ca77501e6e1000d8b` |
| Producer `manifest.json` | `2c734c55d5f4c343b48eebaa7c515f9b8305ac4c8b71b247f4f9fab23f77e967` |
| Producer `freeze.json` | `f4d222e62e325db9e86ee5c1a3aa5cbea6e846f1a47b313ae2a5807633b0d3de` |
| Producer `declaration-inventory.json` | `2365c9cc4ad8ebc0ba23d4ebc5cf3221dd138112cb0e612866b69070e0c22815` |
| Producer `check16-origin-census.log` | `4beca862c3ff1945d2c37cec011b82424251e2c944d91b7ec28b46fe8ed78277` |
| Producer `check16.json` | `a08f4570879f84142e7cf35123286f04497afe7fc173607e90f42f612ad948cf` |
| Checked `NativeContextExpansion.olean` | `eb9b4fbea2038c42c3cad801adc323c6ce89300cc648eeb37de62c9c756a4e16` |

Producer scratch paths are under
`/workspace/scratch/f98087c7ac1a/context-expansion-r4`.
Reviewer evidence is under
`/workspace/scratch/f98087c7ac1a/context-expansion-review-r4`:

- `reconciliation.json`, SHA-256
  `1b37c70a3f33c8425e45701c484945e9c2e4be38fa62a69bf0692c845d3d5e78`:
  every comparison, complete census reconciliation, all check exits and
  material diagnostic lines, and source-search results.
- `reconcile.py`, SHA-256
  `0f34f7c50605b8d54ad7f69b6e028580233fbaa85ed8c056c7a5ffa270bb3bf2`:
  the independent read-only verification procedure.
- `named-root-types.txt`, SHA-256
  `39378935e7c812e847684837ee84e7c7b605a4ddd1f8a79a521015096f459e51`:
  all 50 complete named-root types and axiom sets extracted from the reconciled
  inventory, without abbreviation.

The complete 1,110-line module, paper and handoff were inspected. Governing
reads include `AGENTS.md`, its pre-sprint proof-closure contract, design and
sprint authority, the Lean skill and both references, the pinned project,
the original `Contracts.lean` roots, source-preservation §§1,3,5, the fixed
Value-birth-level qualification, whole-proof closure §§1,6, lifecycle §6,
the prior merge/current review boundaries, and relevant native bodies.

## 2. What is constructed and checked

All new names below have prefix `YulangClosure.NativeContextExpansion`.
`scanStep` and `scanLoop` compute the complete parser. `checkFilter`,
`applyFilter`, `applyEffect`, `admit` and `decompose` compute the outgoing body.
`expand` requires successful entry preparation and an already canonical
processing key. Successful operation/resource projections remain explicit
in `Availability`; no semantic solution or complete-Context law is supplied.

For arbitrary tables `t`, graph `g`, availability `a`, levels, fuel, full
key and body, `construct_full_context` has these exact operational premises:

```text
Reachable t g
key ∈ g.core.vertices
g.pending key = active
expand t a levels g.core.q fuel key = some body
```

Its conclusion, for `next = install g key body`, is:

```text
Reachable t next ∧ next.bodies key = some body ∧ Held next key body ∧
  ∀ depth, InstalledAt t next depth key.
```

The supplied `expand` equation is a finite executable local result. It is not
a recursive child-coverage hypothesis. Its real-native derivation remains a
separate obligation; choosing arbitrary true availability fields does not
establish that derivation.

`decompose_exact` retains the exact `Parsed`, ordered `Aligned` relation from
every filter to its executed `Check`, post-check Context, consumed decision,
continuation equation and publication-success guard. `every_filter_executed`
derives the full count and a callback result for each selected weight.
`full_body_child_payload` ranges over **every** child in the checks and the
residual and derives its child-local Context, inherited source set and full
transformer, self-relation guard and successful enqueue projection.

`Built` has computed and transported constructors only. It accepts neither
`ClosedAt`, a favorable child list, semantic truth nor a completion memo.
`Invariant` ties the stored `g.bodies key` to that provenance and to `Held`.
`Held` supplies every child's registration/path and every fiber's
membership/original-parent path. `install` stores the computed body itself.

`InstalledAt` uses that exact body in its positive-depth `some body` branch.
There is an essential boundary: its `none` branch permits retained, queued
or active owners, and these exhaust `Pending`. Thus
`installed_all_depths` is a structural retention/unfolding result, **not**
proof that every registered key has a body or has finished. The stronger
body-existence equation is supplied by `construct_full_context` only for its
selected successfully expanded owner. The paper and handoff preserve this
distinction; later integration must do so too.

For arbitrary `keyOf : Nat × Nat → Key`, `historical_full_context` concludes
`∀ depth, InstalledAt t s.graph depth (keyOf pair)` from
`ReplayReachable t keyOf s` and the two exact indexed equations
`s.replay.operations[operation]? = some batch` and
`batch[index]? = some pair`. `dependency_skip_full_context` uses an actual
dependency member, `old_old_full_context` the previous product invariant,
and `full_product_context` executes the ordinary/incoming Replay event.
The empty-event induction establishes origins, freshness, installed-body
invariance and historical registrations. No recursive closure or completion
argument is hidden in those roots. Their `ReplayReachable` premise remains
an abstract constructed event history awaiting native authentication.

## 3. Complete local native case mapping

Native locators refer to the manifest-pinned files under
`crates/yu-solver/src`.

| Review point | Source and result |
| --- | --- |
| All Context constructors | `candidate_context.rs:242–266,3670–3765`: PrefixLeft, Replay, Swap, WithoutLeftFilter, SuffixRightPops and BothFromRight are represented. Identity and visited `(id,mode)` skip before lookup. Outer/Replay/directed modes, strict child-ID decrease, lower-before-upper traversal, exact weight/view validation, first-discovery filter order and deduplication match. Suffix/Both are rejected even when a certificate is present. |
| Parser residuals | The mixed Replay-filter/directed guard and pure-Replay-to-identity branch match the source. `ScanRun` and its two computation lemmas relate finite successful transcripts and fuel; they introduce no additional supported-source limit. |
| Entry, kind and scoped guards | `candidate_context.rs:3062–3073,3799–3839`: full Effect demand is rejected; Value transformer must be zero; canonical Effect self-pairs with nonzero transformer fail before local checks. `executeInput`, `expand` and `decompose` retain these successful-input requirements. |
| Identity, empty filters and consumed endpoint | `candidate_context.rs:3828–3888`: identity bypasses parsing; empty filters do not publish discharge and preserve the stored Context. With nonempty filters, consumption is exactly an Allowance upper selected by the full validated callback list. The unconsumed branch keeps the original directed pair with the computed post-check Context. |
| Registered versus new filter | `candidate_context.rs:3840–3875`, `candidate_extrusion.rs:635–879,1147–1180`: a registered row/Allowance bound attaches the origin and replays without a second physical insertion. Otherwise the native reflexive, placement or operand branch runs. Every required callback success is retained. |
| All bound placements | `placedBound` covers both row/row level choices, row/rigid and rigid/row. `placed_bound_pair` proves that positive or negative storage denotes the original directed pair. `apply_bound_exact` retains Context, sources, transformer, origin/physical/Replay successes and the relation guard. |
| Checked identity and ancestry | `candidate_context.rs:3898–3936`: the validated checking-filter scope licenses identity Context for checked Allowance fibers, while retaining the complete processing parent. Installation and `Held` preserve the original-parent dependency; residual placement does not invent a preferred owner. |
| All Effect operands | `candidate_effect.rs:730–783,1237–1305`: Bottom, every indexed Support member, Support tail, Contribution/member membership, exact closed-weight allowed data, Allowance tail, conflict and unavailable cases remain present. Conflict is a successfully recorded diagnostic obligation, not local semantic success. |
| Whole emitted child keys | `candidate_context.rs:3025–3036,3361–3372,3456–3482`; `lib.rs:15214–15250`: child-local source Context/interner node, canonical endpoints, processing-parent sources/transformer and enqueue success match. A nonzero canonical self-child fails even though an inline reflexive apply call returns locally without constructing a child. |
| Value boundary | The complete `ValueRequest V` is forwarded unchanged, including arbitrary endpoint data, stored Context, sources and all five fields of optional demand. This proves no indexed Value dispatch/record-adaptation rule. Filtered Value requests are rejected by the Context stage. |
| Generation transport | `candidate_intrusion.rs:568–708`; `candidate_context.rs:4230–4254,4318–4331`: the prior copy-selection/frozen-prefix construction is reused. Every check and residual leaf is transported; weight/view/registered metadata, consumed decision and entire child list remain intact. |

`Body.transport` and `body_fibers_transport` act on all stored leaves, not one
chosen filter. `held_merge` first retains each old fiber, then selects its
actual canonical carrier and composes its new transport path with the old
parent path. Unchanged physical bounds retain their stored fiber Context;
changed ones use `post` of that complete old fiber key. In `Step.merge`,
`post` is specifically `postContexts g`, computed from installed publications.
The standalone transport/invariant lemmas are algebraic for arbitrary `post`;
that broader parameterization is not a native-state correspondence theorem.
`identity_post_context` and the imported Allowance carrier theorem preserve
checked identity fibers. Absorption is explicitly
`∀ row, qNew (qOld row) = qNew row`.

## 4. Honest committed-readback and terminal boundaries

The first missing owner is correctly named **CONTEXT-COMMITTED-READBACK**.
At `lib.rs:14288–14420`, Context and Dispatch are distinct frame stages.
Native publication at `candidate_context.rs:3875–3888` precedes Dispatch;
the graph publishes at successful body installation after the erased local
macro-step. Consequently an active or failing Dispatch cannot be read back
as an installed completed body merely because `discharged` was set. Partial
callbacks, failed publication sampling and transaction erasure must use the
same actual committed history.

For `discharged.contains(relation)`, native code skips the filter callbacks;
for `pair_is_current` at `lib.rs:13507–13518,14443–14456`, Dispatch may skip
the residual operation. These cases require the prior **same complete
processing relation owner** and its constructed/transported body, or its
still-active owner. `Step.reuse` does not construct that body and does not
acknowledge a new physical Replay occurrence. The note and handoff correctly
retain these as open readback duties.

One particularly concrete integration constraint must remain visible.
`expand` requires the key to be canonical under the current representative
map. `mergeGraph` leaves the original child keys and pending phases in place.
If a queued, not-yet-expanded key changes endpoints during a merge, native
`candidate_context_transport_task` at `candidate_context.rs:3767–3785`
creates its canonical processing relation with a Derived dependency. The
next owner must connect that original obligation to the transported processing
owner/body. Neither registration of the new key nor `InstalledAt` of the old
pending key proves this connection. The current local result makes no such
claim; a readback/terminal construction must explicitly supply this transport
case, potentially with an additional constructor justified by those native
events. It cannot simply infer that all pending owners have disappeared.

Settlement must use the actual Transport/current-none/empty-worklist cut and
must include work queued by an earlier merge in the same settlement loop.
The broad algebraic `Step.merge` does not assert that every abstract merge
interleaving is executable. A transformed nonzero self-relation still needs
successful native interning at its actual owner. Full `keyOf` readback must
identify the fixed ordered physical input BoundKeys, attached relations,
stored Context composition, source union and transformer order in the same
execution. Repeated/numerically reused operation IDs and distinct Replay
occurrences retain separate births and acknowledgement obligations.

These are nonblocking application constraints within the explicitly open
frontier, not a source-qualified counterexample and not a request to narrow
the original theorem.

## 5. Full census, checker evidence and retained failures

I inspected the census program: it selects by originating module index,
visits **all declarations**, rejects originating axioms, prints complete
types/axiom sets and checks transitive axioms. Its proof/deep-term printing
options are enabled in the final source. I independently parsed all **855
unique complete blocks**, reconciled every type, declaration kind and axiom
set with the JSON inventory, checked all 50 named roots and all private
entries, and found no type omission or unexpected dependency.

| Complete transitive axioms | Theorem constants | All declarations |
| --- | ---: | ---: |
| None | 196 | 632 |
| `propext` | 51 | 102 |
| `propext`, `Quot.sound` | 49 | 121 |
| Total | **296** | **855** |

There are 16 private declarations including 12 private theorem constants.
There is no `Classical.choice`, project axiom, `sorryAx`, native-evaluation
assumption or checker bypass in the originating dependency census. A separate
source search over the four-module project import cone finds only nine uses
of the operational function named `admit`; none is a proof tactic or hole.

All sixteen recorded check receipts and their preserved main-source snapshots
were reconciled. Exits are
`1,1,1,1,1,1,1,1,0,0,1,0,0,1,0,0`.
Call 01 preserves the Lake installation-configuration detection failure.
Calls 02–08 preserve ordinary declaration/elimination/option-bind proof
errors; call 11 preserves record-update syntax and resulting proof errors.
Call 14 preserves the audit counter's type-inference failure. Calls 09–10
and 12–13 are successful constructive stages. Call 13 explicitly rebuilds
the final source hash. Call 15 succeeds but has abbreviated generated types;
only call 16 supplies the complete final census. No final error or warning
appears in the final check log.

Recorded final commands use the provisioned native Lake
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`:
`--version`, `--no-cache env lean --version`,
`--no-cache build +YulangClosure.NativeContextExpansion`, and
`--no-cache env lean -j1 -M1024 AuditNativeContextExpansion.lean`.
All four exit zero. Actual versions are Lake `5.0.0-src+eb6cafb`
and Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The final call takes 2.248739791 seconds, with 1.961329 user + 0.232453
system child CPU seconds and 1,006,124 KiB observed child maximum RSS.
Recorded total checker wall time is 66.621791178 seconds across 16/20 calls.

**Reviewer Lean execution: 0/2 calls used.** No unresolved elaboration/kernel
risk required another focused check, and no broad rerun was performed.
This is fresh independent proof/source review and validation of recorded
checker evidence, not a new independent kernel run. Python verification used
`PYTHONDONTWRITEBYTECODE=1` and the reviewer-owned `TMPDIR`. No Rust, Cargo,
network, installation, dependency or shared-cache operation ran.

## 6. Application to the unchanged parent and stop receipt

The original parent remains the exact `SourceProblem.InferenceSoundness`
definition in `Contracts.lean:127–130`: every supported source, scope,
generated constraints and successful solution must yield **one** original
source witness satisfying both its source judgment and `sameScoped`.
This component removes an assumed complete outgoing Context body from the
local graph construction. It supplies the computed body and its transport
when the corresponding local event is established. It does not derive the
native execution or source witness merely from graph registration.

The next applications, still owned by the primary's original proof lanes, are:

1. **CONTEXT-COMMITTED-READBACK / REPLAY-MERGE-READBACK:** construct the common
   native projection with parser runs, callback success, publication/Dispatch
   cuts, prior same-owner bodies, original-to-canonical pending transport,
   exact product/merge data and occurrence births.
2. **VALUE-DISPATCH:** consume the unchanged Value request through all actual
   indexed Function/tuple/record/variant children and source record adaptation.
3. **TERMINAL-DIAGNOSTICS/ACK:** eliminate relevant pending owners and conflict
   leaves using actual diagnostics and ordered acknowledgements from that
   same history, and identify accepted ReturnReady.
4. **ROW/CONTEXT-SEMANTICS / SOURCE-INFERENCE:** interpret retained fibers and
   directed Contexts, connect the original constraint laws, and construct the
   same original scoped source witness, complete Call and effect hygiene.

All original source/world quantifiers, optional records, method selection,
generalization, lawful independent uses and fixed Value-birth-level occurrence
qualification remain intact. No arbitrary-model preservation, alternate
typing definition, assumed `LocalLaws`, source restriction, new semantic
authority or production-readiness claim was introduced.

Only this exact leased repository review file and the three named reviewer
scratch files were written. No producer source, note, handoff, root import,
shared status, Rust, configuration, dependency, Git index or ref was changed.
Primary adjudication, status synchronization, integration and frequent coherent
pushes remain with `/root`. The review finished within its 900-second bound;
exact full-stage wall/peak-memory consumption was not instrumented.

**WRITES STOPPED.** No child, checker or background process remains. This is
the frozen final review receipt; its SHA-256 is supplied in the submission.
