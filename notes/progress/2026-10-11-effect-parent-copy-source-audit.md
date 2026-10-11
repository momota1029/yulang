# Effect parent/copy intrusion: bounded source-owner audit

Date: 2026-10-11
Status: frozen, unreviewed research-only source characterization
Baseline: `0aa618f8d0fab512de4b401df4bca66950c0b8cb`
Branch supplied by primary: `research/simple-sub-intrusion`
Method/owner: complementary static source audit; no constructive all-path rank proof
Exclusive lease: this note only
Budget: 30 minutes of static inspection; no tests, builds, executable experiments,
Git commands, delegation, compiler edits or shared-record edits

## Objective, authority and claim boundary

Trace authentic Effect producers, storage, extrusion, reconstruction, replay and
SCC consumers. Identify the source owner of a possible return path from a genuine
extrusion copy to its parent. The assigned prover owns the constructive all-path
rank obligation; this note neither reproduces that proof nor selects a dependency
graph or changes the selected operation.

Governing sections are **Direct decision**, **Selected operation and compiler
responsibility**, and **Retained boundary** of
`notes/design/2026-10-10-parent-copy-scc-intrusion.md`; §§1–5 and **Authority and
integration** of the top-level inference principles; and §§2–4 of
`notes/design/2026-10-08-source-generalize-definition.md`. The accepted operation
retains the genuine extrusion parent and equates the pair when it enters the
same SCC. It does not require a merge on every source history. No new meaning of
“same SCC” is selected here. Necessary abnormal-path safety remains governed by
the top-level principles, without a general full-restoration requirement.

Inputs are the intrusion dependency graph proof, the orientation source map,
the independently authored Value conformance audit, and the reviewed local
recursive source/scheduling record, with hashes below. The Value result supplies
no Effect exclusion theorem.

**Bounded result:** no authentic source expression forcing a genuine Effect
parent/copy SCC was established. The exact unresolved owner is non-row Effect
admission, including its replay entrypoints: a row receives a Support/Allowance
operand without structural extrusion or a check on that operand's retained tail
level. This is an inspected source fact, not a demonstrated source-reachable
rank violation or semantic defect. The existing recursive control supplies a
genuine parent/copy relation but lacks the return path and the initial replay
event described below. There is no universal exclusion, theorem closure,
independent certification or gate-status promotion.

## Source-owner matrix

All Rust locators are under `crates/yu-solver/src/` at the pinned snapshot.
Here `p` is an actual parent, `c` its copy, and `r` an Effect row. “Level” means
the stored lexical level; no independent global rank is assumed. Physical edges
are the existing SCC owner's adjacency, not a chosen semantic replacement.

| Route / owner | Actual construction or consumption | Level and possible SCC return-path responsibility |
|---|---|---|
| Collected Effect allocation: `lib.rs:10052–10099` | One row per Effect component, initially level 1 and `non_generic=false`. | Allocation creates no bound edge. |
| Source lexical initialization: `candidate_source.rs:251–326,532–541` | Body starts at 1; lambda body/formals stay at the current level; block initializers are one level deeper; component levels are installed before fact admission. | Writes initial levels, rather than lowering a live graph during solving. Source scheduling owns the levels later used by comparison and capture. |
| Fresh Effect allocation: `lib.rs:10187–10208` | Empty bounds, caller-supplied level, `non_generic=false`. | No parent record or edge merely from allocation. |
| Ordinary row comparison: `candidate_extrusion.rs:840–863`; candidate dispatch `lib.rs:11689–11693` | Canonicalize; skip identity; for `a <= b`, if `level(b) <= level(a)`, store upper `b` on `a`; otherwise store lower `a` on `b`. Replay opposite bounds. | No level mutation. A direct row edge goes from higher/equal level to lower/equal level. The reverse comparison need not create the reverse physical edge when levels differ. |
| Non-row Effect comparison: `candidate_extrusion.rs:854–863` | Non-row lower with row upper is stored as that row's lower; row lower with non-row upper is stored as that row's upper. Both use ordinary replay. | **Unresolved seam:** there is no `candidate_extrude` call or retained-tail level check here. An all-path nonincrease premise cannot follow from row-to-row owner selection alone. |
| Physical insertion: `candidate_extrusion.rs:406–565` | Canonical typed owner and bound; Positive means lower, Negative means upper; record evidence/capture incidence and mark intrusion dirty. | Does not change levels or enforce a level order. Does not enqueue opposite products by itself. All direct callers must justify the endpoint they supply. |
| Positive Effect extrusion: `candidate_extrusion.rs:80–177,308–326` | If the parent is younger than target, allocate `c` at target; retain the actual parent; store upper `c` on `p`; recursively copy selected lower bounds. Also visit incoming Allowance capture incidence. | Strictly lower-level copy creation, physical `p -> c`. Copy bounds use recursively remapped endpoints. Direct insertions do not activate replay. Incoming incidence is metadata, rather than a reverse SCC edge. |
| Negative Effect extrusion: same row constructor, `candidate_extrusion.rs:80–164` | Allocate/retain as above; store lower `c` on `p`; recursively copy selected upper bounds. | Again physical `p -> c`, with no initial opposite replay. Positive/negative creation provenance alone supplies no `c -> p`. |
| Effect view extrusion: `candidate_extrusion.rs:180–207,258–306` | Support, Allowance and AnnotationMember traverse their actual tail at the current polarity; remap the view to that tail. Positive incoming-incidence transport installs a remapped Allowance on the remapped source. | A remapped view is not the original view. Incoming-incidence source and tail must both be checked when reasoning about level order; direct insertion has no extra guard. |
| Annotation tails: `candidate_effect.rs:979–996,1513–1536` | Scope/name lookup reuses the one actual annotation Effect row; otherwise allocate at the annotation level. Composed-negative singleton rows return that tail directly. | Names across different annotation scopes do not identify rows. Same-scope sharing is real. Direct-tail routes cannot be omitted from source coverage. |
| Support/Allowance producers: `candidate_effect.rs:1452–1577` | Covariant explicit rows produce a shared source view with optional scoped tail and a fresh port at the same construction level; Positive installs Support, Negative installs Allowance. Omitted/operation rows follow their actual branches. | Ordinary construction-level ports/tails are explicit; later propagation of an existing view to another row is a separate premise. Closed views have no tail edge. |
| Formal/root annotation routes: `candidate_effect.rs:1054–1078,1117–1178,1315–1356` | Formal singleton symbolic ports use shared rows; composed-covariant formals can use views. A whole-binding root row checks computation. A variable-only computation allowance uses its tail directly. Local publication uses the paired exposed annotation root. | No positive root computation Support is invented. Exposed/local roots and older formal rows must retain their distinct ownership and scopes. |
| Support/member consumer: `candidate_effect.rs:889–955` | Support compared with a non-row upper emits each AnnotationMember plus `tail <= upper`. Contribution/AnnotationMember against Allowance is discharged when allowed; otherwise forwards the member to the allowance tail or reports mismatch. | This can emit new Effect comparisons. Support versus a row is first stored by the non-row admission branch above. AnnotationMember retains a tail for transport/capture, but is absent from the SCC node set. |
| Contextual filters: `candidate_context.rs:2730–2801` | A registered Allowance filter records origin and explicitly replays; an unregistered filter calls `candidate_apply_effect`. Exact consumed endpoints can stop ordinary dispatch. | Uses the same unguarded non-row admission seam. Context/residual records are not independently added as SCC edges. Stored registration does not establish every future replay. |
| Capture closure: `candidate_scheme.rs:300–326,446–457,565–666,755–782` | Eligibility is `level > boundary && !non_generic`; older rows are retained without expanding their mutable bounds. Local Effect rows additionally capture incoming Allowance incidence. Views, AnnotationMembers and contextual payloads retain mapped tail nodes. | Capture has richer dependencies than SCC adjacency. A captured incidence can include a source owner reached through a tail; it is not permission to infer a tail-to-source SCC edge. |
| Fresh-use preparation: `candidate_scheme.rs:1008–1021,1046–1068` | One remap per current canonical row; eligible local rows become fresh rows at use level; older/fixed rows keep identity. Support/Allowance/AnnotationMember views remap to the same row mapping. | Freshening is not extrusion: it does not call `retain_extrusion_parent`. The local-versus-shared mapping must justify any level relation between a restored owner and view tail. |
| Authentic restoration: `candidate_scheme.rs:1221–1266`; `candidate_extrusion.rs:659–680` | Rebuild captured endpoints, preserve the captured bound side/owner orientation, attach FreshUse evidence, and directly insert before enumerating opposite bounds. | No renewed level-based owner selection or extrusion. The premise is the authentic capture/remap image. Arbitrary direct restoration and cfg(test) cycle helpers are not source evidence. |
| Current/future replay: `candidate_extrusion.rs:700–803` | Current insertion saves opposite count; each step rereads canonical live endpoints. Ordinary insertion explicitly drives replay; a later opposite insertion can activate prior stored bounds. | Replayed non-row operands return to the same admission seam. Suspension receipts alone do not show completion. New direct extrusion bounds are not automatically replayed. |
| SCC adjacency: `candidate_intrusion.rs:415–444,621–634` | Effect row points to both bound sides; Support/Allowance points to its actual canonical tail. Contributions/AnnotationMembers are excluded. No Effect-to-Value edge is constructed. | These are the only inspected physical return-path carriers within Effect. Parent records, capture incidence, contexts and evidence do not supply extra adjacency. |
| Qualifying equality: `candidate_intrusion.rs:476–491,517–604` | Require distinct canonical actual parent/copy in one SCC; transfer both bound sides, splice capture metadata, map copy to parent, lower parent level to the minimum, canonicalize and replay merged lowers. | This is the solving transition that can change live Effect level/rank. Its premise must already hold; its own consequences cannot justify the first qualifying SCC. |
| Source Generalize / Call outputs: `candidate_scheme.rs:843–918,950–976,1355–1378`; `shadow_apply.rs:1331–1442`; `candidate_call.rs:327–374` | Complete component schedules precede capture. Incoming/local uses recapture and restore. Apply records its real demand, argument evaluation, invocation and application Effect ports; invocation row is allocated at application level. Callee and invocation computation effects flow to application output. | These paths expose actual endpoints to later comparison; a returned interface or successful capture is not a proof of the complete fixed/retain source closure, Call semantics or Effect rank. |

The legacy `lib.rs:11696` path can lower levels using the old extrusion owner,
but candidate dispatch returns earlier at `:11692`. It is not evidence that the
candidate non-row branch performs that operation. Rollback restores prior
journaled Effect levels (`lib.rs:9485`) and truncates new rows (`:9495`); this is
an existing lifecycle route, not an additional source edge constructor or a
new general rollback requirement.

## Authentic control and first missing event/edge

Reuse the exact symbolic-formal control from
`notes/progress/2026-10-10-local-recursive-contextual-source-witness.md` §1:

```yulang
act io
my outer sink = {
  my witness (cb:int -> ['t] ()) = {
    my checked: int -> [io, 'u] () = cb;
    my ignored = sink witness;
    checked
  };
  witness
}
```

The prior record reports zero-recovery parsing and successful candidate solving
for this control at its named historical baseline. No execution was repeated
here; those reports do not establish a parent/copy merge. The negative concrete
formal variant is rejected by source preflight, so it cannot provide a current
source witness for the missing constructor.

The current source owners preserve the recorded control derivation: `sink` is
at 1, the forming witness and its formal tail `t` at 2, and the checked
annotation/tail initially at 3. The recursive occurrence retains the open
initializer rather than allocating a published scheme frame. `sink witness`
extrudes its demand to sink's level. Following the forming witness and later
Function publication reaches the original formal `t2` at Negative polarity,
creating genuine `c1` and storing `c1 <= t2` as a lower on `t2`. The retained
parent/copy record is authentic; the physical creation edge is `t2 -> c1`.

**Earliest absent event on this route:** `Work::Visit` installs that lower at
`candidate_extrusion.rs:123` by calling only `candidate_insert_bound`.
`Work::Bound` likewise uses direct insertion at `:314`. Neither calls
`candidate_replay_bound`; dirty marking only enables an SCC check. Thus the
creation step does not activate the new lower against already retained checked
uppers. A later opposite insertion can activate a pair, but no such later event
establishing the required return path was derived for this selected control.

**First missing physical edge:** the inspected route has no `c1 -> ... -> t2`.
The checked facade's tail belongs to its separate local annotation scope, not
the witness formal's `t2`. Its wrapper incidence cannot identify that tail with
`t2`. Parent provenance and tail-indexed capture incidence add no reverse SCC
edge; copying/remapping a view changes its tail to the mapped coordinate.
Consequently this control does not establish a qualifying Effect parent/copy
SCC. This route-local obstruction does not establish that every Effect source
route has the same obstruction.

## Exact unresolved source premise

A candidate all-path exclusion might require every physical row-to-view-to-tail
step to preserve a suitable rank. This audit does not adopt that hypothesis.
The ordinary scalar branch establishes only the direct-row level orientation.
For a Support/Allowance bound, `candidate_apply_effect` never inspects the
tail, and direct insertion/restoration never enforces that ordering either.
Thus an original view arriving through ordinary replay can be stored unchanged
on its new row owner. The SCC builder will then follow that view's actual tail.
View extrusion has a remapping guarantee only when extrusion actually runs.

The missing source correspondence is therefore exact: establish whether all
authentic source/replay/restoration emissions at **this non-row admission owner**
supply an appropriately related mapped tail, or exhibit one actual emission
whose retained tail closes a return path to the genuine parent. The data
needed are the original source occurrence, construction order, actual row/view
identities and levels, bound evidence lineage, and completed replay event. The
test `close_cycle` and arbitrary direct restoration supply none of this source
reachability. No compiler repair is authorized by the local missing guard
alone.

The selected source Generalize definition requires complete typed fixed/retain
closure and preservation of original scopes; level eligibility alone does not
establish that contract. Call port recording likewise does not prove all Call
laws. These are separate unverified bridges, not substitutes for the absent
Effect return-path evidence.

## Evidence, omissions and next action

This is a static constructor/consumer inventory, grounded in actual source
branches. There is no executable oracle. Producers, replay and SCC consumers
are separately located implementation owners, but they share the same compiler
and do not form an independent semantic oracle. Prior execution evidence is
reused only with its historical baseline and limited claim. No random seeds,
enumeration ranges, model mutations, benchmark samples or new runtime results
apply. No second synthetic probe was attempted.

Reads used `cat`, bounded `rg`, and `sed -n` on the named dependencies; final
`sha256sum` snapshots matched the primary-supplied source/input hashes. One
locator search included nonexistent `candidate_local.rs` and exited 2; the
actual local owners are in `candidate_effect.rs`/`candidate_scheme.rs` and were
read. No whole-source reachability enumeration or complete theorem-proof reread
is claimed. CPU/peak memory and exact elapsed wall time were not measured;
read tool calls completed in subsecond time. No solver/Cargo process or executable
experiment ran.

Unverified: all authentic source histories; a concrete parent/copy SCC witness;
a universal Effect rank/exclusion invariant; complete replay/fairness and memo
coverage; source-Generalize correspondence; complete Call, Effect hygiene,
soundness, principality and production cutover. No parent gate closes here.

Recommended next action: give the existing proof/source owner the non-row
Effect admission premise above, with the exact source occurrence and replay
lineage requirement. Adjudicate that premise before adding another abstract
rank probe or deriving an implementation change.

## Dependency snapshot and commit packet

The primary supplied the full baseline and reported no repository dependency
changes during the assignment. The following current-file SHA-256 values were
read locally; the nine source and three assigned research-input hashes matched
the supplied snapshot. No Git comparison was performed by this worker.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-11-intrusion-scc-dependency-graph-proof.md` | `f8c06bd945ca586dc2ee43ac970f138ab7b2ed2b8c6566b0aa11a1fafb109330` |
| `notes/progress/2026-10-11-intrusion-scc-dependency-orientation-audit.md` | `3554e418f55d0d588b74aabe7adb02f26445babb88f1a2d4b7d9a93a4d04c44a` |
| `notes/progress/2026-10-11-value-intrusion-semantic-conformance-audit.md` | `cebf34d075bf0a20a68116f802519c2ba296863467e4cd53a37ef79323732b9a` |
| `notes/progress/2026-10-10-local-recursive-contextual-source-witness.md` | `6db0a0f4c1eeb547e11ddb7b093c8042dc7716f3c1719a9f67cd79c6577a1629` |

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-11-effect-parent-copy-source-audit.md`.
- Baseline SHA: `0aa618f8d0fab512de4b401df4bca66950c0b8cb`.
- Dependency changes: none reported by primary; source/input snapshot matches
  as stated above. The worker made no dependency edits or Git checks.
- Review status: frozen, unreviewed source characterization; no independent
  review or status promotion claimed. Producer writes have stopped.
- Checks already run: bounded source-owner inspection and exact dependency
  SHA-256 snapshot; leased-note whitespace/patch-marker inspection. No builds,
  tests, probes, Git operations or additional execution evidence.
- Proposed checkpoint commit message:
  `research: map Effect parent-copy source reachability seams`.
- Shared-record deltas left for primary/curator: record the non-row Effect
  admission premise, authentic recursive-control missing event/return path,
  source-owner matrix and uncovered source scope; retain all original parent
  theorem/production gates without promotion. No shared files were modified.
