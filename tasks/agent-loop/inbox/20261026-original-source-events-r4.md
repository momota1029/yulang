# OriginalSourceEvents repaired author handoff

**Author:** `/root/whole_soundness_route_r4`; generic leaf author, not reviewer.
**Primary:** `/root`. **Dependency baseline:** supplied `5428c5e62`, unchanged.
**Status:** repaired metadata/data/local-consumer packet frozen for a distinct
fresh review. Full original inference soundness remains OPEN.

The rejected `b5a4b389` packet and its rejection receipt remain intact. This
handoff supersedes that packet's current producer description; it does not
rewrite the rejected snapshot or supply independent acceptance.

## Exact repaired outputs

| Output | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` | `df3469e907867c6f884b17b589d078b58a3dd674a589e1d16baa05b0f004e61b` |
| `notes/theory/2026-10-26-original-source-events.md` | `96108ef0429329c85e876b42f315ee3e6c8356c3b47a6e086ab40c7e59bd7de1` |

The hash of this handoff is recorded in the final non-self-referential
`/workspace/scratch/f98087c7ac1a/source-events-r4/repair/freeze.json`.
Primary receives that manifest's hash separately.

## F1 repaired by a generic proof

Only the existing choice-right route changes: tag **3** replaces tag 1 in
both `owners` and `entries`. Descent/choice-left remains 0, forest-tail remains
1, and retained-evidence extension remains 2. All original Lambda, receipt,
parameter-entry and actual Return telescope routes are unchanged.

The rejected scheme could produce the same whole Owner and EntryRegistration
for a choice's right branch and the next forest sibling, with the same binder
and scope. That also aliases ActualKey and RecordKey if their other original
operands agree. Current sourceRules not constructing choice did not justify
the exported generic route claim. The repair does not narrow the tree domain.

The checked generic construction now has:

- Complete `treeRoutes`/`forestRoutes` inventories for every RuleTree/RuleForest
  constructor.
- Prefix/edge separation through `tree_route_shape`, `route_edges_separate`
  and `tree_sibling_separation`, including arbitrary descendant suffixes.
- Mutual structural `tree_routes_nodup`/`forest_routes_nodup` proofs.
- Ordered-sublist proofs from both real owner and entry walks into those
  inventories, including at-most-one local output at a node.
- The four required arbitrary-input results: `owner_routes_nodup`,
  `forest_owner_routes_nodup`, `entry_routes_nodup`,
  `forest_entry_routes_nodup`. No uniqueness law or Site condition is assumed.
- Reserved-tag exclusion at every depth in both trees and forests, applied to
  a genuinely collected entry by `retained_owner_separate_from_tree`.
  `distinct_retained_routes` preserves separation between new retained owners.
- Separation in both complete key constructors, including
  `different_record_routes_different_keys`.

All prior 40 public root type/axiom blocks are exactly unchanged, checked in
`repair/prior-root-preservation.json`. The original source-to-owner, Value and
computation packet, actual returned-object Shared installation, older-frame
preservation, independent history-record and six-field local readout
applications still compile. No core source, field payload, domain, State,
primitive or complete Call meaning was changed.

The final scratch file keeps the rejected old walk definitions in a separate
namespace and proves the old collision explicitly. It then verifies the
repaired owner and entry outputs, both complete keys, nested choices and a
retained slot below a non-root entry. It also reruns every previous probe.
The old collision is labeled a generic rule-tree discriminator, never an
original independently admitted source-program counterexample.

## F2 repaired by actual-origin census

The old scratch namespace filter reported 49 constants / 17 theorems.
Independent review correctly found **52 / 19** in that old audit. Its two
private `sourceRules.match_4` equation theorems and splitter were omitted by
the namespace prefix. All three had no axiom dependencies; this was an audit
completeness defect.

The new audit enumerates **all current-module constants by actual origin**
with `env.getModuleIdxFor? name == none`. It explicitly prints the private
sourceRules equation theorems/splitter and every new generated declaration.
All constants have their actual kind, complete type and transitive axioms
printed and checked. No namespace filter is used for completeness.

| Final isolated inventory | Count |
| --- | --- |
| OriginalSourceEvents originating declarations | 785 |
| Originating theorem constants | 268 |
| Named originating public roots | 72: prior 40 plus 32 new |
| Entire current audit-module declarations | 97 |
| Entire current audit-module theorem constants | 34 |
| Named scratch probe roots | 24 |

The count change from 678/180 to 785/268 includes generated declarations; it
is not a claim that 88 new public mathematical results were added. All 32 new
named roots and all preserved 40 roots are listed exactly. Integration must
reconcile generated constants already originating in other imported modules,
using exact names and actual integrated origins rather than summing the
isolated 268 theorem count.

Complete machine-readable records include exact names, kinds, canonical axiom
arrays, original rendered axiom summaries, full types and type hashes:

| Evidence under `source-events-r4/repair/` | SHA256 |
| --- | --- |
| `origin-census.json` | `ea687873102678c9a539b3392d7a16ea73fb9380973b9013e71e54b4babf168a` |
| `current-census.json` | `39c84d7480fbbc620ac5716f90d157531d60911ddd0dec6b38ba411a65aab766` |
| `required-roots.json` | `561fc5bf023b6776847beaf5ad0a3f016bdcdf6781c6a4a4e7df1723264836cd` |
| `root-delta.json` | `f3ff64fbff4855da705f1e6370cd89352d30eab94c22c20b009d434c7eca6cb0` |
| `probe-roots.json` | `3043e4ca36e24ca6e6a05d288a03bd6601b31df7e2d842959092ed6ed047eb38` |
| `prior-root-preservation.json` | `034320225417b11d46ef084b351e8722011b5f23116fbeb9dab7cc86fbe135fa` |
| `check/OriginalSourceEventsRepairAudit.lean` | `544046f073206f95b38b858710591523811fb5e0d52dd343f59ca65d8a19e130` |
| `check/check06.log` | `b7beda0ce830ad960849b397836f45ef92e57e09e452cbd1cc04fb938d66b870` |
| `checks.json` | `bcb9ff61c6e0666386b420511f72fe54eac6a01d18f28ad93c6828c17d058b7f` |

`repair/census-schema.md` gives the exact log delimiters and JSON schema. The
complete native Lean log remains authoritative. Every declaration's axiom
closure is checked against only `propext`, `Classical.choice`, `Quot.sound`.
No project axiom, sorry, assumed postcondition or unsafe native evaluation is
accepted.

## Retained rejection and bounded execution

Before editing, all 274 original artifact hashes and all three rejected
outputs were verified and copied along with the old freeze: **278 payload
files** under `source-events-r4/repair-before-20261026T154444/`. Its snapshot
manifest hash is
`6680d0084380c51074d54a6711e9ef083e1cd5190e7bcda9f741a786bb493568`.
The old freeze remains
`bbbb36eb541980033766ecda670e92627623b8269d2557457f3f09c437c22ee3`.
Original attempts, failed logs and the original required-root inventory were
not overwritten. Repair attempts and snapshots use the distinct `repair/`
directory and its own checker ledger.

The independent rejected review remains unchanged in
`tasks/agent-loop/inbox/20261026-original-source-events-review-r4.md`; an exact
copy is retained as `repair/rejected-review.md`, SHA256
`5efbe584a8f39949a87bf0d3cd5767fcc463a5213a3577014be2a9707010a80f`.
That receipt is REPAIR REQUIRED, not acceptance of this new packet.

The supplemental lease allowed 1500 seconds and fourteen focused checks. Six
were used. Repair checks 1–3 preserve failed local proof/elaboration attempts;
4 compiled final module bytes cleanly; 5 passed all probes/census; 6 passed the
complete final census with explicit declaration kinds and actual scratch
origin. No prior failure was deleted or relabeled. Separate process-start and
universe-suffix parser failures are retained with their causes and zero proof
impact.

Pinned native Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; absolute authorized Lake;
`-j1 -M1024`; one CPU/thread; at most 120 seconds and 1280 MiB aggregate per
call; isolated cache/TMPDIR/PYTHONDONTWRITEBYTECODE. Final check 6 took 8.087 s,
peak 1,180,651,520 aggregate RSS bytes. All calls stayed within the bounds.
No children, Git, core/shared imports, Rust, configuration, dependency or
expected-output edits were made.

## Original semantic boundary remains exact

This is source-owned metadata, dependent packet and local Shared-consumer
construction. It does not prove full semantic admission coverage merely from
a raw/decorated record round trip. Description/EventProof can vary while actual
raw identity and runtime ownership remain fixed; no total JointWitness-map
invariance is asserted.

The actual global owner-indexed readout, complete original Event/D_F
correspondence, Outcome-to-retained-evidence emission, route-preserving core
Frame linkage, native cell/contract alignment, target guards/captures/view
presentation, full PhiW, Checking/L4 and native inference soundness remain
explicitly open. The response projection collision is an interface fact, not
a claim that two independently admitted original histories are unsound.

## Stop and fresh review

After final non-self-referential repair-manifest creation: **WRITES STOPPED**
for all leased repository, scratch, cache and checker outputs. No descendants
or running checks exist. All frozen hashes are sent to primary. Fresh
independent review and eventual publication remain primary's responsibility;
this author supplies no self-acceptance or full-goal closure claim.
