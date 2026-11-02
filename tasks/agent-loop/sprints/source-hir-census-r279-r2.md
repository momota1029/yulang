# R279-r2 — fixed-source HIR census owner extension

Status: CANDIDATE until the r2 owner-coverage/integrity gate, separate proof GO,
and independent review complete. This is a versioned extension of R279-r1; it
does not change the source, claim, parent obligation, semantic authority, or
production authority.

## Objective and falsifier

For the unchanged 87-byte ASCII source

    my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }

derive one of these outcomes from the indexed production owners:

1. `SOURCE_PIPELINE_ROUTE_EXCLUSION`: every normal successful return of the
   specified parse/HIR pipeline for this exact source has a number of
   top-level `HirItem::Binding` entries other than two.
2. `COUNTERCASE_TO_CENSUS`: a permitted path, including a recovery-bearing
   path, returns `Ok(hir)` with exactly two top-level Binding entries.
3. `UNRESOLVED`: an owner or source-to-census edge remains uncovered. Name the
   exact owner; do not infer from empty diagnostics, default operators,
   fixtures, or expected output.

The direct falsifier is a normal pipeline return `Ok(hir)` with two top-level
Binding entries. Diagnostics and recoveries cannot be treated as parse/lowering
failure without source evidence. An `Err`/panic edge excludes only the paths
that actually reach it; account for every other normal `Ok(hir)` path.

The reviewed R278 premise remains conditional: `assemble` filters
`hir.items()` to Bindings and returns `CandidateError::Unsupported` unless the
count is exactly two and no original item is an Expression. Therefore a proved
count-not-two invariant for this exact source implies exclusion at that guard.
It does not establish an observed `assemble` call, same-HIR identity, later
guard results, ordinary-source rejection, global unreachability, an accepted
source counterexample, or theorem closure.

## Immutable dependencies and r1 preservation

R278 contract SHA-256:
`26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233`.
R278 theory SHA-256:
`bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e`.
R278 independent review SHA-256:
`7a67c5e08cd671e9588a07abe75e8e501185568dac0f64fb8a565bdbddbc6f5f`.

R279-r1 contract SHA-256:
`b946d87a15bb9c232597585821221b605c1e9a2bfe2794e4680f7238d825d6a2`.
R279-r1 owner-coverage STOP receipt remains unchanged at
`tasks/agent-loop/history/20261103-r279-stage1-stop.md`, SHA-256
`3c51593c20207fafe4087a4995b1502a4d4ddeb78b95fd7ee51c4ba3811b2824`.
R279-r1 contract, ranges, view, index, admission, and STOP are preserved.

The r1 admission prose says 181,149 bytes. Its authenticated index and STOP
receipt establish 181,148 bytes. Record this as a clerical admission-prose
erratum only: no payload/hash integrity failure occurred. The r2 view length
is derived from its bytes and index below.

Inventory remains
`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`, SHA-256
`42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f` (229
entries). Every r2 source path must come from that inventory.

R279-r1 exact source artifacts, all retained byte-for-byte:

- ranges `tasks/agent-loop/sprints/source-hir-census-r279-ranges.json`, SHA-256
  `3b484b3abe6c9d8c28f13985ebf2e0b1ddb4f978930483c53be279e354e1056d`;
- view `tasks/agent-loop/sprints/source-hir-census-r279-source-view.txt`,
  SHA-256 `6817f43b2b4d44dbaf06fc6a582278054430d9e8d79974b223c49d2534c8c3b8`;
- index `tasks/agent-loop/sprints/source-hir-census-r279-view-index.json`,
  SHA-256 `6cf12c5eed870bce75b665b797bc01e5ae2551c2e310681d8cd2d1f8590b1950`.

R279-r2 exact artifacts:

- ranges `tasks/agent-loop/sprints/source-hir-census-r279-r2-ranges.json`,
  SHA-256 `b832e8b3cadc8b46bb8da0a6d5f1628689b89860471f0dfd4aa93393523a08c3`;
- view `tasks/agent-loop/sprints/source-hir-census-r279-r2-source-view.txt`,
  SHA-256 `c1883ddd04c811ffb38be10d2cab3265b5cb9e06346b904a061a1bf56d4c41a5`;
- binary-offset index
  `tasks/agent-loop/sprints/source-hir-census-r279-r2-view-index.json`,
  SHA-256 `b53c00d63fda81afb2a705b127e489abae78f775e939bd1ab04f932382b64a2a`.

The r2 view contains 46 indexed payloads: all 27 r1 payloads unchanged, plus
19 production payloads. Its indexed byte length is 246,273. R2 additions cover
the declaration re-export and use-item scanner; the selected normalized use
decision; imported/local operator construction, table building and syntax
environment defaults; structural recovery traversal and classification; HIR
recovery validation, partition, attachment, and error emission. No payload
authorizes reads outside its exact indexed interval. The fixture-only r1
payload is not evidence and must not be rendered or inspected by the reviewer.
No `#[cfg(test)]` interval is admitted.

## Required caller / callee / normal-return accounting

This table identifies the five uncovered production edges; it is a gate
checklist, not a proved census conclusion. Sol must account for the exact
condition and result at each edge, including recovery-bearing cases.

| Edge | Caller → callee | Required normal-return account |
|---|---|---|
| Header item advance | `header::discover_header` → `declaration::next_use_item_lex` → `use_decl::next_use_item_lex` | Establish which token/current-item result and origin/line advance the exact source produces, including whether the call is reached on each header loop path. |
| Header use selection | `header::discover_header` → `use_declaration_selected_normalized` → `use_declaration_selected_lexical` / `prefixed_use_candidate_normalized` | Establish the actual Boolean for the exact source and whether header discovery continues or stops; do not infer from the fixture or source spelling alone. |
| Effective operators | `full_parse::parse_file` → `effective_full_parse_operators` plus `SyntaxEnvironment`/`OperatorTable` construction | Account for imported and local declarations, duplicate handling, `Result`/`expect` failure propagation, and the operator table used by root parsing. No default-empty assumption. |
| Structural recovery projection | `ParsedFile::try_structural_recoveries` → `structural_diagnostic::try_collect` → production walk/classification | Account for all projected Missing, RawError, and Invalid occurrences, traversal errors, ordinal exhaustion, and structural invariant errors. No empty-diagnostics assumption. |
| HIR recovery acceptance | HIR module lowering → `validated_recoveries` → partition / attachment / `ErrorSink` | Establish which recovery classes attach to bindings, direct items, module errors or values, which conditions return `Err`, and which recovery-bearing paths still return `Ok(hir)` and their top-level Binding count. |

The following source-to-result chain must be justified using only the r2 view:

`fixed source → header/root parse and recoveries → exact returned ParsedFile →
HIR lowering and recovery handling → returned HirModule.items() → Binding count`.

Every normal successful route through this chain must be covered. A permitted
two-Binding `Ok(hir)` is decisive counterevidence and ends the census attempt.
An owner gap or unclassified recovery return is `UNRESOLVED`, not a pass.

## Sol gates, leases, and resource accounting

Producer is stopped Sol `/root/sol_r274_source_acceptance`, requested
`gpt-6-sol/high`. The original R279 stage 1 was charged 200 seconds and
returned INCOMPLETE. Cumulative Sol charge before r2 is 11,600 seconds. This
new contract explicitly re-reserves the canceled future work without refund,
reset, or double counting:

| Component | Seconds | Gate |
|---|---:|---|
| R279-r1 stage 1 | 200 | Charged; STOP/INCOMPLETE, preserved |
| R279-r2 owner coverage and integrity | 200 | Fresh hash, WAITING acknowledgement, Luna GO, fresh resume; no census proof or output writes |
| R279-r2 census derivation | 800 | Separate Luna GO only after r2 owner gate passes; begin with fresh resume; exact two output leases below |
| Fresh independent review | 900 | After producer freeze; independent source-first review of the complete source-to-census implication, recovery propagation and R278 guard application |
| Luna preparation/adjudication | 300 | Source-view preparation, stage gates, adjudication, records and integration |
| **Total** | **2,400** | No extension or reset |

R2 owner gate scope: first match this contract and the versioned r2 admission,
then return a fresh current-session WAITING acknowledgement. Luna revalidates
the direct contract/admission/source pins and every inventory, range, payload,
offset, bound, nonoverlap, byte-equality and view-length relation before GO.
After GO and a fresh resume, Sol independently checks all 229 inventory entries,
all 46 payloads, and caller/callee coverage for all five edges. Return READY or
INCOMPLETE with an exact missing owner/edge. No census derivation, output write,
or outside-view read during this 200-second gate. Charge the full reservation
on issue; cumulative Sol charge becomes 11,800 seconds.

Only a completed r2 READY permits Luna to issue a separate 800-second proof GO.
The derivation starts after a new resume acknowledgement. Sol must return
`SOURCE_PIPELINE_ROUTE_EXCLUSION`, `COUNTERCASE_TO_CENSUS`, or `UNRESOLVED`,
with the source-to-census equations and normal-return accounting. Cumulative Sol
charge becomes 12,600 seconds. If owner coverage is incomplete, stop; do not
spend the 800 seconds rediscovering an omitted owner.

During the proof stage only, exact output leases are:

- `notes/theory/2026-11-03-source-hir-census-r279.md`
- `tasks/agent-loop/inbox/source-hir-census-r279.md`

No other write path. No tests, builds, probes, Cargo, Lean, execution, broad
search, caller search, fixture substitution, code edits, generated/scratch/cache
outputs, external paths, or semantic changes. Read only the exact indexed
production payloads; do not inspect the fixture-only payload.

After the producer freezes both outputs, a fresh independent referee receives
900 seconds and no write lease. The review must independently reconstruct the
source-to-census implication, recovery propagation, and application of R278's
reviewed guard; repeating only the conditional count guard is insufficient.
The reviewer must not read tests or the fixture-only payload. Luna retains the
300-second preparation/adjudication allocation.

## Closure boundary

This packet can at most exclude the fixed witness from the specified public
experiment. It cannot close the unchanged Parent/A/B obligation or establish
independent `Need_D`, R70/R71 canonical-fiber coverage, accepted-source
soundness, F1/FK1, foreign continuations, or whole-language closure. Parent/A/B
remains **0→0**; `Need_D`, R70/R71 and full soundness remain **OPEN**; no safe
implementation slice exists (`NO_SAFE_CODE_SLICE`).
