# Frozen handoff: Replay cross-route ownership

Sprint-ID / contract revision and SHA-256:
`npair-replay-cross-route-ownership-20261018` / r1 /
`48f9efa39434561c4c565699468bf22dea35ad406b905f7c44202ab22d08ced0`.

Assignment-ID / handoff revision: `cross_route_owner_audit_20261018` / 1.

Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original scope,
quantifiers, accepted semantics and fixed `c` preserved by the contract's
Fixed outcome and Required report sections. Parent OPEN, original-condition
closure **0 → 0**. No semantic adoption or production authorization.

Baseline: `7704277586c5b5b7dcf5b9b1138c4cb122590165`.
Prior closeout SHA-256:
`bb598941f3444baec8177e50665a22380e1337e858f2a6064359c9c424d83b32`.
All five contract source hashes, candidate/handoff hashes and three runtime
hashes matched. The frozen note's baseline tables contain their exact paths
and full hashes, plus four additional read-only source-owner hashes and the
governing inference-principles hash. No dependency bytes were changed.

Role / actual worker / session / receipt: researcher /
`/root/cross_route_owner_audit_20261018` / current-session / live assignment,
read-only startup ACK sent, then Luna explicitly authorized the two outputs.
Requested Sol/high; observed model UNKNOWN, effort UNKNOWN.
Author and contributing descendants: this worker only; descendants none.

Exact exclusive leases / complete changed-path set:

- `notes/theory/2026-10-18-replay-cross-route-ownership.md`
- `tasks/agent-loop/inbox/20261018-replay-cross-route-ownership.md`

Outcome class: **source-native-evidence**, including a conditional source
derivation and a precise missing observation; neither ownership alternative
has been established. No source-qualified counterexample or theorem closure.

## Result and parent application

The actual capture rule is `local = level > boundary && !non_generic` after
canonicalization (`candidate_scheme.rs:694–731`). Reconstruction recomputes
representatives/metadata and freshens only if stored local and current
level/non_generic still permit it (`1522–1533`). The diagnostic census does
not print graph rows/boundary, representatives, metadata snapshots or route
row maps (`336–347`, `2311–2322`). ValueRow 44 therefore remains unclassified
by this audit at both actual routes.

Retained source/constraint/consumer evidence:

- Module route 0/use 1 owns the selected copied negative Function 299, ports
  `[295,296,297,298]`; native source negative Function 264 has ports
  `[260,262,263,261]`.
- Module route 1/use 2 uniquely retains lower positive Function 310, ports
  `[306,307,308,309]`. Route 0 retains positive Function 290 instead. The two
  use identities remain distinct.
- Lower Relation 58 records `Function310 <= ValueRow44`, identity transformer,
  no demand. Admission 56 records OwnerEmission/processing58; Emission 56
  links it to Value44/ValueLowerAtom/index0 with exact constructor readback.
  Its cause does not name a FreshUse capture/map or source occurrence.
- Replay dependency has child61/lower58/upper35 and selected demand use1,
  root299/output_scope32/input8. Source control flow reaches the later
  positive-function-node-absent rejection, after the upper transport and
  ancestry checks succeeded. The checker therefore returned consumer61 and
  four distinct FunctionPort children with Swap/Swap/Preserve/Preserve and
  required scope transforms. Concrete port relation/transformer IDs were
  not printed; the same-route typed endpoint comparisons were not reached.

The result changes the next evidence request, not the parent status. First
missing premise: actual representative/level/non_generic/boundary/local and
row-map lineage at capture and reconstruction, linked to the emitted lower
owner and both exact uses. Responsible source owners are `Capture::row`,
`prepare_candidate_fresh_use`, lower bound admission/emission and Replay
FunctionPort construction; Luna assigns any implementation/runtime successor.

## Frozen artifact and coverage

Note SHA-256:
`572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308`.
Handoff SHA-256 is returned with submission to avoid self-reference.

Checks run: read-only `rg`, `cat`, `nl`/`sed`, `sha256sum`,
`git rev-parse HEAD`, `git status --short`, and output-path absence checks.
Contract, five source and three runtime hashes were rechecked after note
creation and remained unchanged. No tests, builds, probes, mutations,
runtime commands or scratch writes. Existing diagnostic coverage is one
failed test/run, one emitted Replay row, ten positive Function census entries,
one lower admission/emission. No seeds/ranges apply.

The source and diagnostic share the implementation; they are not independent
semantic oracles. The successful-prefix inference assumes the frozen log
corresponds to the pinned executable source. Binary identity was not separately
authenticated. No actual drain ID/completion, concrete port relation IDs,
source occurrence lineage or ownership classification was verified. See the
note for exact source symbols/ranges, hypotheses, falsifiers and omitted cases.

Resources: 360s author grant, Astra0; no descendants or heavy processes.
Observed audit interval starts `2026-10-18 02:40:28 UTC`; note/hash recheck
timestamp `02:42:24 UTC` (116s observed interval, excluding prior startup and
final handoff preparation). Exact total active wall time, CPU and peak RAM
were not instrumented. Conservatively reserve/charge the complete 360s grant;
no author budget is returned or rolled over from this report.

Mutual TODO `CROSS-ROUTE-OBS-1`: original parent above; obtain capture identity,
source definition/use/occurrence, graph row key/index and metadata at capture;
current representative/metadata and mapped rows at both reconstruction routes;
lower Relation58/admission56 occurrence lineage; and Relation61's four actual
port pairs against both routes' endpoints. Required inputs are these frozen
sources/runtime. Proposed successor output and runtime paths need Luna's exact
lease. Falsifiers: metadata inconsistent with claimed sharing, borrowed flag
inconsistent with claimed required freshness, changed representative omitted
from a map, wrong lower producer, or mismatched FunctionPort endpoints.

Recommended next action: one constructor-owned observation successor under a
new explicit implementation/runtime contract; preserve both uses and semantics.
No further in-envelope work remains once these bytes are frozen.

Worker state: STOPPED; all writes stopped on submission; no unresolved
descendant leases. Independent review NOT_RUN/pending; this author cannot
review its own evidence. Research-only checkpoint is pending Luna's review
and integration; no Git mutation performed.

Commit packet: exact two leased paths above; baseline
`7704277586c5b5b7dcf5b9b1138c4cb122590165`; changed dependency hashes none;
review pending; checks as listed; proposed one-line message:
`research: locate missing Replay cross-route ownership observations`.
Shared-record deltas intentionally left to Luna/curator: record stopped author,
freeze exact output hashes, preserve parent OPEN/closure0, assign fresh review,
then adjudicate the named constructor-observation successor.
