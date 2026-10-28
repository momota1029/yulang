# NATIVE-FRESH-USE-CONTEXT-COVERAGE/r5 proof handoff

Assignment `/root/native_fresh_use_context_coverage_proof_r5`, revision 1.
Session `NATIVE-FRESH-USE-CONTEXT-COVERAGE-20261028/r5`.
Contract SHA-256 `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa`.
Primary baseline `1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`; research base
`bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (contract identities, no Git query).
Requested Sol/high; observed model/effort UNKNOWN. ACK was sent before source
body reads. One author, no descendants. Exact leases are this handoff and
`notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR5.lean`.

Outcome: **candidate, constructed but UNCHECKED; fixed outcome INCOMPLETE**.
No successful reachable source/native counterexample is established. No kernel,
axiom-audit, independent-review, source-correspondence or production acceptance
is claimed. The first unproved source interpretation is identified below.

## Governing sources and preserved parent

Read the actual original statement in
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5
(SHA `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`),
with `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6
(`ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`)
and corrected theory §§1,3,6
(`67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`).
The original Simple-sub PDF is located by the manuscript's explicit reference
`/home/momota1029/rust/simple-sub-reference-paper.pdf`, §§3.5.1–3.5.2,5.3;
its body is outside this packet's admitted source list and was not read.
No fact is newly attributed to an unread PDF.

The actual `YulangClosure.SourceProblem.InferenceSoundness` definition is:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`Contracts.lean` SHA
`2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
The same shared `e`, supported domain, lexical/type/event scopes, optional
records, method selection, complete Call, effects and generalization remain
unchanged. No concrete `SourceProblem` instance is constructed here.

Selected annotation policy §§1,1.1,1.2,3,4 read at SHA
`a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`:
contravariant concrete annotation is local subtraction permission; covariant
annotation permits a concrete effect; actual inflow, residual, symbolic
connections and handler subtraction remain separate. Read
`OriginalEffectHygiene.lean` constructor/consumer seam at SHA
`926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`;
its whole interpretation premises remain open.

R4 review/outcome were read as rejected/unchecked research, not imported or
used as semantic authority. No other R5 lane's artifact was read or imported.

## Artifact, declarations and source mapping

Lean artifact SHA-256:
`3878c3c4039f33eb938bc2450f9ae5ee5329309f5ac711891869e9986c773146`.
Only direct import: `YulangClosure.Contracts`. No root import edit.
Namespace prefix for every name below:
`YulangClosure.NativeFreshUseContextCoverageR5`.

The file contains **31 authored theorem terms**, all unchecked:

- `put_same`, `put_other`: exact functional map insert reads.
- `rebuild_identity`, `rebuild_prefix`, `rebuild_suffix`, `rebuild_swap`,
  `rebuild_both`, `rebuild_replay`, `rebuild_without`: each corresponding
  branch's constructor equation, retaining successful child, payload and
  certificate lookup premises. These premises are local Rust reads, not
  all-image observability or domain conclusions.
- `fresh_both_fails`: empty FreshUse certificate substitution makes the
  BothFromRight branch return `none`, for every remap/weight map.
- `intern_reads`, `intern_old_table`, `intern_next`, `intern_checkpoint_read`:
  successful reuse/append local actions; old reads preserved for IDs below
  `before.next`; checkpoint reads preserved when `cutoff < before.next`.
- `step_exact_verified`, `run_exact_verified`, `fresh_initial_exact`,
  `fresh_no_unverified_seed`: derive `(∃ copy, remap key = some copy) ↔
  key ∈ verified` from an initially empty map and concrete local map writes;
  seeded validation of an unverified key is unreachable in that fresh model.
  **This is not the required source-reachability exact-domain theorem.**
- `discharge_raw_key`, `discharge_context`,
  `discharge_effective_nonzero`, `discharge_effective_zero`,
  `discharge_other_effective`: explicit discharge write footprint.
  Zero residual requires absence of an old residual; the model does not
  silently assume the native journaling invariant that supplies that fact.
- `identity_not_stored`, `selected_relation_discharge_iff`,
  `selected_context_discharge_iff`: logical identity has no stored row;
  raw-context/dependency selection is unchanged by pure discharge writes.
- `attached_prefix_weight`: a root relation whose raw root is a nonzero
  PrefixLeft directly derives selection of that node's weight. It does not
  assume node/weight selection, but does require the actual attachment.
- `transport_keeps_parent_raw`, `reused_key_context`: a selected child and
  retained Transport edge select the raw parent; full-key reuse preserves
  context equality. Equality of canonical endpoint pair alone is insufficient.
- `effective_root_can_change`, `raw_root_survives_that_change`: explicit
  local configuration with PrefixLeft root 1 and discharged effective root 0.
  This is a countermodel to effective-root stability from append-only storage,
  **not** a reachable native trace or a Yulang counterexample.

Source pins authenticated with `sha256sum` (all matched the contract):

| Source | SHA-256 |
|---|---|
| candidate_context.rs | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| candidate_scheme.rs | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| candidate_extrusion.rs | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| NativeFreshScopeTransport.lean | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| NativeScopeTransformer.lean | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |

Exact Rust mapping:

- `candidate_context.rs:1566–1677`: RenameStep models outer root, verified skip,
  checkpoint-bounded read, strict child order, omitted verified-child push,
  ready marker, all seven rebuild cases, existing-map validation and publish.
  `context_payloads:1696–1728` rejects BothFromRight in FreshUse discovery;
  generic rename still represents it. Allocation/resource failures and error
  rollback are omitted because this packet concerns successful executions.
- `candidate_context.rs:2629–2661`: `Intern` preserves old-ID reuse and append;
  actual `context_keys`/table coherence remains an interpretation obligation.
- `candidate_scheme.rs:4415–4448`: capture roots via `relation_context`, prepare
  weights, then invoke rename with initially empty remap.
- `candidate_scheme.rs:4701–4704`: later admission RE-READS the effective parent
  root before lookup. No equality with the earlier preparation root is assumed.
- `candidate_context.rs:3062–3101,4278–4294`: full-key interning, canonical
  target pair, explicit copied Context, retained FreshUse Transport edge.
- `candidate_extrusion.rs:965–1065` and
  `candidate_context.rs:3992–4075`: restoration uses live canonical owners and
  Replay fibers; Replay reads raw lower/upper contexts and may reuse interned
  Context/relation keys. The full closure of those effects is not formalized.
- `candidate_context.rs:3297–3303,3799–3887`: effective root selects discharge
  residual; zero-word checking can write discharge and residual state.
- `candidate_context.rs:1167–1237,1090–1096`: final retained selection reads raw
  relation.key.context and follows both directions of dependency incidence,
  then Context children/weights. Stored contexts omit ID 0.

## Parent application and exact remaining obligations

The pure-discharge frame removes discharge-table writes themselves as a cause
of loss of an **already attached raw Context** in the stated closure projection.
It does not derive attachment of every prepared image. The original source
parent obtains no completed instance from these candidate terms.

First unproved successful native branch interpretation:
`candidate_context.rs:1662`, `self.context(node)?`, requires an invariant tying
`context_keys` lookup at :2642 to the table and its dense next ID at :2645.
`Intern` describes those successful actions, but no theorem derives that
invariant from every admitted native construction history. The rest of the
Rust driver has also not been interpreted as `RenameRun`; exact transitive
source-reachability domain and native final-mask loop interpretation remain open.

First decisive restoration premise, owner primary native/proof integration:
for every not-yet-admitted captured parent p, classify earlier restoration
children that can discharge p through Replay/full-key interning aliases. If
`post_check_context(p)` changes before its later :4701 re-read, prove that its
originally prepared renamed image remains attached to some relation selected
by the authentic completed module/local readback, or produce the exact
successful reachable source trace where it is omitted. A selected original
parent raw context is not automatically its separately prepared image when
weight copies differ. This premise is neither assumed nor discharged here.

Mutual TODO `R5-NATIVE-INTERPRETATION-1`: primary owns native construction-history
coherence, full driver interpretation and final-mask connection; inputs are the
frozen source pins above; falsifier is a successful source execution outside the
local action projection. TODO `R5-RESTORATION-ALIAS-1`: classify those actual
earlier-child aliases and retain the first prepared image that loses attachment;
require authentic completed readback, not a supplied selected-root set.
No new dependency/lease is requested or presumed. Whole inference soundness,
A/B, effect hygiene, principality, termination and production remain OPEN.

## Commands, verification, resources and STOP

Actual commands: bounded `cat`, `sed`, `rg`, `sha256sum`, `wc`, file nonexistence
checks, clock reads, and `apply_patch` on the two leases. Observed shell command
exits were 0. No tests, probes of compiled behavior, Git, Lean, Lake, checker,
version executable, network, descendants, cache or generated-output writes.
Actual checker diagnostics/goals, printed theorem types and axiom results:
**NOT_RUN**, so no axiom list (empty or otherwise) is asserted.

Read toolchain/configuration: pin Lean 4.35.0; no external packages;
`moreLeanArgs = ["-j1", "-M1024"]`.
`lean-toolchain` SHA `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
`lakefile.toml` SHA `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
`lake-manifest.json` SHA `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`;
README SHA `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`.
These are configuration observations, not tool-runtime receipts.

Primary-only handoff after independent acceptance and authorization: run the
skill checker on module `YulangClosure.NativeFreshUseContextCoverageR5`, repeat
`--theorem` for all 31 fully qualified names enumerated above, inspect every
printed type and complete `#print axioms` output. Resolve installed Lake
read-only before invocation; use the primary-owned isolated scratch/cache
`notes/theory/lean/.task-tmp-native-fresh-use-context-coverage-r5`. This handoff
does not grant or perform those checks.

Grant 1,000 seconds, no renewal. Exact total active duration/CPU/RSS UNKNOWN;
known clock observations include 07:28:07, 07:29:25, 07:31:40, 07:33:01,
07:34:08 UTC on 2026-10-28. Primary retains the full reserved grant for accounting.
No check attempts consumed. No scratch or generated paths created. No runtime
failure log exists because execution was contractually deferred; the material
failure evidence is the unproved source/native and restoration seams above.

**STOP: both leased artifacts frozen; writes stopped; no descendants or
outstanding generated-output leases.** Pending independent review and primary
adjudication; not self-certified or commit-ready as a closed proof gate.
