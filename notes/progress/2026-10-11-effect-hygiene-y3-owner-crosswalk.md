# Effect hygiene: current Yulang3 owner crosswalk

Date: 2026-10-11
Status: frozen, unreviewed research checkpoint; parent and admission gates OPEN
Claim class: bounded static source ownership characterization
Yulang3 baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`
Supplied Oracle revision: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only; no compiler/test/shared-record writes

## Objective, authority and hypotheses

Locate the first missing compiler edge between an Oracle-qualified negative
annotation occurrence and its actual call/output consumer, then identify the
existing downstream owners of replay, generic use, extrusion, intrusion and
private result observation. This is a locator/handoff artifact. The existing
[singleton proof boundary](../theory/2026-10-11-negative-formal-effect-source-proof.md),
[covariant bridge](../theory/2026-10-11-oracle-effect-hygiene-source-bridge.md), and
[current-source falsification](2026-10-11-negative-formal-effect-current-source-falsification.md)
retain their claims; this note supplies no repeated Oracle theorem or new probe.

Exact governing sections:

- [Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
  §§1–5 and Authority and integration: native generation/propagation and proof
  correspondence; necessary abnormal-path safety only.
- [Annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1–5: composed-negative local concrete subtraction, composed-positive
  allowance, connected symbolic variables, original boundary ownership and
  surviving independent contributions. §6 retracts the old callback result.
- [Concrete implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md),
  Annotation checking and publication owner, Conflict ownership and replay,
  and Practical formation and reconstruction envelope: actual exposed/checking
  interfaces, one semantic pair authority, original provenance and mapped tails.
- [Contextual admission](../design/2026-10-10-contextual-attachment-admission-design.md)
  §§3–4: per-occurrence atom-set identity, ordered context and actual transport
  owners; §§5–6: bounded internal gate and explicitly disabled general concrete
  formal acceptance. Top-level principles supersede unconditional rollback.

Hypotheses for the static result: inspected dependencies retain the hashes below;
HIR has formed the resolved annotation tree; the private entry is
`CandidateInference::solve`. Literal Y3 parsing, candidate execution, complete
Call/provider correctness, successful universal replay and binary correspondence
are not assumed. The supplied Oracle revision and previously recorded dump are
inherited evidence, not independently rebuilt or rerun here.

## First irreducible mismatch

Use the already qualified one-function witness, without adding a provider body:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> [tick] ())) = cb ()
```

The prior Oracle observation prints `(() -> [tick] ()) -> ()`. This is Oracle
syntax; the previously identified Y3 spelling uses `act`, `our`, and a space
before the formal. This lane does not claim executable admission of either
literal spelling in Y3.

Static derivation: formal preflight starts Negative
(`candidate_source.rs:98`); Function result descent preserves the sign
(`119`); the row therefore has `positive=false`, one concrete member and zero
variables. Predicate `row.concrete.is_empty() && row.variables.len() == 1`
(`118`) fails. `shadow_apply.rs:92` returns this rejection before collection.
The paired owner independently repeats the rejection
(`candidate_effect.rs:1035`), before producing the four-port pair. Removing
only entry preflight therefore leaves the constructor unavailable.

This is the first irreducible construction/admission mismatch. Investigation
stops at that seam: downstream entries below identify existing owners and the
premises a future handoff must supply; they do not establish feasibility of a
new implementation or prove a negative attachment that is never constructed.

**Technical gap:** no composed-negative concrete formal pair is emitted, hence
no actual attachment from this row can reach its binder's call/output consumer.
**Authority blocker:** contextual admission §§5–6 explicitly keep concrete
formal acceptance disabled until the later admission gate. The selected meaning
is already settled; this restriction is an implementation boundary, not a
semantic question or permission to keep rejecting ordinary inputs permanently.

## Constructor, transport and result-owner crosswalk

Locations below are in `crates/yu-solver/src/` unless prefixed with `yu-hir`.
An owner is an integration locator, not evidence that the missing transition
exists. All call/output statements for the rejected witness are prospective
paths through existing admitted-source machinery.

| Stage | Exact production owner / source location | Retained fact and missing correspondence |
| --- | --- | --- |
| Resolved occurrence | `yu-hir/src/module/local_source.rs:289` parameter construction; `source_annotation.rs:367` annotation; `parse_row:505`, resolution `538–551` | Retains binder, lexical scope, definition owner, exact annotation/row keys, separate variables and declaration-resolved operands. These facts supply source identity; they do not supply operational subtraction eligibility. |
| Formal action | `candidate_source.rs:270–282`, `execute_candidate_action:660–663` | Records actual parameter level and schedules FormalAnnotation before its body. The rejected witness does not execute this schedule. |
| Paired constructor | `candidate_effect.rs::candidate_formal_pair:1034`; `candidate_formal_effect_port:1054`; `candidate_formal_annotation:1073` | Starts Negative (`1090`), reverses argument and preserves result (`1045–1049`), emits paired Value links (`1101,1105`) and retains the negative formal domain (`1106`). The negative concrete branch is absent. This is the first implementation/proof owner. |
| Same source Call | `candidate_source.rs:394–411`; `shadow_apply.rs::admit_candidate_fact:1304`, NativeInterface `1378–1381`; `candidate_call.rs:390–426` | Retains actual callee/argument/result/application effect, checks input incidence, builds a Function demand and records formal linkage. `PendingCallConstruction` (`candidate_call.rs:213`) remains pending; linkage alone is not complete provider/output semantics. No binder-local subtraction activation is emitted in this owner. |
| Invocation into body effect | `shadow_apply.rs:1343–1362,1422–1439`; Function port owner `candidate_context.rs::candidate_function_port_admit:2557` | Allocates actual invocation row J; J and callee evaluation flow into application B. Argument ports Swap; result ports Preserve (`2576–2606`). Existing context transport cannot create a missing annotation operation. |
| Owning function output | `lib.rs::admit_lambda_fact:11233`; formal domain `11242`; body/entry flow `11263–11342` | Creates latent returned row O, admits B and entry into O, and constructs the positive Function. This is the direct inference result consumer for local subtraction, with returned Value obligations as well as Effect obligations. The inferred-entry record supplies no annotation subtraction permission. |
| Current/future lower activation | `candidate_extrusion.rs::candidate_apply_effect:840`; `candidate_replay_bound:763`; `candidate_context_begin_replay:2911` | Physical orientation follows levels, insertion enumerates opposite bounds, and newly retained fibers meet ordered opposite fibers (`2933–2969`). Both new-lower and new-upper arrivals enter this machinery. No all-history negative attachment invariant follows from these existing loops. |
| Actual check/discharge | `candidate_effect.rs::candidate_check_effect_operand:888`; `candidate_context.rs::candidate_context_execute_relation:2744`, `candidate_zero_word_filters:2613` | Support expands members/tail; Allowance accepts matched atoms or forwards the unchanged unmatched atom to its tail. Closed zero-word filters register/replay Allowance (`2769–2798`). These are checks; neither owner emits attachment-qualified subtraction or lineage-owned residual/gamma construction. |
| Replay completion | `candidate_context.rs::candidate_context_consume_replay_child:3060`, `candidate_context_drive_replay:3110` | Queued children are owned by the typed drain; Queued is not Complete (`3117–3121`). A later handoff must prove actual child discharge, not merely batch generation. |
| Capture and fresh use | `candidate_scheme.rs::capture_candidate_graph:691`, payload/bundle capture `750–799`; `freshen_candidate_graph:965`, `prepare_candidate_fresh_use:981`, `begin_candidate_fresh_bound:1221`; actual Local route `1373–1374` | Captures reachable bound contexts and bundles; per-use mapping reconstructs Support/Allowance/member views (`1054,1062`), freshens contributions (`1064–1067`), remaps context payloads (`1089–1106`) and restores bounds. Coverage of a future negative relation/filter/residual graph and independent local authority remains unproved. |
| View/level extrusion | `candidate_effect.rs::candidate_copy_effect_view:806`, `candidate_remapped_effect_view:832`; `candidate_extrusion.rs:265–319` | Preserves owner, position, nominal members and attachment-source fields; keys reconstruction by original view/mapped tail and transfers bound origins. This existing covariant carrier is not proof of complete negative attachment/recipe transport. |
| Qualifying intrusion | `candidate_intrusion.rs::settle_candidate_intrusion:358`, SCC qualification `479–486`; `merge_candidate_rows:513–605` | Merges actual recorded parent/copy pairs in one SCC; transfers both bounds and origins, canonicalizes, then replays lowers (`548–603`). Row equality must preserve distinct attachment/recipe identities. Current/future fanout to not-yet-constructed negative residuals remains a missing premise. |
| Private final observation | `candidate_scheme.rs:891–900` graph capture; `lib.rs::run_candidate:10361`, `finish_candidate:10368`; `shadow_apply.rs::CandidateInference::export:123–147` | Captures root Value graph containing four Function ports; finishing asserts no closed public types/schemes. Export rejects conflicts and wrong roots/missing graphs. This is a private graph observer, not production/runtime effect removal or public F5 cutover. |

## Explicit guards and disabled consumers in this scope

The relevant independent barriers are formal root computation rows
(`candidate_source.rs:98`, `candidate_effect.rs:1076`), negative concrete or
non-singleton-variable formal rows (`candidate_source.rs:118`,
`candidate_effect.rs:1035,1068`), general negative concrete signature rows
(`candidate_source.rs:125`, `candidate_effect.rs:1507`), and multiple symbolic
tails (`candidate_source.rs:125`, `candidate_effect.rs:1510`). These guards are
not all one removable preflight.

Live `LocalWeight.left_word/right_pops` have type `[(); 0]`
(`candidate_context.rs:115–118`). `source_weight:2174` stores empty words;
`unit_push` is dormant positive-source preparation (`2187`). The explicit
detached adapter `materialize_unit_push:2200` produces no live relation/bound/
registration (`2197–2199`). The live filter consumer requires empty words and
an actual matching closed boundary (`2651–2654`), and rejects filter-bearing
Value work (`2757–2759`). Detached arithmetic cannot supply the missing live
producer/consumer edge. General mixed-component admission and Catch/complete
Call are separate unresolved owners under contextual admission §§1,5–6;
they were not expanded into this audit.

Full-scope gaps retained: every actual negative occurrence, correlated symbolic
tails, all applicable current/future lowers, independent same-family instances,
complete same-call provider/output incidence, latent returned Value use, exact
residual/gamma lineage, fresh-use graph completeness, extrusion and qualifying
intrusion preservation, general contextual termination and production publication.
The successful covariant slice does not close these quantifiers. No new language
meaning, representation decision or general rollback obligation is proposed.

## Evidence, independence and next action

Commands: bounded `cat`, `sed`, `nl -ba`, `rg` source/authority reads and
`sha256sum` snapshot/recheck. No build, test, executable experiment, Oracle run,
mutation, seed/range enumeration, benchmark or delegation. Several initial broad
captures truncated; decisive predicates and cited lifecycle/export excerpts were
read again with bounded ranges. This static lane has no independent oracle or
transition checker; it depends on the supplied reviewed Oracle evidence and
shared accepted policy. Source-to-binary correspondence and all unexecuted paths
remain unverified. CPU/RSS and total wall time were not instrumented; shell work
was lightweight, with no heavyweight process. No numerical resource budget was
specified by the packet.

Workflow exception: the initial orientation command used read-only `git status
--short` and `git rev-parse HEAD` despite the packet's no-Git instruction. They
reported an empty status and the assigned SHA; no Git mutation or subsequent Git
command occurred. This is disclosed, not counted as compliant verification.
Equality of the inspected bytes to pinned baseline blobs remains primary-owned.

Recommended next action: assign the existing NEGATIVE-FORMAL-SOURCE-STEP premise
to a coupled constructor/same-call/output proof handoff at the first three solver
owners in the table, using the existing singleton lemma and original quantifiers;
retain the later admission gate OPEN. Authorize only the smallest reversible
source-evidence slice if that proof requires it, under the existing authority
process. Do not schedule general enabling from this locator artifact alone.

## Dependency snapshot and commit packet

SHA-256 identifies inspected file bytes, not Git object identity.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/theory/2026-10-11-negative-formal-effect-source-proof.md` | `262c2569935c30a369846f50fede295d7f024677dca203b5d11e56ed6484f856` |
| `notes/theory/2026-10-11-oracle-effect-hygiene-source-bridge.md` | `51be142a399a4c1b65281292141c0d12b65b3996f960f5d4962423aec024ebb8` |
| `notes/progress/2026-10-11-negative-formal-effect-current-source-falsification.md` | `e593817a959e098d0bfe789dc8a4d86d26abcf2f86f58b7778fb07d7189595e6` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |

Commit packet:

- Exact leased/change path: `notes/progress/2026-10-11-effect-hygiene-y3-owner-crosswalk.md` only; frozen, writes stopped before submission.
- Baseline: `b37bfab842dd3f0a39d15c358399a068ff8e3194`; supplied Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency hashes changed during this lane: none observed on freeze recheck; no dependency edited. Baseline-blob equality remains primary-owned.
- Review status: unreviewed bounded static characterization; no independent certification, theorem/admission/implementation closure or production authority.
- Checks already run: bounded exact owner reads, dependency SHA-256 snapshot/recheck and note whitespace/local-link integrity; no builds/tests/Oracle execution.
- Proposed one-line checkpoint message: `research: map effect hygiene Y3 constructor and consumer owners`.
- Shared-record deltas intentionally left to primary/curator: link the first constructor/admission seam and downstream owner handoff; keep NEGATIVE-FORMAL-SOURCE-STEP, full hygiene, complete Call, soundness/principality and F5 OPEN. No task/index/authority/theory-status or question-board file changed.
