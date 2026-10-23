# Source derivation and receiver lifetime — outcome

Sprint: SOURCE-SAFETY-20261023, contract revision 2.
Contract: `tasks/agent-loop/sprints/source-safety-20261023-rev2.md`, SHA-256
`ef97bfef1c00c9126a85187d17928129d1c3b81bfb609adb02cc7f018071e1e7`.
Revision 1 is retained unchanged, SHA-256
`6a9a4a7b14179340cd302b39d8e44fdd3fe937d10b05aad4817f518fe0ed351b`.
Baseline: `6bf6ec8a82eadaa75467e896f5a2658d0c3f12f8`.
Author: this primary only. No children, dispatcher, independent reviewers or
nested CLI. Claim class: **unreviewed paper construction and an explicit
source-owner-model discrimination**. No original A/B or production gate closes.

## Applied to the original parent

The user requested closing the source-to-plan gaps after the explicit typed
core safety work. The new manuscript is `docs/yulang-source-type-safety-ja.tex`:

- Sections 1--3: source declarative rules for universal payload introduction,
  rigid checking, pattern/field retrieval and per-use instantiation. A generated
  constructor callable retains ordinary Call/receipt/argument forcing; it is
  not silently replaced by caller-side evaluation. The source elaboration
  theorem constructs execution-type derivations from finite source, direct,
  role and selection derivations, rather than assuming finished typed code.
- Section 4: the old uniform resumption rename differs from the previously
  reviewed source-owner realization. An explicit one-parameter named source
  worker emits P, then handles its callback's Q; an outer P handler resumes it.
  Renaming the old Boundary receiver to the fresh resumed owner retains a
  protection which the fixed-receiver source-owner machine expires. This is
  a paper discriminator, not an executed compiler/VM counterexample or a Bad
  state. Old execution-type safety is not refuted.
- The candidate repair separates immutable evidence identities from control
  slots; active owners are borrowed, inactive control spans get fresh owners,
  and old receivers/targets/release state are not copied into renewed authority.
  Value preservation/progress, finite transfer and refined safety are written
  for the repaired machine. Existing effect inclusions must be regenerated.
- Section 5: an actual receipt creates an origin inventory; typed transport and
  target queries construct receiver tables from it. The missing producer of a
  source recipe and the selection of multiple input occurrences are explicit,
  not hidden inside an arbitrary well-scoped-table premise.
- Sections 6--7: direct `compose f g x = f (g x)` initially exposes a bad choice
  of owner: f's invocation is outside the active context by the time its
  request reaches compose's marked output. Existing reviewed named-frame
  research instead identifies x's terminal frame as the actual static owner.
  The direct Var/Arg/Unannotated/Defined guards and group-range condition were
  read at the pinned Oracle source. The manuscript supplies an EnterGroup
  realization, same-packet Stamp/Protect transfers, and Theorem 7.4 for the
  source-derived origin/receiver/target and the whole-output identity case.
  This is a candidate realization for the direct named-group case, not a new
  authoritative group/lifetime architecture or a general inference theorem.
- Section 8: rank-2 field/method use and qualified evidence application compose
  with the repaired/group machine. Fixed-snapshot first-success determinism is
  distinguished from global resolver uniqueness and snapshot correctness.

Both earlier manuscripts now point out the lifetime dependency and the need to
recheck their effect derivations; their old bytes stay available at the baseline.
No authoritative source, compiler code, test or expected output was changed.

## Authority and remaining premises

The 2026-10-15 forwarding decision explicitly leaves concrete suspension,
escape and resumption representation open. The discriminator is against the
existing source-owner realization's unwind/enter rules, not a claim that all
possible suspension semantics have already been selected. The repair remains
candidate; Draft representation is not promoted to Authoritative.

A source interpretation choice was found to affect actual meaning and
was asked through the asynchronous user-input tool: if two distinct input
occurrences share the same lexical 'e, does output 'e? select both origins or
require an input-specific choice? No answer was received before manuscript
freeze. The manuscript leaves the source selector A_m pending and does not
implement either branch. Different binders/instances remain distinct even when
their row types coincide. The direct compose construction has one source key for
e and does not depend on the unresolved two-input interpretation.

Remaining original obligations:

1. General source origin construction through non-Var callees, aliases,
   anonymous/returned functions, arbitrary captured owners and source expansion.
   The known direct-versus-Block callee discriminator from the reviewed note is
   retained. Rejecting those ordinary sources would not close the parent.
2. The complete nonexpansive/value-generalization classification, including
   constructor applications, beyond the displayed rank-2 payload construction.
3. Full role impl uniqueness, compact/raw matching, reachable snapshot and SCC
   publication correspondence. Typed selected code alone cannot prove these.
4. Complete surface/declaration-to-13-expression/11-pattern lowering, inference
   principality/completeness/termination, compiler acceptance, VM/native and A/B.
5. Fresh independent review and mechanization of old and new paper arguments.

Thus this is substantive source/value construction and a direct compose bridge,
not whole-language closure and not a claim that only implementation remains.

## Direct dependencies and exact source reads

The original user document remains SHA-256
`28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
Prior core and selection hashes are pinned in the manuscript and rev1 contract.
Additional authorities/reviewed inputs are pinned in rev2. Source-owner
realization sections 2--3 and charter section 13 govern the lifetime comparison;
2026-10-05 approved release crossing q1/d1 governs actual crossing and live-target
reuse. The 2026-10-15 compose and callback-forwarding decisions both remain intact.

Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` reads:
`poly/src/expr.rs:478` (13 expression constructors), `lowering/expr/tail.rs:741`
(direct omitted-call producer), `:801` (frame selection), `:845` (Var guard),
`:1058` and `:1092` (whole body/value discharge). An earlier historical locator
placed the latter functions in lambda.rs; the actual pinned read found them
in tail.rs, and the manuscript uses the correct owning file.

Current native owners inspected read-only: `yu-hir/module/local_source.rs`,
`yu-hir/module/source_annotation.rs`, `yu-solver/candidate_source.rs`.
Annotations are already retained in the current source carrier; the older
2026-10-10 observation of missing retention is not reused as a current fact.
The native carrier's value grammar and the omission-evidence/receiver-attachment
seams do not establish this full proof. NO_SAFE_CODE_SLICE under proof-first scope.

## Frozen artifacts and document checks

Manuscript freeze clock: 2026-10-23 15:12:17 UTC.
Primary observation start: 14:30:31 UTC, 2,506 seconds to freeze within 7,200-second
cap. Earlier startup reads preceded that observation; no worker budget is claimed.
Runtime model/session metadata UNKNOWN. No agent execution is inferred from a
configuration. Four previous UNKNOWN workers and their quarantined paths remain
reserved; live list_agents showed only this root.

| Artifact | SHA-256 | PDF |
| --- | --- | --- |
| `docs/yulang-source-type-safety-ja.tex` | `dc165671ef3ceaa2692503723c2607df5395e59d7421d45dfff46abe7668aca2` | 18 pages |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` | 44 pages |
| `docs/yulang-dot-selection-safety-ja.tex` | `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b` | 23 pages |

PDFs/logs are under `/tmp/yulang-source-safety-20261023/`, with op/ and dot/
subdirectories. Final XeLaTeX outputs have no warnings, undefined references or
overfull boxes. Source retains 5 underfull paragraph notices (long locators),
operational retains 10, selection none. Source PDF pages 7 and 15 were visually
inspected. Label inventory has 24 unique labels and no unresolved internal refs.
`git diff --check` passed before freeze.

An interim static state check rejected a RUNNING root with unavailable session
metadata. No fake session was supplied. At freeze the root records actual
manuscript authoring cessation. A second check rejected the 16,675-byte canonical
JSON form even though the compact file was 16,083 bytes; redundant frozen-lease
and resolved-history prose was shortened without removing any reservation,
pending gate or receipt locator. Final size: 15,238 file bytes, 15,830 canonical
checker bytes. `python3 tools/agent_sprint.py check`: STATIC CHECK PASS.
Direct comparison to baseline confirms the same four UNKNOWN rows and all
quarantined leases; manuscript/user hashes and all internal reference labels
were checked. These are static/document receipts, not independent proof review.
Compiler builds/tests, executable proof probes, Oracle/VM execution, independent
review and mechanization: NOT_RUN. Document rendering is not mathematical proof.

## Integration boundary

This is an unreviewed research preservation checkpoint. Primary manuscript writing
has stopped; remaining activity is exact record/Git integration. No background
continuation is launched. Stage only the three manuscripts, two contracts and
this outcome for the research checkpoint; then synchronize current.json and the
current-direction paragraph without changing original A/B records. Preserve all
original untracked user and quarantined R349 artifacts. Inspect the outbound range
before a non-forced current-branch push. A later user answer or proof repair needs
a new revision; frozen bytes are not silently claimed reviewed.
