# FORCE-DECLARATIVE-CONSTRUCTION-20261025/r10

Status: **FROZEN BY LUNA; N and R source-construction assignments issued.**
Fresh ceiling 6,540 seconds; no r9 carryover. The goal, accepted source domain,
quantifiers, expected outputs and semantics remain unchanged.

## Authority and pinned inputs

The original goal is complete Lean proofs of Yulang semantics and type
inference for the unchanged accepted source domain. r7's checked abstract
`abstract_observe_counted_run_iff` is valid only for its fixed arbitrary
`H`, `beta`, and `inst`; it does not instantiate a source View packet.
The r8/r9 reports are bounded obstruction evidence, not semantic rules.

| Input | SHA-256 |
|---|---|
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/YulangClosure/ForceAdmin.lean` | `620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97` |
| `tasks/agent-loop/sprints/force-admin-result-discharge-20261025-r7-outcome.md` | `b89cbb133006aaae4563789460466ddc790df1460418f124dee36d86b5558d29` |
| `tasks/agent-loop/inbox/20261025-force-packet-specialization.md` | `7492d74c018645394f54559695cc0f7b3278edce2fbd34eb6f20b06504be0f76` |
| `tasks/agent-loop/inbox/20261025-force-result-relation.md` | `9972764cc9b750fa5fc218b1c571fd29b58ffb46f6a7bc0e566aaaa4e1bfb430` |
| `tasks/agent-loop/inbox/20261025-binder-packet-export-trace.md` | `5c0ca8b96c5d5aa5093adae85f917269c0343bfe26c63efded2736f7b5007bd2` |
| `tasks/agent-loop/inbox/20261025-force-runtime-return-trace.md` | `208834c17ad78d4994cf9596bc9f6e9fd275691e9f60d2d10c7baaa9d2b321c4` |
| `tasks/agent-loop/sprints/force-source-realization-20261025-r8-outcome.md` | `4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb` |
| `tasks/agent-loop/sprints/force-producer-export-trace-20261025-r1-outcome.md` | `bf544d639797fbecad878095916588d300eddf1e9c786d37786c9ebca01e232f` |

The paper source points for N are §§1.8, 3.1, 4.7–4.8, 5.1 and 7.1–7.3
(lines 1188–1209, 1241, 1541, 1749–1776, 2058–2073, 2244–2263).
For R use the expose/Force, observation, transport and leave clauses cited in
the r8/r9 frozen reports, especially lines 485–494, 553–613, 1244–1245,
1346–1356, 1404–1421, 1528–1532 and the latent example 1994–1998.
Workers must verify relevant clause text in the pinned paper; citation numbers
alone do not establish entailment.

## Proposition N — declarative binder-indexed packet construction

Target: `declarative_packet_opening_correspondence`.

Construct the packet/template interface directly from the accepted typed
derivation. State the binder-indexed opening operation for
`View_c((View_d(Lambda a.v))[T])`, including retained outer packet `c`, one
opening of `a` across all applicable coordinates of `d`, delayed-shape
reconstruction, shared captures, existing free identities and source-indexed
scope/interpretation. Derive each constructor equation toward
`decorate_type_instance_commutes`, or name the exact paper premise that does
not determine it. The arbitrary `inst` parameter from r7 cannot be passed off
as this opening operation.

Exact sole artifact lease:
`tasks/agent-loop/inbox/20261025-declarative-packet-construction.md`.
Grant: 1,200 seconds. Produce a proposition-by-proposition derivation, complete
constructor coverage table, exact unresolved equations and falsifiers. This
stage is declarative/source analysis only: no Lean, tests, builds, compiler or
native execution, production edits, scratch files, Git, descendants or child
teams. Do not claim source/native implementation correspondence.

Discriminators: open type descriptor `U beta`; nested type binder; distinct
outer and inner wrappers; shared captured coordinate; delayed force-result
shape; duplicate ingress entries governed by the same binder. A construction
that drops, duplicates, rebinds or reorders any applicable coordinate fails.

## Proposition R — entailment of Force normal-leave result relation

Target: `accepted_force_leave_entails_result_transport`.

First attempt a derivation of the proposed all-suffix normal-leave relation from
the accepted expose/Force/transport clauses. Do not treat r8's `FR-ROUTE` as a
rule. If the derivation stops, either isolate the exact missing premise or
construct two interpretations satisfying every relevant accepted clause and
all shared typing/occurrence premises that disagree on the returned-thunk
discriminator `force.result.force.effect`.

An underdetermination result is accepted only if each interpretation checks all
clauses in scope, their shared domains/occurrences, and the discriminator.
Two invented transition systems or runtime models with incomplete clause
coverage are not a source countermodel. Preserve the original result
provenance, latent suffixes, domain/image and fresh output occurrence questions.

Exact sole artifact lease:
`tasks/agent-loop/inbox/20261025-force-return-entailment.md`.
Grant: 1,200 seconds. Source/spec analysis only; same prohibitions as N.

## Bounded implementation lane and review

After N/R STOP, Luna spends at most 300 seconds on the already pinned r9
owners: annotation/local-source → solver export, and Delay formation →
RootCompReturn. Report an independently approved end-to-end safe contribution,
or `NO_SAFE_CODE_SLICE` with exact owner and missing certificate. No code edit
is authorized by this lane.

One fresh independent `spec_auditor` reviews N and R after both authors STOP,
up to 600 seconds aggregate (300 per artifact). Source conformance review must
check all relevant accepted clauses, the whole-packet discriminators, model
coverage if claimed, and separation from provisional/compiler evidence.
Reports must be frozen before review; unknown writers retain quarantined
leases. Two new authors maximum concurrently. The three legacy UNKNOWN
reservations remain quarantined.

## Conditional Lean phases

No Lean phase starts from r9 evidence alone. After N/R frozen artifacts pass
independent review, Luna may issue the matching phase under this contract only
when its entry condition is actually met:

1. **N (up to 1,200 seconds):** only if the reviewed artifact contains a
   complete source-selected packet interface and all opening equations. Write
   `notes/theory/lean/YulangClosure/SourcePacket.lean`, prove the exact
   constructor lemmas and `decorate_type_instance_commutes`, run one bounded
   Lean check, and record `#print axioms`. A conditional or assumed packet
   map does not satisfy entry.
2. **R (up to 900 seconds):** only if review accepts a source-derived unique
   normal-leave equation. Write
   `notes/theory/lean/YulangClosure/ForceReturnRows.lean`, derive exact finite
   domains/images and allocation from that equation, run one bounded Lean
   check, and record `#print axioms`. A model-separation result enables no
   theorem phase.

If a phase is not enabled, its grant expires; do not replace it with a different
claim. Proof files are separate exclusive leases. A fresh nonauthor
`prover`/`compiler_referee` reviews any enabled proof output (600 seconds
aggregate), and Luna performs serialized bounded Lean checks only after writer
STOP and frozen hashes (240 seconds aggregate, 1 CPU, 1 GiB, 120-second
process cap). No tests or builds.

## Resources, stop and outcome

Fresh ceiling: **6,540 seconds**, allocated as N 1,200 + R 1,200 + Luna safe-slice
300 + N/R source review 600 + conditional N Lean 1,200 + conditional R Lean
900 + fresh proof review 600 + serialized Lean checks 240 + Luna integration
300. No carryover. No Astra assignment this sprint: R is an independent
source-clause attack and N is a bounded declarative construction; later proof
work can use the exact reviewed interface. At most two author assignments run
concurrently. No tests, builds, native/compiler execution, production code
edits, Git operations, force-push, broad staging or blanket cleanup.

Stop on changed pinned inputs, missing source authority, uncovered constructor,
incomplete model clauses, exhausted grants or source ambiguity. Keep N1,
O-NORM, O-RESULT, implementation correspondence and the original parent OPEN
unless their original obligations are separately established and reviewed.
Success is a faithful reviewed packet construction, a derived Force result
equation or a complete independently checked source underdetermination proof;
bounded obstruction is still a valid outcome but closes no theorem.
