# Question: flat Application owner family

Question ID: `flat-application-owner-family`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `15e83939a`; proposal SHA-256 `61d5fd8e3a359c9ad7fce203ee7927553964b4eeae4a923319aca49a846f826a`
Task/thread locator: unavailable; the active objective is supplied in the conversation context, with no exposed thread identifier
Governing source/section: `rules/design-authority.md`, “Authority order”, “Design status”, and “Approval and implementation gate”; `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`, Gate E; reviewed proposal `notes/theory/2026-10-08-flat-application-owner-completion-decision-object.md`

## Requested scoped decision

Choose the authority direction for the missing flat Application source-owner family used by the successor inference work. This question concerns the source-owner definition only. It does not approve compiler implementation, production cutover, or any change to Oracle-visible behavior.

The user's stated objective is to complete type inference and replace the F5 implementation on the `yulang3` branch. The exact user wording is retained here as task context, not treated as approval of this candidate definition.

## Background and current premises

The frozen proposal defines a fresh bounded `Application_N` family for the Name/Int literal Application case. It gives explicit occurrence grammar, opaque complete-contract boundaries, constructor-owned registration and installation/lookup/inversion, a tagged old-family inclusion/retraction, and conditional consumer seams. It does not claim that `Application_N` is the independently fixed historical family. Its compiler-referee and spec-auditor reviews pass only within that conditional, non-authoritative scope.

The proposal leaves a concrete original-consumer realization obligation: identify its `R_a = Comp(empty, Int)` against the exact literal Return image `J_a` before claiming the original consumer bridge. SeedExposure, CallInitial/I0, admission, solving, generalization/export, principality, and Gate E remain separate open work. No tests/builds or implementation were performed for this proposal.

## Options and consequences

1. **Select the reviewed fresh family as the successor definition for this source-owner seam.** This permits subsequent construction to use `Application_N` as the intended family for the Name/Int case, while preserving its stated opaque complete-contract boundary and all listed residual gates. It does not assert equality with an independently fixed historical family. It does not authorize implementation or cutover; any observable behavior change still needs an explicit reviewed decision and Gate E approval.

2. **Require correspondence to an independently fixed existing family first.** Keep `Application_N` as non-authoritative research. Before using it as the successor source owner, supply the actual existing grammar/contracts, original insertion and lookup, typed attachment inversion, and a complete correspondence/preservation argument. This avoids selecting a new owner definition now, but the current inspected sources do not supply those items, so the affected Application owner gate cannot advance on the current evidence.

These are alternatives about definition authority, not claims that two complete compiler behaviors have been proved equivalent or different.

## Affected work

Blocked scope: selecting the Application source-owner family as a durable successor definition and constructing dependent owner/consumer proofs on that selection.

Independent authorized work: read-only mapping of the current F5 implementation and its cutover seam; bounded proof work that does not assume either owner family; existing record synchronization and safe research checkpoints.

Required answer: select option 1 or 2, with any scope restriction. The separate answering primary must prepare and display an identified answer draft for explicit approval before publishing a finalized local answer. A preference or this question's presence is not approval.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary discovers and validates an explicitly approved local answer and commits the matching question/draft/answer together. The answering primary never mutates Git. Posting does not pause the goal; dependent work waits while independent work continues on disjoint owned paths.
