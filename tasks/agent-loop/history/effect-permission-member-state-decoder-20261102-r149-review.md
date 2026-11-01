# R149 independent review

Status: **STOPPED — accept the bounded proof repair and conditional source characterization. Complete member/state construction, source/native application, and production remain OPEN.**

Reviewer: `/root/r149_independent_review`; read-only; no descendants. No builds/tests, file/cache mutations, Git mutations, or dirty working-tree Rust inspection.

## Authentication

Before interpreting submitted content, the reviewer authenticated:

| Artifact | SHA-256 |
|---|---|
| Contract | `3ef1dfd0acd0720b8256d16d81dcd6233c72466a7a5f5116e68083e8a9ddfd36` |
| Admission | `c8080af78bb1a4df698c7e13df11dbf1b59160a752db2a0face60496032d114a` |
| Source handoff | `729408db75945047857226f109f37eb451656f36a64c4ade219c95f97c7e8472` |
| Proof handoff | `fed2e456f43137d2226584339a787f91fc8ac0eb59f9c8a30e097398c62481df` |
| Repaired R118 source | `f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27` |

All ten exact baseline blobs declared by the contract matched at `87dfe33bcd4c572d740dc33b454114b6018a4376`. R119 remains baseline-identical. R148 review/outcome and R147/R148 source/proof handoffs were authenticated against their recorded hashes. Historical receipts were used as bounded dependencies, not substitutes for inspected source.

## Source contract result

The actual concrete member emission is Support expansion under the exact active `RelationId`. Baseline `candidate_effect.rs:1059–1097,1444–1466,2440–2448,2521–2557` constructs latent views, Support bounds, and concrete `AnnotationMember(view, member)` tasks. Neither `View` nor `Contribution` authenticates an incoming input/protection state.

`candidate_context.rs:3452–3454,3481–3512,4213–4216` supplies relation identity and active-relation inheritance. Replay at `4462–4468` orders lower and upper transformers. A derivation-qualified state association is therefore a plausible conditional ownership contract; a mutable View-wide field would conflate distinct paths already preserved by relation/scoped-flow identity.

The source handoff correctly does **not** claim a complete implementation-ready construction. Two premises remain open:

**INITIAL-STATE — source handoff section 70; `candidate_effect.rs:1089–1097,1453–1458`.** No inspected constructor determines every actual member's incoming input/protection state. For `protect_body(s,i)`, initial inputs `[]` add protection `s`, while inputs `[i]` do not. This proves the state matters, not that the two executions are jointly source-reachable. Closing evidence must establish the source-owned seed/initialization law for operation emissions, latent annotation members, and Contribution paths, including inherited-state coverage and structural initialization boundaries.

**CONSUMER — source handoff section 72; `candidate_effect.rs:1468–1498`, `candidate_context.rs:4231–4291`.** The reached allowance decision reads family membership and does not consume evaluated protections. Recording observations or transporting transformers does not establish eligible Catch subtraction. Closing evidence must connect the same member/derivation state to the actual permission/provider/arm and continuation decision, preserve attribution and independent protections, and release the selected scope throughout corresponding compose output occurrences.

These are disclosed blockers, not new defects in the bounded handoff. The source contract's conditional obligations for combined inventory bounds, identical FreshUse maps, replay, attribution, collisions, rollback, and independent protections are consistent with the pinned definitions. Scope inventory validation alone does not certify additional state coordinates. No source-qualified counterexample or production readiness is claimed.

## Lean repair

Independent byte comparison establishes that R118 differs from baseline only in the two authorized proof-term repairs:

- `NativePermissionDecoderR118.lean:87`: after dependent case splitting, use `rfl` for the exact lookup equality instead of carrying the stale lookup equation.
- `:136–138`: refer to the surviving `family` and `permission` names after equality elimination.

Definitions, imports, theorem types, assumptions, and axioms are unchanged. The repairs address the two reported elaboration failures at their source.

The inspected R118/R119 declarations agree with the fully qualified printed types in the proof handoff. `read_family_exact` derives the ordinal-checked view/member lookup from successful `readFamily`; `read_permission_exact` derives the unique registration match at its separate storage coordinate; `decode_member` derives owner equality, both exact reads, and concrete membership from partial decoder success. R119 `selected_retained_member` retains explicit premises for native read, retained permission read, ordered search, and consumer indexed read, then joins the exact reads and membership in that same permission.

Complete reported axiom sets:

| Declaration | Axioms |
|---|---|
| R118 `contains_member` | `[propext]` |
| R118 `read_family_exact` | `[propext]` |
| R118 `read_permission_exact` | `[propext]` |
| R118 `decode_member` | `[propext, Quot.sound]` |
| R118 `unequal_coordinates` | `[propext]` |
| R118 `post_state_is_not_prepare_input` | `[propext, Quot.sound]` |
| R119 `selected_retained_member` | `[propext]` |

The author receipt records Lean 4.35.0, one targeted R118/R119 build (exit 0, 4.441 seconds), and a separate theorem-kind/type/axiom audit (exit 0). Fifteen generated output files match the recorded size and SHA-256 list. The reviewer did not rerun Lean; runtime and before/after cache history remain author receipts, not independently reproduced measurements. The author reports cache growth from 48,734,666 to 49,408,795 bytes (+674,129), with no deletions.

## Disposition

No major or minor correctness finding against the bounded submission was established. The accepted finite consequences do not supply Rust equations, initial-state constructor history, pointer identity, full operation identity, R45 extraction, source reachability, or original parent-theorem closure.

Original H/A/B, full effect hygiene, source/native correspondence, whole-language soundness, semantic adoption, and production gates remain OPEN. All reviewer work STOPPED.

## Proof handoff whitespace correction

After the main review, one extra final LF was removed from the frozen proof
handoff to make `git diff --check` clean. The independent reviewer verified
that appending exactly one LF reconstructs the reviewed SHA-256
`54bdfb6a2f48d53f7bb211b2b77c8e677bbd5c5f4c7abedcf72d48a54136bb5e`; the
corrected artifact hash is `fed2e456f43137d2226584339a787f91fc8ac0eb59f9c8a30e097398c62481df`.
No other byte or review conclusion changed. R118 source remains
`f976e0b3b5e8b2b70ee902bdca30ce140db503a4972e8cf1b621892b57bf5d27`.
