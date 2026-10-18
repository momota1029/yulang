# Sprint R50 — active-Link admission design and preservation

Status: ACTIVE, revision 1
Branch: `research/simple-sub-intrusion`
Baseline: `815c16ba1a0f264eb6e27369e6ebcb4a617ab62b`
Parent: full inference/evaluator theorem and original Simple-sub A/B, with original
quantifiers, source domain and accepted semantics; **OPEN, 0 -> 0**.

## Fixed outcome

Produce one independently reviewed, approval-ready proposal for authenticating
an active monomorphic Link at scoped Apply, together with a structural
preservation/refinement argument and an implementation handoff; otherwise state
the exact premise preventing such a proposal. The before-state is R49's reviewed
`NO_SAFE_CODE_SLICE`; the after-state must identify a concrete producer-to-
consumer evidence protocol and its obligations, or a sharper obstruction.

The proposal is not adopted architecture or language semantics. It may be sent
to the user for approval after review. This sprint does not authorize compiler,
fixture, expected-output, test, public API or semantic edits, builds, Cargo,
tests or runtime probes. R49's original active-root behavior remains unchanged:
recursive Names Link to the same open monomorphic initializer root; no active
Name is routed through LocalScheme or FreshUse. Existing generalized-local
FreshUse admission must retain its exact occurrence and transaction checks.

## Parent and non-goals

Preserve the original full inference/evaluator theorem and Simple-sub A/B claims,
quantifiers, source domain, expected behavior and accepted semantics. R50 can
establish only a proposal-level structural preservation argument. It does not
prove source typing, Desc/D_q formation, complete Call membership, effects,
soundness, principality, termination or evaluator correctness, and it does not
close or refute the parent.

Do not synthesize a LocalFreshRoute, borrow sibling evidence, rely on endpoint
equality alone, freshen the active root, reorder Install, weaken existing
rejection behavior, or present an invented flag as source authentication. If a
preservation step depends on unapproved semantics or a missing operational fact,
name that premise and stop at the approval-ready alternatives.

## Frozen authorities and source snapshot

All pins below are SHA-256 of exact worktree bytes at activation. The source
snapshot is read-only for this sprint.

| Dependency | SHA-256 | Use |
|---|---|---|
| R49 contract revision 2 | `aa0823710a5dae66eac151bf3da92ca21448328f4f115f90031b6abedb4f3679` | Fixed blocker and corrected authority provenance |
| R49 closeout | `fa1ad4b883b65d69147b0138d7117c6a43fc3422ab0a1b7812b0d45fa409326d` | Reviewed bounded admission result |
| R49 compiler review | `6604e40429c028a8925b587b3ddec69845b31461b90c9b8e4930757404d6c75f` | Independent source-path review |
| R49 spec review | `77fd5cfa5df3f9590ef38f87fd4716c619fb2724e63b3233634e87989a4e955e` | Corrected approval-pin review |
| Active self-recursion authority | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` | Monomorphic active-root behavior |
| Approved recursive-binding answer | `1c0ea94c359f08496185595448ab9082b4eac174ab247d67d37f316462db145b` | User-approved source scope |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | Proof/implementation direction and natural behavior |
| `candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Active Link construction and action execution |
| `candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Exact-occurrence scoped authentication |
| `candidate_scheme.rs` | `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278` | Installed scheme, route and transaction ownership |
| `shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Scoped admission caller/gate |
| `lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Route transaction commit/rollback boundary |
| Existing sibling fixture | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` | Direct and nested recursive Name identities |

The R49 revision-1 approved-answer hash typo is closed by revision 2; do not
reuse its superseded “all pins matched” assertion. At activation, Luna
recomputes every dependency pin above. Any changed byte stops dependent work and
returns to Luna before the review snapshot is frozen.

Two tracked test-only diffs and 58 older untracked R36–R48 artifacts were
observed at activation. They are outside R50 write leases and remain read-only;
no broad staging, cleanup or ownership inference is authorized by their
presence. They require separate primary reconciliation before the tree can be
called clean.

## Lanes and exact leases

### Luna — read-only design and implementation handoff (600 seconds)

Trace the actual producer, action execution, scoped Apply witness, authentication,
transaction lifetime and first consumer. Develop the smallest candidate evidence
protocol that carries provenance of a successful exact active Link to its
matching Apply without making it a FreshUse. State candidate fields, producer
and consumer checks, active-scope lifetime, Install/failed-attempt cleanup,
rejection cases and storage/work cost. Compare retaining a separate
occurrence-indexed ActiveLink record with any smaller action-local certificate;
recommend one only if the source lifetime proves it sufficient. Map future code
seams, but make no code changes.

Exact writes:
- `notes/design/2026-10-19-active-link-admission-r50-draft.md`
- `notes/progress/2026-10-19-r50-implementation-handoff.md`
- `tasks/agent-loop/inbox/20261019-r50-design.md`

### Sol — constructive preservation/refinement proof (900 seconds)

Treat the design as a candidate protocol, not approved semantics. State each
source fact, proposed premise and derived consumer guarantee separately. Prove
that matching exact Name occurrence, Local identity, active initializer/root,
scope and successfully executed Link provenance would authenticate the scoped
Apply while preserving a single monomorphic root and not creating a FreshUse.
Cover nested helper-body recursion, ordinary installed generalized locals,
source action order and stale/sibling/root-substitution attacks. Apply the result
to the original parent and keep every non-discharged A/B premise open. If the
protocol needs an assumption that cannot be justified without user approval,
return that as the exact remaining premise.

Exact writes:
- `notes/theory/2026-10-19-r50-active-link-refinement.md`
- `tasks/agent-loop/inbox/20261019-r50-proof.md`

No descendants are authorized. Sol cannot independently review its own result.

### Independent review

After both lanes freeze the same dependency snapshot, Luna assigns fresh
compiler and spec reviewers. Review the exact proposal/proof/handoff for source
applicability, authority status, preservation of monomorphic Link behavior,
occurrence/root/scope identity, action and transaction lifetime, generalized
FreshUse noninterference, falsifiers and all overclaims.

Exact review outputs:
- `notes/progress/2026-10-19-r50-compiler-review.md`
- `notes/progress/2026-10-19-r50-spec-review.md`

## Resources, stop and integration

Fresh cap: **2400 seconds**, no carryover. Luna design/map 600; Sol proof 900;
two independent reviews 300 each; Luna integration 300. Astra 0. Charge grants
when issued. Reserve integration after the frozen review seam. CPU/RSS UNKNOWN
unless actually measured. No build, Cargo, test or runtime process is authorized.

Stop at a coherent reviewed approval-ready proposal, the first unsupported
preservation premise, authority/dependency/lease change or resource boundary.
At close, record that the design is **PROPOSED, NOT ADOPTED**. Any adoption
requires the applicable independent review and explicit user approval; any
compiler implementation requires a later exact code contract. The parent remains
OPEN 0 -> 0 unless separate original-scope evidence proves otherwise.

Next consultation: reviewed proposal/obstruction or a material authority,
dependency, lease or resource change. No R51 work is authorized here.
