# Sprint R39 — original Call introduction and result consumer

Status: FROZEN for the bounded source-owner/native-trace investigation; no
semantic adoption or code-edit authority.
Branch / baseline: `research/simple-sub-intrusion` /
`887eed4370278cd9e789fb2b9b10ff58369da540`.
Parent: unchanged full Yulang inference/executor theorem and original
Simple-sub A/B claims, quantifiers and source domain, including complete
Call/effects, F1/FK1, N-Transport, soundness, principality and termination.
R38 closeout: `notes/progress/2026-10-18-r38-candidate-review-closeout.md`,
SHA-256 `8ed59d6013f0be42e3f3609dd45fe4db37d9897dc7fec6d1b7790d1cb1f58050`.
R38 candidate: `notes/theory/2026-10-18-call-result-owner-r38.md`,
SHA-256 `63ba5b3fe053b8ced790f089ab0a6defcf554b440114b94a9f901cec3176af92`.

## Fixed outcome

At the exact original specimen occurrence `q = loop y` inside `helper`,
determine from the original source-rule inputs whether the result's ordinary
`Desc` owner, sort, introduction scope and complete ordered dependent telescope
are supplied. Independently trace that same source occurrence through the
current source Apply construction, admission, occurrence-qualified propagation
and actual Result consumer. Return either the exact joined evidence or the
first missing source/native owner edge, then apply it to the unchanged parent.

Do not repeat R38's flat rule-inventory audit, infer `sigma/Delta` from endpoint
shape, or recast the proposal `Delta_R = Gamma_q` as an existing rule. No
language rule is adopted by this sprint. Any later adoption is a separate
authority decision. Do not reduce the source domain or parent quantifiers.

Success is a reviewed evidence or obstruction chain that answers whether the
remaining gap originates in the original Call typing-schema supplier, native
occurrence/port retention, or both. A descriptor name, request list, native
endpoint, assumed transition test or green test alone is not success.

## Frozen direct inputs

Authority and theorem pins:

| Input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/progress/2026-10-18-r38-candidate-review-closeout.md` | `8ed59d6013f0be42e3f3609dd45fe4db37d9897dc7fec6d1b7790d1cb1f58050` |

Current source/native snapshot pins (the worktree contains pre-existing
uncommitted changes; code authors are UNKNOWN and no worker may modify these
inputs):

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/candidate_scheme.rs` | `8c370e47d5e8692a618fedf41be07d7ae3ac961f9070bfed6730e2b8e2f1137e` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |

## Parallel assignments and exact leases

**Proof / source-rule owner — Sol/high, 900 seconds.** Start from the actual
original Call typing-schema supplier required by the Call source definition;
trace its construction inputs back to the exact `q` and the original helper
binding. Recover the authentic validating owner, source sort, introduction
scope and complete ordered telescope if they are supplied. Distinguish the
Call schema's result coordinate, body Result, invocation effect, returned
provider/world and every pending/W/Z arm. If an input is absent, identify the
first absent field and its source owner; do not write a replacement rule.

Write only:

- `notes/theory/2026-10-18-original-call-introduction-r39.md`
- `tasks/agent-loop/inbox/20261018-original-call-introduction-r39.md`

**Native source trace — Luna/high, 720 seconds.** Trace the exact original
specimen and occurrence from `candidate_source.rs::emit_candidate_source`
through its `ApplySourceInput`, `shadow_apply.rs::admit_candidate_fact`,
occurrence-qualified propagation, `candidate_call` observation and the actual
Result consumer. Establish how this `q` is selected without relying on
`calls[0]`; identify every source occurrence, result port, consumer and
retained edge, or name the first absent link. Reuse R38's inspection only where
its exact pins still match. Do not assume a logical `Desc` or use tests as its
substitute. Do not edit Rust files, tests, fixtures, expected output or any
other existing worktree change.

Write only:

- `notes/progress/2026-10-18-original-call-result-trace-r39.md`
- `tasks/agent-loop/inbox/20261018-original-call-result-trace-r39.md`

The two writer leases are disjoint. Both outputs must include exact input and
artifact hashes, current worker/model observations, source-to-consumer chain,
checks/omissions, parent application, remaining owner and writer-stop receipt.
No descendants or generated files are authorized.

## Review and resources

Total sprint envelope: **2520 seconds**, Astra 0. Proof 900 + native trace 720
+ independent proof/source review 300 + compiler review 300 + conditional
focused check 120 + Luna integration 180. Charge each grant in full when
issued. At most one heavy Cargo process; no test is allowed until Luna records
a launch receipt after both applicable reviews are CLEAN. If the chain is
absent or review blocks, skip Cargo and preserve the full parent OPEN.

Fresh reviewers receive frozen artifacts only. The proof/source reviewer
checks exact q ownership, dependent-context formation and telescope order. The
compiler reviewer checks occurrence identity, all native Result propagation
edges and the actual consumer. Neither reviewer may be an author or coauthor
of the reviewed artifact. Cargo, if authorized, may verify only the exact
native assertion; it cannot establish the original source rule or parent
theorem.

Stop on changed dependency hashes, unknown/moving writers, a counterexample,
required semantic adoption, lease expansion, or exhausted assignment grant.
Return any authority/lease/resource change to Luna. No production code change,
semantic adoption, expected-output change, bypass, nested CLI, Git operation or
unlisted path is authorized.
