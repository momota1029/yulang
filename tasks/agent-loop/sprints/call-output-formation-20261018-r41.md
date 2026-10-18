# Sprint R41 — Call output formation design candidate

Status: FROZEN revision 1; proposal-only design work. It does not adopt a
language rule, change implementation, alter expected output, or close the
original theorem. R38 and R40 remain frozen inputs.

Branch/baseline: `research/simple-sub-intrusion` /
`887eed4370278cd9e789fb2b9b10ff58369da540`.

## Parent and fixed outcome

Parent: unchanged full Yulang inference/evaluator theorem and original
Simple-sub A/B claims, quantifiers, accepted source domain, complete
Call/effects, F1/FK1, N-Transport, soundness, principality, termination and
production gates. R40 ended with a reviewed exact-q partial derivation and a
reviewed native structural Result consumer. Parent conditions remain **0 → 0**.

At the same exact `q = loop y` inside `helper`, prepare one approval-ready
**candidate source-formation design** for the mutually dependent ordinary
output description `A_q` and complete original `Q_q` interface. The candidate
must not use a `Q_q` arm telescope as an unformed premise for introducing
`A_q`, then require `A_q` to form that same `Q_q`. It must specify an ordered
typed signature, exact declaration/reference, complete arm formation, and an
erasure/preservation argument against the existing accepted Call contract.

The work may conclude that preservation needs an unavailable original law or
that the candidate changes accepted behavior. In that case it must name the
exact unproved judgment or counterexample and stop. It must not describe the
candidate as derived from current rules, equivalent, conservative, principal,
or authoritative without the required evidence. R38's `Delta_R := Gamma_q`
proposal is an input only and is not preselected.

## Frozen direct inputs

| Input | SHA-256 |
| --- | --- |
| R40 contract `tasks/agent-loop/sprints/application-result-formation-20261018-r40.md` | `a1ca3da89e79c7722f2f4e4a228086db360f0279ea1ee7e31ae6b970315eaa45` |
| R40 proof `notes/theory/2026-10-18-application-result-formation-r40.md` | `fedca7cc54b8a552cfa1f3fee9ad396dc4646e28e4ebbfa0f5b93c26f3669275` |
| R40 proof review `notes/progress/2026-10-18-r40-proof-review-receipt.md` | `a6575438f13815cd62c052e1daa94d9fc00986c90595d7f3be9db84861c2f4a5` |
| R40 native trace `notes/progress/2026-10-18-typed-result-consumer-r40.md` | `71b7cae74f965f08e8c2877072ca179e47de5d4e05b335c19d95c7deb53ca2ea` |
| R38 candidate `notes/theory/2026-10-18-call-result-owner-r38.md` | `63ba5b3fe053b8ced790f089ab0a6defcf554b440114b94a9f901cec3176af92` |
| R38 contract `tasks/agent-loop/sprints/ordinary-call-result-owner-20261018-r38-rev2.md` | `f119bf4f031ab8b28fd060921723ddb235bf208ff3b48a87bc169aa1b7fa0421` |
| Call source definition `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| Owned Call construction `notes/theory/2026-10-07-owned-call-contribution-construction.md` | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` |
| IF construction `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| Typed computation core `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Generalize definition/proof `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Result synthesis policy `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| Top-level inference principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `candidate_context.rs` | `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` |

The Rust files above are unknown-author dirty inputs and are read-only. Do not
acquire their leases, edit them, or infer source meaning from native rows.
Revalidate every listed byte hash at assignment start; any mismatch stops the
affected lane for Luna adjudication. The current Git baseline remains the
recorded `887eed4370278cd9e789fb2b9b10ff58369da540`.

## Lanes and exact leases

**Source-rule candidate — prover/Sol-high, 1200 seconds.** Construct one
proposal-only formation signature for `A_q` together with the complete
`Q_q`. The candidate must:

1. select q structurally in the fixture and distinguish direct `loop x` and
   all `helper x` applications;
2. state the earliest context prefix at which the output description may be
   introduced, with every declaration's owner, class/sort, original scope,
   order, typed dependency and binder-before-use condition;
3. form q's complete structural, callee-pending, receiver-pending, W/Z and
   future arms after/beside that declaration without circular premise order;
4. keep the output ValueDescription distinct from invocation effect, actual
   returned provider/world, helper body result, and complete Call's other
   fields; preserve synthesis A and all original source quantifiers;
5. define the candidate's erasure to the existing Call source contract and
   prove the requested preservation direction(s), or isolate the exact
   missing original law / behavior mismatch. Do not assume every new binder
   is semantically invisible;
6. state consequences for the unchanged parent, exact falsifiers, alternatives
   left unresolved, and why R38's full-context candidate is accepted,
   repaired, or rejected.

This is a design candidate, not a source derivation. No implementation,
expected-output change, rule adoption or semantic approval is authorized.

Write only:

- `notes/design/2026-10-18-call-output-formation-r41-draft.md`
- `tasks/agent-loop/inbox/20261018-call-output-formation-r41.md`

**Native owner map — Luna/high, 600 seconds.** Independently map each proposed
field and lifecycle step to the already reviewed R40 native trace: source
producer, recipe/input, admission, typed Result child, Preserve/dependency,
Context/Dispatch, helper body endpoint and extrusion copy. Label each as
existing, proposed, absent, or unverified; include the exact producer and
consumer symbols and source locations. Record which proposed source facts are
not represented natively. This is ownership evidence only, not a source rule
or typed correspondence. Keep `NO_SAFE_CODE_SLICE`; no Rust or test edits.

Write only:

- `notes/progress/2026-10-18-call-output-formation-owner-map-r41.md`
- `tasks/agent-loop/inbox/20261018-call-output-formation-owner-map-r41.md`

The two lanes have disjoint output paths. No descendants, generated files,
scratch paths, changes to R38/R40 artifacts or other writers' files. Luna owns
this contract, current state, review assignment and integration.

## Review, resources and stop conditions

Total cap **2400 seconds**, Astra 0: proposal construction 1200 + Luna owner
map 600 + fresh independent whole-candidate review 420 + integration 180.
Charge grants in full. No transfer from R40; its budget is exhausted. The
reviewer must not be the candidate author or a coauthor. Reviews apply to
exact frozen bytes and all listed inputs, and must check dependent formation,
original Call coverage, erasure/preservation claims, falsifiers, inference
principles, expected-output protection and parent quantifiers. A review does
not approve semantics.

Stop on changed input bytes, unknown writer movement, a source acceptance
counterexample, a required new authority decision, expanded leases/resources,
or exhausted grant. User approval and the normal independent design gate are
required before any new language/API/semantic rule reaches implementation.
No Cargo, tests, CLI, runtime, production code, expected-output edits, Git
mutation, adoption or parent promotion is authorized here.

R41 is complete only when the exact candidate and owner-map artifacts are
frozen, independently reviewed, and integrated with the remaining premise,
source owner, checks, hashes, grant accounting and unchanged parent status.
