# Sprint R44 — select and validate an Application output-owner rule

Status: FROZEN revision 1; design-and-proof candidate gate. JOF is not yet
Authoritative. No compiler implementation is authorized by this contract.

Branch / baseline: `research/simple-sub-intrusion` /
`19d02ce40a107c7ac182748879be1c665391c7c2`.

## Authority and selected recommendation

The user delegated this unresolved choice on 2026-10-19:

> そういう判断はおすすめを自動的に選んでもらっていいですよ．駄目だったら変えればいいので

Luna selects the **JOF source-formation candidate** as the recommended route:
introduce the ordinary flexible Application output description after its
operands are typed and before any output-indexed Call header is formed. This
opens a bounded design-and-proof gate; it does not yet adopt the candidate,
prove preservation of the original language, or close any parent theorem.
Independent review and primary adjudication remain required before recording
it as Authoritative or granting code leases.

Frozen direct inputs and SHA-256:

| Input | SHA-256 |
| --- | --- |
| R43 contract | `065f0983dea404bb278810ca4b82d430049bfbcb0ce6413236fc05e407a16387` |
| R43 theory result, final committed bytes | `50c8499da6b441980953868e007fc8f22446a8cea19d1015d7ad8affedeb5c61` |
| R43 hash correction | `f2c5237983cf59cb3b5883eccb38e03bf43d42e080f0ab2374d64fccd08c241b` |
| R41 formation proposal | `faf3c347909a59acafabf78d77f0597a5b48c033ec3fb5ce957681000ff675da` |
| R41 contract | `1ff014a662f02e4c5e6d5fd084da88f7af6fd993b85437a063fb65807ae745f4` |
| R41 native owner map | `0558299c19e83b9b9428843139e54fdcbca8b3bfd93427e2b322186d538bf0d9` |
| R41 review receipt | `ddf08604d352976fcab2cbf7538f9785be3ad8b88564faa61874d72e6dc43efa` |
| R42 decision | `fd51992ded8fd106d2c7ff5790c33864efbbffd4a655b9c0c2c0ae384e60d83c` |
| R42 implementation gate | `855c07f2a6de1e156209f91c7c9f9ea2169369feb0381edb63ddeceb013c1758` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Original Call formation | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` |
| Original Call owner definition | `0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110` |
| Typed-computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Code-Call input construction | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012b1c951a8805dd9f6` |
| Call source-interface definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| Generalize definition and proof | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |

## Original outcome, parent and success evidence

Parent: the unchanged full inference/evaluator theorem and original
Simple-sub A/B claims, quantifiers and source domain; complete Call/effects,
F1/FK1, N-Transport, soundness, principality, termination and production.
Parent remains **OPEN, 0 → 0** throughout this sprint.

Fixed outcome: produce and independently review one complete, source-level JOF
formation candidate for the ordinary Application/Call owner, instantiated at
`q = Application(Name(loop), Name(y))`; derive its binder order and
Generalize action from the specified candidate; expose every unsupported
source premise and falsifier. If the candidate cannot form complete headers
without a circular or later dependency, record the concrete conflict and
revise the recommendation inside this design gate. Do not turn the R43 bounded
absence into a repository-wide claim or use another generic search.

Success requires a well-formed candidate whose result/effect and complete Call
headers have typed, acyclic scopes; no premise may use already formed `Q_q`, a
solved endpoint or native solver state. The review must test the dependency
order against Generalize, both independent frames and aliases, and all original
pending/result/provider/future/W/Z arms. A clean review approves only the
candidate scope. It does not prove old/new strategy equivalence, soundness,
principality, termination, source/native correspondence or production.

## Two continuing lanes and permissions

**Proof/design — Luna primary, 1650 seconds.** Derive the proposed output-owner
formation and its actual `q` instance from the pinned Application, Code-Call,
Call-interface and Generalize sources. Treat R41's `Delta_A := Gamma_q` as the
selected candidate, then test every dependent field against its real formation
owner. Keep the candidate's full ordered context; do not infer a narrower
telescope from names, native levels or successful solving. Output:

- `notes/design/2026-10-19-call-output-owner-jof-r44-draft.md`
- `notes/theory/2026-10-19-jof-application-formation-r44.md`
- `tasks/agent-loop/inbox/20261019-call-output-owner-jof-r44.md`

**Implementation boundary — Luna primary, 450 seconds, read-only.** Reuse
R41's frozen native owner map and R42's implementation gate to state the exact
future certificate flow and the still-open source-to-native proof edges. Do
not read or change quarantined `candidate_scheme.rs`, `shadow_apply.rs`,
`candidate_local_self_recursion.rs`, `tasks/current.md`, or R35–R41 unknown-owner
artifacts. No Rust/test/build/Cargo/runtime work. Output:

- `notes/progress/2026-10-19-jof-implementation-boundary-r44.md`

**Fresh review — independent `compiler_referee` and `spec_auditor`, up to 450
seconds each.** Review the same frozen candidate and proof. The referee attacks
formation, Generalize, A/B risks and the complete Call; the auditor checks the
selected sources, user-delegated decision scope, and no unsupported semantic
or implementation claim. Neither producer nor prior R41/R42 authors certify
the new bytes. Luna adjudicates and records any repair.

Aggregate cap: **3000 seconds** (primary 2100, reviewers 900); Astra 0; no
carryover. Exact elapsed CPU/RSS are unmeasured. The reviewed implementation
gate is conditional: no production edit until the design is Authoritative,
the required source/native proof premises are addressed, and exact Rust leases
are released by their actual owners.

## Non-goals, falsifiers and stop conditions

No new q-only compiler branch, source restriction, eager solving, speculative
typing search, expected-output change, or alteration of the original theorem.
The candidate must apply uniformly to the source constructor family it claims
to cover; `q` is an instance, not a name-specific rule. Preserve bounded
approved Application cases and all existing Call arms without duplicate or
overlapping owners.

Falsifiers include: an output/header type needs an input introduced after its
use; effect formation depends cyclically on the output; any complete pending,
provider, future, W/Z or receiver arm cannot be formed; full-context dependency
changes ordinary Generalize eligibility without an accepted account; the
candidate restricts a natural program or contradicts an existing authoritative
case; or native consumers cannot carry the chosen certificate without guessing
scope. A falsifier triggers a batched revision of the proposal, not silent
semantic adoption.

Stop at the exact new-rule boundary if any such conflict remains. Keep the
original parent OPEN. Next selector consultation is at frozen review/adjudication,
a concrete falsifier, a new authority/lease dependency, or code-gate readiness.
