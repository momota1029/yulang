# Sprint R42 — Call output owner decision packet

Status: FROZEN revision 1; proposal-only semantic decision preparation. No
language rule is adopted, no implementation is authorized, and no expected
output changes.

Branch/baseline: `research/simple-sub-intrusion` /
`887eed4370278cd9e789fb2b9b10ff58369da540`.

## Parent and fixed outcome

Parent: unchanged full Yulang inference/evaluator theorem and original
Simple-sub A/B claims, source domain and quantifiers, complete Call/effects,
F1/FK1, N-Transport, soundness, principality, termination and production
gates. Current conditions remain **0 → 0**.

Use the reviewed R41 proposal to prepare one decision packet for the original
Application/Call output-description owner. State exactly what new source
commitment JOF would make, which existing judgments it extends, how its
`A_q` scope and ordered dependencies interact with original challenge and
return binders, what its source/native implementation would require, and what
evidence remains unavailable. Include a small dependency-sensitive strategy
model that distinguishes binder orders, explicitly as a design discriminator
and not a source-qualified counterexample.

Success is either a precise proposed choice that can go to the user after
fresh design review, or `NO_SAFE_ACTION` with the exact missing authoritative
input. Do not present R41 as a conservative formalization, a source-derived
rule or an accepted semantic equivalence. This packet does not adopt JOF or
authorize dependent implementation.

## Frozen direct inputs

| Input | SHA-256 |
| --- | --- |
| R41 contract `tasks/agent-loop/sprints/call-output-formation-20261018-r41.md` | `1ff014a662f02e4c5e6d5fd084da88f7af6fd993b85437a063fb65807ae745f4` |
| R41 candidate rev2 `notes/design/2026-10-18-call-output-formation-r41-draft.md` | `faf3c347909a59acafabf78d77f0597a5b48c033ec3fb5ce957681000ff675da` |
| R41 candidate handoff rev2 `tasks/agent-loop/inbox/20261018-call-output-formation-r41.md` | `1a37cbb61253021a685b44098302cede8565600db5256d321368f3c7f153a92e` |
| R41 native owner map `notes/progress/2026-10-18-call-output-formation-owner-map-r41.md` | `0558299c19e83b9b9428843139e54fdcbca8b3bfd93427e2b322186d538bf0d9` |
| R41 review receipt `notes/progress/2026-10-18-r41-review-receipt.md` | `ddf08604d352976fcab2cbf7538f9785be3ad8b88564faa61874d72e6dc43efa` |
| Call source definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| Owned Call construction | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` |
| IF construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| Generalize definition/proof | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| Top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| Current native owner paths: `candidate_source.rs`, `candidate_call.rs`, `shadow_apply.rs`, `lib.rs`, `candidate_context.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`, `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479`, `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137`, `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`, `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` |

Rust paths are dirty by unknown authors and remain read-only. Revalidate all
direct hashes at assignment start. Any mismatch stops the affected lane.

## Lanes and exact leases

**Semantic decision draft — prover/Sol-high, 1200 seconds.** Use dependency-
sensitive strategy semantics to analyze JOF's choice
`Gamma_q ; choose A_q[Gamma_q] ; q-local arms` against original dependency
orders that choose a description before an inherited challenge or after a
later return/provider. Construct a finite abstract model (for example binary
challenge/output) that exhibits unequal strategy sets under the two orders.
Label it only as a design discriminator. Do not claim the original source
language realizes the model.

State:

1. the exact proposed owner, source sort, scope and ordered dependency list;
2. which original output-header and complete-Q judgments would be extended;
3. whether an inherited challenge becomes a free dependency or a later
   return/provider dependency is removed;
4. options and semantic consequences, including reject/redesign, adoption of
   a reviewed JOF extension, or `NO_SAFE_ACTION` if original authority is
   insufficient;
5. why the choice is not settled by operation erasure, native rows, endpoint
   solving, R41's internal review or R36's definitional-copy lemma;
6. evidence required for both preservation directions, principal inference,
   Generalize consumers, both frames, F1/FK1 and source/native commutation.

Write only:

- `notes/design/2026-10-18-call-output-owner-decision-r42-draft.md`
- `tasks/agent-loop/inbox/20261018-call-output-owner-decision-r42.md`

**Implementation gate — Luna/high, 420 seconds.** Write only the concrete
prerequisite gate for any future implementation: exact source certificate
fields; complete result/effect/provider/world/future tuple retention; transfer
through ApplySourceInput/NativeInterface/typed Result and extrusion copies;
consumer rejection conditions; Generalize/copy/publication obligations; and
the source owners and approvals that must exist first. Reuse R41's native map;
do not repeat its source-to-consumer trace. `NO_SAFE_CODE_SLICE` continues.
No code or test changes.

Write only:

- `notes/progress/2026-10-18-call-output-implementation-gate-r42.md`
- `tasks/agent-loop/inbox/20261018-call-output-implementation-gate-r42.md`

The two assignments have disjoint exact paths. No descendants, generated
files, scratch paths, semantic changes, expected-output changes, Cargo, tests,
CLI, runtime, Git mutation, or external contact.

## Review, resources and stop conditions

Total cap **2400 seconds**, Astra 0: decision draft 1200 + Luna implementation
gate 420 + fresh independent design review 600 + Luna integration 180. Charge
grants in full. Reviewer must be independent of both authors and test strategy
model validity, source-domain limits, semantic consequences, preservation
claims, original quantifiers, expected-output protection and consistency with
inference principles. Review does not adopt a rule or approve implementation.

Stop on changed input bytes, an actual source-qualified counterexample,
authority mismatch, unknown writer movement, need for new semantics outside
the candidate packet, expanded lease/budget, or grant exhaustion. User
approval and the normal design gate are required before JOF or another new
source semantic decision reaches implementation. Parent remains OPEN.
