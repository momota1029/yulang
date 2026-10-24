# Same-birth replay, actual occurrence provenance and publication

BIRTH-LEVEL-REPLAY-20261024/r1. Baseline `7af2bbfe9588128e90f6706f99243e91b63a7ae3`. Worktree `/home/momota1029/rust/yulang-semantics-proof-20261024`, branch `research/semantics-proof-20261024`.

## Original objective and changed method

User explicitly asks another closure attempt under the selected immutable birth-level induced SCC rule. Preserve original source/Call/effect/type/event scopes, actual extrusion occurrences/pairs, generalized use independence, required safety and principal coverage. Implementation/tests excluded; Astra-only children. This sprint traces a concrete source through the first disputed replay, replacing an abstract factorization-only attempt.

Candidate (notation must match original Lam/Let/App/Rcd/Sel grammar):

```text
let top = lambda h.
  let rec f = lambda x. (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

h starts at level1 and f's root/formal at2. A same-birth F/F recursive demand can precede a cross-level F/H demand. Completing f can replay Record(B) through a low anchor and copy B to target1. No occurrence attribution or rejection is assumed: prove the exact actual source sets and their semantic ownership. Current code is inspected evidence, not authority replacing the selected operation.

## Outcomes and exact leases

- `/root/astra_corrected_machine`: only `notes/theory/2026-10-24-birth-level-replay-intrusion.md`. Three stages: finite actual native allocation/bound trace; exact contextual source-set and pair retention/activation trace; apply to selected qualification/publication, deriving preservation, real discriminator or exact attribution gap. Account for memo/recapture and the source/implementation correspondence. One final frozen handoff.
- `/root`: only `notes/theory/2026-10-24-birth-level-publication-replay.md`, `docs/yulang-whole-proof-closure-ja.md`, `docs/yulang-proof-index-ja.md`, this contract, `tasks/agent-loop/sprints/birth-level-replay-20261024-outcome.md`, and `tasks/agent-loop/current.json`. Construct exact freshening/quotient action for the pre-publication graph and source comparison where independently derivable; apply producer evidence without guessing event tags.
- `/root/astra_semantics_direction`: read-only30s selection complete, STOP/no descendants; inspect actual source-set composition and attribution.
- `/root/astra_semantics_review`: read-only80s fresh frozen review; author neither target; trace the decisive source owner and the publication consequence, include end-boundary recommendation.

You are not alone; no other writes/reverts. Original checkout and unknown external leases quarantined; protected question directory excluded. No tests, builds, compiler execution/probes, implementation/manifests, worker Git/network, scratch files or descendants. Static source/hashes only. Old frozen notes and authoritative rule remain unchanged.

## Falsifiers and success boundary

Do not identify current contextual source-set membership with authentic occurrence ownership without a constructor correspondence. Do not silently use a scalar reference history as a whole Yulang execution trace. Do not claim coverage refuted without an actual source witness or explicit required acceptance. Do not infer type target level or publication telescope from Value birth. Preserve every inherited lower/upper bound and event/Call evidence; no source domain restriction or fresh low anchor per use.

A new conditional lemma alone is not parent closure. Deliver exact source-derived evidence at the replay seam, apply it to publication, and state all remaining owner obligations. If no conclusive original proof/refutation follows, retain OPEN rather than filling missing evidence with a changed rule.

## Runtime and review

Prior4290s + current300s (direction30+producer190+review80) =4590s charged. This envelope is explicitly replanned for the user's retry and the new concrete source-owner method; no automatic renewal or per-stage reset. Maximum1 Astra child concurrently; requestedAstra/medium, observed model/effort/duration UNKNOWN. Primary budget remains its own stricter bound. Actual final STOP and descendant receipts required. One independent review then bounded repairs; no self-certification. Normal explicit-path Git integration only after frozen hashes and full outbound inspection.

## Frozen inputs

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `notes/theory/2026-10-24-birth-level-scc-intrusion.md` | `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/progress/2026-10-14-value-occurrence-intrusion-implementation.md` | `35dca7a9033a52d46367229c0119887b944bc6c0f37a560de74f33da4653c0e5` |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_source.rs` | `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `5893555fe89c594feabca200d1d8f26631877200da61e6ae39c80d375f748bb1` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
