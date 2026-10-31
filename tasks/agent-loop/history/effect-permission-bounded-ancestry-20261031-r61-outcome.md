# R61 outcome — bounded ancestry reader

Status: **CLOSED_BOUNDED_PASS_RESEARCH_ONLY**.

## Result

The frozen Rust change factors the existing relation-ancestry visitor's parent selection into a pure helper and exposes a private borrowed reader over the same complete indexed relation/dependency tables only after the existing visitor succeeds. Review found the original validation, LIFO scheduling, work charging, reservation ordering, and error behavior preserved.

The Lean construction derives directed retained ancestry and a checked path witness from successful ordered visitation, then applies the existing policy/consumer theorems to the same constructed inputs. Audit14 and the independent reviewer authenticated the theorem roots and their complete reported types/axioms. Independent review: **BOUNDED PASS**, no correctness findings inside this scope. Review placement: `tasks/agent-loop/inbox/effect-permission-bounded-ancestry-r61-review.md`; report body SHA-256 `ce97b0ccaca0c1c0b36944d14f0d545d2212dcdb22c559c83dac46ac2d8c83fc`.

## Frozen evidence

- Rust `candidate_context.rs`: `cf73489b771067c2cd01d738a29e74f8a180c8fece782b5829871f02db36d106`.
- Rust `candidate_receiver.rs`: `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`.
- Lean `BoundedAncestryR61.lean`: `9e1c783016bc14487dd0a4ebc2839dfab0dc3daf911ee88fa02f3624e2ad60a4`.
- Rust handoff: `62a206465d2c8bc89605472e5601f4ef6fff0bf0fbc8a240fe5521dc394da725`.
- Lean handoff: `95d2f3c293eccd2140460399b5011ad38c97480e5d66b67b2769a8004261ccff`.
- Contract SHA-256: `4ee44b5aae475fefaa185249681f1631f43f33d8cf6c4d498d1cc94879e9d435`.
- Admission SHA-256: `4cf7bdbd57fc0d5c869799e77b11ac73c37e3d25fd15ee4a01a3e41a3f6c66b2`.

Audit14: Lean 4.35.0, exit 0, warning-free; all 50 authored roots and 46 retained inherited roots checked, 96 complete root reports in total. Authored census: 4 empty, 9 `[propext]`, 37 `[propext, Quot.sound]`; no `Classical.choice`, project axiom, sorry, or native-evaluation dependency. Producer receipt input SHA `18b44e56868be57a9ba7820f7ba3395be004af70252c779caf240b52e627d1a6`, stdout SHA `ed5156930dcb602b3378978e1f9a3c6b932acffda2301fd0bf5f14c16d227874`, empty stderr; 8.4327s, peak RSS 993552 KiB. These are authenticated producer receipts, not a reviewer rerun.

## Explicit OPEN limits

The result does not yet connect the pointer-anchored native success and full source records to the same Lean `Native` plus a successful model run. Pointer-to-`Nat`, Internal-root extraction, arbitrary allocator/resource/failure trace equivalence, outer Rust-to-Run simulation, complete Context/R50, R51/publication, runtime, original A/B, soundness, principality, termination, full hygiene, and production remain OPEN. Reservation booleans abstract reserve outcomes and are not faithful models of `Vec` capacity/allocation. No Rust build/test/typecheck, Cargo, formatter, or Lake run is claimed.

## Git / state

R61's reviewed checkpoint contains the two Rust files, Lean module, Rust/Lean handoffs, this review placement, this outcome, and the synchronized `current.json`. No unrelated dirty paths are included. The sprint's `current.json` must retain pending questions, UNKNOWN worker observations, and quarantined leases unchanged; only R61 author/reviewer states and closeout references are updated.
