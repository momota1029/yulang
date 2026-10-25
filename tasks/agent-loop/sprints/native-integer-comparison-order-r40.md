# Sprint NATIVE-INTEGER-COMPARISON-ORDER-20261026/r40

Status: READY; Luna primary, one registered Lean prover, one fresh independent
source/math reviewer after freeze.
Branch: `research/simple-sub-intrusion`
Baseline: `ddeed3d91df9293827628e29c48d32fd90a9d279` (R39 question-preparation
contract committed; R39 current-state delta is being included with this admission)

## Original goal and fixed outcome

Original user goal: complete the Yulang type-inference and executor Lean proofs,
with Lean and its governing specification as the authority and Rust as a source
of correspondence evidence. The manuscript's primitive table at
`docs/yulang-operational-type-safety-ja.tex:901–902` assigns mathematical
integer relation operations `IntEq`, `IntLt`, `IntLe`, `IntGt`, and `IntGe` to
Boolean results. The primitive execution type-preservation statement is at
`:923–942`.

Prove the signed decimal comparison algorithm used by the current runtime agrees
with Lean's mathematical `Int` ordering on every pair of successfully decoded
integer strings. Add one standalone research module
`YulangClosure.NativeIntegerComparison` importing the accepted
`NativeLiteralReadback` definitions. Its comparison model must follow Rust's
actual algorithm: accept an optional ASCII minus and nonempty ASCII digits;
normalize leading zeros and negative zero; compare magnitudes by digit length
then ASCII digit order; reverse the magnitude order for two negative inputs;
and use sign order for mixed signs. It must not define comparison by first
calling `mathematicalValue` and comparing those integers.

Required theorems:

1. Model parsing agrees with the existing `NativeLiteral.Grammar` for all byte
   strings and rejects malformed inputs.
2. For successful `NativeLiteral.decodeInteger left = some a` and
   `decodeInteger right = some b`, model comparison returns exactly Lean's
   `Int.compare a b`.
3. The model's five Boolean projections for equality/less-than/less-or-equal/
   greater-than/greater-or-equal agree with the corresponding relations on
   `a` and `b`, matching the five runtime branches.
4. Include kernel-checked discriminators for `-0`, leading zeros, sign reversal,
   equal magnitudes with different spellings, malformed words, and values beyond
   machine integer width.

Do not claim the Lean kernel executes Rust, that all Rust integer producers have
been reverified in this sprint, or that an arbitrary runtime trace has been
realized. The existing producer invariant supplies the grammar premise for
actual produced integers; this sprint proves the comparison/readback meaning
once that premise holds.

## Frozen source and dependencies

- Manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`;
  primitive meaning `:901–902`, primitive preservation `:923–942`.
- `notes/theory/lean/YulangClosure/NativeLiteralReadback.lean`, SHA-256
  `53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54`;
  `Grammar`, `decodeInteger`, `mathematicalValue`.
- `tools/inference-playground/src/runtime/decimal.rs`, SHA-256
  `83ba443036c7da05f9d72d4bbba98b05c4cab2135062743ffe8e3f05250d1cae`;
  `parts` and `compare` at `:6–27`.
- `tools/inference-playground/src/runtime/machine.rs`, SHA-256
  `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`;
  five comparison consumers at `:2785–2805`.
- `crates/yu-hir/src/module/source_annotation.rs`, SHA-256
  `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`;
  exact `PinnedPrimitiveOp` identities at `:82–105`.
- Prior bounded source/readback handoff:
  `tasks/agent-loop/sprints/native-literal-readback-20261025-r1-outcome.md`
  and `notes/theory/2026-10-25-native-literal-producer-invariant.md`.
- Prior integer implementation result:
  `tasks/agent-loop/sprints/integer-comparison-and-permission-bridge-20261024-outcome.md`.

The repository Lean pin is `leanprover/lean4:v4.35.0`, with project `-j1`
and `-M1024`. Do not change the toolchain, package manifest, root import or
Rust implementation while constructing the theorem.

## Claim boundary and falsifier

Claim class: candidate source-to-Lean mathematical correspondence. It can close
only the decimal comparison relation slice of primitive execution fidelity.
Original all-primitive execution preservation, complete machine safety,
source/native trace realization, accepted source input reachability, integer
producer correctness beyond the separately reviewed invariant, inference A/B,
and production remain OPEN.

Falsifier: a grammar-valid pair for which normalization, sign handling, length,
lexicographic order, or one Boolean consumer differs from `Int.compare` on the
two decoded values. Required discriminators include `-0` versus `000`, leading
zero variants, both-negative reversed order, mixed signs, and arbitrarily long
valid values. Invalid text must be rejected by model parsing; it must not be
silently assigned an integer comparison.

## Exact leases and roles

Luna alone writes this contract and `tasks/agent-loop/current.json`, performs
source/HIR-to-consumer mapping and primary verification, and integrates Git.
One registered `lean_prover` owns exactly:

- `notes/theory/lean/YulangClosure/NativeIntegerComparison.lean`
- `tasks/agent-loop/inbox/native-integer-comparison-r40.md`

The prover receives the frozen sources and the exact claim above. The prover
does not edit `YulangClosure.lean`, repository policy, Rust, existing Lean
modules, expected outputs, tests, source notes or the question board; it does
not run builds/checkers or touch `.lake`. The Luna primary is the sole Lean
checker/cache owner under the existing `.lake/build` lease and owns one uniquely
named audit source and complete verification receipt under `.lake` and
`tasks/agent-loop/inbox/`. After the candidate freezes, a fresh non-author
`compiler_referee` owns only
`tasks/agent-loop/inbox/native-integer-comparison-r40-review.md` and checks the
source branches, theorem meanings, boundary examples and omissions read-only.

No Rust writer is assigned: current Rust implementation is already integrated,
and there is no safe implementation change in this packet. The 8 existing
UNKNOWN reservations stay quarantined. Capacity allows one proof worker while
keeping a separate slot for review and one for integration; no extra research
worker or child team is started.

## Resources, build and stop conditions

New R40 ceiling: 1800 active seconds total: prover at most 900, Luna at most
600, reviewer at most 300. Lean/checker maximum 14 calls and 180 cumulative
checker seconds, one process at a time, 120-second per-call cap; no Cargo, Rust
tests, benchmarks, or additional compiler processes. No prior unused budget is
carried forward. Primary records actual launch/model/runtime observations and
charges the full grant if cessation cannot be established.

Primary resolves an already-installed pinned Lean/Lake before invoking any
proxy, builds changed imports before the module, checks every required theorem
signature and its full `#print axioms`, and scans the changed dependency cone for
holes or checker bypasses. Allowed project axiom set is `{propext, Quot.sound}`;
no `sorry`, `admit`, project axiom, `Classical.choice`, `native_decide`, or
weakened theorem is accepted. Preserve every failed proof/check receipt. Stop on
the first blocked authority premise, changed frozen input, exceeded resource
limit, or unresolved failure at the cap.

## Source application and integration gate

Luna's source receipt must connect: the exact HIR primitive identity, the
`machine.rs` integer-kind extraction and `decimal::compare` call, each
Ordering-to-Bool arm, and the existing integer `Grammar` producer invariant.
It must state which premises come from Lean and which are source-read evidence.
The result supplements the actual-call primitive/readback chain; it does not
claim arbitrary Rust execution was verified.

After checking the candidate and source receipt, freeze exact hashes, obtain the
one fresh review, close any accepted blocking/major finding in one bounded
repair pass, then Luna may add the module to `YulangClosure.lean` and verify the
integration target. Commit only the contract, current state, reviewed proof,
handoff/review/verification artifacts and intended import. Keep both pending
question directories completely unstaged and uncommitted. Inspect the full
outbound range and intended upstream before a normal non-forced push.

Before: arbitrary-precision signed integer readback is proved, and Rust integer
relations use sign/normalized-magnitude comparison, but no Lean theorem joins
those facts. After: the exact Rust comparison branches are related to decoded
mathematical integers, narrowing the primitive source/native gap by one scalar
operation family. The full Yulang executor and inference theorem remain OPEN.
