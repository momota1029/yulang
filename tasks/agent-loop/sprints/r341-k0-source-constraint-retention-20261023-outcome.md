# R341 outcome — K0 source-constraint retention and conditional S0

**Status:** closed as a bounded research sprint. The unchanged S0 source-typing
implication is accepted under its four stated premises. No solver, runtime, or
production gate is promoted. Contract rev1 SHA-256:
`62cb4018db42e0266f0f357ed6f44c187d6397865905b68487fe143d00250769`.
User audit SHA-256:
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

## Dispositions

- **Authentic Definition-root Link — PASS.** The source action is the actual
  body Value endpoint ≤ root Definition Value. Successful fresh and duplicate
  receipts both add the inequality to live `H`; store identity and completion
  stamps do not establish entailment. Before bound insertion the drain retains
  the request; after insertion the exact owner-side cell is read back and
  remains in the physical bounds through replay, acknowledgement, drain-frame
  retirement, and root capture. The lower body's negative direct-upper-row
  lane represents precisely the requested Value inequality.
- **All seven K0 constructor families — PASS.** The authenticated inventory
  covers literals, enclosing Value-Lambda parameter Names, annotation-free
  Value Lambdas, Apply, else-complete If, Group, and binding-free
  Block/StatementBlock. It includes every condition and branch, every
  expression-prefix Effect, both Lambda auxiliary Effect rows, and each
  Apply's actual invocation Effect. The parameter Name uses its registered
  formal endpoint; its unused collected Value component is not identified
  with that formal.
- **Kind-preserving row transport and unchanged S0 application — PASS.** The
  proof specifies the source-to-native map, sort tags, nested Function-row
  support, Lambda entry/return Effects, Apply invocation Effects, and the
  final representative map. `H(S)` retains its independent live B/Q/P/R
  interpretation; inactive historical receipts add no formulas. Reifiability
  is restricted along the same map. The retention bridge composes with the
  reviewed R336 D1/G-sound and R337 J results to derive exactly:

  ```text
  ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ)
    ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
  ```

  No M/runtime premise is inserted. This is conditional source typing; it
  does not prove that a solution or a `NativeComplete₀` state exists.

## Frozen evidence and review

- Primary census: `notes/theory/2026-10-23-r341-k0-source-retention-census.md`,
  SHA-256 `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb`.
- Proof rev1: `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md`,
  SHA-256 `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f`.
- Producer handoff rev1:
  `tasks/agent-loop/inbox/20261023-r341-k0-source-retention-prover.md`,
  SHA-256 `42953aa3220116db99ec5a7d31c050721f20230120f83205fe52f4ed26b50188`.
- Fresh non-contributor `/root/r341_retention_referee` (`compiler_referee`)
  independently returned bounded PASS for the root Link, seven constructor
  families, and kinded transport/S0 application. All contract, audit, census,
  proof/handoff, eight production-source, and bounded R336/R337/R339 pins
  matched. No BLOCKING/major/minor finding or authentic final-H counterexample
  was reported. Luna accepted the bounded result. The reviewer was read-only;
  full 900-second grant charged conservatively; exact stop clock unavailable.
- Separate delta receipts: R338 admission correction PASS and R340 S0/S0+M
  appendix PASS. Fresh/duplicate admission retains `H_after=H_before∪{q}`;
  unchanged S0 keeps its four premises, while M/runtime belongs only to the
  separate safety composition. They do not reopen the unchanged producer
  proofs.

## Remaining gates and evidence limits

Whole N/cache/coverage, non-E Function/Function cache and retirement,
designated/foreign processing obligations, W, Z, model existence, broader
source completeness, export witness transport, M/runtime safety, principality,
original Simple-sub A/B, catalog, and production remain **OPEN**. No compiler
defect or safe implementation slice was found. No tests, Cargo/builds, or
execution probes were run. The static state/tooling check passed; it is not
mathematical evidence.

R341 grants: primary census 2,100s; proof 2,400s; delta reviews 300s; fresh
referee 900s; integration reserve 300s. Charge the full 6,000s conservatively,
with no carryover. The supplied user audit remains untracked and is excluded
from Git integration.
