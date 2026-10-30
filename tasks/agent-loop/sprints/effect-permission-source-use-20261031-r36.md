# R36 — source-owned callback use and permission-row selection

Status: CANDIDATE until admission is recorded in current state.
Sprint ID: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`
Branch / baseline: `yulang3` / `1388bdc476e5dc0c0bb96532715c7280aa95b10e`
Contract revision: 1

## Original outcome and success evidence

Advance the user's selected annotation-effect hygiene policy toward Rust/Lean
correspondence. Preserve the original language domain and semantics: a
contravariant annotated concrete effect grants local subtraction permission;
a covariant annotation allows that concrete effect; symbolic variables remain
connected and are never erased. This bounded gate identifies an exact source
callback use and its permission row. It does not close the original whole-
language hygiene or soundness claims.

R35 established an authenticated, complete source annotation-row inventory
with composed path polarity. R36 must construct a source-owned
`SourceCallbackUseWitness` from the same retained HIR snapshot, root, Lambda,
formal and resolved source occurrences. For each supported direct callback
use, bind the exact parameter `Name` occurrence resolved to that formal to the
exact `Apply` occurrence where that Name is the callee. Preserve the source
owner identities and `NameConsumption::Observe` fact. Select the callback
permission only from the formal's approved function shape and its exact result
row path and polarity (the R35 `Function.result` coordinate); retain ordered
concrete entries, duplicates and symbolic entries unchanged.

Success requires: (1) a Rust lookup/API in `program.rs` that derives, rather
than accepts from callers, the source coordinates and selected R35 row; it
withholds unsupported or ambiguous shapes and foreign/shadowed/mismatched
occurrences; (2) constructive Lean definitions and theorem types deriving the
corresponding R35 source-row facts and exact source-use coordinates from the
authenticated lookup; (3) pinned Lean 4.35.0 stdin audit with complete theorem
types and axiom reports and no holes/project axioms; (4) fresh independent
review of frozen Rust/Lean bytes and their correspondence.

Falsifiers include a foreign formal, shadowed Name, swapped Apply occurrence,
covariant allowance accepted as the callback permission, a dropped symbolic
entry, or a result row selected from a different nested path.

## Authority, lanes and exact output leases

Authority: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§1 and §1.1; source ownership and identity: the exact pinned HIR and syntax
inputs in the R36 manifest; prior abstract inventory: R35's frozen Lean module
and independent review in that manifest. No new semantic choice is authorized.

- Rust implementer, requested Luna/high: write only
  `tools/inference-playground/src/runtime/program.rs` and
  `tasks/agent-loop/inbox/effect-permission-source-use-r36-rust.md`.
- Lean prover: write only
  `notes/theory/lean/YulangClosure/SourceCallbackUseR36.lean` and
  `tasks/agent-loop/inbox/effect-permission-source-use-r36-proof.md`.
- Fresh independent reviewer: after both producer outputs are frozen, read the
  manifest-pinned dependencies and both outputs; write only
  `tasks/agent-loop/inbox/effect-permission-source-use-r36-review.md`.
- Luna owns all central state, contract/manifest/admission/ledger/outcome,
  review adjudication, staging, commit and push.

Do not change `Instruction::Apply`'s shape. Do not read or write quarantined
`tools/inference-playground/src/runtime/machine.rs` or `receiving.rs`, or any
other path. If the source witness requires those definitions, another source
owner, or broader authority, stop and return the exact seam to Luna.

## Two lanes, boundaries and non-goals

Rust may inventory multiple direct parameter-Name-as-callee Apply uses; it must
not choose an arbitrary first use. Every witness is tied to exact source root,
HIR snapshot, Lambda/formal, Name occurrence and Apply occurrence. A grouped or
otherwise unsupported source shape may be withheld explicitly; no whole-source
claim follows from that restriction. `Observe` is a retained source/runtime
classification only; it does not mean permission was consumed.

Lean must state exact premises and bind lookup-derived values in theorem
conclusions; caller-supplied equalities are not authentication. Apply R35's
actual result-row path/polarity and preserve concrete order/multiplicity and
symbolic information. If the abstract source model lacks a constructor needed
to connect the direct Name/Apply edge, report the precise missing premise;
do not weaken the target or manufacture source restriction.

This is a source-side planned-use witness, not execution, a runtime Name
receipt, callback invocation, Grant, Catch, handler result, native Step/History,
or Rust/Lean vector simulation. It does not prove original Simple-sub A/B,
whole-language hygiene, soundness, principality, progress, termination or
production readiness. The actual runtime consumer owners remain quarantined.

## Resources and verification

Aggregate envelope: 6,000 seconds total: Rust 1,600; Lean 1,600; fresh review
1,200; Luna 1,600 including 500 closeout; Astra 0. No transfer from prior
sprints. At most two producers before review. No Cargo, Lake build, tests,
target/cache/scratch, copy, extraction, worktree, clone or new environment.
Lean verification uses the pinned project toolchain 4.35.0 and the existing
read-only stdin audit route; record every theorem type and complete axiom set.

Independent review must check exact-source conformance, the falsifiers above,
source-to-Lean correspondence, open parent claims, and frozen hashes. Any
blocking finding keeps the checkpoint out of the pushed range until repaired
and freshly reviewed. A successful bounded gate may be committed and pushed
only by Luna after exact-path staging and outbound-range inspection.

## Continuation and stop conditions

Related construction and proof steps within these leases may continue without
new consultation. Stop at an authority/dependency/lease seam, unavailable
source identity, unsupported semantic shape, falsifier, budget limit, or user
STOP. Keep all 32 pending records, UNKNOWN workers, quarantined path leases,
and the existing R17 WAITING reservation unchanged. Do not interpret capacity
release as writer cessation.
