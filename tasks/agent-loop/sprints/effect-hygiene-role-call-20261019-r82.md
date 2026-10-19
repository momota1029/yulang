# R82 — one role-call compatibility contract

Status: ACTIVE — adoption package only; no source-code authority  
Prior boundary: R81 Stage1 closeout,
`notes/progress/2026-10-19-r81-closeout.md`, SHA-256
`94d97c332604dbda0aa94802ccf7836f5cc149c2e45b0fd548c01c34e5675a91`  
R81 contract SHA-256:
`57989ca9d6f7b54d2bffa37fb5399f9d0bcaf16ea5193109d7bb7c7547914c16`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
R80 manifest SHA-256:
`a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`
(103 exact source pins; recheck before source claims).

## 1. Goal and fixed user priority

Balance breadth with depth across effect hygiene, method syntax and roles, and
an early runnable surface. The first surface remains the role-qualified call
`SecondInt::second 1 2`, intended to complete with `2` through ordinary
Call/Apply. Broad dot dispatch and field/method collision semantics are
deferred so this first path can reach execution without introducing another
lookup decision. The six effect frontiers remain a bounded status map; this
packet does not continue storage/fiber enumeration.

Original Simple-sub/evaluator and A/B claims, source/native correspondence,
quantifiers, expected outputs and prior gate statuses remain unchanged. Parent
and A/B stay OPEN 0→0; R50 stays NOT_ADOPTED. No frozen `main` changes.

R81's contract prohibits in-place correction after its major review finding.
This is a separately versioned successor contract with new outputs, frozen
inputs and fresh review. R81 artifacts remain immutable.

## 2. Stage 1 — one aligned adoption package

Stage 1 has no code/test authority. It produces one shared bounded
compatibility definition, one adoption document that quotes/references that
definition by hash, a proof that specializes to exactly the same judgment, a
readiness record, and fresh reviews. The compatibility definition is authored
and frozen before proof work begins.

Use the decision draft's smaller domain:

- module-local monomorphic role/member;
- `int` receiver with Value entry;
- explicit parameters are either `int` or `()` Value, or explicitly annotated
  `[_] int` Computation;
- ordinary `int` result;
- exact arity; no polymorphism, `bool`/`str`, closed effect-row matching,
  Computation receiver/result, higher-order slots, implicit adapter, or field
  collision rule in the pilot.

Every source executable formal gets its entry role from its own outer source
annotation under charter §21. The signature never supplies binder annotations.

Define exactly three classifications and their pilot consequences:

1. **Compatible:** both declarations are in the supported domain and slot
   count, ground endpoints, result and Value/Computation roles agree. This only
   clears role/member compatibility; ordinary inference, effect constraints,
   candidate construction and runtime admission remain necessary.
2. **Incompatible:** both sides use supported forms but arity, ground endpoint
   or entry role differs. Reject that implementation declaration before
   executable member admission; retain the exact source anchors. No implicit
   adapter.
3. **Unsupported:** a source slot or annotation lies outside the pilot domain.
   Do not admit it through this provisional path and do not report a general
   language rejection. Ordinary language inference outside the pilot remains
   untouched.

Stage1 success requires the design table, all source examples, proof theorem,
classification cases and adoption questions to use this exact domain and these
outcomes. In particular, `bool`, `str`, closed rows, Computation receiver/result,
Box and dot collision must not be proven as supported or mislabeled as
Incompatible.

The proof lane proves only classification by cases and §21 binder-role
preservation for Compatible declarations, then specializes R81's request-prefix
simulation to this exact source envelope. It does not turn P1–P4 into producer
facts or close parent A/B. Preserve the corrected unanswered-request trace:
first Value receiver request `observe(1)` exits with its suspended suffix; no
later argument request or result is promised.

Concrete cases must include: supported pure result `2`; supported Value and
explicit Computation arguments; Value/Computation mismatch; supported type or
arity mismatch; at least one Unsupported form; missing role/member/implementation;
duplicate implementation key; same member spelling in distinct roles. General
dot collision is explicitly OPEN and has no syntax/precedence claim.

## 3. Exact outputs and leases

- `notes/design/2026-10-19-r82-role-call-compatibility.md` — Luna only; freeze
  before proof starts.
- `notes/design/2026-10-19-r82-role-call-adoption.md` — Luna only.
- `notes/theory/2026-10-19-r82-role-call-preservation.md` and
  `tasks/agent-loop/inbox/20261019-r82-proof.md` — prover only, after the shared
  definition hash is pinned.
- `notes/progress/2026-10-19-r82-stage1-readiness.md` — Luna only.
- `tasks/agent-loop/inbox/20261019-r82-compiler-review.md` and
  `tasks/agent-loop/inbox/20261019-r82-spec-review.md` — reserved for independent
  reviewers only, if their read-only roles permit a receipt; inline verdicts
  remain valid review evidence.
- `tasks/agent-loop/current.json` — Luna only.

Fresh exact review targets are the frozen R82 contract, compatibility
definition, adoption package, proof, handoff, readiness, R81 closeout and R80
103-entry manifest. Review Stage1 conformance, identical classification
boundaries, §21/request-prefix fidelity, proof premises, and the user adoption
surface. Any major blocks readiness. No same-contract correction retry; a
changed decision requires another versioned successor.

No source, HIR, solver, runtime, test, fixture, expected-output, CLI, or public
documentation path is leased. No tests/builds/probes/CLI/Git operation is
authorized.

## 4. Resources and stop gates

Stage1 cap 1200 seconds, charged at grant: Luna design 300, proof 300,
compiler review 200, spec review 200, Luna integration/closeout 200. No Astra,
no time carryover, and no Stage2 reservation. At most these four lanes are
active/reserved. Unknown runtime or cessation retains its exact lease and
charge.

Stop on a counterexample, source/design conflict, missing exact pin, major
review finding, exhausted budget or uncertainty in approved behavior. Keep
conditional claims conditional, preserve OPEN parent scope, and change no
expected output. New semantics stay Draft until fresh independent review and
explicit user adoption.

## 5. Later executable gate

After Stage1 passes independent review, present the exact adoption package for
explicit user decision. Only after adoption may Luna issue a separate
implementation contract with exact source-owner pins, code leases, focused
commands and producer-to-proof bindings. It should implement the first
qualified call end to end and verify its result through the existing ordinary
runtime. The old R80 Stage2 reservation does not revive. Dot-method syntax and
field/method collision are a later separately reviewed decision.
