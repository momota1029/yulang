# R81 — effect hygiene and first role-qualified call

Status: ACTIVE — Stage 1 only  
Original goal: deliver type inference and evaluation with proofs while keeping
the working tree coherent. Current user priority: balance breadth with depth;
prove a useful range of effect hygiene, method syntax and roles; get the first
surface running early; do not spend indefinitely on effect-storage/fiber depth.  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Prior boundary: R80 rev2 closeout, `notes/progress/2026-10-19-r80-rev2-closeout.md`,
SHA-256 `8b6593f1d2bc55a1c37065e2e9fd780cec46f3c92b3076329bde065f80f989f7`.  
Prior source manifest: `tasks/agent-loop/sprints/r80-producer-manifest-20261019.md`,
SHA-256 `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`;
103 entries must still match before any source claim.  
R80 contract SHA-256: `e7ff179d48156bf3aa897c4e8f186916936a6b0bbcea7bc0314cad3a7e7f110e`.

## 1. Target and boundaries

Reach the first role-qualified method call through declaration validation,
selected-member materialization, ordinary Call, candidate admission and
runtime execution, while establishing source-qualified local preservation
evidence and a broad, bounded effect-hygiene frontier map. The first runnable
candidate remains:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

Its proposed output is `2`. It is a Draft until the exact package below passes
independent review and the user adopts it. Do not silently turn this contract
into semantic approval.

Keep the original Simple-sub/evaluator claims and quantifiers, source/native
correspondence, A/B obligations, expected outputs, and R78/R79/R80 statuses.
Original parent and A/B remain OPEN 0→0; R50 remains NOT_ADOPTED. No frozen
`main` changes, broad storage/fiber inventory, universal effect-hygiene claim,
or expectation edits.

## 2. Stage 1 — adoption package, no code

Stage 1 produces three frozen artifacts: a bounded decision package, a
constructive request-prefix/role-entry derivation, and a runnable-path handoff.
The package must:

1. Correct the R80 counterexample. The pure `SecondInt` program may complete
   with `2`. An unhandled effectful Value receiver must expose the first
   outward request and suspended suffix; it must not promise later requests or
   a final value. If using handlers to show completion, give the complete
   supported source and derive the exact result from ordinary Apply/runtime
   consumers without changing existing expectations.
2. Define a bounded compatibility judgment for role signatures and executable
   implementation binders: arity, receiver and parameter entry roles, ground
   types, and permitted annotations. The outer source annotation fixes each
   binder's Value/Computation role under charter §21. State exactly which
   mismatches reject, which require an explicitly selected adapter, and which
   remain outside the pilot. No implicit signature-to-binder role inheritance
   and no permission-as-effect-cap reinterpretation.
3. Give concrete missing-role/member, multiple-implementation, same-name
   callable-field, Value and Computation cases with proposed outcomes. Keep
   general dot collision policy OPEN if the chosen qualified pilot does not
   exercise it.
4. Connect the local preservation argument to the ordinary Value/Computation
   entry rules, exact permission, ordered request propagation, shallow
   unmatched outward requests, and one concrete continuation path. Retain the
   six-frontier status map. For each frontier state what is proved, conditional,
   inspected, OPEN/uninspected and the exact owner. Do not call a status map a
   proof; do not expand into an exhaustive storage/fiber survey.
5. Replace each R80 producer hypothesis only when its exact constructor and
   consumer are pinned and established. In particular, continuation template,
   native operation/formal and K,D/residual consumers, protected-sibling
   preservation, and complete source-to-HIR projection may remain explicitly
   OPEN if their owners are outside the manifest. Do not inspect unpinned files.
6. Name the first executable source path through declaration validation,
   member identity/materialization, CandidateInference, RuntimeProgram and
   ordinary Call, plus focused future commands. Execution is evidence of this
   example only, not a parent theorem.

### Stage 1 claim classes

- **Proof lane:** prove a bounded ordinary-Apply request-prefix simulation for
  the selected-member call under explicitly stated source/producer hypotheses;
  prove the bounded compatibility judgment preserves §21 formal-entry roles.
  Apply both results to the original open goals and name every remaining
  premise/owner. This is a conditional derivation unless actual producer facts
  replace the hypotheses.
- **Design lane:** author exact complete source cases, compatibility table,
  diagnostic/admission boundary, effect outcomes, and first executable path.
  Mark all new choices Draft and list the exact adoption questions.
- **Review:** one fresh `compiler_referee` and one fresh `spec_auditor` review
  frozen decision/proof/handoff bytes and their pinned dependencies. Any major
  finding blocks adoption readiness. No automatic retry; a new attempt needs a
  separately versioned contract.

### Stage 1 exact outputs and leases

- `notes/design/2026-10-19-r81-role-call-adoption.md` — Luna only.
- `notes/theory/2026-10-19-r81-role-call-request-prefix.md` and
  `tasks/agent-loop/inbox/20261019-r81-proof.md` — prover only.
- `notes/progress/2026-10-19-r81-stage1-readiness.md` — Luna only.
- `tasks/agent-loop/inbox/20261019-r81-compiler-review.md` — compiler reviewer
  only.
- `tasks/agent-loop/inbox/20261019-r81-spec-review.md` — spec reviewer only.
- `tasks/agent-loop/current.json` — Luna only.

No source, test, fixture, expected-output, runtime, task-history or public-doc
lease exists in Stage 1. No test/build/probe/CLI/Git operation is authorized.

## 3. Stage 2 — unissued and gated

Stage 2 may be separately granted only after (a) Stage 1 has no unresolved
major review findings, (b) Luna has recorded exact review receipts, and (c) the
user explicitly adopts the exact semantic package. Then implement only the
adopted bounded slice through source → HIR/member identity → candidate
construction/propagation → RuntimeProgram → execution. A Stage 2 successor
contract must pin its own baseline, exact owners, files, focused verification
commands, proof-to-source bindings and rollback/stop gates. It may not inherit
unused time or broaden the adopted envelope.

## 4. Resources and stop gates

Stage 1 cap: 1200 seconds, charged at grant: Luna design/bookkeeping 600,
proof 300, compiler review 150, spec review 150. No Astra and no carryover.
Stage 2 has zero issued/reserved time. At most the four named assignments are
active/reserved; unknown runtime or cessation keeps its exact lease and charge.

Stop the affected lane on a counterexample, missing pin, source/design conflict,
major review finding, exhausted budget, or uncertainty about approved meaning.
No source edit or Stage 2 activation follows from a proof artifact, green check,
conditional result, or this contract. Preserve every incomplete parent as OPEN
with its original owner and quantifiers.

Consult the next-action selector at the next material blocker, integration
seam, resource/authority change or sprint closeout. Luna owns all authority,
current-state updates, review adjudication and Git integration.
