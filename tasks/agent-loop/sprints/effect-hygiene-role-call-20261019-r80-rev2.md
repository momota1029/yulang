# R80 revision 2: role method vertical slice with effect preservation

Status: CANDIDATE — final selector delta and Luna activation pending  
Revision: 2; supersedes unactivated R80 revision 1, preserved unchanged  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
Original parent: Simple-sub/evaluator and A/B OPEN 0→0; R50 NOT_ADOPTED  
Direction: user requests breadth and depth together, effect hygiene across its observable paths, method/role progress with proof, and an early runnable surface.

## Fixed end outcome

Deliver a reviewed, runnable role-qualified method call through the existing source → HIR → ordinary Call → candidate admission → playground path. The candidate example is:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

After the user explicitly adopts the reviewed call and declaration rules, the vertical slice must execute this program and produce `2`. This syntax and its resolution rules are a draft proposal; the user's priority does not itself adopt them. Keep general `.member` collision behavior outside the slice and OPEN.

The same slice must preserve the approved §21 Value/Computation boundary and ordinary Apply behavior. Its preservation argument will connect a selected source member to its exact `(ImplId, MemberId)`, validated executable member root and lexical environment, generated ordinary Call, and runtime target. Unsupported or unvalidated declarations remain rejected before candidate publication or execution.

## Stage 1 — proof and adoption package, 2100 seconds

No source, test, fixture, expected-output, runtime, semantic-adoption, build, test, probe, CLI, or Git action is authorized in Stage 1.

### Proof lane — 1200 seconds

Build a source-qualified simulation argument for the candidate call lowering to ordinary Call. Track the selected member occurrence and identity, implementation formal annotations, argument construction and order, lexical bindings, receiving roles, and outward effects. State exact premises from the reviewed R78 receiving/selection certificate and R79 source audit. Reuse those results conditionally; do not claim native K/D, residual typing, arbitrary continuation resumption, or universal effect hygiene from them.

Alongside the role-call path, prepare an effect-hygiene frontier map with evidence and remaining owner across six distinct behaviors: (1) direct matching handler selection and arm priority, (2) retained Computation arguments versus Value entry, (3) wrong or sibling receiver permission, (4) shallow unmatched outward requests, (5) one concrete continuation capture/transport/resumption path including protected-sibling status, and (6) one static-to-runtime operation path through effect annotation, HIR/candidate evidence, native `K,D` or residual owner, and execution. Include the existing U/O/S fixture conclusions where relevant. For frontiers (5) and (6), identify the exact source/native constructors and consumers and first unproved premise; do not claim universal coverage from one occurrence. Do not perform exhaustive storage/fiber/capture inventories. At most 300 seconds total may go to parser/root-dispatch reconstruction or following one concrete continuation/storage path. If one exact premise remains after two materially different methods, report it OPEN with its source owner rather than repeating the same proof attempt.

Success is an occurrence-indexed conditional preservation argument and an honest, source-owned status map across all six frontiers. It must show what is established, conditional, and OPEN, and explain why the next highest-value proof action does not return to open-ended storage bookkeeping. Tests alone establish none of these claims. Parent evaluator/A-B remain OPEN unless their original quantifiers are genuinely discharged and independently reviewed.

### Design lane — Luna, 600 seconds

Correct the known R79 defects and produce one compact decision package for the whole vertical slice:

- Explicitly annotate Computation on both role signature and executable impl binder; do not infer binder role from the signature.
- Include complete unique, missing role, missing member, missing implementation, duplicate same-key implementation, and two-role same-spelling programs with expected draft outcomes and diagnostic anchors.
- Give the ordinary Value and Computation entry cases, receiver/argument evaluation order, and outward request behavior with exact source examples. Tie each compatibility claim to charter §21 and the ordinary Apply consumer.
- Specify declaration validation, exact member identity, member root/environment, ordinary Call provenance, candidate preflight/admission, and runtime metadata ownership.
- State the proposed first-run test and CLI commands against pinned entrypoints. They are future-only in Stage 1.
- Preserve callable-field/dot collision, arbitrary open-world lookup and unresolved source/native effect obligations as explicitly OPEN.

No new semantic alternatives are invented implicitly. Mark every novel call/diagnostic choice as Draft. The user approval surface must be a small explicit list whose adoption is sufficient to begin one end-to-end implementation sprint.

### Stage 1 review — compiler/source and spec/design, 150 seconds each

Review the frozen proof and decision package independently. A major finding prevents adoption readiness; no automatic correction retry. Keep R78/R79 frozen and attach their findings as read dependencies.

## Stage 2 — implementation after explicit adoption, 3300 seconds

Stage 2 is not active and has no code or verification authority until the user explicitly adopts the exact reviewed revision and Luna records the authority revision. If adopted, revalidate source pins and create the implementation contract revision before opening code leases.

- Luna/implementer: 1800 seconds for one end-to-end implementation across source-owned role/member identity, validation/materialization, ordinary Call construction, candidate admission and runtime dispatch. A focused reversible prototype may be retained only if it follows the adopted semantics and the production gate is explicit.
- Fresh compiler/source review: 600 seconds; fresh spec/design review: 600 seconds. Review the frozen code/proof and the exact command results; do not treat tests as proof.
- Luna integration/closeout: 300 seconds.

The Stage 1 proof author must bind the conditional simulation to the actual implementation bytes in a leased correspondence handoff before final review; reviewers check that binding but do not supply it. The selector-identified prospective owners are HIR declaration/local-source and source-identity paths, solver `candidate_source.rs` and `shadow_apply.rs`, playground `runtime/program.rs`, and a focused runtime module-expression test plus one `.yu` fixture. Exact paths and hashes must be fixed before Stage 2; workers cannot expand them. Verification must cover unique resolution, all named resolution failures, Value entry, explicit Computation retention, effectful operands/order and outward requests. The key success is the adopted source program running to `2` through the ordinary Call path.

Any source/native dependency outside the frozen manifest requires a Luna-owned versioned manifest/contract correction before inspection. If it is not added, name the owner from already authorized evidence and mark that frontier OPEN/uninspected.

If the user does not adopt the package, stop at `AWAITING_ADOPTION`; do not reinterpret preference as approval. That is an authority boundary, not evidence of compiler failure.

## Effect-hygiene bounds and original gates

This sprint broadens effect coverage along receiving, permission, handler matching, outward propagation, one continuation path, and static/native correspondence. It does not continue open-ended storage/fiber/future capture inventories. It does not claim universal hygiene, native residual soundness, complete continuation behavior, or closure of the original evaluator/A/B theorem. Preserve all original quantifiers and accepted-source scope. A genuine counterexample is recorded as REFUTED for its exact claim and returns to Luna; never shrink the source domain to salvage the route.

## Frozen inputs and prior findings

Use the exhaustive read manifest at `tasks/agent-loop/sprints/r80-producer-manifest-20261019.md`, SHA-256 `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`. It pins the production parser/HIR/recovery inventory, HIR/solver/runtime owners, existing receiving fixtures, top-level inference principles, charter §21, R78 proof, and the four frozen R79 artifacts. No worker expands the read set; Luna may issue a versioned manifest correction before the affected read.

R78's runtime certificate remains conditional at raw source → LocalSource and leaves native/residual/universal claims OPEN. R79's source proof stopped at the previously unpinned parser root dispatcher; its role draft failed §21 binder annotation and missing-role completeness. R80 revision 1 is preserved unchanged and is not an active contract.

## Exact Stage 1 leases

Luna owns:

- this revision, `tasks/agent-loop/current.json`, and `notes/progress/2026-10-19-r80-rev2-closeout.md`;
- `notes/design/2026-10-19-r80-rev2-role-call-decision.md` and `notes/progress/2026-10-19-r80-rev2-runnable-handoff.md`.

The proof worker owns only `notes/theory/2026-10-19-r80-rev2-role-call-effect-preservation.md` and `tasks/agent-loop/inbox/20261019-r80-rev2-proof.md`.

Fresh compiler/source reviewer owns only `tasks/agent-loop/inbox/20261019-r80-rev2-compiler-review.md`; fresh spec/design reviewer owns only `tasks/agent-loop/inbox/20261019-r80-rev2-spec-review.md`. If read-only roles prohibit writing, Luna records inline-only receipts with target hashes and cessation evidence. Freeze all review targets before review.

Stage 1 spends a fresh 2100-second allocation: proof 1200, design 600, compiler review 150, spec review 150. Luna's 600 seconds include handoff, current-state updates and closeout/AWAITING_ADOPTION bookkeeping; there is no separate Stage 1 integration reserve. No carryover from R78/R79 or R80 revision 1. Reserve no hidden worker/runtime time. Stage 2's 3300 seconds are an unissued conditional maximum and do not reserve a worker or authorize execution before adoption.

No Astra. Stop at a material semantic contradiction, missing required source authority, exhausted allocation or major review finding. Close only the bounded conditional simulation and decision readiness after independent review. Do not close or reclassify the original A/B gate.
