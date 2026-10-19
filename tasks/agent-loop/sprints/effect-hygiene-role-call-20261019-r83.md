# R83 — adoption-ready qualified role call

Status: ACTIVE — design/proof/review only; no code authority  
Prior boundary: R82 closeout,
`notes/progress/2026-10-19-r82-closeout.md`, SHA-256
`a296ae59e8db86f3f3a2ea19071a0afbb6140e28f4a64a9b0d32c4b1843c347c`  
R82 contract SHA-256:
`a11cd61b71548ce144f60557c3c8b6fe32d3cce698b4dd58657fb6e33d85adce`  
R81 conditional proof SHA-256:
`d3b3d52e19332506c6fab8eea7878a5ff1c81f90cf96dff548b30ab5f88c767f`  
R80 manifest SHA-256:
`a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`
(103 source pins; revalidate before source claims).

## 1. Goal and invariants

Follow the user's current priority: balance breadth with depth; cover useful
effect-hygiene behavior and method/role semantics with proof; reach a runnable
surface early; avoid indefinite storage/fiber analysis. The candidate surface
is `Role::member receiver args`, initially
`SecondInt::second 1 2`, proposed result `2`, lowered through ordinary curried
Call/Apply. General dot-method lookup and field collision remain OPEN and out
of scope for this pilot.

Original Simple-sub/evaluator and A/B statements, accepted source domain,
quantifiers, source/native correspondence, expected outputs, and all previous
gate statuses remain unchanged. Parent/A-B stay OPEN 0→0; R50 stays
NOT_ADOPTED. No frozen `main` changes or production work.

R82 is closed REPLAN_REQUIRED. This is a separate versioned successor with new
outputs. Preserve the exact R82/R81 bytes. The R81 proof may be reused only
under its stated producer hypotheses P1–P4 and exact pins.

## 2. One exact compatibility definition

Luna first freezes one shared compatibility definition. Define source-signature
eligibility and implementation-form eligibility **independently**. In
particular, `ImplEligible(i)` must not compare binder count against a signature.
Then classify the pair:

```text
if !SigEligible(s) || !ImplEligible(i): Unsupported
else if arity, supported endpoint, result, or §21 entry-role vectors disagree:
    Incompatible
else:
    Compatible
```

Thus extra/missing binders are Incompatible when all forms on both sides are
independently supported; an excluded binder or slot form is Unsupported.
Compatible does not imply body typing, exact source-member identity, candidate
admission, runtime support, or any of the R81 hypotheses P1–P4. It permits only
the ordinary checking/admission steps that already exist or are separately
authorized.

The selected narrow envelope remains: module-local monomorphic role/member;
`int` Value receiver; one or more explicit parameters from `int` or unit `()`
with Value entry, or explicit `[_] int` with Computation entry; ordinary `int`
result. Exclude bool/str, other receivers/results, closed rows, Computation
receiver/result, higher-order slots, adapters, dot-method collision and
polymorphism. Charter §21 alone determines executable binder roles; a
signature never annotates a binder.

The definition file's hash is a mandatory direct dependency of adoption and
proof artifacts. No proof work begins before Luna freezes it. If the exact
scope/outcomes change after proof starts, stop and replan; no automatic retry.

## 3. Stage 1 deliverables

Produce the complete reviewable adoption offer in this one sprint:

1. A shared definition with separate eligibility predicates, a total and
   disjoint Compatible/Incompatible/Unsupported classifier, and exact
   provisional consequences.
2. Complete source examples whose classifications all match that definition:
   pure result `2`; Value and explicit Computation cases; supported arity,
   endpoint and role mismatches; at least one Unsupported form; missing role,
   member and implementation; duplicate implementation key; same spelling in
   distinct roles. Do not include Box or dot-collision cases.
3. A proof of classifier totality/disjointness, the finite §21 role-preservation
   lemma for Compatible declarations, and specialization of the R81
   ordinary-Apply prefix result to exactly the shared envelope. Keep R81 P1–P4
   OPEN, the exact first unanswered `observe(1)` request/suffix, and the six
   effect-hygiene frontiers as evidence-status map only.
4. A source-to-runtime handoff for the first role-qualified path and exact
   future owner boundary. No current source facts may be inferred from the
   proposed path.
5. An exact adoption question list that authorizes the same compatibility
   boundary, source outcomes and qualified-call route represented by the
   reviewed artifacts.

**Falsifier:** any input has two classifications; either eligibility predicate
mentions matching arity; a case differs between table, source, theorem or
adoption question; Unsupported is reported as a language rejection; or
Compatible silently supplies body typing or P1–P4.

The six effect frontiers remain: ordered handler selection, §21 entry,
wrong/sibling permission, shallow unmatched outward request, one continuation
path, and one static-to-native/runtime path. Their exact evidence/owner limits
are inherited from R81/R80. Do not start six new proofs or inventory
storage/fiber forms.

## 4. Exact leases and review

- `notes/design/2026-10-19-r83-role-call-compatibility.md` — Luna only; freeze
  before proof.
- `notes/design/2026-10-19-r83-role-call-adoption.md` — Luna only.
- `notes/theory/2026-10-19-r83-role-call-preservation.md` and
  `tasks/agent-loop/inbox/20261019-r83-proof.md` — prover only after definition
  hash is fixed.
- `notes/progress/2026-10-19-r83-readiness.md` — Luna only.
- `tasks/agent-loop/inbox/20261019-r83-compiler-review.md` and
  `tasks/agent-loop/inbox/20261019-r83-spec-review.md` — reserved for independent
  read-only reviewers; inline verdicts are valid.
- `notes/progress/2026-10-19-r83-closeout.md` and
  `tasks/agent-loop/current.json` — Luna only.

Fresh compiler/source and spec/design reviewers independently inspect the
frozen contract, definition, adoption offer, proof, handoff, readiness, R82
closeout, R81 proof and R80 source manifest. Any unresolved major finding
blocks user adoption. No automatic repair cycle. No code, tests, fixtures,
expected-output, runtime or public-doc paths are leased; no tests/builds/probes/
CLI/Git operation is authorized.

## 5. Resources and next gate

Fresh R83 cap: 600 seconds, charged at grant: Luna definition/adoption 150,
proof 150, compiler review 100, spec review 100, Luna integration/closeout 100.
No Astra and no carryover. No Stage2 resources are issued or reserved.

After clean independent review, present this exact package for explicit user
adoption. Only then may Luna issue a separate end-to-end implementation contract
that pins role/member source constructors, validation, ordinary Call formation,
candidate admission, RuntimeProgram execution, producer bindings, and focused
verification commands. Reaching `2` is an early surface goal, not parent-proof
closure.
