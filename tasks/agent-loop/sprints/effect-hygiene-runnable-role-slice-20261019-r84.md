# R84 — broad hygiene map, proved role call, early executable path

Status: ACTIVE — decision/proof/source-path/review only; no code authority  
Prior boundary: R83 closeout, `notes/progress/2026-10-19-r83-closeout.md`,
SHA-256 `fb85fa14d8c5da7ce3bbc234d619d17b5c77902c4e1bd982df5322eb7667b00b`  
R83 contract SHA-256:
`68fdfda6599d3b894482d4ef447e2940802c64ef97573a602b63abf003ff648b`  
R83 judgment/adoption/proof remain frozen and unadopted.

## 1. Goal and unchanged boundaries

Produce one adoption-ready decision package for the first role-qualified
method call, backed by a finite role-preservation proof and a source-to-runtime
implementation route. In the same package, cover effect hygiene across the six
known frontiers with an evidence/owner/next-falsifier map. This gives breadth
without turning each frontier into a new proof program, while the call path and
its §21 behavior receive proof depth.

The first runnable candidate remains:

```text
Role::member receiver args
SecondInt::second 1 2
```

with proposed result `2`, using ordinary curried Call/Apply. General dot-method
lookup and field collision stay OPEN and outside this pilot. The first
implementation sprint after explicit adoption must take this source form
through parsing, declaration/member identity, validation, constraints,
ordinary Call/Apply, candidate admission and `RuntimeProgram` execution. It
must be the next implementation critical path, not another design-only loop.

The Simple-sub/evaluator statements, A/B claims, source domain, quantifiers,
source/native correspondence, expected outputs, and previous gate statuses do
not change. Parent/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED. No frozen main,
production, code, test or expected-output changes are authorized by R84.

## 2. One normative compatibility procedure

Luna owns a single typed decision procedure before proof begins. Signature
eligibility and implementation-form eligibility are checked independently;
neither predicate compares signature and implementation arity. The procedure
then checks **every endpoint on both complete declarations**, including
unmatched extra binders, before pairwise mismatch rules:

```text
if !SigEligible(signature) || !ImplEligible(implementation):
    Unsupported
else if any complete-declaration endpoint is OutsideOrUnknown:
    Unsupported
else if arity, supported endpoint type, result, or §21 entry-role vectors differ:
    Incompatible
else:
    Compatible
```

The supported pilot envelope remains module-local and monomorphic, with an
`int` Value receiver, explicit `int` or unit Value parameters, explicit
`[_] int` Computation parameters, and ordinary `int` result. Other receivers,
results, endpoint types, closed rows, higher-order slots, adapters, polymorphism
and unsupported declaration forms are outside this pilot. `Unsupported` means
the case is outside the proposed pilot; it does not reject the language
program. `Incompatible` applies only after all endpoint evidence is supported
and known. Role entry comes from each executable binder's own annotation under
charter §21; a role signature never annotates a binder.

The definition must include mixed-failure cases before proof starts:

- extra `bool` endpoint plus arity mismatch → `Unsupported`;
- `bool` endpoint plus role mismatch → `Unsupported`;
- all-supported extra/missing binder → `Incompatible`;
- all-supported role mismatch → `Incompatible`;
- equal supported declaration vectors → `Compatible`.

Compatibility does not establish body typing, selected source-member identity,
candidate admission, runtime support or R81 producer hypotheses P1–P4.

## 3. Stage 1 evidence and breadth/depth balance

1. Freeze the judgment and adoption offer from one normative procedure. Every
   example and outcome must be mechanically traceable to its ordered cases.
2. Prove classifier totality and disjointness, the finite §21 binder-role
   preservation lemma, and specialize R81's ordinary-Apply request-prefix
   result to this exact envelope. Keep P1–P4 OPEN. Preserve the exact first
   unanswered `observe(1)` request and suspended suffix. No parent/A/B closure.
3. Map these six effect-hygiene frontiers together, with current best evidence,
   the exact open owner/premise and its next falsifier:
   - ordered handler matching and priority;
   - §21 Value/Computation entry;
   - wrong or sibling permission;
   - shallow unmatched outward request;
   - one continuation capture/resumption path;
   - one static-to-native/runtime path.

   This map is broad coverage, not a claim that all frontiers are solved. Do not
   start six proofs, reopen storage/fiber inventories, or promote conditional
   evidence into a theorem.
4. Produce a pinned source-to-runtime implementation route for the exact
   `SecondInt::second 1 2` example, with concrete constructors/consumers,
   producer hypotheses, admission boundaries and future verification command
   candidates. A route is planning evidence, not runnable support.
5. Independent compiler and specification reviewers inspect the same frozen
   package and mixed-failure table. Any unresolved major/blocking finding
   prevents adoption. If clean, Luna presents the exact package for explicit
   user adoption, then issues the vertical implementation contract.

**Falsifier:** a mixed-failure input disagrees across the normative procedure,
case table, proof or adoption offer; an eligibility predicate compares arity;
an endpoint outside the pilot receives `Incompatible`; §21 role preservation
silently inherits a signature role; the route lacks an actual source/runtime
owner; or any conditional producer is called established.

## 4. Exact outputs and leases

- `notes/design/2026-10-19-r84-role-call-judgment.md` — Luna only.
- `notes/design/2026-10-19-r84-role-call-adoption.md` — Luna only.
- `notes/theory/2026-10-19-r84-role-call-preservation.md` and
  `tasks/agent-loop/inbox/20261019-r84-proof.md` — constructive proof lane.
- `tasks/agent-loop/inbox/20261019-r84-source-path.md` — bounded read-only
  source-path lane; Luna incorporates the frozen receipt into readiness.
- `notes/progress/2026-10-19-r84-hygiene-and-runnable-path.md` — Luna only,
  incorporating the six-frontier map and reviewed source-path handoff.
- `tasks/agent-loop/inbox/20261019-r84-compiler-review.md` and
  `tasks/agent-loop/inbox/20261019-r84-spec-review.md` — independent read-only
  reviewers; inline verdicts are valid.
- `notes/progress/2026-10-19-r84-closeout.md` and
  `tasks/agent-loop/current.json` — Luna only.

The source-path lane may read only the exact manifest-pinned source owners and
frozen R80/R81/R83 evidence. It owns no compiler source path. All other paths
are excluded. Proof begins only after the judgment hash is frozen. Reviewers
consume frozen direct dependencies only. No automatic repair cycle.

## 5. Resources and gates

Fresh R84 cap: **700 seconds**, charged at grant: Luna judgment/adoption 150;
proof 150; source-path handoff 100; independent compiler review 100; independent
spec review 100; Luna integration/closeout 100. No Astra and no carryover.

R84 authorizes no source edit, code, test, build, probe, compiler CLI, Git,
fixture or expected-output mutation. It grants no semantic adoption. After a
clean review, the adoption question is the final gate before a separate
implementation sprint. That sprint should go directly to a runnable
role-qualified method slice while preserving the six-frontier evidence map and
its open obligations.
