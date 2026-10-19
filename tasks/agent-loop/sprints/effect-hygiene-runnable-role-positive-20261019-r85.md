# R85 — positive role-call certificate and runnable adoption gate

Status: ACTIVE — contract/proof/review only; no code authority  
Prior boundary: R84 closeout `notes/progress/2026-10-19-r84-closeout.md`, SHA-256
`2fa55b61aaf430e29be13274ee0d624887c5efd160f7126af8b9e4325e016bf5`  
R84 source path: `tasks/agent-loop/inbox/20261019-r84-source-path.md`, SHA-256
`c5cb26e5e70739b7ea467c13ccd89bf0219aa538ba78a3917ea75ae1240f4165`  
Canonical proposed contract:
`notes/design/2026-10-19-r85-role-call-positive-contract.md`, SHA-256
`fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609`.

## 1. Goal and preserved user priority

Prepare a cleanly reviewed, adoption-ready positive contract for the exact
first role-qualified call `SecondInt::second 1 2`. Give its positive
interface-role preservation and conditional ordinary-Apply behavior proof
depth, and preserve R84's six-frontier effect-hygiene map and exact future
source-to-runtime route. The design and proof must not grow another total
Compatible/Incompatible/Unsupported classifier.

The canonical contract file above is the **only semantic decision surface**.
This sprint contract, proof and readiness reference its exact hash; they do
not restate its predicates, outcome tables or role rules. If the proposed
contract bytes change, stop and replan; do not continue proof/review against a
moving decision.

The user's original goal and all Simple-sub/evaluator A/B statements, accepted
source domains, quantifiers, source/native correspondence and prior gate
statuses stay unchanged. Parent/A-B remain OPEN 0→0; R50 remains NOT_ADOPTED.
The first implementation route must be `Role::member receiver args` lowered
through ordinary receiver-first curried Call/Apply. General dot lookup and
callable-field collision remain OPEN. No storage/fiber inventory or six-proof
expansion is authorized.

## 2. Stage 1 work

1. Luna freezes the source-to-runtime adoption handoff and readiness using the
   exact R84 source-path receipt and its 103 manifest-pin validation.
2. The proof lane establishes the finite positive `InterfaceMatch` role
   preservation property and specializes the corrected R81 request-prefix
   result under P1–P4. Keep `CheckedBody`, `ValidatedTarget`, endpoint
   evidence and actual producer construction as separate premises. Preserve
   the no-handler stop at `observe(1)` with its suspended suffix. Parent/A/B,
   F1/FK1 and native/source correspondence remain OPEN.
3. Luna records broad effect-hygiene status across all six R84 frontiers with
   exact current evidence, open owner and next falsifier. This is a breadth
   map, not six theorems and not a new storage/fiber study.
4. Fresh independent compiler/source and specification reviewers inspect the
   same frozen semantic contract, proof and readiness. Any unresolved
   major/blocking finding prevents adoption. No automatic correction cycle.
5. If reviews are clean, Luna presents the exact canonical contract and
   readiness for explicit user adoption. Only after adoption may Luna issue a
   separate vertical implementation contract for the first runnable example.

**Falsifier:** a positive certificate does not require all stated premises;
source binder roles are inherited or rewritten; ordinary body typing is
smuggled into interface matching; an identity/root/environment/graph/admission
producer is claimed without evidence; the source route has no concrete owner;
or the six hygiene frontiers are reported solved by the local role-call lemma.

## 3. Exact leases

- Canonical contract is already frozen at the SHA above; no worker may edit it.
- `notes/theory/2026-10-19-r85-role-call-preservation.md` and
  `tasks/agent-loop/inbox/20261019-r85-proof.md` — constructive proof lane.
- `notes/progress/2026-10-19-r85-readiness.md` — Luna only; cite R84 source
  handoff and six-frontier statuses without changing them.
- `tasks/agent-loop/inbox/20261019-r85-compiler-review.md` and
  `tasks/agent-loop/inbox/20261019-r85-spec-review.md` — fresh independent
  read-only reviewers; inline verdicts are valid.
- `notes/progress/2026-10-19-r85-closeout.md` and
  `tasks/agent-loop/current.json` — Luna only.

Proof begins only after acknowledging the frozen canonical hash. Reviewers
consume the exact contract, canonical proposed decision, proof, R84 source-path
handoff, R84 readiness, R84 closeout, R81 proof and R80 manifest. The source
handoff may be reused only at its frozen hash; no new source reads are needed
unless a reviewer finds a specific manifest-pinned falsifier. No source edit,
test, build, probe, compiler CLI, Git, expected-output or production path is
leased.

## 4. Resources and gate

Fresh R85 grant: **1200 seconds**, charged at grant: Luna readiness/runnable
handoff 300; proof 300; compiler review 200; specification review 200; Luna
integration/closeout 200. No Astra and no carryover.

R85 grants no semantic adoption. A clean review is followed by an explicit
user adoption decision; then one separate implementation sprint takes the
authentic source identities, ordinary Call/Apply path, actual producer and
admission evidence through a runnable `SecondInt::second 1 2` demonstration.
