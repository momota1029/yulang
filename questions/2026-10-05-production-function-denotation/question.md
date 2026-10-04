# Production Function-bound denotation

Question ID: `production-function-denotation`
Question revision: `q1`
Predecessor/history: `../2026-10-05-production-function-bound-membership` (Option 2 policy selected; exact membership left open)
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `82e7b5a5d`; current source files are unchanged at question publication
Task/thread locator: unavailable; active goal is the Yulang inference replacement thread
Governing source/section: `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` §§1–3; `notes/design/2026-10-02-source-interface-adequacy-theorem.md` §§2–4; `notes/design/2026-10-04-production-callback-endpoint-generation-draft.md` §4; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.2, 3.7, 10; `notes/progress/2026-10-05-production-complete-function-interpretation-audit.md`

## Requested scoped decision

The approved Option 2 policy permits production Function bounds to include
endpoint-compatible observations without source-constructor witnesses, while
requiring an exhaustive, comparison-independent membership/admission rule.
The main callback theorem cannot be evaluated until the denotation of those
production bounds is specified at fixed `(nu,K,D)`.

Which source of meaning should define that exhaustive production
Function-bound denotation?

## Background and current premises

- The Authoritative callback contract fixes B generation: expected context
  selects Handler/boundary before body constraints; endpoints are independently
  synthesized; one ordinary `F_lit <: F_cb` checks the completed literal.
- Theorem C and the source-indexed realization define a source-generated
  reference relation `P_ref`; the approved Option 2 answer prevents imposing
  that reference image as an exhaustive production-membership policy.
- The conditional source-contract package §3.7 gives a sufficient positive
  abstraction shape `H_G(R)` with whole-tuple `W`/`Z` rules and a complete hard
  envelope `G`. Its concrete rules are not selected.
- Current `ResolvedExpr`, F5 `LambdaRecipe`, four Function endpoints, facts,
  and provenance do not define complete observation membership or independent
  challenge admission. The direct gate audit found no source counterexample
  and no evidence that existing `Rel_C`, `K,D`, typed paths, occurrence /
  incidence, and subtraction evidence require a new carrier.

The earlier Option 2 answer is not reopened: this question does not ask whether
source-witness-free extras are allowed. It asks how the allowed production
bound is interpreted without making endpoint shape alone authorize arbitrary
continuations, origins, authority, or dependencies.

## Options and consequences

### A. Interpret the endpoint through the existing complete source relation

Define production membership as the set of complete typed observations at the
actual descriptor's original `Rel_C` / `nu,K,D` fiber that satisfy its
independently interpreted endpoint constraints, roles, paths, and retained
dependencies. Admission is separately defined from the punctured typed
context. This is not equality with `P_ref`: the relation is over complete
typed observations and may include observations not emitted by the bounded
source-constructor generator.

Consequence: one semantic relation remains the basis for source execution and
type membership, with no separate `W`/`Z` grammar. The required endpoint-to-
relation satisfaction rule must be derived without using success of the
pending comparison. If existing evidence cannot state that rule, this option
does not resolve the gate.

### B. Give production bounds an explicit conservative abstraction relation

Define production membership by an exhaustive positive grammar over the
source base, with explicit extra-member and rewrite clauses, a complete hard
envelope, and separate comparison-independent admission. `W`/`Z` in §3.7 are
one candidate form; their actual clauses and evidence inputs must be specified
before adoption.

Consequence: conservative members need not be source executions, but each
extra rule becomes part of the successor's semantic contract and must preserve
role/entry, typed paths, origins, continuations, scopes, authority, and
`nu,K,D`. The rule cannot be inferred from four-port equality.

### C. A precise third interpretation

Give one explicit membership/admission rule and state whether it is derived
from A or extends it as in B. Include its complete-observation operands and
the condition that prevents comparison-dependent or arbitrary provenance
admission.

## Affected work

Blocked scope: claiming the production callback membership/admission theorem
or production adoption without a denotation for `D_A` and `P_A`.

Independent authorized work: principal-scheme derivation and source-generation
proofs that do not identify their relation with production membership.

Required answer: select A or B, or give a precise third interpretation. This
answer will not authorize implementation; it will establish only which
membership semantics the next proof must attack.

Pending publication: keep this question unstaged and uncommitted until an
explicitly approved local answer is validated and integrated by the questioning
primary. Posting does not pause the active goal; independent authorized work
continues.
