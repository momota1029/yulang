# Annotation/profile source preservation: bounded falsification

Date: 2026-10-06
Status: Frozen unreviewed research-only evidence; no semantic or implementation authority
Assigned baseline: `37739d7fc6e7e2cbe90a81812b735f8526a707e9`
Exclusive lease: this file only
Method: adversarial premise inversion and retained parser-contract inspection

## Objective and outcome

Try to falsify preservation of a raw annotation occurrence's endpoint and
depth before pending comparison `Q`, without choosing a new annotation meaning.
No accepted, fully elaborated source counterexample was established. The selected
rules require preservation but leave its source constructor open. Consequently
neither a semantic preservation theorem nor a semantic falsifier follows from
this pass.

The new discriminator is a **same-enclosing-TypeExpression occurrence collision**,
using the existing clean parser control `[e] F [io] -> U`. Its two row owners
are distinct even though their nearest enclosing TypeExpression and Function
nesting depth coincide. A key retaining only that enclosing node and Function
depth cannot preserve both raw occurrences. This refutes that hypothetical key,
not the compiler or the approved language rule. The earlier immediate-versus-
returned-Function depth witness is not repeated.

## Authority, dependencies and claim classes

Only the approved scope below determines language meaning. Draft packages are
inspected as conditional rule interfaces, not adopted as additional authority.

| Governing source / exact section | Selected premise | What remains absent in that inspected interface |
| --- | --- | --- |
| `inferred-function-call-views` §§1.1,2 | Written contracts, public schemes and internal views differ; source occurrence, annotation presence, scope, static slot/profile survive inference/use; one original joint `(nu,K,D)`; formation is independent of Q | The rule associating this raw row with its completed typed endpoint; preservation is required rather than constructed |
| Same §§4,5.1,5.3,5.4 | The approved `apply(f: _ -> [io] _, x) = f x` grants only scoped io removal permission; it does not enact removal | Original contribution association, exact permission/profile constructor, uniqueness/principality and preservation derivations |
| Approved `source-annotation-boundaries/q1`, d1 decisions 1–4 | Binding, parameter and `as` compare their current endpoint directly to the target; export target plus local realization and preserve previous evidence | An endpoint comparison does not identify a nested row's original profile position or conflate evidence roots |
| `callback-context-delivery` §§1,2,2.1 | Role before ports; known instantiated F_cb/beta/Slots(beta) precede body generation; independently synthesize literal endpoints; check once by F_lit <: F_cb | It assumes the instantiated slot/profile and excludes explicit annotation/context overlap; it cannot supply its own raw-profile constructor |
| Same §§3,4 | Static slot differs from dynamic receiver; existing callable's actual role and entry survive invocation through a callback view | No license to key source occurrence by receiver identity alone or rewrite actual entry after a successful comparison |
| Charter user-decision amendments §§13,16–18,21,24 | Corresponding typed paths retain information, outer annotation does not label all descendants; Value entry forces inside invocation, retained entry does not; role and entry are independent | These selected directions do not assign every raw row to a complete Function port |
| `typed-computation-core-elaboration` §§6,9, conditional package | Admitted annotations and known corresponding ports are inputs; distinguish J_arg, closure J_body and complete J_call | No raw-annotation constructor; body/result skeleton does not determine the complete-call endpoint |
| `typed-boundary-realization-draft` §6, Views/signature positions and introductions; observation/path paragraphs | Supplied decorated profiles distinguish positions/occurrences/depth; matching typed paths and event-specific Observe are required | These are conditional source inputs, not proof that arbitrary syntax generates them |

Established results here are the facts visible in the pinned source text/code
and the collision lemma below. Clean source acceptance is an existing parser
**test contract inspected**, not a newly executed result. The endpoint-preserving
typed constructor is an open premise. No complete language theorem is claimed.

The approved call-view a2 answer and the approved boundary d1 answer were read
with their receipts; all named direct inputs were byte-compared to the assigned
revision before writing. Task/index material was navigation only. The older
bridge, constructive occurrence/profile attempt and call-view derivation attempt
were inspected only to avoid duplicating their attacks; they supply no authority.
In particular, this pass consumes the pinned §1.1 clarification rather than
identifying written annotations with inferred public schemes.

## Smallest retained source discriminator

The exact control is present at `crates/yu-syntax/src/tests/type_expr.rs` in
`bracket_rows_attach_at_leading_and_arrow_positions`, and at
`crates/yu-syntax/src/tests/type_expr/bracket_arrow_recovery.rs` in
`bracket_arrow_accepted_controls_keep_right_associative_recursion`. The latter
requires an empty structural-recovery list and no Missing/Error/Invalid nodes.
No test was run in this assignment.

`crates/yu-syntax/src/tests/type_expr/leading_row_cst.rs`:39–49 requires that
the `[io] -> U` TypeArrowTail has the outer TypeExpression as parent, with
no direct nested TypeExpression sibling. The leading-row child contracts and
`type_bracket_arrow_tail_normalized` in `type_expr/mod.rs`:1531–1588 distinguish
the following addresses:

```text
source: [e] F [io] -> U

omega_head  = TypeExpression / BracketRow([e])
omega_arrow = TypeExpression / TypeArrowTail / BracketRow([io])

nearest-enclosing-TypeExpression(omega_head)
  = nearest-enclosing-TypeExpression(omega_arrow)
Function-nesting-depth(omega_head) = Function-nesting-depth(omega_arrow) = 0
omega_head != omega_arrow
```

Depth here counts enclosing Function nesting, not all Rowan nodes. Counting
every CST ancestor would retain the TypeArrowTail distinction in this example;
that is a different key and is not falsified. The test constrains grammar
placement only. It does not select the typed effect meaning of either row.

**Collision lemma, explicit hypotheses.** Suppose a candidate raw-occurrence
key is `(nearest enclosing TypeExpression identity, Function nesting depth)`
and its output is required to retain distinct raw row occurrences. On the
displayed tree both key inputs are equal, so a deterministic key-based identity
function returns equal identities. The required distinct identities are lost.
The lemma is a conditional refutation of that key. Adding the full syntax
address or exact occurrence extent defeats this collision; neither addition
alone proves the typed association.

This control is structurally minimal for this specific collision: one enclosing
Function arrow, its input/output atom, one leading row and one arrow-owned row,
each with one member. Deleting either row removes the two-occurrence collision;
deleting the arrow removes the distinct arrow owner. Byte minimality, alternate
lexical spellings and an exhaustive smaller-program search were not checked.
It is a type-fragment witness, not an accepted complete typed definition.

The attack is on occurrence identity rather than equality of public types or
family names. It does not claim the rows denote unequal solved effects, or that
equal members would permit occurrence merging. No synthetic same-family variant
was executed or needed for the collision lemma.

## Endpoint confusion and comparison dependence: bounded inversion

For the approved io example, changing the exported endpoint at a real boundary
is permitted. Therefore “endpoint preservation” must mean retention of the
original association/evidence while linking it to the completed target view;
literal equality of incoming and exported endpoints is not the selected claim.
Rejecting legitimate target export would reinterpret the approved decision.

Callback B selects the role/boundary before independently synthesizing the
completed literal, while the final Q validates that completed interface.
Using Q success to choose which row occurrence names which typed port would
make its admission premise dependent on the query. It violates the approved
formation requirement directly; this is an authority check, not an executable
counterexample. A later realization certificate from the actual comparison is
allowed and must remain distinguished from pre-Q source association.

The J_body/J_call attack stops at the same source-constructor seam. Selected
Value entry includes Force before the body inside the invocation. The conditional
core §9's identity-body/request-carrier reduction already shows why the body
result cannot stand for the complete call. Re-executing that reduction would
repeat an existing attack and assume admitted typed ports. It supplies no new
raw-row association, so no second toy probe was added.

The precise blocker is the absent constructor in the inspected rule interfaces:

```text
resolved admitted raw occurrence + exact owner/depth/scope
  + selected role/entry + jointly formed original interface
  -> source-certified completed typed port and original local profile clause
```

This is a proof-obligation description, not a proposed language rule or compiler
carrier. Known profile transport assumes its output. No inspected source rule
allows alternative associations after Q success; failure to derive the
constructor is not permission to choose one. No repository-wide absence or
impossibility claim follows from this bounded search.

## Checks, independence, resources and freeze

Commands: bounded `cat`, `sed`, `rg`/`rg --files`; read-only HEAD/status;
Python byte/SHA-256 comparison against `git show 37739d7:<path>`; final lease
whitespace/hash and dependency revalidation. Earlier broad captures were
truncated; findings use subsequent narrow excerpts. `spec/` and the referenced
`web/docs/reference/{types,type-theory}.md` paths were absent, and no substitute
specification was guessed. No builds, tests, executable semantic probes,
formatting, Git mutations, children, or question-board/shared-record writes.

The retained parser tests and owning code are separate artifacts but share the
same grammar intention; inspecting them is not an independent execution oracle.
The semantic authority is external to this note, but the conditional endpoint
argument shares admitted-port/profile assumptions with the Draft packages.
A checker supplied those transitions would only test their consequences.

Coverage: one recorded clean type fragment and its two owner addresses; selected
call-view/boundary rules; previously known J_body/J_call discriminator checked
as an existing limit. No seeds, randomized ranges, numeric enumeration, or
executed mutations. Named shortcuts attacked: erasing the arrow owner while
keeping enclosing TypeExpression/depth; assigning ports using Q success;
equating source annotation with public scheme; equating J_body with J_call.

No numeric resource allocation was supplied in the task packet. Work used only
small read-command processes, initially up to six concurrent independent reads,
later at most four; no compute/build wave or heavyweight process. CPU time,
peak RSS and exact elapsed wall time were not measured. This corrects the
producer's early message proposing sequential reads: actual batching was not
sequential. Resource use is reported as unknown rather than inferred from tool
latency.

Failure conditions: a changed dependency invalidates the affected inspection;
a different meaning of depth can invalidate the key collision; unavailable
admitted annotation/complete-port evidence blocks semantic use; dropping prior
boundary evidence, conflating distinct original occurrences, or creating an
association from Q success fails the selected contract. No protection release,
subtraction, dynamic activation, or membership result is inferred.

Omitted: running the existing syntax controls, whole-definition acceptance,
raw resolution, production HIR/profile construction, recursion/generalization,
inference/principality, full Option A/Option 2 membership/admission, dynamic
protection lifetime and production conformance. The artifact freezes before
review and does not certify itself.

Recommended next action: require the constructive occurrence/profile certificate
to retain the arrow-versus-leading-row owner as well as nesting depth, and
return its still-unsupplied typed association for a narrowly scoped source-rule
derivation; do not enlarge a transport checker that assumes that association.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-annotation-profile-source-falsification.md`.
- Baseline SHA: `37739d7fc6e7e2cbe90a81812b735f8526a707e9`.
- Changed dependency hashes: none relative to this baseline; the prior audit's
  call-view hash differs because its baseline preceded §1.1, which this artifact
  explicitly uses. Current call-view SHA-256 is
  `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`.
- Review status: frozen unreviewed research-only bounded falsification; no
  independent review, semantic theorem closure or implementation authority.
- Checks already run: narrow selected-rule/parser-contract inspection and
  direct dependency byte/hash check. Final lease/hash recheck is returned to
  the primary without a self-referential artifact hash in this file.
- Proposed commit message: `research: distinguish row owners before annotation profile association`.
- Shared-record deltas intentionally left for primary/curator: record the
  same-depth leading/arrow-owner discriminator and preserve the open pre-Q
  occurrence-to-completed-port constructor; link this evidence without claiming
  accepted-source semantic failure or gate closure. No task/index/authority,
  theory, question bundle, compiler, manifest or lockfile belongs to this lease.
