# Sequential explicit annotation boundaries: conditional source adequacy

Date: 2026-10-05
Status: unreviewed research-only conditional derivation; frozen on submission
Lease: this file only
Integration baseline: `f50c8a88882a10f109a71e2842f4d1b02982de53`
Semantic source pin: `0ab7620e167f190691a9ec50fde507d039265aa4`
Decision pin: `28dddc75fd598faf34dd4d069ffb231cb64a82f1`,
`questions/2026-10-05-source-annotation-boundaries/approved-answer.md`, q1/d1
Method: judgment construction and induction on zero, one and two explicit
boundaries; no executable model, compiler changes, tests or Git mutations

## 1. Objective, authority and dependencies

Replace the invalid concrete-transitivity step with a boundary-indexed
query/evidence correspondence. This note derives the bookkeeping consequences
of the selected source meaning and isolates the local realization hypotheses
needed for executable source adequacy. It does not prove those hypotheses.

The exact governing sources at the semantic pin are:

- `2026-10-03-concrete-compatibility-boundary.md` §1: one endpoint-dependent
  `A <: B`; local concrete success cannot establish a third comparison by
  composition. Variable propagation is a separate allowed internal operation.
- `2026-09-29-scc-intrusion-redesign-charter.md` §§1–4: research/approval
  boundary and semantic target; §§18,21,24: result forwarding, source parameter
  roles and receiver-role selection before Function-port interpretation.
- `2026-09-09-successor-expression-structural-tails-draft.md`, “as Type” and
  “Type exit and continuation”: syntax owner and unchanged full-Type exit.
- `2026-10-02-typed-computation-core-elaboration.md` §6: source interfaces,
  argument entry/body bindings, Result/Normalize and skeleton coherence.
- `2026-10-02-typed-boundary-realization-draft.md` §6, “One relational transport
  operation” and “Transport and lifetime theorem package”: path-indexed typed
  packets, shared predicates, evidence persistence and relational-image laws.
  Its §§3–4 structural adapter theorem is conditional on supplied equations;
  it cannot establish a source annotation conversion rule here.
- `2026-10-05-source-contracts-and-common-allowance.md` §§3.1–3.5: complete
  source operands, actual entry, independent admission and shared histories;
  §9: emission conformance does not imply resolver completeness.

All design paths above are under `notes/design/`. Historical observations come
from `notes/progress/2026-10-05-source-adequacy-concrete-transitivity-obstruction.md`
and `2026-10-05-source-boundary-coverage-audit.md`; they are not new attacks.
The baseline receipt records the committed q1/d1 handoff as accepted, with
durable authority-record synchronization still pending. The selected decision
supplies the following meaning directly: binding annotations, argument
annotations and expression `as Type` compare the current endpoint to the
target, export the target plus local realization evidence, and preserve earlier
evidence. No boundary-free intermediate concrete adaptation is permitted.

The question, draft and approved answer were byte-equal between the decision
commit, integration baseline and live files when inspected. The pinned design
and historical-observation blobs were unchanged at the integration baseline.
Uncommitted replacement source files were not used as semantic authority.

## 2. Judgment, witnesses and explicit hypotheses

An annotation occurrence `α` identifies a source boundary, not automatically
a handler activation, callback grant, new runtime boundary ID or a new effect
carrier. Distinct occurrences remain distinct even if targets are equal.

Write a supplied base judgment as

```text
Γ ⊢ e ⇝ (I₀, endpoint A₀, core c₀, packet V₀, graph G₀, obligations Ω₀).
```

`I₀` retains its Value/Computation source tag. `A₀` names the endpoint in the
role-directed checking position, which may be a complete computation interface
for retained arguments. The packet/graph notation refers to existing typed-view
evidence; it proposes no storage representation. `Ω₀` includes the original
joint predicates and dependencies, not just a list of scalar type edges.

For target `Tⱼ` at `αⱼ`, the successful step is

```text
Vⱼ₋₁ : Aⱼ₋₁
resolve_ν(αⱼ, Aⱼ₋₁ <: Tⱼ) ⇓ wⱼ
local-realization(αⱼ, Vⱼ₋₁, wⱼ) ⇝ (cⱼ, Vⱼ : Tⱼ, Gⱼ, Ωⱼ)
──────────────────────────────────────────────────────────────────
Γ ⊢ αⱼ[eⱼ₋₁,Tⱼ] ⇝ (Iⱼ, endpoint Tⱼ, cⱼ, Vⱼ, Gⱼ, Ωⱼ).
```

The rule records one original inequality plus its local resolution witness;
`resolve` is the single selected inequality solver, not a new cast relation.
`Iⱼ` and the executable use of `cⱼ` must come from admitted source elaboration.
This rule does not infer the source tag from the solved target representation.

Hypotheses for the conditional theorem:

**H0 — Base adequacy.** The supplied boundary-free base has source/generated
query correspondence and executable realization under its original scope,
declarations, source roles, admitted clients and shared assignment. This is an
input theorem for the selected fragment, not arbitrary-source completeness.

**H1 — Exact occurrence and endpoint inventory.** Elaboration preserves each
admitted explicit annotation occurrence and target. For consecutive boundaries
at the same checking position, its only queries for this linear annotation
spine are the local queries in this rule, and the next query reads the
preceding exported endpoint. When the checking position changes, H4 must give
the source-derived role projection explicitly (for example, the designated
Force/result projection before a Value-entry argument check); §3's table does
not instantiate that mixed-position case. Other independently required source
queries are retained separately. A targetless synthetic intermediate query
cannot be introduced to make this spine succeed.

**H2 — Local realization and extraction.** Each successful local query has a
source-typed realization at that occurrence, and generation/extraction retain
the same witness. The realization has the target's complete typed view and
accounts for casts/adapters, their execution, future uses and raw resumptions
in the existing source relation. It supplies the typed correspondence of the
actual output to its target, with no invented grant or changed callable entry.
The source realization and its emitted certificate simulate each other in
every independently admitted surrounding use. This is the principal unproved
premise; local endpoint success alone does not establish it.

**H3 — Joint witness and dependency closure.** There is one assignment `ν` and
one jointly consistent predicate ledger for the base and all local witnesses.
All local scopes, operand sharing, typed paths, source origins and still-live
`K,D` agree. Certificates compose by typed evidence transport and source
sequencing/latent wrapping, not by inequality transitivity. New constraints
are conjoined by original identity and checked jointly. The theorem does not
assert that independently solvable local ledgers have a common solution.

**H4 — Role/placement correspondence.** The supplied annotation elaboration
identifies the current checking position without changing source entry or
result tags. For argument boundaries it fits the receipt/entry diagrams in §5;
for bindings and expression annotations it supplies the corresponding producer
and consumer placement. Function introduction/expected context is available
before body generation where charter §24 requires it. This hypothesis does not
choose an unresolved annotation/expected-context overlap or conversion API.

The approved decision establishes the target-export and evidence-preservation
requirements in H1; it does not establish full generation, H0, H2–H4. In
particular, assuming a correct executable local realization is not a proof that
every successful concrete resolver case has one.

## 3. Zero, one and two boundaries

For a linear spine write `S₀=e`, `S₁=α₁[S₀,T₁]`,
`S₂=α₂[S₁,T₂]`. The table instantiates consecutive boundaries at the same
checking position. A mixed-position successor uses H4's role projection
`π(T₁)` and its query `π(T₁) <: T₂`, rather than reading the complete previous
carrier as a scalar endpoint. These are derivation nodes, not a claim about
new parser association of `x as int as str`. Any raw nested spelling needs its
separately admitted syntax/association derivation.

| Spine | Export | Required query trace | Joint certificate |
| --- | --- | --- | --- |
| `S₀` | `A₀` | no annotation query | `(ν, base witness)` |
| `S₁` | `T₁` | `α₁: A₀ <: T₁` | `(ν, base witness, w₁)` |
| `S₂` | `T₂` | `α₁: A₀ <: T₁`; `α₂: T₁ <: T₂` | `(ν, base witness, w₁, w₂)` |

**Zero.** H0 gives the base correspondence. Nothing introduces a comparison
against a final externally requested target or an implicit adapted endpoint.

**One.** H1 gives exactly `A₀ <: T₁`. H2 supplies the same local witness on
source and generated sides. H3 extends the base certificate jointly; H4 places
its realization at the existing source boundary. The exported endpoint is
`T₁` by q1/d1. Earlier evidence is retained in `G₁`, and the current view uses
the typed correspondence of this realization.

**Two.** Apply the one-boundary result to `S₁`. Its current endpoint is `T₁`,
so H1 makes the second obligation `T₁ <: T₂`, without substituting `A₀` for
`T₁`. H2–H4 append the second witness and realization under the same joint
scope/assignment. Local simulations compose through their shared intermediate
view by the existing stateful bind/latent-view laws. This composition asserts
that executing the two source realizations is simulated by retaining those
same two realizations. It proves no direct inequality `A₀ <: T₂` and gives no
license to replace the pair with a newly resolved direct adapter.

For an eagerly consumed value, the conditional execution instance is

```text
c₀ >>= (v₀ => realize(w₁,v₀) >>= (v₁ => realize(w₂,v₁))).
```

State is threaded through every bind. A request from the first stage carries
the second stage as a pending suffix; divergence prevents that suffix from
running. Latent conversions retain their own source-delimited future uses;
they need not execute eagerly according to this display. H2 selects the
correct local case, rather than replacing all adapters with this eager case.

**Conditional theorem.** Under H0–H4, source checking and generation/extraction
for `S₀,S₁,S₂` correspond in success and retained local witness traces, export
the endpoints in the table, and mutually simulate the composed supplied
realizations on all admitted finite prefixes and future-use/resumption
developments. Failure or absence of any hypothesis places that instance outside
the theorem; it is not a new source rejection policy or proof of nonexistence.
The induction extends to any supplied finite linear spine with the same
hypotheses. Only the zero/one/two instances are worked here; arbitrary source
branching and recursive-group generation are not covered.

## 4. Exact evidence transport across two boundaries

Let `Mⱼ` be H2's typed correspondence and `χlocalⱼ,Dlocalⱼ` only the profile
and dependency incidences justified by that local source realization. They may
be empty. They are not manufactured for every annotation by this notation.
With source tags retained in every union, existing §6 transport gives

```text
χ₁ = M₁*χ₀ ∪ χlocal₁
χ₂ = M₂*χ₁ ∪ χlocal₂
   = (M₂ ∘ M₁)*χ₀ ∪ M₂*χlocal₁ ∪ χlocal₂.
```

The identical relational-image equation holds for `D`. For an original
profile witness, its final membership explicitly retains positions `p₀,p₁,p₂`
with `χ₀(p₀,b), M₁(p₀,p₁), M₂(p₁,p₂)`. Predicate identity and inherited
origins stay attached to the same witnesses. Local new predicates extend the
common ledger by conjunction; inherited predicates are neither freshened nor
dropped. Legitimate newly created source wrapper/event identities are accounted
for by H2 and are not equated with inherited identities.

Keeping evidence means the original graph and `w₁` remain accessible with
their occurrence provenance when `w₂` is added. It does not mean every old
profile is visible at every final path: relational image transports only
paths in the correspondence domain. An unmatched incidence remains at its
original graph location. No equality of value pointers, endpoint variables or
effect-family heads unions alias profiles. No composition law on `M₁,M₂`
establishes concrete transitivity on their endpoint queries.

Candidate-specific `Inc_C` still checks the current handler, owner and original
receiver activity. Persistent old evidence does not revive an expired grant.
Complete executing-view observation comes from the supplied local realization;
a profile image alone does not prove that an event has an `Observe` witness.

## 5. Argument annotations and existing entry roles

Charter §21/core §6 fix `x:A` to Value entry for an ordinary value annotation,
and `x:[E] A` or `x:[_] A` to retained Computation entry. Calls always reify
the whole argument `D` inertly, establish actual receiver/receipt, and then use
the actual callable's entry skeleton. Receiver Pure/Handler role is separate.

For the conditional **Value-entry instance**, suppose H4 identifies the
post-designated-force value endpoint as `Aarg`, and H2 supplies a value
realization `w : Aarg <: A`. The entry diagram is

```text
inert whole D -> actual receipt -> designated Force(D)
             -> local result realization w -> rebind x:Value(A) -> body.
```

This checks the role-directed result endpoint, not the inert carrier's erased
shape against the ordinary value annotation. Effects/divergence of `D` remain
inside the same invocation. The local realization can have its own source
effects, accounted for in the complete call. Entry still occurs when `x` is
unused, and no recursive force of a latent returned `A` is added. Pending
resumption after receipt does not replay that receipt or restart the force.

The entry skeleton is selected authority. The exact post-force realization
placement and typed-port correspondence displayed here are H2/H4's conditional
instance, not a claim that core §6 has proved all argument adaptation rules.
An expression annotation inside `D` keeps its own earlier occurrence/witness;
when explicitly consumed it is interpreted by its source realization. The
argument boundary consumes that expression's exported endpoint in the proper
role-directed position, preserving its evidence through force/result paths.

For the conditional **retained-Computation instance**, H4 instead provides the
current complete interface `Comp(Earg,Aarg)` of `D`. Its target is the outer
annotated computation interface `Comp(E,A)`, using the wildcard's existing
symbolic endpoint where applicable:

```text
inert whole D -> actual receipt
             -> locally certified view at Comp(E,A)
             -> bind x:Computation(E,A) -> body.
```

There is no entry Force. H2 must certify an inert retained view and every
subsequent demanded use; it cannot realize a retained boundary by eager
execution before the body. The complete interface check is one original
inequality in the appropriate role; this display does not decompose Function
effect ports or computation effects into independent scalar comparisons.
Assigning `E=empty` does not convert this entry into Value entry. Returning `x`
still follows `Result(Computation(E,A))=Comp(E,A)`, with no implicit extra layer.

For two boundaries in either role, each successor consumes the preceding
export at its own checking position. A force/result correspondence can remove
a result-path prefix between those positions; H4 must exhibit that mapping.
Thus unlike two plain value annotations, a mixed expression/argument chain
cannot be proved merely by writing the same erased endpoint twice.

## 6. Discriminator, independence, limitations and next action

The inherited smallest three-endpoint non-composition witness is

```text
A={foo?:string}; B={}; C={foo?:int}
A <: B succeeds; B <: C succeeds; A <: C fails.
```

Two admitted explicit boundary nodes with targets `B,C` have the trace
`[A <: B, B <: C]`, whereas a single boundary targeting `C` requires the failed
direct query. This is the discriminator for deleting the intermediate node or
retargeting the second query to the original anchor. It is an inherited
proof-interface counterexample, not a new executable optional-record adapter
or a verified raw-source program. This note supplies no identity/drop-field
realization for those checks. Without their H2 witnesses it cannot certify the
runtime example. Zero/one/two boundaries are minimal for distinguishing the
chain-compression shortcut; no broader minimality search was performed.

A second logical obstruction is witness gluing: separately satisfiable local
conditions `ν(z)=Int` and `ν(z)=String` on the same rigidly distinct tags have
no common assignment. This is a logical countermodel to independent local
existentials implying joint success, not a Yulang source witness. H3 rules out
that proof shortcut without selecting a new solver mechanism.

No Oracle was run. Independence comes from the committed user decision and
the already recorded endpoint discriminator; the transport algebra follows
the supplied path correspondences. A checker implementing these same rules
would test their bookkeeping, not prove H2/H4 from source. No such checker was
added. Named shortcut mutations considered analytically are: compress the
two-query trace, discard `w₁`, solve separate assignments, union evidence by
pointer equality, force retained entry, and omit unused Value entry. The first
has the inherited discriminator; the others violate explicit hypotheses or
selected entry/evidence rules. There is no reported mutation-execution count,
seed or enumeration range.

Unverified scope: arbitrary source annotation formation and role projection;
complete local concrete/Function/effect realization; annotation/expected-context
overlap; casts with State/imports; arbitrary patterns; production HIR/solver
coverage; generalization, recursion/SCC lifecycle, principality and resolver
completeness. The base fragment restrictions in H0 are material. No source
boundary semantics is inferred from syntax recognition or current rejection.

Recommended next action: independently review this frozen derivation, focusing
on H2/H4 and the shared-witness seam; then derive one admitted annotation's
local realization from the actual source rule and existing typed paths. Another
toy trace checker would leave that premise untouched.

## 7. Commands, resource account and commit packet

Commands already run: pinned `git show` reads of the sources/sections above;
`git rev-parse HEAD` and decision/full blob IDs; Python byte comparison of the
question/draft/answer across decision, baseline and live files; blob comparison
of the eight direct design/observation dependencies between semantic pin and
baseline. Reads were bounded but two initially combined captures truncated;
the needed decision, core §6, typed transport §6, source-emission §§3.1–3.5,
historical witness and selected syntax sections were reread in bounded outputs.
The compatibility document was read for §1's governing decision; its unrelated
long candidates were not used. No broad source search was completed or claimed.

Resource budget used: zero builds/tests, zero probe processes, zero generated
outputs beyond this one leased note; short single-shell source reads, with at
most four independent read commands in a batch. CPU time/peak RAM and exact
wall duration were not instrumented. No heavyweight resource was requested.
Independent review: pending; this producer's derivation and reread are not
independent certification. Freeze: writing stops before submission to primary.

Commit packet:

- Exact leased paths: `notes/progress/2026-10-05-annotation-boundary-chain-derivation.md`.
- Baseline SHA: `f50c8a88882a10f109a71e2842f4d1b02982de53`.
- Source pin: `0ab7620e167f190691a9ec50fde507d039265aa4`;
  decision pin: `28dddc75fd598faf34dd4d069ffb231cb64a82f1`.
- Dependency changes from source/decision pin to baseline: none among the
  direct dependencies checked. Live semantic replacements are excluded.
- Review status: frozen, conditional research derivation; independently
  reviewed by `compiler_referee` with no blocking/major finding. One minor
  same-position scope ambiguity was closed by clarifying H1/§3 above; the
  mixed-position projection was already conditional in H4/§5. H0/H2–H4 remain
  unclosed. No theorem closure, authority or production conformance.
- Checks: source/decision equality and exact-section inspection described above;
  final path/hash/syntax-hygiene inspection to be reported with submission.
- Proposed commit message: `research: derive conditional sequential annotation boundary adequacy`.
- Shared deltas left for primary/curator: record the q1/d1 query-trace consequence,
  retain local realization/role-placement and common-assignment gates, link this
  conditional artifact in task/theory records if accepted, and update the
  decision receipt/durable governing record only after applicable review.
  No shared file, authority source, question bundle or index was modified.
