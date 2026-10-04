# Production callback endpoint generation

Date: 2026-10-04
Status: Draft; design/proof gate only; no implementation authority
Reviewed-by: independent compiler_referee and spec_auditor focused and delta
reviews, 2026-10-04; no remaining findings
Scope: raw/HIR callback application, B step 6 completed Function endpoint, and
source-to-endpoint correspondence with Theorem C
Authority: preserves the Authoritative callback contract and reviewed
conditional Theorem C; adds no comparison semantics, solver carrier, or
provenance owner
Depends on: [callback context delivery](2026-10-03-callback-context-delivery.md),
[typed computation core](2026-10-02-typed-computation-core-elaboration.md),
[source-generated theorem package](2026-10-04-source-generated-callback-structural-theorems.md),
[concrete compatibility](2026-10-03-concrete-compatibility-boundary.md), and
[HIR/source-core boundary](../progress/2026-10-04-hir-source-core-boundary.md)

## 1. Design target and retained decisions

This design fixes one reference generation path for known-callee callback
applications. Expected callback context reaches an unannotated literal before
body generation; parameter, body, and result endpoints are independently
generated; the completed interface is checked by one ordinary `F_lit <: F_cb`.
No endpoint is copied from or equated with the expected endpoint. Any early
propagation is only an observationally/solution-equivalent scheduling of that
reference rule.

A prebuilt Pure value follows the separate callback-slot invocation-view path.
Its introduction role and §21 entry remain unchanged. Theorem C concerns this
path and its checked view; it does not establish adequacy for the literal's B
comparison. Both paths reuse `Rel_C`, `K,D`, source segments, operand tuples,
binder scopes, `nu`, `d+`/`b+`/`d-` occurrences, receipts, `Flow`/`Observe`, and
existing directed-weight/subtraction evidence. They add no carrier or
independent effect-subtyping relation.

## 2. Raw/HIR callback application

The resolved expression tree needs an application node because the current
lowerer rejects non-leaf associated expressions. The proposed node is:

```text
ResolvedExpr::Apply {
    occurrence: HirOccurrenceId,
    form: ApplicationForm,
    callee: Box<ResolvedExpr>,
    argument: Box<ResolvedExpr>,
    range: Range<usize>,
}
```

For the already selected source witness, the production realization is one
unary lambda with an identifier binder:

```text
LambdaExpression := Backslash Identifier Arrow Expression
```

```text
\x -> x
```

The generic operator-shaped-character scanner excludes `\`, though the NUD
dynamic-operator lookup can still recognize it when the operator table has an
entry; otherwise existing token/unknown recovery applies. `->` already has an
exact `Arrow` token scanner. For the selected source form, recognize the complete bounded opener
`\ Identifier ->` as a lambda production before dynamic-operator lookup.
This reserves only the complete unary lambda header and leaves a standalone
or otherwise nonmatching `\` to existing operator/token recovery. After the exact
arrow, parse the body with the ordinary expression grammar and its surrounding
delimiter/line stops. The CST node retains the introducer, binder, arrow,
body, and source ranges; a lambda nested in a `CallTail` or `MlArgument`
remains a child of that application form. Recovery after a recognized header
must retain the binder and resume at the existing body stops; its malformed
header diagnostics remain a parser conformance obligation. The reviewed source
contract supplies this unary witness; it does not select a multi-binder
grammar, so this design makes no claim about one.

For this bounded callback application, `Apply` denotes one source application
step with one whole argument: an `MlArgument` or a `CallTail` containing one
argument expression. `CallTail` with zero or multiple items remains outside
this correspondence claim until its argument-carrier rule is specified;
lowering preserves its complete source grouping and cannot invent tuple or
sequence meaning. Each `MlArgument` tail supplies one argument stage, so
`f a b` lowers by structural association into nested application nodes rather
than one flattened multi-argument call. `f(a)(b)` similarly has two call
stages when represented by two call tails.

An inline lambda is admitted by this bounded bridge only inside an admitted
binding's value/body, where its enclosing `DefinitionRootId` already exists.
The resolved lambda stores its `HirParameter` (id, spelling, and range), not
only the id. Its id uses that root and a unique ordinal distinct from the
binding-header parameters. `owns_parameter` traverses nested resolved
expressions and validates the stored identity. Direct expression roots without
a `DefinitionRootId`, and other binder forms, are not covered by this bridge;
this is not a source rejection rule.

The application node stores neither expected types nor Pure/Handler role.
During typed source generation, the known callee interface identifies the
callback slot and supplies transient `(F_cb, beta, Slots(beta))` context before
recursing into a literal argument. The literal remains an ordinary lambda HIR
node elsewhere. Nonliteral arguments retain their existing interface and use
the existing-value adaptation path. Unresolved callees do not silently cause a
callback literal to be introduced as Pure.

This is a production node/lowering design, not a claim that current syntax/HIR
already implements it. The source spelling `\x -> x` and general `λ x -> e`
form are already used by the Authoritative callback contract (§2, §8), so this
draft proposes their CST realization instead of asking to choose a spelling.
The current `yu-syntax::SyntaxKind` has no dedicated lambda-expression node,
and current `ResolvedExpr::Lambda` is created only when a parameterized
binding head is lowered; it does not represent an inline function literal in
an application argument. `lower_simple_chain` rejects non-leaf associated
expressions. Thus the approved source form has no raw-to-resolved-HIR witness
on this branch yet. The lambda production proposed above is a bounded
realization of the approved unary identifier example; other binder forms and
multi-binder surface syntax are not claimed.

## 3. B step 6 endpoint construction

The source generator returns the existing typed-core triple `(I,d,n)`. Keep
the outer application owner and the lambda's latent invocation owner distinct.
`S_apply` owns the call of the host/callee with the callback value as its inert
whole argument and the host call's operand tuple. The host's later invocation
of that callback has its receipt in the host invocation context. It does not
own the callback body's argument carrier, force, inner receipt, or body result:
constructing a function literal does not invoke it. Those belong to the
lambda's existing latent invocation source segments
and operand tuple `X_latent`, under the literal's binder scope and captured
roots. Their `nu,K,D` entries are the original shared-coordinate and binder
references at that owner, not copies of the outer application tuple.

```text
GenerateCallbackLiteral(literal, callback-slot F_cb, X_latent):
  reserve/reuse the lambda's source label, latent operand tuple, and binder
  scope under its original captured roots in X_latent
  pass the expected callback boundary and select Handler before body visit
  (P, I_body, d_body, n_body) := GenerateLambda(
      literal, Handler, boundary(F_cb), X_latent)
  synthesize P, I_body, and Result(I_body) independently; do not assign them
  from F_cb
  C_lit := existing lambda relation for P and n_body
  in the lambda's latent invocation graph, use its symbolic whole argument D
  and the existing invocation/entry relation; do not use S_apply's argument
  tuple or receipt as D or the inner receipt
  project the completed Function endpoints from selected occurrences/evidence
  in this same X_latent:
       d- : D -> designated Force view at J_arg
       d+ : same Force-origin component -> latent CallView at J_call
       b+ : body/result-consumer component -> latent CallView at J_call
  derive the contravariant argument descriptor from abstract components
       and concrete attachments in the d- projection; subtract a concrete contribution
       only when its attachment is witnessed by existing subtraction evidence
  derive the covariant output row as canonical flat [b+, d+], retaining
       original occurrences and their evidence references
  F_lit := Fun(P, d-, [b+, d+], Result(I_body))
  I_lit := Value(F_lit)
  n_lit := Normalize(I_lit, lambda(P, n_body))
  emit exactly one ordinary inequality F_lit <: F_cb
  return (I_lit, lambda(P, n_body), n_lit)

GenerateApply(f, arg, X):
  reserve the outer application label and whole-argument tuple in X before
  descending; preserve any receipt in the host invocation context
  if arg is an inline literal in a known callback slot F_cb:
      obtain the lambda's existing latent tuple X_latent under its binder and
      captured roots; do not alias it to X
      (I_arg, d_arg, n_arg) := GenerateCallbackLiteral(arg, F_cb, X_latent)
  else:
      (I_arg, d_arg, n_arg) := ordinary independent argument generation
  C_apply := existing outer call composition of f and the inert whole arg,
             preserving its own receipt; any callback invocation has its
             distinct receipt in the host call context
  return existing application result (I_apply, d_apply, n_apply)
```

This is a reference schedule, not a second judgment. Every arrow must resolve
to existing source path/Flow/Observe/incidence and subtraction evidence in
`X_latent`. The row component of the contravariant descriptor is the common part of
its abstract type components. Concrete-bearing structure is retained only to
identify witnessed attachments for partial reverse addition. Nested rows
survive only when they retain a distinct abstract component or attachment
that cannot be represented by the flat covariant view. The rule does not
flatten such contravariant structure blindly or perform total subtraction.
If an arrow, attachment, or endpoint projection is absent, generation stops
at that proof obligation; query success cannot manufacture it.

The two owners matter in ordinary source. `host (\\x -> x)` may ignore the
callback, so constructing the literal does not force an argument or create an
invocation receipt. `host` may instead return the callback and a later source
call may enter its latent graph. In both programs the literal's Function
interface is generated from `X_latent` before comparison; its existence does
not assert that an invocation occurred.

For the bounded one-argument callback literal:

1. Select Handler and its callback boundary before body generation.
2. Independently generate parameter interface `P`, body interface `I_body`,
   and body derivation `d_body` under that role and the original lexical scope.
3. Form the typed-core constructor/result skeleton
   `Value(Fun(P, Result(I_body)))` and its lambda derivation. This skeleton is
   not yet the completed four-port Function endpoint.
4. Complete the existing `yu-types` Function node by projecting its parameter,
   result, and coupled effect-port endpoints from the *same* generated source
   graph and existing source evidence, with these selected occurrence maps:

   ```text
   d- -> whole inert argument carrier D and its designated Force view at J_arg
   d+ -> the same Force-origin contribution observed at complete J_call
   b+ -> body and designated result-consumer contribution at complete J_call
   ```

   The contravariant argument descriptor retains abstract components and only
   the concrete attachment/subtraction structure witnessed by the existing
   directed-weight evidence at `d-`. The covariant output is the canonical
   flat row whose source occurrences are `d+` and `b+`, displayed `[b,d]`;
   `Flow`, `Observe`, `Path`/`Inc_C`, receipts, and shared `nu,K,D` retain their
   correlations at the original occurrences. These are coupled projections
   from one source graph, not independent `Type` comparisons or a row-union
   rule. If existing evidence does not provide a required attachment or
   path, generation stops at that proof obligation. It must not invent a
   subtraction result or use `never`, `Any`, or an empty row as a role marker.
5. Normalize the computation derivation against that completed interface and
   emit exactly one ordinary `F_lit <: F_cb` query.

The port projection in step 4 is intentionally an operation on the existing
source graph/evidence, not a new `EffectPort` carrier. The checked endpoint for
a prebuilt Pure value is produced separately by Theorem C's lift: copy the
whole old tuple and relation constructors, then add only fresh logical
coordinates `W` with total definitions `Def_T(W;X,Z)`. Thus
`F_checked(X,Z,W) = F_G(X,Z) and Def_T(W;X,Z)`. Forgetting `W` preserves the
old tuples, scopes, and observations. It adds no complete-call bound leaf and
no persistent evidence owner.

The complete invocation relation in the Pure-value checked path is the
existing typed-core `call`/`bind` composition, with its original operands and
scopes:

```text
argument expression -> inert whole carrier D
actual callback receipt -> callback invocation view
within that view: Force(D) >>= typed rebind(Value(a)) >>= body >>= designated result consumer
return from this invocation
```

Generation preallocates the application and source identities before
descending, then emits the existing child relations and references. The
callback-value receipt and argument receipt are separate operands. The
force/body composition is the existing state-threaded bind; it carries
requests and pending suffixes without replaying either receipt. `d-`, `d+`,
and `b+` are projections of this one graph, with static `Path`/incidence
references at their selected positions before the ordinary inequality is
resolved. No second complete-call relation is conjoined after graph
projection. This is separate from B's callback-literal introduction: the
Pure value keeps its original role and Value entry, while the slot supplies
only the invocation view.

The graph `G` is assembled before the selected linked `[b,d]` observation
projection. `d-`, `d+`, and `b+` remain distinct occurrences with their
existing incidence; shared operands and `nu,K,D` are bound once at their
original scopes. The callback challenge-admission rules are generated from
the punctured source context, independently of the inequality and its
success.

## 4. Source-to-endpoint theorem and exact remaining premise

### Theorem P (conditional production correspondence)

The reference rule is recursion over the finite resolved HIR graph. It
preallocates existing source labels and `HirParameterId`s under each admitted
binding root, then lowers children while preserving their source identities.
The raw/HIR crosswalk is bounded to the expression constructors below. The
surrounding Theorem C challenge/provider derivations remain the existing
decorated source inputs described in that theorem; this crosswalk does not
claim that current raw HIR generates the full challenge language.

| Resolved HIR node | Existing typed-core/source constructor |
|---|---|
| integer | literal with its original source operand tuple |
| name | lookup of its resolved lexical root or `HirParameterId` |
| lambda | `lambda(P, body)` with role/context selected before body recursion |
| unary Apply | `call(callee, inert-whole-argument)` and the producer's actual `ExecuteCallable` image |
| Error / unsupported form | outside this correspondence theorem |

For an Apply whose argument is an inline literal in callback position, the
known callee's callback boundary is threaded into the lambda before its body
is visited. The lambda still independently generates `P`, body, and result;
the resulting completed endpoint is checked once by ordinary
`F_lit <: F_cb`. For an existing Pure value, the call constructor preserves
its actual Value entry and only the slot's typed invocation view. The
constructor trace consists of the existing relation nodes and their operands;
it is not a second semantic graph or a new runtime carrier.

For a finite resolved callback application in Theorem C's source envelope,
whose application stages have one argument each as in §2, and, when an inline
callback literal is present, that literal is nested under an admitted binding
root, assume the syntax,
HIR, and source generator implement the clauses in §§2–3. Then the structural
generation induction must establish:

- each HIR call/lambda maps to its typed-core call/lambda derivation;
- callback context reaches an inline literal before body generation, while
  body/parameter/result endpoints remain independently synthesized;
- the Pure-value checked view is the total-coordinate extension of the same
  old relation, with `W` total on that old tuple and no added bound leaf;
- challenge admission is generated without the tested inequality; and
- all original `nu,K,D`, source roots, paths, receipts, `d-`/`d+`/`b+`
  occurrences, attachments, and provenance survive through the linked
  observation projection.

The structural induction establishes finite lowering and B's role-first
generation order, conditional on the port projections in §3 being supplied by
existing source evidence. It yields the typed-core lambda skeleton and
independently synthesized child endpoints; it does not prove adequacy of the
completed four-port Function projection. The checked-lift clause copies the
old tuple and scope and adds only total definitions for fresh `W`;
query-independent challenge admission follows from the punctured-context
rules in Theorem C §3. To identify the Pure-value production endpoint with
Theorem C's generator, and thus apply its bound inclusion, the following
source-to-endpoint correspondence remains:

The B literal path has a separate obligation at this same port-projection
boundary: its completed Function node must be constructed from the independently
synthesized endpoints and the role-selected `d-`/`d+`/`b+` evidence in §3.
It is not covered by Theorem C, and its final `F_lit <: F_cb` query cannot
substitute for missing endpoint evidence. The open premise below is the
source-generator conformance needed to apply Theorem C's mathematical
construction; production endpoint interpretation remains a separate bridge.

> **Source-generator conformance premise:** the finite constructor trace
> passes the source checks of Theorem C §§2.2–2.6 and §3: each local primitive
> certificate preserves its original operands/evidence and is shared by actual
> and checked constructions; relational constructors are the specified
> positive ones; tuple fields and binder/
> rigid-quantifier scopes are copied; recursion uses finite derivations and
> retains latent labels; the checked lift copies whole old tuples and adds
> only total definitions for fresh coordinates; and punctured challenge rules
> do not depend on the query. The finite audit also verifies each required
> typed path, receipt, `d-`/`d+`/`b+` incidence, and witnessed concrete
> attachment/subtraction reference under the same `nu,K,D`. A missing field
> fails the audit before the query; no endpoint equality or query result can
> supply it. The audit does not test either desired inclusion.

**Finite source-to-generator theorem.** For each finite resolved-HIR input in
the stated envelope for which generation completes, the source-local
primitive and decorated challenge/provider certificates must be valid, and
the generator's finite audit must resolve every selected endpoint, typed path,
occurrence/incidence, receipt, and witnessed concrete attachment/subtraction
reference in the owning source tuple. Missing evidence stops generation before
the query; it is not inferred from shape or success. Under these source-
checkable conditions, the reference generator emits a finite trace satisfying
the source-generator conformance premise. The proof is structural induction
on resolved HIR, with back edges mapped to preallocated labels. Integer/name
cases copy their local tuple and certificate; Lambda uses its own latent tuple
and binder scope; Apply preserves the outer whole-argument tuple and dispatches
through the producer's actual entry image. At a callback literal, the three
selected occurrences are references in that same latent tuple, while the
outer Apply keeps its own tuple and any host-owned receipt. In every case the
relation constructor is the existing positive source constructor, so no
constructor adds a root observation or tests the pending inequality. The
checked-lift construction copies the entire old tuple and scopes before adding
only total fresh-coordinate definitions. Punctured challenge generation reads
the source context and providers before the query. These cases discharge
Theorem C §§2.2–2.6 and §3's finite-generation, tuple/scope, lift, and
query-independence checks; they do not prove the semantic validity of supplied
primitive/provider certificates, existence of the required port evidence for
every source program, or the desired inclusion.

**Relational-graph correspondence theorem.** Under the source-generator
conformance premise, induction over the finite resolved HIR graph maps each
constructor to its same-tag constructor in Theorem C's `G`: leaves preserve
their local relation and tuple; lambdas preserve their independently generated
latent invocation graph and captured roots; each Apply preserves callee, inert
whole argument, distinct receipts, and the producer's actual `ExecuteCallable`
image. For a Value-entry closure invocation, this image uses the state-threaded
`Force(D) >>= B` composition; retained entry and operation producers preserve
their respective source images. The graph is joined before the
`[b,d]` projection, so the map preserves the designated occurrences and their
existing paths/incidence. By construction there is no root observation clause.
Theorem C's bound-derivation inversion then handles every generated
alternative, latent descriptor, and finite future-use/resumption witness; its
challenge rules give domain inclusion. This proves correspondence with
Theorem C's **mathematical** generator and yields its full-bound result for that
relational graph. It does not, by itself, identify the denotation of a
production `yu-types` endpoint with that graph.

The one remaining production theorem is the **endpoint realization law**.
Each owning source constructor first has its local relation `Rel_j`, either
the exact source relation or a source-certified conservative abstraction as
allowed by Theorem C §2.2. For every finite output of the rule above, the
production Function endpoint/constraint trace must denote the least relation
generated from those `Rel_j` leaves, with the same full source tuples, binder
scopes, `nu,K,D`, occurrence incidences, and joint hiding. The checked
Pure-value endpoint is exactly the total-coordinate extension of that same
generated relation. A finite source audit must show that each endpoint
constructor preserves its old operands and scope for arbitrary child
relations in the same fiber, and that the production recursive bound contains
exactly the finite derivations (including prefixes, latent/future-use and
resumption developments) of that constructor graph. These are the two clauses
of one realization law, not extra semantic constructors. If a `Rel_j`
abstracts value dependence, its local source certificate must establish the
admitted observation projection; endpoint shape alone cannot stand in for
that certificate. The law cannot be inferred from printed `Fun` ports,
binary lower/upper facts, or a successful query.

The merged [callback local-abstraction result](../progress/2026-10-04-callback-local-abstraction-boundary.md)
sharpens this obligation. An endpoint-only denotation from grounded ports
cannot in general factor through exact name/body recipes: identity and
constant functions can share those ports while differing on a fixed singleton
input. A source-owned saturated integer-body relation supplies a local
abstraction and a projected first-order lift, but its observation projection
forgets concrete input/output root equality. It therefore does not establish
Theorem C's full production correspondence, higher-order callback adequacy,
or the relation used by this generator. This is evidence against silently
assuming exact recipe factorization from ports, not a production
counterexample or an approved choice of local abstraction.

Under this law, the finite crosswalk above is a source-checkable certificate
that production emitted Theorem C's generator using the same certified local
relations on both sides. Theorem C then directly gives
`D_checked ⊆ D_actual` and `P_actual ⊆ P_checked` for the Pure-value checked
path, and the total-coordinate clause preserves every old tuple. Without
this law, the source induction establishes correspondence only to the
mathematical graph, not to a production `yu-types` endpoint. Neither
`Force(D) >>= B` nor common `nu,K,D` alone proves the law. This is the exact
remaining blocker; no production counterexample or additional user semantic
choice has been found.

The current code does not expose this relational representation directly:
`ResolvedExpr` contains only Lambda/Integer/Name/Error, `ConstraintStore`
facts contain ordered lower/upper `Term`s, and a separate provenance log
links occurrences to facts. `TermView` contains polarized type endpoints,
including four-child Function nodes. Those structures retain useful source identity and endpoint
sharing, but they have no call/bind/request relation nodes, whole-tuple
composition, rigid relational scopes, or typed runtime receipt/Flow/Observe
edges. The current Function term also has no introduction-role or invocation-
view tag. This is evidence that the present artifacts alone do not provide
the required denotation theorem; it is not evidence that a new carrier is
necessary, since an expanded HIR plus existing source semantics might support
a proof-only reconstruction. No carrier or implementation is authorized by
this observation. The identity-lambda endpoint link documented in
`notes/progress/2026-10-04-production-hir-empty-record-shadow.md` remains a
local projection result, not whole-bound denotation.
For inline literals, this induction covers raw/HIR shape, role selection,
independent child synthesis, and final ordinary B query only; completed-port
evidence and its source correspondence remain proof obligations. B literals
do not inherit Theorem C's Pure-value inclusion result.

### Proof structure after the premise is discharged

Induct on the finite resolved graph, allocating existing source labels before
children so recursive references target the same labels. The lowering
induction preserves ordered child/group structure and lexical identity. The
generation induction follows the existing typed-core constructors; at a
callback literal it threads the transient expected boundary before entering
the lambda body. For the checked Pure view, the relation-constructor induction
copies each old tuple/scope and the total-coordinate equations, so projection
forgets only `W`. Query-independent challenge admission follows the punctured
context clauses of Theorem C. The source-generator conformance premise
establishes that the abstract relation graph is Theorem C's generator. The
separate endpoint-interpretation bridge is still required before treating the
production `yu-types` endpoint as denoting that graph and claiming production
domain/bound inclusions. B literal completed-port validation remains separate
because that path uses the ordinary inequality and does not inherit Theorem
C's Pure-value result.

## 5. Implementation conformance and authority gate

Implementation must preserve the reference B query and prove any optimized
scheduling observationally/solution-equivalent, including principal
solutions, method/adapter choices, and residual/evidence semantics. No
endpoint equality stronger than B is allowed. The syntax/HIR lowering owner
creates the application node and nested identity ownership; the existing
source-generation owner threads transient context and emits the finite graph
and endpoint references. Neither HIR nor a separate elaboration product owns
a persistent callback type.

This remains Draft. The raw/HIR lowering and B step-6 reference generator are
specified above; their implementation and the endpoint realization law are
not authorized yet. The realization law is the single unclosed production
premise for the Pure-value path: it connects the checked endpoint and its
total-coordinate lift to the finite Theorem C relation. The B literal path has
a separate generation conformance clause: it must construct its completed
ports from independently synthesized endpoints and the same existing
occurrence evidence before issuing its ordinary inequality; Theorem C does not
claim bound adequacy for that path. Neither clause adds a carrier or changes
semantics. The bounded
complete-header arbitration paragraph received focused compiler/spec delta
review; the lexical-classification wording was corrected, and no blocker was
reported for the arbitration itself. That review does not certify malformed
header recovery or endpoint realization. Compiler edits remain unauthorized
until the design is reviewed and explicitly approved. No code, tests,
snapshots, or diagnostics are changed by this document.
