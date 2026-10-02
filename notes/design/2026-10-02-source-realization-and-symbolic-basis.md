# Source realization and finite symbolic ownership

Date: 2026-10-02
Status: Draft; conditional source-realization package; no implementation authority
Scope: monomorphic ownership basis, operational kernel, selected-fault reflection
Approved-by: none
Drafted-by: primary with bounded control/heap and symbolic-basis architect inputs
Reviewed-by: compiler_referee and spec_auditor, independent package reviews, 2026-10-02; no findings within the declared conditional envelope
Projection-basis-review: structural observation package and position-indexed admission repair reviewed; independent compiler_referee closure clean, 2026-10-02
Execution-image-review: §7 constructive query/shallow-control package independently reviewed by compiler_referee and spec_auditor; no findings within the resolved-input envelope
Guarded-closure-review: §8 independently reviewed by compiler_referee and spec_auditor, 2026-10-03; no blocking/major findings; minor pure-rule side-condition omission corrected by primary reference/diff inspection
Admission-row-review: §9 independently reviewed by compiler_referee and spec_auditor, 2026-10-03; no findings within the explicit-list and eligible-row fragments; pending existential-level representation interpretation excluded
Supersedes: none

## 1. What this package establishes

The finite safety-certificate theorem in
`2026-10-02-finite-abstract-safety-presentation.md` takes finite graph and
predicate inputs. This package constructs the predicate input from a finite
monomorphic descriptor graph, identifies the operational kernel that can be
lowered to that heap machine, and derives universal error reflection for
selected-arm incompatibility. It does not assume finitely many ground types
or bounded execution depth.

At the initial checkpoint, callback-boundary relevance/visibility and effective
general value adaptation prevented unconditional source realization. The
reviewed typed-boundary relation and §7 below now construct visibility queries
for finite resolved ordinary templates. Raw-source template generation,
general value adaptation and open-client interaction remain separate.
These are not evidence of a non-finite presentation. The exact source
embedding remains valid: it copies the source relations without establishing
their effective implementation.

This is a new successor construction, not a Simple-sub-original rule or an
Oracle-derived visibility algorithm. Finite records and control labels are
proof/implementation bookkeeping. They introduce no new source constructs,
capture authority, or accepted loss of source programs.

## 2. Finite ownership descriptor input

Let `Ω` be a finite graph containing the code and ownership descriptors of
one monomorphic elaborated program, including the finite bodies of any
linked clients under consideration. It need not be well typed: its formulas
remain unsolved. This theorem does not construct `Ω` from arbitrary raw
source or prove that a source typing derivation admits such elaboration.

Its finite inventories are:

| Inventory | Contents |
|---|---|
| `T` | symbolic endpoint and finite type-term graph nodes, including free/imported endpoints |
| `O` | typed operation instances at value-lookup sites: declaration, family arguments, payload and response endpoints |
| `H` | handler arm instances, environments and typed argument/result endpoints |
| `B` | whole explicit callback-boundary contract templates and their receiver/callback slot sites |
| `Slots(b)` | finite static annotated contract-position inventory of the original signature profile of each `b∈B` |
| `V` | value, latent, residual, continuation and store-view templates |
| `J₀` | lexical source constraints, including original symbolic `K` formulas |
| `Σ` | finite primitive/adaptation type-query schemas, each with fixed endpoint arity `a_s` |

An endpoint denotes an arbitrary type under a single assignment `ν`. A finite
graph may contain recursive references; it is not unfolded to collect its
nodes. A tuple/list of endpoints has finite descriptor arity. Each operation
lookup has one fixed substitution map into `T`; application, thunk creation,
and `Force` retain that instance. Distinct lexical lookups have their own
local endpoints unless source sharing relates them. Free/imported endpoints
are not freshened.

`Slots(b)` is supplied within the finite monomorphic graph `Ω`. Its entries
identify original annotated profile positions, including distinct call-effect
and latent-result-effect positions. These static slots are distinct from the
potentially unbounded dynamic typed paths and execution occurrences that
witness transport and observation. Recursive references are not infinitely
unfolded to generate slots. This premise neither generates annotations nor
proves their finite elaboration from arbitrary source.

The monomorphic restriction is precise: executing a descriptor again may
allocate fresh runtime objects, but does not generate a new type endpoint,
type term, predicate schema, or type-level substitution. Runtime type
inspection/decomposition that recursively creates new type queries is not
included by calling its result a scalar. Generalization and polymorphic
instantiation are still later obligations.

This restriction is a proved property of the supplied fixed descriptor
machine, not a consequence of finite raw syntax. The role/elaboration
package `2026-10-02-source-computation-role-elaboration.md` gives a conditional
warning: its candidate unknown-target adapter equations construct type
positions absent from the initial producer inventory. Typed-computation-core
§7 has not established these equations as required source conversions;
proof-only checking creates no such positions. Neither finite source
templates nor removal of that unadopted candidate alone instantiates this
`Ω`. Source checking and a finite solved or parametric constructor/query
presentation remain required.

## 3. Constructing the symbolic basis

Define finite symbolic predicate names, with their intended meanings under
`ν`, as follows:

```text
PΩ = { Source_j                    | j ∈ J₀ }
   ∪ { Query_s(t₁,...,t_a_s)       | s ∈ Σ, (t₁,...,t_a_s) ∈ T^(a_s) }
   ∪ { Compat_o,h                  | o ∈ O, h ∈ H }
   ∪ { Admit_b,p,o                 | b ∈ B, p ∈ Slots(b), o ∈ O }
```

`Source_j` contains the original static constraints; the query product
enumerates all endpoint combinations of each supplied primitive/adaptation
schema, including combinations reached through abstract collisions.
`Compat_o,h` means the complete `OpCompat` relation of those
instances, including invariant family arguments and payload/response checks.
`Admit_b,p,o` means admission of instance `o` by the explicit concrete typed
contract at original profile slot `p`, under the same `ν` and including its
invariant family arguments. For a wildcard/absent capture contract it is
false; family equality alone does not make it true. Typed `Flow` preserves
this original profile-slot identity while transporting its observation path;
admission does not read an arbitrary matching family or the current
destination port. For example, call slot `E[α]` and latent-result slot `E[β]`
of one boundary yield distinct admission queries for `E[Int]`, with constraints
on `α` and `β` respectively. The Cartesian inventory lists possible queries,
not obligations to enforce all of them. A compatibility predicate becomes an obligation only
at an actually selected arm in the concrete machine, or at a selected state
of the declared conservative abstract machine.

Each name references its symbolic endpoints in `T`. It can stand for a finite
formula emitted by its descriptor; taking those finitely many component
atoms instead gives the same finiteness result. This notation does not claim
that underlying type equality/subtyping is decidable, or that a solver may
treat related predicate valuations as independent concrete type assignments.
Boolean cells lacking a realizing `ν` have empty concrete interpretation.

The separate `2026-10-02-parametric-open-row-presentation.md` constructs a
finite schema for open typed-row membership constraints. Substituting an
operation request into that schema computes its membership formula without
enumerating all future requests. This extends the available symbolic row
algebra, but does not prove that novel client endpoints/grounded queries
belong to the fixed finite `T/PΩ` inventory here. Connecting these parametric
queries to complete invocation and handler interactions remains required.

`2026-10-02-symbolic-request-register-quotient.md` constructs an alternative
finite symbolic inventory for a bounded register kernel: unknown request
points use equality partitions, unary-query colors and capped existential
capacities instead of new ground endpoint names. Its uniform lifting theorem
handles arbitrarily many input points within that interface. It does not
derive a bound on live source dependencies, reduce general `OpCompat`, or
turn this fixed-source descriptor theorem into a modular source theorem.

The name-level bound is

```text
|PΩ| ≤ |J₀| + Σ_{s∈Σ}|T|^(a_s) + |O||H| + |O| Σ_{b∈B}|Slots(b)|.
```

The structural observation candidate in typed-boundary §4 replaces a supplied
per-event `Route` test by projection of executing typed view delimiters before
dispatch. Given finite executable view decorations, routing reads their marked
current ports and needs no new type predicate. Contract admission and selected
compatibility still use `Admit_b,p,o` at the original profile slot preserved
by typed `Flow`, and `Compat_o,h`, under the same `ν`. Reading a marked current
observation port does not replace that original admission slot.
Its control theorem and corrected admission basis are reviewed; arbitrary-source elaboration
of the finite decorations remains open. If such elaboration adds symbolic
shape/position choices, their guards must lie in `J₀` or the finite query
schemas before the basis theorem can be instantiated. A hidden typing oracle
is not part of this construction.

Let `D` be a heap relation whose records link predicate names to dynamic
instances of templates in `V`, requests, values, store roots, or continuations.
There can be arbitrarily many records in an execution; their field tags and
symbolic endpoints come from finite `Ω`. They are not enumerated as new
predicate names. The finite heap abstraction represents them by address
links along with the objects they constrain.

**Basis closure theorem.** For execution of the descriptor machine, all type
queries and retained family predicates belong to `PΩ` or its Boolean algebra;
every live dependency references the same endpoint assignment `ν`.

Proof is induction on the execution prefix. Initialization copies formulas
from `J₀` and retains the supplied boundary templates and their original
`Slots(b)` references without unfolding recursive signatures. Lookup reads
its one static operation/value descriptor. Closure,
thunk, cell and continuation construction allocate runtime identities and
copy symbolic references. Call, adaptation code and `Force` reuse their
descriptors; the latter never opens a fresh operation instance. Request
construction uses some `o∈O`; selected-arm checking uses `(o,h)∈O×H`;
concrete-contract admission uses `(b,p,o)` with `b∈B`, `p∈Slots(b)` and
`o∈O`. Its `p` is the original profile identity retained through typed `Flow`,
not a newly allocated dynamic path or the transported destination port. Every
remaining supplied query uses a schema in `Σ` with arguments from `T`, hence occurs in its Cartesian
inventory. No other type query exists in the descriptor instruction vocabulary.
Bind, guard evaluation, forwarding
and raw resumption either execute another such instruction or transport
existing references. Runtime tests inspect values/identities, not newly
generated type syntax. Joining paths takes Boolean combinations in the same
algebra. Every copy retains the same endpoint IDs, so one `ν` interprets all
views. These cases are exhaustive for this descriptor machine.

Solving is not secretly performed by this induction: an eventual substitution
must act uniformly on all endpoint references and predicates. No equation is
discharged here. In particular, removing a handled request from immediate
support does not remove its predicate from a still-dependent latent, result,
store or continuation view. This proves symbolic closure before concrete
materialization, not the later lifecycle transport theorem.

## 4. Operational kernel and concrete heap encoding

Use fresh concrete addresses and records of bounded arity. Environments,
lists and unbounded stacks use linked records. Code and template references
are static labels in `Ω`.

```text
Closure/Thunk(body, env, lineage)      Cell(value)
Binding(slot, value, next)            Link(value, next)
Call(invocation, owner, boundary, parent)
ObserverFrame(site, viewRoot, portDescriptor, receiverRefs, parent, mode)
Handler(activation, owner, site, env, parent)
Suffix(site, env, next)
ReenterCall(template, env, suffix, next)
ReenterHandler(template, env, suffix, next)
Request(opTemplate, payload, origin, event, dependencies, observations, suffix)
EventObservation(event, observerOccurrence, port, actualPath, next)
Dependency(predicateTemplate, view, next)
Search(request, candidate, crossed, phase)
Adapter(boundaryTemplate, value, phase, next)
```

Field count is fixed per tag; a larger source tuple has a statically fixed
tag or linked spine. Identities point to their fresh allocation records.
The roots hold the current control/environment, live mutable store, active
activation and observer heads, continuation, and pending search. Saved suffixes retain
code, environments and references to cells, never the old contents of the
mutable store. A raw continuation may be stored and resumed multiple times.

For the explicit control clauses in the ordinary-computation package, expand
each finite syntactic continuation `F` in bind into `Suffix(site,env,next)`.
Appending bind stores its next suffix instead of applying a host-language
function later. Recursive calls allocate another record of an existing tag;
they do not copy or unfold the recursive code graph. Opaque host functions
are not allowed as unexamined fields.

| Source clause | Heap control |
|---|---|
| return / bind | return to the saved site and environment using the current state; a request carries the appended suffix |
| closure application | enter body using the closure environment and caller's live store/active heads; push the fresh invocation and its return suffix |
| typed CallView entry / exit | enter or leave exactly its executing observer occurrence; nested entries preserve all enclosing active observers |
| request observation | before dispatch, walk executing enclosing view delimiters and record each occurrence's marked current port; retain the same event and symbolic dependencies |
| invocation suspension / resume | save the source invocation and crossed observer scopes with the suffix; execute re-entry using the supplied live state and reinstate only scopes entered by that source suffix |
| thunk construction / force | store or enter the body/environment; copy origin and predicate/dependency references |
| operation construction / request | store the fixed typed operation instance; on demanded force allocate a new event with that instance |
| search | walk current active frames in order, updating the active head on unwind; retain pending search across pattern/guard evaluation |
| shallow selection | leave selected activation, pass its raw suffix to the arm; do not add a re-entry for the selected handler |
| forwarding | add exactly the source-prescribed wrappers for crossed computations; continue outward |

Re-entry of an invocation does not authorize restoring an exited maker or
consumed handler. Expiration changes active roots, not heap reachability.
Stored handler records alone are not active. Frame ownership/reference
remapping on resumed invocation occurrences must agree with the source
wrapper; this table does not invent a fresh capture grant by remapping an ID.
Observer frames are likewise execution bookkeeping, not authority. A saved
frame does not count as a running `Observe` witness while the captured suffix
is outside it; a resumed suffix re-enters its source-prescribed observer
scope without making an expired receiver or handler active. The typed-boundary
§4 context projection supplies the routing candidate for finite decorated
views; it uses neither adapter tags nor family membership. Its saved-context
extension preserves view nesting without rebinding authority. The user has
selected outside selector evaluation; the projection/control theorem and
position-indexed admission basis have clean package/repair review within
their declared decorated-kernel inputs. Raw-source elaboration remains open.

`2026-10-02-typed-source-owner-realization.md` supplies an explicit candidate
for that ownership protocol: saved executable owner spans resolve to exact
live occurrences or fresh execution occurrences, and owned/borrowed delimiters
govern completion. It preserves original value/evidence ownership references.
Its theorem covers the decorated operational kernel, conditional on supplied
source profiles/maps, rather than deriving arbitrary raw-source elaboration.

The kernel table is a compilation schema conditional on the finite source
descriptors and wrapper transitions. Section 7 expands visibility into
concrete graph-query instructions for those resolved ordinary inputs, using
the typed-boundary relation rather than an unexamined `DerivationLink` graph.
Arbitrary source adaptation and template generation remain unproved.

## 5. Simulation and selected-fault reflection

Relate a source descriptor execution to its concrete heap encoding by equality
of code positions and the decoded rooted graph, up to bijective fresh runtime
identity renaming. Decode environments, current store, ordered activations,
raw suffix and pending search together. Symbolic templates are unchanged.
For a supplied realization of the primitive clauses, the kernel table gives
source-step simulation by finitely many heap instructions: return/bind follow
the suffix record; call allocates and enters; force enters without new type
lookup; search updates one current frame at a time; selection/forwarding
construct precisely their different suffixes. Normal return and resumed
execution both use the current store. Induction composes these cases.

Composing this encoding with the earlier finite-address heap representation
gives the weak source simulation

```text
c ≼ν q and c →ν c′  ⇒  ∃q′. q →#ν* q′ and c′ ≼ν q′.
```

The simulation premise includes primitive realizations and same-`ν` initial
coverage. Primitive realization must finish each individual source step;
arbitrary infinite administrative stuttering is not a witness. Intermediate
abstract states participate in saturation, so the finite-certificate proof
works with this finite-path simulation as well: induction preserves reachable
representatives at source observation boundaries.

**Selected-fault construction.** Make `Selected(o,h)` an explicit control
observation after runtime selection and before checking compatibility. Its
static descriptor IDs are registers; it is not an operation that can skip
or redirect selection. Put

```text
Bad_q(ν) = ⋁{ ¬Compat_o,h(ν) | (o,h) is a selected pair represented by q }.
```

The represented-pair set is finite: it is a subset of `O×H`, obtained by
enumerating the finite register/store alternatives. In the exact-register
encoding it has one pair. A concrete incompatible selected pair occurs in
every representing abstract state's pair set. Therefore

```text
c ≼ν q ∧ SelectedIncompatibleν(c)  ⇒  Bad_q(ν).
```

This is universal reflection, not existence of some unreachable bad
representative. With initial coverage and the weak simulation, the earlier
certificate domain `S` excludes every concrete selected-arm incompatibility.
The result does not prove coverage of all source faults or general type
safety. If uncertainty adds spurious selected pairs, their predicates can
shrink `S`; that is disclosed abstraction loss, not a concrete source error.

## 6. Exact remaining source definitions and future use

The follow-up `2026-10-02-typed-boundary-realization-draft.md` constructs finite
recursive adapters for fixed resolved Function/Thunk graphs. The user selected
typed-value transport for both scope choices; its §6 now gives the common
transport/query candidate. A typed-flow map transports value/profile paths,
but it does not alone identify the effect port at which a request emitted by
an executing adapter subcomputation is observed. §4 of that package now makes
this distinction explicit: the ordinary source `CallView` relation must
derive the event-to-observation edge, while typed flow carries the boundary
profile to the corresponding view port. The finite adapter pair graph does
not supply that edge on its own. This is one incidence graph with distinct
value-flow and request-observation edge domains, not a new adapter-specific
visibility rule.

The package does not select general `≈`, derive decorated `CallView` ports
and profiles from raw source, or prove re-entry ownership and arbitrary-client
closure.

The constructive results have the following boundary:

1. **Visibility realization.** Typed-boundary §6 now supplies common typed
   value flow, receiving ownership and exact-handler incidence. The incidence
   path has two source-derived parts: typed correspondence carries a boundary
   profile between matching value paths, while ordinary `CallView` execution
   relates each exposed request event to its complete-view effect port. The
   fixed-shape adapter pair graph supplies operational control but not that
   event-observation link. Derive profiles, typed maps, observation links and
   exact re-entry ownership from source typing to instantiate the common
   relation for all source rules. Active-frame walking alone does not prove
   callback relevance. Preserve concrete-contract visibility uniformly
   through direct/Force exposure, nesting, escape and shallow re-entry. Do not
   add boundary exclusions merely to make the traversal executable.
2. **Checking and required conversions.** Typed-computation-core §7 separates
   source introduction/consumption, proof-only checking, and executable
   admitted casts. First derive which conversions source acceptance requires;
   the old arbitrary thunk/function shape equations are not source authority.
   The inclusions in the checking fragment are semantic propositions, not an
   effective finite solver. Derive their relational presentation and finite
   query closure, plus source-preserving descriptors for required executable
   conversions, including force positions and return lineage. Calling
   `Adapt` or interface inclusion an instruction does not satisfy this premise.
3. **Uniform future interactions.** The basis theorem applies after fixing
   finite `Ω`, including linked client bodies. For each such client it
   covers arbitrarily many calls/resumes to those bodies. This is
   `∀finite client L. ∃finite presentation P(C linked with L)` under the
   same monomorphic/realization premises. It does not establish
   `∃finite P(C). ∀admissible L` for a reusable component. Arbitrary new
   client operation instances or opaque latent callback bodies are not in
   `O`; collecting their descriptors requires a modular interaction theorem,
   not a claim that runtime allocation is the only source of growth.

   The companion `2026-10-02-heap-backed-client-interactions.md` removes
   a bounded retained-handle premise by storing typed view packets in a
   linked client pool. Its command-driver theorem is uniform for one supplied
   finite template-closed signature. Source interface encapsulation must
   still derive that signature or a finite parametric/regular replacement;
   the linked-client basis theorem above does not discharge it.

   `2026-10-02-parametric-component-linking.md` now separates an alternative
   per-program route: first link reusable finite constraint templates, then
   construct that linked program's query inventory. It proves graph grafting
   and the joint projection law under binder separation; source template
   completeness and finite instance/query closure remain open. The stronger
   uniformly grounded arbitrary-client inventory is not required by charter
   §12 merely to establish a finite presentation per finite program.

These gaps localize the remaining source theorem. None proves class 3 or
authorizes narrowing the supported source envelope. The fixed-input result
is class 1 for this abstract judgment; cyclic execution is covered without
unfolding, but an exact regular quotient is not claimed. The accepted
Milestone-2 embedding and generic principal-certificate algebra need no new
review unless these definitions change their premises. Generalization,
fresh instantiation, intrusion, the next feasibility gate and implementation
remain downstream of a complete source presentation and acceptance bridge.

## 7. Construct the ordinary query and shallow-image control

This section discharges the remaining supplied **routing routine** premise
for a finite linked resolved ordinary template. It constructs the guarded
execution image, with symbolic type predicates still interpreted under one
assignment. It does not construct that resolved template or solve all its
typing constraints from arbitrary source.

### Input and finite control generation

Use the finite linked descriptor graph from §2, the core's generated source
consumers, the reviewed owner/view context grammar, and the common typed-flow
descriptors. That graph and its reachable code can be assembled from finite
open templates and supplied source-respecting instance maps by
parametric-component-linking §7. That
construction precedes this query lowering and the finite heap abstraction;
it removes a supplied merged-kernel premise within that resolved envelope.
All callable bodies and primitive execution routines reachable
in the linked context are supplied finite code. An external response that
introduces callable code needs its linked provider or a separately proved
interaction summary; it is not implicitly represented by an existing body.
Unknown-shape conversions are not included by naming them `Adapt`.

The finite profile/map states are those of typed-boundary §6's graph query.
All fields are finite static labels or links to runtime records, including
variable-length queues, paths, environments and dependency lists. A future
source map that cannot be realized with these states/linked records needs
its own realization proof. No unbounded type expression is hidden in a
finite scalar field.

Generate entry/exit and successor code labels for each core instruction.
Use shared finite-control routines for list walking, exact identity comparison,
queue insertion, visited membership and template-state transition lookup.
Their loops jump back to the same labels. Recursive source definitions also
retain code back edges; neither control construction unfolds recursion.

Symbolic tests branch on formulas in the finite `P_Omega` basis; structural
tests branch on record tags, scalar tests or runtime identity. This generates
a symbolic analysis graph, not an implementation of runtime type reflection.
Predicate satisfiability and full source checking are separate obligations.

### Exact finite administrative queries before abstraction

At a query boundary, hold the source roots and evidence fixed while running
the administrative query. The query invokes no user computation and mutates
only its private queue/visited/result records. Effectful source patterns,
guards and arms are separate code, never administrative predicates.

| Query | Concrete routine |
|---|---|
| current activity of an occurrence | walk the current active roots/list; compare exact occurrence IDs; saved heap reachability alone does not suffice |
| observations for a fresh event | walk executing view delimiters, read their marked current ports, append event/occurrence/port records before dispatch |
| typed profile/receipt path | start jobs at the event's recorded observations; traverse matching evidence edges in product with the supplied profile/map states and candidate owner |
| incidence | for each actual path witness, test the exact handler, owner and original boundary receiver against current activity |
| protection/grant | accumulate existence of an incident witness; for a grant additionally require exact receiver/owner equality and the original slot's `Admit_b,p,o` |

A path job retains all tuple coordinates needed by the common relation,
including original profile-slot/source tags. Matching joins use the same
view, event and intermediate typed port. Equal family heads or equal value
pointers cannot substitute for these joins.

Use a queue and a visited set of **concrete job tuples**, stored as linked
records. Pop a job, compare its full tuple with visited entries, skip it only
on exact equality, otherwise mark it and enumerate the applicable outgoing
transitions. A finite execution prefix has a finite evidence graph. Its
product with the fixed finite query states and current candidate has finitely
many distinct jobs; the visited routine therefore terminates, even when
profile/evidence edges have cycles. Active and executing lists likewise have
finite concrete length. The result equals the least path relation by the
usual worklist invariant: visited jobs are reachable, and every unprocessed
successor is queued. Exhaustion proves absence only for this exact graph.

Compute `Visible` from the resulting exact `Protected` and `Grant` booleans
and the source activity/coverage premises. This expands the common relation;
it introduces no new authority, selector or source-specific exception.

### Ordered shallow control, including effectful selection

For an original request, walk candidates in source order, performing the
source-prescribed unwinds between them. At the yielding candidate boundary,
compute the original event's applicability in that boundary configuration.
Then leave the candidate before executing its pattern/guard/finish/arm code,
as required by the outside-selection source equation. The pending match
retains the original applicability fact for that event, not a live grant for
new selector or arm requests.

All pattern/guard and value-arm code is generated with ordinary bind and
pending-continuation records. If that code performs an effect, dispatch its
new event in the current outer context; preserve the pending old match in
the new raw suffix. Returning resumes that match with the current store.
Exhaustion forwards the original request with only the source-prescribed
forwarding wrapper. Selection supplies its raw suffix without the selected
handler wrapper. `Selected(o,h)` is observed before static compatibility
checking; incompatibility never changes selection into forwarding.

Raw resumption reconstructs exactly the saved `Bind`, `Owner`, `View` and
forwarding-handler frames. Owner resolution searches for the saved exact
live occurrence and borrows it, or creates the permitted fresh executable
occurrence. Completion acts according to owned/borrowed mode. Original
boundary/receipt IDs are not rewritten by this executable-owner map. These
are the existing owner-realization instructions, now composed with the same
activity routine above. The selected shallow handler is never restored.

### Abstraction must preserve the query program, including negative results

Only after defining these concrete routines apply the existing weak-store
abstraction to their instructions and their auxiliary records. A comparison
of colliding abstract addresses permits both concrete equality outcomes.
In particular, the visited structure remains an abstracted concrete data
structure; it is not replaced by an exact set of abstract addresses.

Why this matters: one abstract state can represent a protected state and an
unprotected state at the same candidate, with no grant in either. A may-path
query reports possible protection. Using `not MayProtected` as the concrete
absence test then suppresses visibility in the represented unprotected state.
It loses a real capturing branch, and may consequently omit a selected-arm
fault or residual effect. Conversely, treating an address collision as a
visited concrete job can skip a later distinct witness. These are failures
of naive abstractions, not changes to source handler hygiene.

The instruction-level simulation avoids those shortcuts: for every concrete
query step its actual record and comparison outcome remain abstract choices.
Induction on the finite concrete query run reaches a representing abstract
return with the same Boolean result. Both true and false concrete outcomes
are covered. Abstract runs may also return additional answers or loop through
collisions; neither supplies a new source execution. Concrete query termination
provides a finite matching abstract path; not every abstract administrative
path must terminate. Saturation terminates on the finite joint abstract state
space, including query queues and pending control. No timeout/truncation is
used to decide a negative query.

This proves weak simulation for these query/search/control routines under
the stated resolved input. The same assignment and original `K,D` references
are preserved by every step. It does not prove an exact alias quotient or
approve possible loss of source acceptance from extra abstract paths.

### Generate the outward image after routing

Predispatch `Observe` and outward support are distinct. Add an output
observation when a request crosses the particular invocation/force/handler
output delimiter being summarized, or exits the root. A request handled
inside that delimiter contributes no outward request there; a request handled
later outside it has already crossed that port. Match/arm requests follow
their own current context. Preserve the complete request packet and raw
suffix as part of the observation, not only its family head.

Return and latent-value observations likewise retain their typed packets,
source path correspondences and dependency references. Constructing a latent
value emits no observation of its future execution. When the linked context
later consumes it, ordinary source code enters its own corresponding view.
Resumptions use their current store and new event observations; they are not
erased because the earlier request was consumed. Thus a raw suffix that
emits the same family can contribute an outward effect after shallow handling.

Enumerate the generated finite control/heap states and instruction transitions.
Let `G_ij` be their Boolean guards, `I_i` initialization, `Bad_i` the §5
universally reflected designated faults, and `Out_i(w)` the finite complete
output-observation alternatives. Define, in the finite Boolean algebra,

```text
R_i = I_i or disjunction_j (R_j and G_ji)          [least fixed point]
S   = Base and not disjunction_i (R_i and Bad_i)
U(w)= S and disjunction_i (R_i and Out_i(w)).
```

`Base` retains source and generic-arm checking constraints. The graph
construction does not solve them. Finite worklist reachability computes
`R`; Boolean operations produce `S,U`. This is the existing principal
certificate theorem instantiated with constructed ordinary control/query
routines. Its principal claim is relative to this conservative graph and
designated-fault judgment. Coverage of every source fault is still required
for full type safety.

An outward row is a derived projection of `U`: join the guarded family
instances of outward request packets at that port. Keep `S`, the joint
packet relation and live `K,D` alongside it. No family is subtracted merely
because a generic arm exists, and no removed row entry discharges a dependent
type predicate. There is no new source row constructor in these equations.

### Scope of closure

For finite linked resolved ordinary templates with the stated primitive and
typed-map inputs, this construction removes a supplied `Visible`/route oracle
and expands ordered shallow image computation into guarded finite control.
Known admitted adapter code can participate if already supplied and proved;
arbitrary adapter or raw-source shape generation is not derived here.

Still open: generation of all resolved source templates, effective complete
type/subtype predicates and scoped checking, reusable parametric summary
completeness, foreign interaction summaries where code is not linked, and
the acceptance bridge for this conservative abstraction. Neither full
Milestone 3 nor lifecycle/implementation readiness follows from this result.

## 8. Guarded positive obligations and joint bound closure

### Operational guards and checking obligations

This section concerns the explicit ordinary routing generator of §7, not
every supplied query signature `Sigma`. Its activity/incidence/protection
tests use runtime identity, active owners and typed paths. Its grant test
uses the original slot's `Admit` relation. When that relation has been
normalized to the existing equality/row membership grammar, its query is
within that grammar; arbitrary supplied `Admit` is not covered by this claim.
Source guards execute ordinary code. `Compat` is checked after selection,
and proof-only `VIncl/CIncl` does not determine runtime control.

Let `B` be the Boolean algebra over a fixed finite operational inventory
`P`. Guard formulas are interpreted under one complete assignment `nu`.
They may reference endpoint equalities evaluated under that same assignment;
finiteness does not prove their realizability or effective satisfiability.
The earlier interim signed-gate interpretation overstated a mandatory
arbitrary negative-subtype solver. This generator instead permits the
following conditional separation of routing and checking.

Suppose initialization factors as `I = J0 and I0`, with `Base => J0`, and
the transition guards permit reachability to factor as `R = J0 and R0`.
Then, for selected states `s` whose designated compatibility fault is
`not Compat_s`, the corresponding certificate clause is

```text
S = Base and AND_selected_s (R0_s implies Compat_s)
         and OtherFaultExclusion.
```

`OtherFaultExclusion` retains the separate clauses for all other designated
faults. The formula follows from `Base` implying `J0`; it does not remove
the other faults or infer the factorization from copied ledger references.
Establish the actual initialization/transition premises before using it.
If `J0` constrains transitions in a way that prevents the factorization,
retain the original `R` rather than applying this normal form.

The occurrence of `not Compat` in `Bad` therefore does not by itself demand
a solver for arbitrary negative subtype formulas. A selected state imposes
a positive checking obligation under its operational reachability guard.
Generic-arm uniform checking remains in `Base`, with its original scopes,
and cannot be replaced by compatibility at reached caller instances.

A complete checking predicate `C` enters the positive kernel below only
after a proved decomposition into that kernel's guarded obligations.
Unnormalized `Admit`, complete effectful Function contracts, and other
queries outside the established equality/row kernels remain interpreted
obligations. The pure Function rule below is not their decomposition proof.
No opaque predicate is made effective by naming it in a finite alphabet.

### Guarded lift of the finite pure closure

Use the finite endpoint graph and fixed-scope pure rules of
`2026-09-29-intrusion-abstract-semantics-draft.md` §1's finite saturation.
Let `N+`, `N-` be its positive/negative endpoints and subterms, and `V` its
variable identities. Introduce the finite fact inventory

```text
Q[p,n]          for p in N+, n in N-
L[v,p]          for v in V, p in N+
U[v,n]          for v in V, n in N-
Mismatch[p,n]   for p in N+, n in N-.
```

Every fact has a label in `B`, initially false. For each input obligation
`g => p <: n`, OR `g` into `Q[p,n]`. Multiple inputs for one pair retain
their disjunction. These labels describe one joint conditional bound graph;
they do not run independently mutating solvers for separate branches.
Sharing a pair label shares only the pure proof obligation. Original source
occurrences, profile/path IDs and `K,D` incidences remain separate; equal
type pairs or guard truth do not merge capture/protection views. This
bookkeeping is neither Oracle `StackWeight` routing nor a source construct.

Lift each existing finite Horn rule. For premises with labels `a_1,...,a_t`
and an admitted rule side guard `g`, OR
`g and a_1 and ... and a_t` into every conclusion label. The side guard
expresses only a proved applicability condition at the fixed scope/level.
It supplies no new type nodes, extrusion or generalization operation.

In particular, the lifted pure rules include:

- `Q[Var(v)+,Var(w)-]`, for `v != w`, inserts both `L[w,Var(v)+]` and
  `U[v,Var(w)-]`, retaining the same guard on both directions;
- `Q[Var(v)+,n]`, for nonvariable `n`, inserts `U[v,n]`, and
  `Q[p,Var(w)-]`, for nonvariable `p`, inserts `L[w,p]` under their guards;
- `Q[Var(v)+,Var(v)-]` generates no new bound;
- `L[v,p]` and `U[v,n]` insert `Q[p,n]` under the conjunction of
  their labels, so lower/upper propagation retains branch correlation;
- pure `Fun+(a-,r+) <: Fun-(a+,r-)` inserts `Q[a+,a-]` and
  `Q[r+,r-]`, with argument contravariance and result covariance;
- a positive union on the left inserts both component obligations;
  a negative intersection on the right inserts both component obligations;
- `Bottom` on the left, `Top` on the right and proved matching atomic
  trivialities close without generating a new obligation.

The distinct-variable case retains both bound insertions rather than choosing
one side. No negative-union or positive-intersection choice rule is added.
All facts use the same existing endpoints and ownership levels.

An irreducible pair contributes to `Mismatch[p,n]` only where the pure
carrier law proves that pair impossible. Its label is the region in which
that proved failure is required. In particular, rigid `kappa` is not an
atom disjoint from every concrete type: no `kappa != Int` or mismatch
classification follows from checking rigidity. Unsupported constructors
remain outside this closure theorem rather than being classified as failure.

### Finite schedule and pointwise exactness

Process eligible rules until no conclusion label grows. A worklist must
reschedule dependents whenever a premise label grows. A once-only visited
pair is invalid: reaching `Q[p,n]` under `g1` does not process its later
addition under `g2`. Comparing labels means equality in the finite Boolean
algebra, not merely remembering the endpoint pair.

For example, `L[v,Int]=p or r` and `U[v,Bool]=q` require
`Int <: Bool` under `(p or r) and q`. Where the pure mismatch law for those
atoms is proved, this is its failure guard. Adding `r` after processing `p`
must extend the derived label rather than being skipped as a visited pair.

One explicit representation is truth tables over the `2^|P|` Boolean cells.
Each fact/cell can be inserted once, giving at most
`number_of_facts * 2^|P|` fact/cell insertions. This is a termination bound,
not a claim that the resulting table or rule scheduling is practically small.
Symbolic labels may share formula nodes instead, subject to equivalent
finite-algebra operations. At each cell, at most `number_of_facts` synchronous
rounds add every reachable fact: each nonstable round adds a fact. The same
round bound therefore holds pointwise for the symbolic construction.

**Evaluation theorem.** Fix one `nu` and evaluate every label at its induced
operational valuation. Evaluation commutes with false, OR and AND, hence
with each lifted Horn stage. By induction, the evaluated stage is exactly
the corresponding unguarded pure Horn stage with the active inputs and
side guards at that `nu`. Taking the finite fixed point proves exact
pointwise closure and independence from any fair rule-processing order.

Guards may depend on the same endpoints whose bounds are being recorded.
They are interpreted at fixed `nu` throughout this theorem, not re-solved
or independently sampled after each insertion. Boolean cells not realized
by any assignment are algebraic cells only; no feasibility claim is made
for them. Routing-guard realizability, including semantic type equality,
remains a separate checking obligation.

### Joint solution preservation and binder discipline

Assume the existing pure carrier laws preserve solutions and every admitted
side guard justifies its rule at that assignment. Retain all initial guarded
clauses and append derived guarded clauses. Evaluation at fixed `nu` reduces
the preservation argument to the existing pure bound-insertion,
decomposition and transitivity laws: every added active clause is entailed.
Conversely, any solution of the saturated relation satisfies the retained
initial clauses. Thus the original and saturated **joint constraint
relations** are equal under those premises.

The mismatch formula is the OR of labels for proved impossible pairs.
It denotes only the established failure region of this fragment. This
does not give SAT completeness, complete source checking or source
principality. Equivalence is of the retained relations, not a claim that
the closure decides every interpreted predicate or selects a witness.

Keep original clauses, source contracts, all `K,D` references and their
binder blocks alongside the derived graph. In particular, preserve
`exists shared. forall kappa. exists body` without moving captured endpoints
under the universal or solving rigid `kappa` as flexible. A Boolean cell
does not license a fresh shared witness or independently inferred arm.
Existential request opening and its pack/unpack correspondence remain
distinct from existential inference variables in the pure equality kernel.
Fixed-scope closure neither instantiates nor skolem-unifies `kappa`;
unresolved rigid checks remain in `Base` or the scoped checking gate.

This is conditional closure of one joint bound relation. It does not
materialize type witnesses from independently satisfiable marginal graphs,
and does not merge protected profiles or declaration instances by equal
effect support. Re-entry and raw-resumption control still come from §7;
positive obligations cannot change selection into forwarding.

### Contribution and next source gate

The pure bound-propagation rules are a Simple-sub-original ingredient in
the stated fragment. Their Boolean guard lift is a new successor
construction; the source handler/routing rules are user-selected Yulang
extensions. Neither provenance transfers authority to a broader effectful
Function rule or a changed source acceptance policy.

The contribution is a finite conditional bound graph retaining all
operational branches jointly, together with a precise guard/check separation
when the displayed factorization premises hold. It corrects the interim
claim that this ordinary generator necessarily requires arbitrary negative
subtype solving before any progress is possible.

The next gate is normalization of the **actual emitted predicate syntax**
and its joint equality/row realization, including routing guards and
original-slot `Admit`. Complete inclusion predicates need proved
decompositions before this closure can be instantiated for them. Arbitrary
first-order subtyping is not silently substituted for that bounded task.

Full source principal presentation and its acceptance bridge remain open.
No source capability is narrowed, no generalization/lifecycle theorem is
closed, and no implementation gate is opened by this conditional package.

## 9. Original capture admission and mixed guarded row blocks

### Concrete original-slot admission

Use ordinary-computation §4's annotation distinction and typed-boundary §6's
original-slot profile/path relation. Fix a source boundary `b` and its
capture component at position `p`. For the explicit concrete list
`{F_i(rho_i)}`, compile its admission test as

```text
Admit_nu(b,p,q) = OR_i
  (head(point(q)) = F_i and Eq_nu(args(point(q)),rho_i)).
```

Tuple equality is coordinatewise **semantic equality under the same `nu`**;
it is not fresh instantiation or comparison of independently chosen type
arguments. The empty list gives false. This formula comes from the original
capture component, not an inferred residual or public row. The family's
declared arguments determine `point(q)`; operation-local `beta` stays in the
existential request packet and its `K,D`, not in that family tuple.

Wildcard, omitted and result-only annotations supply no capture grant.
Their admission component is false for this purpose; transported protection
and the separate result filter remain intact. No false admission test erases
a protected profile or means that the request cannot occur. Candidate
activity, typed incidence and ownership are still checked by the common
relation at the actual ordered-search configuration.

This compilation covers explicit finite concrete capture lists with the
existing typed correspondence premises. It does not interpret an arbitrary
open tail as permission, infer a capture list from a public row, or decide
broader annotation forms. Those forms remain outside this construction.
An explicit `[E]` admits that family's requests through the original slot;
it creates no operation arms, complete handler coverage or whole-family
subtraction. Open-tail syntax such as `[E 'a,F; 'e] A` is not normalized here:
its existence does not settle tail capture semantics or justify rejecting
that source form. The row algebra's union, intersection, difference and
conditional constructors are mathematical expressions, not source operators.
Unknown semantic endpoint equality remains an interpreted predicate unless
an applicable equality theorem supplies its realization.

**Admission equivalence.** At fixed `nu`, a request is admitted by the
original list exactly when its family head and invariant argument tuple
match one listed component. Finite disjunction enumerates precisely those
components; coordinate equality expresses their existing invariant test.
Thus replacing the original concrete-list test by the displayed formula
preserves its truth at each candidate, without changing event identity,
operation-local correspondence, source profile identity or capture authority.

### Mixed obligations remain whole blocks

The operational inventory may combine row memberships, named-point queries,
correlated capacity predicates and global endpoint predicates. Consider a
finite block of the form

```text
Xi = K(nu) and (forall u. Phi(nu,u))
           and B(named memberships,counts,global nu)
           and AND_j (g_j implies C_j).
```

`Phi` uses the admitted pointwise row grammar. `B` uses the counting-aware
row package's admitted Boolean combinations and correlated counts. Each
`g_j` is a finite operational guard with its original interpretation;
each `C_j` is a checking obligation at its existing binder scope. Retain all
row arguments and shared endpoint dependencies in these expressions rather
than suppressing them in the notation. Full effectful checks need not belong
to the pure positive closure of §8.

Split only the finite truth vector of guards, obtaining the equivalent
**whole-block** disjunction

```text
Xi = OR_t [ K(nu) and AND_(j:t_j=true) C_j
                  and (forall u. Phi(nu,u)) and B
                  and AND_j (g_j iff t_j) ].
```

Every branch uses one shared assignment `nu`, all original constraints,
and one complete guard valuation. This is Boolean case expansion of a
logical relation, not a source selector or a choice of a good execution
branch. False guards remove their implication consequent only in the
branch retaining their false equation. Inconsistent guard vectors denote
no solutions; they do not introduce new feasible type assignments.

**Proof.** A solution determines its finite guard vector and satisfies its
corresponding branch. Conversely a satisfying branch fixes each guard's
truth and retains exactly every consequent required by the original
implications. `K`, universal membership constraints and `B` are unchanged.
Both implications hold under the same endpoints and row assignments.
The expansion is not `forall u. OR_t ...`: its branch belongs to the entire
constraint derivation, including named queries, counts and checks.

### Positive closure inside the retained relation

Where a checking consequent has a proved decomposition into §8's pure
guarded obligations, saturate it with that closure and retain its initial
clauses. Its conditional solution-preservation theorem keeps each branch's
joint relation equal. Complete effectful Function inclusion, unnormalized
`Admit` and other unsupported checks remain separate original obligations.
Neither case expansion nor a finite fact graph proves their decomposition.

In particular, retain the generic-arm universal checking relation in `K`
or its original checking block. Do not select a different arm elaboration
for each guard vector or actual caller instance. Source roles, declared
bounds, consumer code and captured endpoints remain fixed. Operation-instance
§§2–3 and 7–8 distinguish hidden request witnesses, rigid arm openings and
solvable inference variables; the Boolean expansion does not exchange them.

A block such as `exists shared. forall kappa. exists body` keeps that scope
on both sides of the equivalence. Expansion takes place in the admitted
finite block at its existing scope; it is not permission to distribute or
exchange the source quantifiers. A witness already shared outside the arm
cannot be freshly chosen per guard cell, and `kappa` cannot be solved from
an actual Int-only caller domain.

### Eligible row projection must include guard dependencies

Before hiding a row variable, join every occurrence affected by that
variable: pointwise constraints, named memberships, count predicates,
operational guard equations and any admitted checking dependencies. The
counting-aware projection theorem applies only if the resulting whole block
satisfies its input and dependency conditions. Its symbolic residual retains
correlated witness counts rather than projecting each query independently.

In particular, a row to be hidden must not occur in a family-argument type,
named-point endpoint, global `K`, nonpointwise checking predicate or live
external `K,D` incidence that falls outside the projection grammar. A row
dependency cannot be split into independent membership and endpoint names
to evade this condition. If a checking consequence still depends on that
row outside the admitted grammar, stop that projection; retain its coordinate.
Whole returned-interface observations count among those external live
dependencies: retain their coordinates, or join their complete relation
before a projection whose premises cover it.

Guard memberships and counts do not disappear merely because their reached
checking obligation is positive. Join them before projection. Within an
eligible branch, apply the existing exact row image theorem, then retain
the finite union of projected whole branches. Existential projection
distributes over this finite union without moving its alternatives under
the pointwise request quantifier.

This gives exact logical projection in the declared fragment, not a choice
of whether source rows are finite or arbitrary subsets. Use the corresponding
projection theorem's domain/capacity premises for that interpretation.
Counts have no new source spelling or runtime type reflection.

Projection applies to a literal local block `exists Y. Xi(nu,retained)`
at its original binder position; `nu` supplies only parameters available
there. Never commute it across a later universal. For example,
`exists Y. forall kappa. Y={kappa}` cannot be eliminated as
`forall kappa. exists Y. Y={kappa}`. Named terms containing that inner
rigid binder make the proposed elimination outside this fragment unless
a quantifier-safe full dependency argument is supplied. Formula equality
does not replace the source requirement for one uniform arm template.

A mathematical discriminator is
`exists X. q1 in X and q2 not in X iff q1 != q2`.
Thus exact row elimination can require semantic endpoint disequality within
the invariant family tuple. This is neither polarity reversal nor a rigid
syntactic clash, and provides no assumption `kappa != Int`. It is an
emitted-grammar example, not an executed source or Oracle fixture.

### Fixed named-query all-row elimination

There is a stronger subcase requiring no counting or domain-capacity premise.
Fix `nu` at the correct local `exists X` binder after mixed guard splitting.
Let `N` list all named point **terms** `q_1,...,q_m` in `Phi`, `B` and guards;
their interpretations may coincide. Suppose all `r` row variables `X` are
hidden, and `Phi` is zero-preserving inclusion/equality or otherwise proved
true outside named points when every row input is zero. Let `B` contain only
named memberships and row-independent global predicates, including the
retained equations `g_j iff t_j` of this branch. Exclude counts,
nonemptiness, unnamed-point queries and absolute complement. No `X` occurs
in `K`, active checking consequences, endpoints or live dependencies outside
the joined block.

Enumerate the `2^(m*r)` bit arrays `b_iX`. Define

```text
Consistent_nu(b) = AND_i,j,X
  (Eq_nu(q_i,q_j) implies (b_iX iff b_jX)).

Residual = OR_b [ K and activeC and Consistent_nu(b)
                     and AND_i Phi(nu,q_i,b)
                     and B(nu,b) ].
```

At `u=q_i`, singleton tests use the same semantic point equalities and
row-membership inputs use `b_iX`; named membership occurrences in `B` and
the retained guard equations use their corresponding bits. Thus coincident
names cannot be assigned inconsistent row memberships.

**Proof.** Restrict any satisfying row assignment to `N_nu`, the interpreted
named points. Named memberships remain unchanged. Outside `N_nu`, all
row/singleton inputs are false, so the exterior premise makes `Phi` true.
The restricted assignment yields a consistent bit array satisfying the
residual. Conversely, from a residual array construct
`X={q_i(nu) | b_iX=true}` for each row. Consistency gives exactly the specified
memberships even when names coincide; the displayed instances establish
`Phi` on named points and the exterior premise establishes it elsewhere.
`B`, `K` and active checks are unchanged, proving both directions.

This works for finite rows and arbitrary subsets alike. With no named terms,
all rows are empty and the exterior premise covers the whole universe.
Apply the corollary to each whole guard branch without changing its binder
position. It closes row realizability at fixed `nu` for this named-query
fragment without invoking counting algebra. Semantic endpoint equality and
active checking predicates remain unsolved. Exact semantic elimination is
not uniform syntactic template inference, and supplies no permission to
cross a later rigid checking scope or choose captured witnesses per cell.

### Guard replacement preserves the generated query machine

Let an original query guard and its normalized formula be equivalent at
every assignment admitted by the retained joint block. Keep the same
instruction successors, packet fields, native delimiters and current-state
threading. At any such fixed assignment, replacing that guard preserves
the enabled transitions. Apply this to each concrete-list admission query.
Mixed-block expansion and row projection normalize the joint certificate
relation; they are not machine-guard replacement or selection of one branch
program.

Stage induction then preserves the generated reachability relation `R`:
initialization and successors have identical truth at every retained
assignment. With unchanged `Base`, designated faults and complete output
alternatives, the certificate formulas `S` and joint observations `U` are
pointwise identical as well. After joint reachability and complete
observations are joined, eligible certificate projection compares extendible retained
assignments; it does not supply a guard value at an arbitrary discarded
row witness without its original joint extension.

The inventory stays finite: original concrete lists, guard vectors, named
queries and counting thresholds are finite input data, and the existing
projection/closure constructions produce finite formulas. Their products
may grow. This section asserts no practical resource bound or effective
semantic endpoint satisfiability algorithm. Boolean cells and branch vectors
are not independently realizable endpoints.

### Exact advance and remaining realization

This construction normalizes original finite concrete capture admission and
shows how guarded positive checks coexist with pointwise and counting-aware
row constraints in one preserved block. It prevents both public-row capture
grants and independently solved guard/check marginals. The operational
machine continues to select before checking compatibility, with all actual
successors covered by the existing source simulation.

Its ingredients are ordinary-computation §4, typed-boundary §6, the open-row
and counting-aware projection packages, and operation-instance §§2–3, 7–8.
Admission follows the selected Yulang source rules. The mixed-block
normalization and composition with guarded closure are new successor proof
constructions, not Simple-sub-original routing or extrusion theorems.

Still required: realization of semantic tuple equality at the actual emitted
endpoints, normalization of every admitted guard/query form, complete
checking decompositions and the source acceptance/principal-denotation
bridge. Broader capture syntax, external live dependencies and general
Function contracts remain governed by their existing unresolved gates.
No source capability is narrowed and no lifecycle or implementation approval
follows from this conditional package.
