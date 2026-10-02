# Source realization and finite symbolic ownership

Date: 2026-10-02
Status: Draft; conditional source-realization package; no implementation authority
Scope: monomorphic ownership basis, operational kernel, selected-fault reflection
Approved-by: none
Drafted-by: primary with bounded control/heap and symbolic-basis architect inputs
Reviewed-by: compiler_referee and spec_auditor, independent package reviews, 2026-10-02; no findings within the declared conditional envelope
Supersedes: none

## 1. What this package establishes

The finite safety-certificate theorem in
`2026-10-02-finite-abstract-safety-presentation.md` takes finite graph and
predicate inputs. This package constructs the predicate input from a finite
monomorphic descriptor graph, identifies the operational kernel that can be
lowered to that heap machine, and derives universal error reflection for
selected-arm incompatibility. It does not assume finitely many ground types
or bounded execution depth.

Two remaining source definitions prevent an unconditional source-realization
theorem: inductive callback-boundary relevance/visibility, and effective
general value adaptation. Open-client interaction also remains separate.
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
| `B` | explicit callback-boundary contract descriptors and their receiver/callback slot sites |
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

The monomorphic restriction is precise: executing a descriptor again may
allocate fresh runtime objects, but does not generate a new type endpoint,
type term, predicate schema, or type-level substitution. Runtime type
inspection/decomposition that recursively creates new type queries is not
included by calling its result a scalar. Generalization and polymorphic
instantiation are still later obligations.

## 3. Constructing the symbolic basis

Define finite symbolic predicate names, with their intended meanings under
`ν`, as follows:

```text
PΩ = { Source_j                    | j ∈ J₀ }
   ∪ { Query_s(t₁,...,t_a_s)       | s ∈ Σ, (t₁,...,t_a_s) ∈ T^(a_s) }
   ∪ { Compat_o,h                  | o ∈ O, h ∈ H }
   ∪ { Admit_b,o                   | b ∈ B, o ∈ O }
```

`Source_j` contains the original static constraints; the query product
enumerates all endpoint combinations of each supplied primitive/adaptation
schema, including combinations reached through abstract collisions.
`Compat_o,h` means the complete `OpCompat` relation of those
instances, including invariant family arguments and payload/response checks.
`Admit_b,o` means admission by the explicit concrete typed contract. For a
wildcard/absent capture contract it is false; family equality alone does not
make it true. The Cartesian inventory lists possible queries, not obligations
to enforce all of them. A compatibility predicate becomes an obligation only
at an actually selected arm in the concrete machine, or at a selected state
of the declared conservative abstract machine.

Each name references its symbolic endpoints in `T`. It can stand for a finite
formula emitted by its descriptor; taking those finitely many component
atoms instead gives the same finiteness result. This notation does not claim
that underlying type equality/subtyping is decidable, or that a solver may
treat related predicate valuations as independent concrete type assignments.
Boolean cells lacking a realizing `ν` have empty concrete interpretation.

The name-level bound is

```text
|PΩ| ≤ |J₀| + Σ_{s∈Σ}|T|^(a_s) + |O||H| + |B||O|.
```

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
from `J₀`. Lookup reads its one static operation/value descriptor. Closure,
thunk, cell and continuation construction allocate runtime identities and
copy symbolic references. Call, adaptation code and `Force` reuse their
descriptors; the latter never opens a fresh operation instance. Request
construction uses some `o∈O`; selected-arm checking uses `(o,h)∈O×H`;
concrete-contract admission uses `(b,o)∈B×O`. Every remaining supplied query
uses a schema in `Σ` with arguments from `T`, hence occurs in its Cartesian
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
Handler(activation, owner, site, env, parent)
Suffix(site, env, next)
ReenterCall(template, env, suffix, next)
ReenterHandler(template, env, suffix, next)
Request(opTemplate, payload, origin, event, dependencies, suffix)
Dependency(predicateTemplate, view, next)
Search(request, candidate, crossed, phase)
Adapter(boundaryTemplate, value, phase, next)
```

Field count is fixed per tag; a larger source tuple has a statically fixed
tag or linked spine. Identities point to their fresh allocation records.
The roots hold the current control/environment, live mutable store, active
activation head, continuation, and pending search. Saved suffixes retain
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
| closure application | enter body using the closure environment and caller's live store/active head; push the fresh invocation and its return suffix |
| invocation suspension / resume | save the source invocation wrapper; execute its re-entry around the suffix using the supplied live state |
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

`2026-10-02-typed-source-owner-realization.md` supplies an explicit candidate
for that ownership protocol: saved executable owner spans resolve to exact
live occurrences or fresh execution occurrences, and owned/borrowed delimiters
govern completion. It preserves original value/evidence ownership references.
Its theorem covers the decorated operational kernel, conditional on supplied
source profiles/maps, rather than deriving arbitrary raw-source elaboration.

The kernel table is a compilation schema conditional on the finite source
descriptors and wrapper transitions. It does not yet implement the unspecified
visibility and adaptation primitives. In particular, a `DerivationLink` graph
could store boundary evidence but is not proved to answer source relevance.

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
transport/query candidate. It does not select general `≈`, derive shapes and
profiles from raw source, or prove re-entry ownership and arbitrary-client
closure.

The constructive results have the following boundary:

1. **Visibility realization.** Typed-boundary §6 now supplies common typed
   transport, receiving ownership and exact-handler incidence, with an
   effective graph query for supplied finite signature profiles/maps. Its
   composition and lifetime package is reviewed. Derive those profiles/maps
   from source typing and establish exact re-entry ownership to instantiate
   it for all source rules. Active-frame walking alone does not prove callback
   relevance. Preserve concrete-contract visibility uniformly through
   direct/Force exposure, nesting, escape and shallow re-entry. Do not add
   boundary exclusions merely to make the traversal executable.
2. **Adaptation realization.** The coupled core's thunk/function equations
   leave boundary equivalence `≈`, admissible payload conversions and other
   non-thunk conversions unspecified. Supply finite recursive descriptors
   and a source-preservation proof, including force positions and return
   lineage. Calling `Adapt` an instruction does not satisfy this premise.
3. **Uniform future interactions.** The basis theorem applies after fixing
   finite `Ω`, including linked client bodies. For each such client it
   covers arbitrarily many calls/resumes to those bodies. This is
   `∀finite client L. ∃finite presentation P(C linked with L)` under the
   same monomorphic/realization premises. It does not establish
   `∃finite P(C). ∀admissible L` for a reusable component. Arbitrary new
   client operation instances or opaque latent callback bodies are not in
   `O`; collecting their descriptors requires a modular interaction theorem,
   not a claim that runtime allocation is the only source of growth.

These gaps localize the remaining source theorem. None proves class 3 or
authorizes narrowing the supported source envelope. The fixed-input result
is class 1 for this abstract judgment; cyclic execution is covered without
unfolding, but an exact regular quotient is not claimed. The accepted
Milestone-2 embedding and generic principal-certificate algebra need no new
review unless these definitions change their premises. Generalization,
fresh instantiation, intrusion, the next feasibility gate and implementation
remain downstream of a complete source presentation and acceptance bridge.
