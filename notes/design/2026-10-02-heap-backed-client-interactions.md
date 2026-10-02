# Heap-backed future interactions and the remaining interface-closure gate

Date: 2026-10-02
Status: Draft; research construction; no implementation authority
Scope: finite driver/carrier for a template-closed command interface; source encapsulation remains open
Approved-by: none for a successor abstraction or acceptance choice
Drafted-by: primary with bounded architect construction
Reviewed-by: compiler_referee and spec_auditor; M3 command-level package review, no findings
Supersedes: no source authority or finite-register theorem

## 1. Move retained handles out of the register bound

The request-register quotient requires boundedly many retained points.
Arbitrary clients can instead retain many callable values, computations,
cells and raw continuations, then reuse them in a different order. There
is no source theorem reducing that memory to the quotient's registers.

The construction below puts retained **typed view packets** in a heap-backed
knowledge pool. A finite driver chooses interactions using that pool.
The pool can grow without bound before abstraction; it does not forget an
export merely because its first call or maker activation has ended. Finite
allocation abstraction then produces a finite conservative carrier.

Prior art: Nguyen, Gilray, Tobin-Hochstadt and Van Horn,
[Soft Contract Verification for Higher-Order Stateful Programs](https://arxiv.org/pdf/1711.03620),
§§3.2, 3.4–3.5, models unknown code using retained escaped values and repeated
interaction, with an operational approximation proof. Those sections were
consulted, not the full paper. They do not prove Yulang's typed boundary,
shallow-handler or invariant-family rules. Our packet/context obligations
below are separate. This is other primary-research prior art plus a new
successor construction, not a Simple-sub-original rule.

The result is command-level coverage for a finite **template-closed
signature**, uniformly over client command sequences and memory sizes.
It constructs driver control and a heap carrier; it does not establish
that the public source interface supplies such a signature for all clients.

## 2. Input signature and the exact closure premise

Supply a finite signature `S` with:

- resolved value/computation/callable interface nodes `T`;
- complete operation-instance templates, including local substitutions,
  payload/response/latent interfaces and all their symbolic dependencies;
- original source boundary, receipt and typed-path templates;
- receiver/handler/pending-search/saved-continuation record layouts;
- finitely many command schemas and their finite-control kernel routines;
- a finite scalar abstraction with sound primitive tables;
- a finite symbolic predicate inventory over one unchanged assignment `nu`.

An instance of a record template can contain fresh runtime identities and
heap links. It does not allocate new type endpoints, declaration maps,
source profile shapes or predicate schemas. Unbounded lists use links.
This is the existing monomorphic descriptor discipline. Generalization and
fresh type instantiation are not performed by inventing runtime identities.

Call a client command execution *template-closed* when every packet, context
frame, source contract and command it exposes or stores uses those templates
and predicate schemas. Its private control locations, number of values,
environments, stack depth and repeated interactions need not be bounded.
The client is not supplied as a finite linked program to the construction.
Commands with hidden infinite routines or undecided source elaboration do
not qualify as finite kernel routines by naming them `Invoke` or `Visible`.

This premise is stronger than having finitely many public root types. The
source-realization package's finite `Omega` for a linked client is also
different: here `S` must cover the entire chosen class of client commands
without adding that client's code sites. No source envelope is narrowed by
stating this theorem's premise.

## 3. One pool of views and a generated driver

A pool member is a reference to a complete packet

```text
Packet = (value, interface-position, profile-root, K-root, D-root, lineage)
PoolEntry = (packet-reference, next)
ForeignFrame = (action-kind, interface-node, environment-list, parent)
```

These are bounded-field records; long environments, profile graphs and
dependency sets use links. There is one joint ledger under `nu`. The pool
does not contain independently chosen type witnesses for each read.
Two aliases of one underlying closure may have different packet references.
Keeping a value pointer alone, or unioning their profiles into one invented
contract, is not this construction.

Generate action cases from `S`:

| Action case | Required behavior |
|---|---|
| retain/copy/project a known view | existing typed transport, original witnesses retained |
| construct data or latent code | represented constructors; computation construction is inert |
| invoke an available callable | pass the whole carrier to its actual complete `ExecuteCallable` |
| force an available computation | execute its designated outer port only |
| resume an available raw continuation | supply a corresponding response, current state and the same operation instance |
| access an exposed cell | read/write through its represented typed view, preserving alias constraints |
| execute a represented handler/control action | actual ordered frames; outside selection/guards/arms; primitive shallow resume |
| return/control-transfer | retain newly exposed packets and the corresponding saved context |

Packet operands are selected by walking the pool/environment lists. The
driver may repeat an action, retain a result and choose any later available
packet. Recursive control uses a loop, not copies of the driver's code.
Imported closures/computations hold a driver entry and references to their
captured pool/context. A component-produced closure or continuation keeps
its actual code/suffix; invoking it does not replace that code with the driver.

The pool records values available to client interaction, not every address
in the component heap. It cannot project a closure's private environment
or mutate a private cell merely because the compiler can represent it.
Explicitly exposed fields/cells and values returned or passed to the client
become available through the same typed-flow rule. Unknown client-private
allocations have their own record kinds/sites; sharing an already exported
address occurs by retaining its packet, not by guessing a private pointer.

Record the client return/control context in heap frames. Erasing a private
program counter to an action kind must not erase ordered handler frames,
owners, suspended versus executing views or exact expiry dependencies.
The driver is entered at represented client-control points, including later
entry to a retained imported closure. It does not spontaneously execute
client callbacks during component-only control. It may choose more client
sequences than one concrete client; these are analysis alternatives, not
additional source executions of that client.

### Command-level coverage

First use fresh concrete driver addresses and exact scalar values. Relate
a template-closed client command state to a driver state containing each of
its available packets, the same live store/context and corresponding heap
environment/control records. The driver can retain additional **available**
client values, but has no right to extract component-private bindings.

For each client command, choose its action schema and walk to its operands.
The kernel routine then performs the same operation with the same packet,
current context and `nu`. Allocation extends the address correspondence;
copy/transport retains the packet's dependencies. Store updates change the
same current locations. A result/request transfer records the same newly
available packet or continuation. A call suspends the driver's continuation
in a frame and runs the actual receiver entry; a callback can later re-enter
the driver through that saved control. Returning resumes the saved context.

Induction covers every finite command prefix, including retaining a handle
across many unrelated calls and invoking it repeatedly. A private client
branch is represented by choosing its realized next action; private state
needed by later commands remains in client heap records. Diverging private
steps with no visible interaction can stutter. This is a coverage theorem
for the represented command interface, not a proof that arbitrary source
clients normalize to those commands. Each command's source refinement and
the signature-closure premise remain necessary.

## 4. Construct the finite carrier

Let `Kinds(S)` be the finite record layouts and `Tplus` the finite template
indices, with one fallback index for administrative lists. Generate foreign
allocation sites `(kind,template-index)` and union them with the component's
finite sites. Let their finite set be `A`. Runtime identities are referenced
by records/addresses, not embedded as unbounded scalar numbers.

For finite control/action labels `L`, scalar classes `D0`, bounded record
arity, and registers holding addresses or finite scalar classes, enumerate
the finite record set `Rec`. Put

```text
Store = A -> powerset(Rec)
Q = driver/component control x Store x finite address/scalar registers.
```

Record alternatives are kept as complete tuples. Linked pool, environment,
activation and dependency lists can have cycles; no unfolding is required.
Weak insertion on allocation/writes and enumeration on reads are exactly
the existing finite-heap construction. Pointer collisions allow uncertainty;
they cannot establish that two concrete events, owners or cells are equal.
Known equality carried by a copy is not permission to merge other aliases.

This constructs finite `A`, `Rec` and `Q` from `S` and component code without
a bound on the client's number of retained handles. If `a=|A|`, `r=|Rec|`,
and the remaining finite control/register factor is `c`, then
`|Q| <= c 2^(a r)`. The size can be enormous; no practical threshold or
resource policy is selected here.

Compose command coverage with local weak-store simulation: map each fresh
driver record to its generated allocation site; actual reads and updates
have representative abstract choices. Induction yields an abstract path
for every covered concrete prefix. This is one-way coverage, not an exact
quotient of aliasing or callback selection.

### Visibility and fault reflection are not existential shortcuts

Typed packets retain original contracts and source-derived observation
paths. Pool membership never creates a boundary, receipt or capture grant.
Receiver/handler activity is queried in the current represented context;
an expired maker's stored packet is not an active authority.

When abstraction leaves identity/path/activity uncertain, the command
abstraction must retain all concrete outcomes, including forwarding and
absence of a grant. Choosing only the capturing branch is unsound. Extra
abstract paths are possible; they do not redefine source visibility.
Likewise, uncertainty about a selected operation's compatibility cannot
filter that selection or turn it into forwarding.

Applying the principal safety-certificate theorem additionally needs its
universal error-reflection premise: every represented concrete designated
failure makes the reached abstract state bad. If a state summarizes several
packets, finding one compatible member is insufficient to declare it safe.
The finite symbolic predicate inventory and sound command/fault routines
must account for all alternatives. Driver construction alone does not
discharge these source typing premises or effective `OpCompat` generation.

## 5. The remaining source obstruction is template closure

Arbitrary client code can retain many values; the heap construction addresses
that memory issue. It does **not** show that arbitrary client packets are
instances of the supplied finite `S`.

The operation-instance package supplies concrete evidence: parameterless
`assertion::assert_eq` has independent value and callback-effect parameters.
The same family point can therefore carry different payload/latent interfaces.
The public family row does not determine those operation-local maps. Their
dependence on stored values, continuations and output views cannot be erased
or independently reconstructed on later reads. The register quotient's
unary family-point colors do not encode them automatically.

Clients can also introduce source callback contracts and original typed
positions absent from the component's own descriptor graph. Such a position
can remain relevant after storing a view or returning a latent value. A
generic foreign-frame tag with no original profile/ownership correspondence
does not suffice merely because that client's code is opaque.

The next source theorem must establish **interface encapsulation**: which
client-private structure can be represented by typed interface parameters,
and how every externally relevant operation-local map, boundary profile,
alias and `K,D` dependency is retained in their symbolic instances. It must
derive a finite signature or a finite parametric/regular presentation closed
under those interactions. Supplying an opaque "compatible imported value"
or an unbounded hidden type term is not such a construction.

This is a precise applicability obstruction, not proof that finite
presentations do not exist. No class-3 impossibility is established.
Finite but unbounded template-closed carriers belong to the first category;
their linked representations also cover unbounded concrete memory without
expanding it as a syntax tree. Their conservative approximation is not a
proof of an exact regular quotient.

## 6. What can be reused, and what cannot be declared complete

Once the source closure/refinement and fault premises are proved, the
existing principal-certificate construction applies to the generated finite
graph under its fixed symbolic basis. Its principality is relative to that
abstract judgment. Spurious alias/visibility paths may exclude concrete
safe behavior; the driver theorem does not approve that loss of source
acceptance, call such behavior ill typed, or prove final Oracle equivalence.

The result advances beyond both a fixed linked-client program and a bounded
register interface: arbitrary repetition, saved handles and client control
size fit one generated command driver for `S`. Whole-source inference still
needs the finite/parametric signature, source checking and acceptance bridge.
Generalization, fresh instantiation, SCC intrusion, the later method/role
gate and compiler implementation remain open.
