# Original source receiver construction and the remaining intrusion correspondence

WHOLE-PRINCIPALITY-SOURCE-20261026/r2. Author: `/root/principality_source_r2`.
Baseline: `45d307a0aa01722b5aac289b07d71953630abca7`, branch `yulang3`.
Status: checked source-side construction; original principality OPEN.
Independent review: not supplied by this author.

## 1. Original target and result

The unchanged parent is [source preservation §§1, 3, 5](2026-10-13-intrusion-source-preservation-proof.md),
with the [immutable-birth-level qualification correction](../design/2026-10-24-birth-level-scc-intrusion.md)
and the [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md).
For every supported original program and lawful finite history, the actual
qualifying extrusion pairs must retain original source conclusions and required
principal coverage. Generalization, monomorphic recursion, all lawful uses,
complete Call/effects, original lexical/type/event scopes, fixed providers, one
joint witness and the future family are retained. Internal solver assignments
may change. The target is not preservation of every arbitrary old valuation.

This packet constructs the original source side of the canonical nonempty
replay example in Lean: the complete raw source, its recursive binding role,
both complete App rules, the actual ordered field telescope, an original
callee-Name derivation from a current installed binding, and the current
returned-callee readout through arbitrary preceding source frames. These facts
do not need a presumed successful source judgment for that Name.

The construction does **not** establish a nonempty *qualifying* occurrence.
Its exact obstruction is the missing constructor correspondence from the
original, source-indexed residual boundary to the actual native extrusion
occurrence's receiving Value. The source receiver is available before erasure;
the actual occurrence association is not obtained merely by erasing its source
checking certificate. The packet establishes neither a source-qualified
counterexample nor a joint principal strategy. No new fiber predicate,
principal package, source domain, instance ordering or success axiom is added.

## 2. Authentic original source, not a synthetic constraint store

The fixed source is the one in [BRD §2](2026-10-24-birth-level-extrusion-redundancy.md),
[AR §§1–4](2026-10-24-actual-replay-receiving-diagram.md), and
[RZ §§1–5](2026-10-24-concrete-extrusion-source-realization.md):

```text
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first = h x, next = f {a = y}}
  in f
in top
```

`SourcePrincipalTransport.program` builds this program using the existing
`OriginalSource.Source` constructors. Names are top=0, h=1, f=2, x=3, y=4;
occurrence sites are independent identifiers. The two App sites are 16 and 20.
Their callee Name sites are respectively 17 and 21. The recursive group site
is 6 and f's binding site is 7.

The existing source generator computes the body context as
`[y formal, x formal, f internal(component=6), h formal]`. The `h` formal is
captured from the outer lambda, while recursive `f` still uses its single
monomorphic binding. It is not a published instance at its recursive call.
The final, post-publication `in f` remains part of the complete program.

`program_call_owners` checks the output of the actual complete builder:
three closure owners at sites 2, 8, 11, followed by the two App owners
`application 16 bodyContext 17 18` and
`application 20 bodyContext 21 22`. This runs through the original
initializer, publication, Shared, lambda and execution wrappers; those wrappers
are not deleted from the source tree to obtain the equation.

Both App equations retain descriptor formation, whole inert-argument
compatibility, the complete Call certificate, source Call incidence, callable
image, the value check on the *returned callee*, and the computation check on
the full callable image. The h call additionally receives the original
singleton-formal clause because the generator's actual source-use test holds.
The recursive f call does not receive that clause. No effect port or complete
Call family is substituted by a scalar arrow inequality.

The generated first record field has the exact children

```text
sourceRules(bodyContext, h x)
executionE(16, returnRebind,
  sourceRules(bodyContext, next = f {a = y}))
```

This is the original suspended suffix that AR1 consumes. It does not assert
that h returns, execute the later f call early, or discard pending operations.

## 3. Source information actually constructed before erasure

### 3.1 The current Name derivation

`h_name_source_derivation` constructs

```text
SourceJudgment (foldedNameKernel inputs readout original 17 1)
  environment bodyContext hName
```

from the independently given current data: decoding the environment yields
`state`; the binding for h names an allocated address; and that address stores
the one tuple consisting of the descriptor, value and provider root of the
Name's final source endpoint. It constructs both original local Name atoms and
the `Judgment.rule` directly. No Name typing, generated solution, full App
certificate, `LocalLaws`, or inference success is an input. The original local
ordinary-formal meaning is the existing `foldedNameKernel` clause, not a new
definition of source legality. All its other source clauses remain unchanged.

This is a local source derivation in the actual recursive context, not a
source judgment for the entire program. The independent original current-world
and complete Function/Call evidence are not manufactured by the raw installed
tuple. RZ's genuine `h : H*` still has its original semantic premises.

### 3.2 The returned-callee endpoint

The decoder's canonical registry gives

```text
h App subject = (Name h at 17, returnedValue)
f App subject = (Name f at 21, returnedValue).
```

`source_owners_after_all_frames` and `source_subjects_after_all_frames` prove
these equations after **any** list of original logical, Shared and runtime
frames. In particular descriptions, later invocations, Return/rebind, response
and one-shot updates cannot replace the static source owner. This uses the
existing complete decoder and its actual preservation theorem, with the
registry constructed from the full concrete source above.

There is a real distinction between the Name's `finalRoot` and the App's
`returnedValue` port. Raw immutable-binding lookup alone does not prove that
the App has already received the callee's return. The `hReturn` constructor
therefore records a supplied actual Return's value/provider pair at exactly
`(17, returnedValue)`. `h_return_supplies_current_receiver` proves that the
existing runtime decoder reads that same value and provider at h's registered
subject, with the supplied actual after-configuration and history. It works
after every preceding frame list and uses the supplied original Return binder;
it does not invent an event site for the source Call certificate.

This last theorem proves a **data/readout equation**. It does not assert
`Admitted` for the supplied Return, derive a Return from divergence, or supply
an executed receipt. The same actual Return and its original admissibility are
the source inputs used in AR1/RZ; no new provider, source owner or event witness
is selected in the readout construction.

## 4. Consume the existing AR/RZ result at its actual native event

The native empty-start history remains BRD/AR's history. H has level 1;
o, B, Y, J, R have level 2. With `A(Y)=Record(a:Y)` and
`K=Function(Y,Record(first:J,next:R))`, its relevant records are

```text
r_h: H <= Function(B,J)                         direct source call h x
u:   B <= C                                    its positive extrusion link
r_r: o <= Function(A(Y),R)                      direct recursive f call
r_c: Function(B,K) <= o                         recursive completion
v:   A(Y) <= B                                  Argument/Swap(Replay(r_c,r_r))
p:   A(Y) <= C                                  Replay(lower=v, upper=u)
z:   fresh T for (Y,+,target=1)                  positive Record field descent
```

The first h demand creates C/B and D/J with a fresh operation-local memo.
The direct recursive f demand creates no copy. The later first comparison
`A(Y) <= C` is the nonempty occurrence: a separate empty memo creates T/Y,
the link `Y <= T`, an empty selected lower list and rewritten `A(T) <= C`.
This packet did not rerun Rust or Scala; it uses the established exact native
derivation and separately reads the current Rust constructors.

AR1/AR2 already supply the important semantic middle. After the actual y-entry
returns i, the recursive call builds `a' = Record(a:i)`, binds **fresh** x',
allocates the next inner closure, and retains its capture. At any compatible
future invocation of that closure, Name x' supplies the same a' to the original
h. The old x is not rewritten. Pending operations remain suspended families;
the future invocation is not inferred merely from closure allocation.

RZ1–RZ4 use those actual constructor projections to give the specific fresh
T/Y event a local checking packet. Both scalar field views are the same
existing I; the parent link is identity checking, the selected list is actually
empty, and the rewritten record check uses the same field/provider tuple.
Their common complete dependent source frame remains AR's original one.
RZ5 proves that **this source packet's** receiving index is H. It does not
select a receiver by inspecting a type row.

The new Lean construction exposes the actual static h owner and its current
returned-callee readout within the original source tree. Thus there is no need
to pretend that the source receiver is absent from the source telescope or
that AR/RZ still lack their concrete whole middle. It also prevents a mistaken
proof from treating h's final synthesis port as the App's returned-callee port.

However, RZ's accepted monomorphic instance and its I view do not quantify over
every original source typing or all independently generalized descriptions.
Nor is RZ5 an identification of the authoritative occurrence field. RZ states
exactly the remaining equation:

```text
actualOccurrence(z).receiver
  = receiving_index(source_frame(Z_real)).
```

For the given packet the right side is H. The left side is not a source rule
binder or a field of `OriginalSourceEnvironment.CallOwner`. `z` is created by
static bound replay, not by a new source App. No original Lean constructor in
the inspected source-generation/environment modules supplies this equality.

## 5. Precise obstruction at the native owner

The current code makes the distinction observable.

| Owner | Constructed fact | Missing conclusion |
| --- | --- | --- |
| `candidate_value_graph::retain_source` | Direct App association uses its definition-root owner and the resolved callee Value. Nested initializers get their own source owner. | It does not introduce a new source App for delayed z. |
| `candidate_context_begin_replay` | Ordered lower/upper dependencies, both bound keys, and the union of the two authentic source sets are retained. | A union is not the selected residual receiving incidence. |
| `candidate_function_port_admit` | Argument ports retain `Swap`; result ports retain `Preserve`; source support remains. | The consumed whole-Function `ScopedDemand` is set to `None` at the child. |
| `bound_scoped_payload_for(..., ExtrusionLink)` | A Value parent link is a distinct scalar boundary, with existing dependency evidence. | The method returns default scoped flow, so `original_call` cannot be read from this link. |
| `candidate_extrude` / `retain_extrusion_parent` | Exact fresh parent/copy, polarity, target, comparison, operation and support are stored before selected-bound traversal. | `Parent` has no authenticated projection from the source residual certificate to one actual receiving Value. |
| `retain_extrusion_parent`, `finish_candidate_extrusion`, `recapture_candidate_extrusion` | The consumer tests `any(qualifies(event))` over the retained source set. | This is not proved equivalent to the authoritative actual occurrence's qualification. |

For this example, definition-root F and formal H have births 2 and 1. The h
seed `(F,H)` is nonqualifying; the recursive seed `(F,F)` qualifies. The latter
has no direct copy. Its swapped argument evidence can nevertheless enter p's
support together with h's boundary. The current any-source consumer can then
qualify the pair using `(F,F)`, whereas the concrete RZ source packet's H
boundary is cross-birth. This is a **correspondence obligation**, not a new
source-qualified failure: the actual z association has not been independently
authenticated, and no lost original source typing/principal instance is shown.

No claim here depends on the superseded cross-level F/G SCC counterexample.
Nor does the example justify the false shortcut that every descendant of a
same-birth Call is copy-free. BRD's actual T/Y generation already refutes that
native shortcut. The original graph, birth values and all support evidence
remain unchanged.

The obstruction is not simply a missing numeric ID. The original source
checking composition is indexed by the complete environment/site/context and
its dependent evidence. The native replay knows a common scalar row B.
AR/RZ construct the appropriate source middle for this particular event family,
but authenticating that construction as the occurrence producer's same middle
requires the simultaneous source/native constructor. Reading another source
set element, assigning H to a new selector, or treating erasure as injective
would add the missing conclusion as an assumption.

## 6. Smallest next construction and natural retention

The next owner is the **original source/native extrusion occurrence
constructor**, starting from this exact fresh `z` rather than an arbitrary
store or an abstract quotient. The concrete target is to construct, from the
original seed/port/bound/replay evidence, the authentication that the source
boundary in RZ's packet is the boundary of that same native occurrence ID,
memo key, polarity, target and retained pair. Only then can its receiving
projection be used in the birth-level query.

The existing source trace family can supply the source half *before erasure*:
the registered h owner, actual supplied callee Return, original h provider,
the AR fresh-binding/capture/future Name chain, and RZ's local field checking.
It cannot supply the missing identification by choosing one successful runtime
trace. Static inference z stands for the original dependent family, including
pending prefixes and future invocations.

The smallest natural evidence to retain is a handle to the original
**signed source boundary and its whole-telescope action**, alongside the
already retained creation/dependency records. For this case it originates at
h's App demand, follows its argument boundary u, composes the actual recursive
Argument/Swap evidence v on the correct side, and follows Record field a into
z. It should be constructed at the original source demand/bound owner and
transported by the same operations. A bare chosen receiver ID or a second
source-set heuristic would not provide that evidence.

Much of the necessary native route already exists in `Derived`, `FunctionPort`,
`Replay`, the bound keys, and the extrusion creation records. A proof may show
that these existing records expose the original boundary without any additional
runtime field. This packet does not claim information was erased from the
entire DAG. If the source boundary was not retained by its natural producer,
the small evidence handle is the proposed retention point; compiler edits and
any semantics decision belong to the primary, outside this proof lease.

Even an authenticated H result would make this occurrence **nonqualifying**.
It would resolve a concrete source/native attribution seam, not establish
source-scoped principal coverage. A genuinely nonempty qualifying case still
needs the source-derived joint strategy across publication/use and the original
`instanceOf` relation. `SimpleSubGeneralizationSoundness` and
`OriginalPrincipality` retain their existing finite algebraic meanings; this
packet does not silently identify them with that semantic ordering.

## 7. Lean declarations and exact application boundary

Namespace: `YulangClosure.SourcePrincipalTransport`.

| Authored theorem | Inputs and exact conclusion |
| --- | --- |
| `program_call_owners` | No hypotheses; exact five-owner list computed from the complete original raw program. |
| `actual_body_bindings` | No hypotheses; h resolves to its captured ordinary formal and f to the internal recursive component 6. |
| `recursive_name_is_monomorphic` | No hypotheses; complete generated recursive Name rule, without a published-instance frame. |
| `h_call_complete_rule` | No hypotheses; exact original h App tree with all six local source atoms and both checking goals. |
| `recursive_call_complete_rule` | No hypotheses; exact original recursive App tree with all five local source atoms and both checking goals. |
| `recursive_field_retains_h_suffix` | No hypotheses; the actual ordered record-field tree places the second field below the h Call's execution Return/rebind binder. |
| `h_name_source_derivation` | Arbitrary original semantic sorts/readout/kernel/environment, decoded current state, allocated h binding and one exact installed descriptor/value/provider tuple; constructs the original local h Name judgment in the full recursive body context. |
| `source_owners_after_all_frames` | Arbitrary original root/readout and finite list of all frame classes; both concrete App owners remain registered. |
| `source_subjects_after_all_frames` | Same inputs; both original returned-callee source endpoints are retained. |
| `h_return_supplies_current_receiver` | Same arbitrary preceding frames, a supplied Return binder, value/provider/observation and after-state; constructs the h owner/current value/provider/current-history readout equation. No Return admission or native occurrence association is asserted. |

The original language is not narrowed by constructing this instance. Other
source constructors, selected-bound families, negative extrusion, fresh memo
reuse, independent descriptions and the original whole-language theorem remain
outside the checked conclusion. In particular the all-frame equations are not
one principal strategy over all future source families.

## 8. Actual checking and complete axiom census

The isolated project is
`/workspace/scratch/e3678bef96db/principality-source-r2`; it copied source/config
inputs and built its own cache. No shared `.lake`, root import, compiler,
configuration, Git, or scheduling record was changed. Installed read-only Lake:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.

Actual versions, both exit 0:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu,
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Nine frozen dependencies were built serially, one module at a time, followed by
the focused module. All Lean invocations used `-j1 -M1024`,
`LEAN_NUM_THREADS=1`, and a 120-second subprocess timeout. Dependency sequence
completed in 40.7 seconds. The final focused build passed without warnings.
No default or full-project build was requested.

The complete originating-module audit enumerated **114 declarations: 41
definitions and 73 theorems**, including private and generated equation/splitter
helpers outside this module's public namespace. It printed every declaration's
complete type and complete axiom list and required all ten authored roots.
The 73 theorem axiom sets are: 35 empty, 19 exactly `{propext}`, and 19 exactly
`{propext, Classical.choice, Quot.sound}`. Every authored theorem except
`actual_body_bindings` uses the latter standard set; that theorem has an empty
set. No project axiom, `sorryAx`, native-evaluation assumption or checker bypass
occurs. The only source scan match in the nine-file imported dependency cone
was a comment saying no coinduction axiom was supplied.

The initial local build failed because the well-founded source builder needed
its actual equation lemmas unfolded, and one runtime proof unfolded before
rewriting the registered subject. The repaired build passed. A later source
Name addition and supplied-binder refinement also passed. The first scratch
audit failed due to an unannotated mutable counter inferred as MessageData;
explicit `Nat`/`String` annotations repaired it. All failures are retained in
the scratch evidence; none is a mathematical counterexample. An initial Lake
`-j` scheduler option was unsupported and launched no Lean check; subsequent
dependency builds were explicitly serialized. Total Lean compilation/audit
invocations: 14, within the 20-check allowance.

Full exact types and axiom results are retained in `evidence/audit.log`, with
machine-readable declaration census in `evidence/census.json`. The audit is
`AuditSourcePrincipalTransport.lean`. Their hashes and the complete direct input
hashes are in the accompanying handoff. All nine imported source files match
both the initial frozen snapshot and current repository bytes. The source
construction is kernel-accepted; original source/native occurrence
correspondence, original principality and independent review remain separate.

**Producer frozen. All writes to this Lean module and note have stopped.**
