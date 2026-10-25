# Declarative packet opening — r10 N, revision 1

Status: **FROZEN candidate construction with one unresolved realization seam;
`declarative_packet_opening_correspondence` NOT ESTABLISHED.** Source analysis,
not independent certification. No Lean phase was activated.

## Assignment and receipts

- Sprint/contract: `FORCE-DECLARATIVE-CONSTRUCTION-20261025/r10`,
  `tasks/agent-loop/sprints/force-declarative-construction-20261025-r10.md`,
  SHA-256 `ddcfe7b8ff5065ab76dae1c753ad43a33b0f7ef38682ff4829dd218c2094e521`.
- Assignment/handoff ID: `N-declarative_packet_opening_correspondence`, revision
  **1**. Sole author/worker: `/root/declarative_packet_construction_r10`.
  Primary: `/root`; session
  `FORCE-DECLARATIVE-CONSTRUCTION-20261025/root-turn-2`.
- Requested model/effort, from the primary's live row: `gpt-6-sol/high`.
  Effective observed model/effort: **UNKNOWN/UNKNOWN**. The actual NEW_TASK is
  the current assignment receipt; exact launch time is UNKNOWN. No model
  change, effective-model observation or descendant is claimed.
- Inherited baseline `9b945b0bb175e8e0919d388dc720babbdf0c2464`, not independently
  verified; no Git command. Sole new/changed/leased path: this file. No scratch,
  generated output, child assignment or other write.
- Source-only grant **1,200 seconds**, conservatively charged in full because
  launch duration is UNKNOWN. Clock observed during work:
  `2026-10-25 01:12:19 UTC` and `2026-10-25 01:14:07 UTC`.

Original parent: complete Lean proofs of semantics and type inference over the
unchanged accepted source domain. This packet addresses N1/O-NORM's
binder-indexed whole-packet opening. O-RESULT, full Force realization, source to
native correspondence, Call A/B and their independent quantifiers, inference,
and the original parent remain OPEN. No inference operation, supported program,
semantic rule, lineage, expected output or production prerequisite changes.

## Direct inputs and prior work

The following pins were recomputed and matched. They are immutable direct
inputs; none is silently treated as a source-native theorem.

| Input | SHA-256 |
|---|---|
| Paper, `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/YulangClosure/ForceAdmin.lean` | `620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97` |
| r7 outcome | `b89cbb133006aaae4563789460466ddc790df1460418f124dee36d86b5558d29` |
| r8 N1 specialization report | `7492d74c018645394f54559695cc0f7b3278edce2fbd34eb6f20b06504be0f76` |
| r8 result-relation report | `9972764cc9b750fa5fc218b1c571fd29b58ffb46f6a7bc0e566aaaa4e1bfb430` |
| r9 binder/export trace | `5c0ca8b96c5d5aa5093adae85f917269c0343bfe26c63efded2736f7b5007bd2` |
| r9 runtime-return trace | `208834c17ad78d4994cf9596bc9f6e9fd275691e9f60d2d10c7baaa9d2b321c4` |
| r8 outcome | `4c63f6f55a4fd5ee2afeb83a5df575704715b7bc093a1934997b4cb4994ba5eb` |
| r9 outcome | `bf544d639797fbecad878095916588d300eddf1e9c786d37786c9ebca01e232f` |

The paper, ForceAdmin module and N1 report were read directly; the relevant N
trace and result-relation report were read. Runtime-return and outcome pins
were verified as contract history, not reused as mathematical premises.
Reused authors/results: r7 `/root/force_admin_abstract_prover_r7` for ordered
abstract observation only; r8 `/root/force_packet_specialization_r8` for the
distinction between a consumed binder and outer wrappers; r8
`/root/force_result_relation_r8` for its explicitly unproved FR-ROUTE target;
r9 `/root/binder_packet_export_trace_r9` only to avoid mistaking a compiler
export gap for declarative impossibility. Paper authorship is its existing
title attribution; no new authorship is assigned here.

Root/base AGENTS, sprint/proof skills, `rules/goal-driven-sprints.md`,
`tasks/agent-loop/README.md`, design-authority, role boundaries and the
authoritative top-level inference principles were read. No compiler owner is
an input to the derivation below. This is a different method from r8/r9:
construct a proof representation from accepted typed derivations.

## What the typed input supplies

Let the actual abstraction introduction be

```text
D : Delta,a ; Gamma ; Psi ; Xi |- v : B
a notin fv(Gamma,Psi,Xi,Declarations)
------------------------------------------------
Abs(D) : Delta ; Gamma ; Psi ; Xi |- Lambda a.v : forall a.B.
```

Let `T` be a type descriptor well formed in **Delta**, together with the
ordinary/qualified evidence used by this particular instance. These are the
paper's actual premises at 1188–1192, 1541, 1748–1768 and 2058–2073.
Capture-avoiding substitution acts on the finite derivation, not on an
unlabelled metadata blob. The paper's 2098–2119 argument freshens inner forall
binders, leaves the external shared graph fixed, and preserves all latent and
scope/view contracts. It is a stated mathematical source argument, not a Lean
proof being supplied by this report.

**Useful reduction:** no inference-to-core exporter is needed to identify the
consumed binder in this declarative problem. The abstraction-introduction node
is its identity; its actual derivation supplies the scope of every applicable
type occurrence. The r9 absence of such an exporter therefore does not block
this construction. An arbitrary front-half `View_chi` is insufficient: the
precise judgment explicitly admits views only from decoration, specified
transport, receipt and simultaneous substitution (1578–1581).

## A finite derivation-indexed template and its opening

The following is a **candidate proof representation**, built from those
source premises. Its telescope is explicit; it is not an installed compiler
packet datatype or a new source rule.

For each node of the retained typed derivation record:

```text
Tpl(node) = (source label, rule tag, lexical type telescope,
             typed parameter expressions, ordered child references,
             declaration/template references, external capture references).
```

Typed parameters include the node's value/row types, operation instance,
source annotation occurrence, role/entry/profile template, selected ordinary
code/dictionary evidence, latent and reentry interfaces, and source-indexed
scope/target correspondence. Type occurrences use binder identity plus scope,
not spelling. Existing identities are constants of their own sorts. Shared
derivation/code nodes and recursive template uses are references to finite
tables, not recursive duplication. Source labels and child order are retained.
This construction records information already supplied to decoration; it does
not reconstruct it from equal types or row/family IDs.

For the frontier belonging to `Abs(D)`, define `open_a(T, -)` by one structural
pass through this template and its scoped parameter expressions:

```text
open_a(T, refType(a)) = T                    -- do not recurse into inserted T
open_a(T, refType(b)) = refType(b)            -- b != a
open_a(T, identityConstant(k)) = identityConstant(k)
open_a(T, node(r,l,params,children))
  = node(r,l, params[T/a], map(open_a(T,-),children))
open_a(T, forall b.body)
  = forall b'. open_a(T,body[b'/b])           -- b' fresh for T, if needed
open_a(T, externalCapture(x)) = externalCapture(x).
```

The `forall` equation applies to a nested binder, not to the consumed frontier:
that frontier is removed once. A recursive type binder is likewise freshened
as needed and preserves its back references. External capture references are
fixed by the abstraction side condition. A **locally created** closure inside
`v` may capture a formal whose type mentions `a`: its slot identity remains
the same while its declared type/template is substituted. These two capture
cases must not be conflated.

The same substitution environment is shared by all children and all coordinate
fields. Declaration-local formal binders stay local: for a nominal template
with local formal parameters `q_i` and actual arguments `A_i`, its opened
environment is `q_i := A_i[T/a]`; the declaration's closed template is not
mistakenly opened at a local `q_i` binder. No per-port fresh row/dictionary
instance is constructed. An existing reference, owner, handler, scope, target,
event or lineage identity is unchanged by this opening; new future runtime
operations in the code remain future operations.

Termination follows from finite syntax plus memoized node/telescope references.
As required at 1199–1209, a nonregular nominal remains a finite declaration
template with an argument environment. Opening never expands its whole
potential representation. Its later finite-path interpretation can inspect
that opened environment.

These equations establish a one-pass **template substitution construction**.
They do not yet establish an equation on the realized source packet, whose
relations are addressed below.

### Delayed shape is rebuilt from the same origin

At an abstract type occurrence retain

```text
Hole(sourceOccurrence, binderKey, polarity, descriptorEnvironment,
     sourceAnnotation/profileRule, dependencyReferences).
```

After opening, feed the resulting descriptor to the source profile scan at
1193–1221. Tuple/record/variant edges keep their labels; function argument
edges flip polarity; other edges retain it. A known thunk adds the distinct
force/effect and force/result shape; a still-abstract outer variable retains
a delayed template. Source roles and Value/Computation entry are retained from
their original source form (1223–1229), rather than chosen from the instance's
row emptiness. Explicit callback wildcard still makes no profile/grant;
negative concrete, omission, computation wildcard and positive upper
obligation use their respective original rules.

Filling a template creates static type/port/profile descriptions. It does not
enter a View, emit an event, allocate a receiver or realize a Boundary/scope.
Such effects remain at their actual execution/receipt sites. In particular a
newly visible callback location is neither absent nor a current observation.

### Scope correspondence and interpretation

Opening acts on the **finite source-occurrence-indexed table**, not a row ID:

```text
(e,j) |-> (s, origin(b,r,e,j))
    becomes
(e[T/a],j) |-> (s, origin(b,r,e[T/a],j)),
```

where substitution affects applicable type/template/binder-instance fields;
it never identifies the existing dynamic handles `s,b,r`. If `e` is an
unaffected row binder its reference stays the same. Distinct `j1,j2` remain
distinct, even when their row/family types become equal. Target tables retain
their source output occurrence and original receiver. This is the direct
reading of 2244–2263 and 2284–2308, with dynamic free handles fixed as required
also at 2581–2583. A qualified imported value must already carry this evidence;
opening does not manufacture it.

An owner/handler read-renaming environment acts on a different sort of
coordinates. Type opening preserves its saved/ambient action tags and its
free-name boundary; it is not a resumption or ambient-state update. Commuting
these two *syntactic* actions on disjoint sorts does not assert that arbitrary
finite tables or arbitrarily selected joint assignments commute.

## Constructor coverage toward commutation

Write `Sub(D)` for the capture-avoiding substituted typed derivation and
`Gen` for the paper's actual decoration/graph construction. The desired
realization equation is

```text
realize(open_a(T,Tpl(D)))  ~=  Gen(Sub(D)),                 (DPC)
```

where `~=` permits consistent alpha-renaming of freshly chosen **static**
binder/label names, while retaining source occurrence correspondence, child
order, external identities and sharing. It does not quotient distinct ingress,
provider, residual, witness or dynamic occurrence lineages. Runtime output
occurrence allocation remains the responsibility of the actual typed transport;
the source does permit fresh view occurrences even though type application
does not allocate a receiver/scope/reference/event.

The following table covers the source constructor classes in the value/code
grammar, decoration table and graph rules. “Template equation” means the rule
tag, fields and children replay under the same substitution; it is not a claim
that an old interpreted relation table can be reused unchanged.

| Constructor class | Derived template equation / source evidence | Realization status |
|---|---|---|
| Variable, literal, immutable graph reference | Same variable/reference/identity; literal empty metadata; capture side condition fixes external graph (1240–1241, 2104–2112). | Selected at template/identity level. |
| Tuple, sequence/list, record, variant, nominal | Open each actual child in source order; use its existing component prefix. No absent component edge; same declaration and one opened argument environment (1239–1243, 1528–1530, 2050–2056). | Known prefix equations replay; actual child presence unchanged. |
| Projection, split, field/optional lookup, switch, pattern | Open declared component/payload types and every branch; same successful-component prefix removal; preserve required/default/presence and forall field type (1243, 1536, 2084–2088). | Known removal equations replay; optional absence stays absent. |
| Union injection/case, intersection evidence/choose, roll/unroll, top/absurd | Same explicit evidence constructor and same raw value where intersection requires it; open component types; freshen recursive type binder. | Structural rule topology preserved; no runtime inspection of abstract T. |
| Ret | Open returned value and **all** its latent interfaces; immediate remains 0 (1528). | All-latent identity is explicitly selected. |
| Let/bind, root initialization | Open source/result/formal types and both subderivations; connect same binder; source order and Receive sites retained (1247, 1529). | Composition of child equations. |
| Delay | Open body graph/interface; retain external captures and substitute internal typed capture slots; no creation-time View (1244, 1531). | Template equation selected; exact realized body uses its child cases. |
| Lambda, wrap, complete Call/App | Same source role/entry/profile origin; open generic input, body, declared result, adapter and all result latent ports jointly; one receiver remains one (1246, 1533–1534). | Complete-call topology selected; dependent on child relation equations. |
| Type abstraction/application, qualified dictionary/member instance | Freshen nested binder; remove only consumed frontier; same instance over all parameters and ordinary evidence (1241, 1541, 2060–2073, 2104–2116). | The template opening above supplies scoped linkage; realized graph still requires DPC. |
| Primitive, Select/RefSet/reference response | Same primitive/selected code and signature; open all type arguments once; preserve concrete constructor/component transports (1240, 1249, 1535). | Replays selected ordinary code; no storage polymorphism or fresh free identity. |
| Perform/operation mapper | Same declaration/member and event-code origin; one opened instance used by P/Q and both mapper codes; actual emission remains at perform (1251, 1535, 1538). | Operation-instance template equation selected; no new event from opening. |
| Case/Catch/Handle, ordered attempts | Same alternatives, phase/coverage source labels and handler occurrence; open input/output/cut types jointly; fixed-cell filter belongs to rebuilt interface (1248, 1536–1537, 1611–1629). | Graph topology selected; no proof of equality of old/new filter tables is claimed. |
| rec, Block, declaration, generated template | Same finite binder/code table and guarded back references; one type environment per reference (1252, 1539, 1636–1647). | Finite template equation selected; no receiver at template expansion. |
| Raw continuation/Resume, scope, View, wait | Open all hole/whole/response types and pending operation interfaces together; keep same six frame kinds, saved/ambient action tags and pending original event (1542, 1636–1680). | Depends on rebuilt frame relations; includes the View-result seam below. |
| Failure/Bad and defaults | Same reason/alternative; opening does not make a failure into a value or erase unexecuted code. | Syntax preserved; raw successor/error completeness is not proved. |
| **Force and normal View/expose leave** | Open operand thunk and body/result types; retain force.effect View separately from force.result transport (1245, 1532, 1653). | **Exact all-latent result relation not derived here. This blocks complete DPC.** |

For identity, known prefix/removal and operation-instance templates there is a
direct parameter calculation: prefix labels/declaration IDs are fixed, the
same parameter environment occurs on both endpoints, and inserted T is never
substituted again. Composition and union inherit these template equations.
This is a constructive reduction beyond the old undifferentiated “missing
packet exporter” premise. It supplies scoped opening and identifies the local
primitive obligations needed by the induction. It supplies no implementation
correspondence.

## Finite-cell reconstruction is not literal table substitution

If T reveals ports, the source constructs a new signature/interface `I'`, new
type/port nodes, and local relations from the instantiated templates.
Unrepresented coordinates are all candidates, not fresh independently chosen
row variables. The exact source obligation at 1756–1768 is

```text
rho( tHat'( rho^(-1)(U) ) )  subseteq  tHat(U),
```

with `rho : S_I' -> S_I` forgetting added coordinates (including new family
colors to the old star and new path coordinates to old unknown). It explicitly
rejects unchanged old truth-table commutation. Thus an equation asserting
`newTable = map(substitute,oldTable)` is not DPC and is not supported.

The finite algorithm at 1346–1421 rebuilds tables by enumerating all consistent
joint cells satisfying the **specified coordinate equations**. For identity,
prefix, shared instance arguments and Boolean operations, using the same
equations on the opened endpoints is compatible with forgetting: old named
equations still hold; old hidden bits are the disjunction over their refined
regions; extra unrepresented columns impose no old restriction. This explains
why reconstruction, rather than old-table equality, is the intended method.
It is not a completed proof for every frame/filter/leave relation, and does
not identify a particular post-fixed-point witness `U'` with the old `U`.

**First remaining realization equation:** define/derive the actual normal
View-return operation on the body result and the operand's result-path
metadata, for each typed suffix. Neither giving that operation a `ForceLeave`
tag nor putting an opaque callback in `realize` establishes it. The clauses
485–492, 1245, 1532 and 1653 require a result operation but this report has not
derived its full constructor equation. Known prefix/removal formulas at
611–624 and 1361–1370 explain a prefix **once selected**; they do not by
themselves prove which incoming packets are combined by this Force leave.
R10 R separately owns that source-entailment question. This is no claim of
logical underdetermination or a countermodel.

Primary seam message received before freeze: R obtained a **conditional** local
route-cut derivation from draft typed-boundary §6, leaving its applicability to
every accepted Force unproved. That message is coordination evidence, not a
new mathematical input to this construction; the draft was not adopted or
read as governing authority here. The shared seam is precisely the
applicability/interface of that result operation at the paper's Force/View
sites, including newly exposed suffixes. No conditional R premise is used.

This seam also matters for nested Force inside lambda/Delay code; it cannot be
excluded from DPC by checking only base-valued abstraction bodies. Accordingly
the construction is not complete enough to enable `SourcePacket.lean`.

## Discriminators and direct parent application

1. **Open descriptor U beta.** Let the consumed binder be `a`, and let `beta`
   belong to outer Delta. `open_a(U beta, refType(a))` inserts exactly that
   descriptor and leaves beta free. In a de Bruijn implementation, the output
   is in a different telescope; applying the old index-zero opening again
   would open beta and can produce `U(U beta)`. The candidate uses one pass;
   a second consumed-frontier opening is not even well scoped.
2. **Nested binder.** For `forall b. C(a,b)` open to
   `forall b'. C(T,b')`, with b' fresh for T. The inner parameter is not
   consumed. This also applies to forall stored in nominal/record payload.
3. **Outer versus inner wrapper.** For
   `View_c((View_d(Lambda a.v))[T])`, the redex opens d's forall frontier and
   D's body; c is outside that application. The required ordered wrapper
   result is `[c] ++ [open_a(T,d)] ++ W_body`, with existing duplicates and
   ordering retained. A blanket map over the final wrapper list is wrong.
4. **Shared captures.** Two fields referencing one captured external packet
   keep the same reference and dynamic handles. An internal formal-dependent
   capture changes its type template once without becoming a distinct slot.
5. **Delayed force-result shape.** Take the accepted schematic body
   `Lambda a. lambda^C x. Force x`, with the lambda formal thunk returning a.
   Its type instance `a := U(E,beta)` reveals the operand path
   `force.result.force.effect`. This is a later effect of the returned thunk,
   not the current Force's force.effect observation. DPC needs the actual
   instantiated Force-leave relation at this new suffix; the tag/topology
   equation alone does not establish it.
6. **Duplicate ingress entries.** Retain `(e,j1)->s1` and `(e,j2)->s2` under
   the same type/row instance, preserving j1 != j2 and the receiver in each
   origin. Row/family equality after opening cannot merge these entries.

These are algebraic discriminators, not executed programs or claimed source
counterexamples. They identify omissions, double opening, binder capture,
lineage collapse, premature latent execution and a wrong wrapper order.

Application to r7: its `wrap_append` already gives ordered concatenation and
its abstract theorem handles finite-success bookkeeping for fixed beta/inst.
The template construction above now supplies a candidate meaning for beta and
an intended packet opening with an authentic binder owner. To apply r7 to
actual source observation, DPC must still be proved at the realized packet
level, including the normal-result seam, with a lossless source encoding and
the separate successor/error coverage. Choosing arbitrary `inst` now would
not establish those premises. N1/O-NORM/O-RESULT and the original parent stay
OPEN; no foreign-continuation or Call obligation is discharged by this local
construction.

## Mutual TODO, falsifier and stop

**DPC-LOCAL-RETURN-1 — Luna/R source-entailment owner.** Original parent
N1/O-NORM, with the shared O-RESULT seam. Inputs: pinned typed derivation,
actual Force operand/result packet, interpretation, all typed result suffixes,
and the paper's actual normal-leave construction. Required output: a
source-derived normal-result packet operation and its constructor equation,
including body-result information, operand-result-path information, source
occurrences and allowed output occurrence allocation. Then verify its type
instance reconstruction equation and forgetting inclusion. Do not assume r8
FR-ROUTE or interpret this TODO as authority to choose a new rule.

Falsifier of this report's remaining-premise classification: a derivation from
the pinned clauses that computes that packet operation at every suffix without
an extra premise. The returned-thunk discriminator above must distinguish
`force.effect` from `force.result.force.effect`, retain the actual incoming
occurrences, and retain external scope/target lineages. A new source equation,
invented model or provisional runtime does not falsify the classification.

If the equation is established and independently reviewed, the next in-scope
construction is induction on the template table above, with its Force/View
case instantiated by that equation and all finite relations rebuilt on I'.
Until then this worker has reached the contract's uncovered-realization stop
condition. The conditional N Lean entry condition is **not met**. This report
is not a request for a second arbitrary-inst theorem or another export audit.

Checks: bounded `cat`/`sed`/`rg` reads, SHA-256 dependency comparison and clock
reads only. No Lean, tests, builds, compiler/native execution, Git, scratch,
production edit, external contact, reviewer appointment or descendants.
CPU/memory unmeasured. Source theorem proof/review, full local-relation
enumeration, concrete encoding and implementation checks are omitted and
remain open explicitly. Review status: PENDING; primary owns independent
review and shared state. No central record was edited.

Writer state: **STOPPED / WRITES CEASED** after freezing this revision; no
descendant leases. The final submission carries this file's exact hash and
stop clock. Commit readiness is a research-only pending-review checkpoint;
no Git action or source/proof closure is claimed. Suggested checkpoint subject:
`research: construct scoped declarative packet opening and isolate return seam`.
