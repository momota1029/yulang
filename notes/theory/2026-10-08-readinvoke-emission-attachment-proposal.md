# Constructing and retaining the ReadInvoke emission attachment

Date: 2026-10-08
Status: independently reviewed conditional construction proposal; research only
Baseline: `c4a22471680223856da7fae16a11bc2f969a0834`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Production implementation / semantic selection / cutover authority: none

## 1. Objective and achieved boundary

Construct the finite source-rule inventory at the owner that knows the original
Call, rather than attempting to infer rule presence from receiver typing.
The proposed builder produces a presentation `E^att`, an actual inserted-rule
handle for every source occurrence, and its finite inventory certificate
together. This is a forward construction, conditional on original operator
rule schemas and contracts. It does not require a finite emission certificate
as an input.

The achieved proposal is:

```text
H_form, H_rules, original complete declaration graph
  |- Build(q_c) = (E^att, rho, inserted, cert_inventory)

H_form, H_rules, H_sem, pi : SourceObs_K(q_c,h)
  |- delta_pi : M_E^att(rho(c),h,O_pi,w_pi;xi)
     DescMem(ReadInvoke(F_c,D_c,IF_c),O_pi,w_pi;xi).
```

`SourceObs_K` denotes an existing finite decorated source derivation in the
independent original kernel, not a new source semantics. The second sequent
is for the structural pure-read branch. In particular it covers the initial
zero-step prefix without a callee Return or constructed argument carrier.
Its correspondence to **independently fixed** `E_c` requires §7's additional
rule-preserving attachment. Neither sequent concludes `M_E_c` without that
attachment. Matching the original root name is insufficient.

Claim classes: candidate constructor definition; conditional inventory and
finite-derivation theorems. The selected IF and ReadInvoke definitions remain
established within their previously reviewed envelopes. This proposal is not
an unconditional source theorem or a theorem about the current compiler
emitter.

Construction scope is the registered inner Name/Result/Delay/Bind/Call
envelope and its original contract/admission declarations, with enclosing
source roots, such as a Lambda, supplied as opaque typed registrations. The
builder does not emit rules for arbitrary enclosing source constructors. Such
constructors need their own cases before this local inventory can be composed
into a larger source-base construction.

## 2. Authority, dependencies and explicit inputs

Governing sources, read at this baseline:

- [source-interface definition](../design/2026-10-08-call-source-interface-definition.md)
  §§1–4 (the supplied locator §§1–6 has only four numbered sections): selects
  IF-Insert/IF-Use and the complete source Call frame, not an E mutation rule.
- [interface construction](2026-10-08-call-source-interface-construction.md)
  §§3–7: dependent clause slots, FrameCall, structural constructors, finite
  registration and original pending/return/future equations.
- [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3.5: independently interpreted finite clause graph, least finite
  derivations, source inventory, independent histories and local DescMem.
  Its concrete clauses remain Draft; §3.5 assumes conformance.
- [nested-source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–4: only the selected block, sequential local binding and inert returned
  capture; no change to its source meaning.
- [pure-read result definition](../design/2026-10-08-pure-read-call-result-constructor.md)
  §§3–5 and [reviewed source-base attempt](2026-10-08-readinvoke-sourcebase-construction.md)
  §§3–6: staged identity result, H_form/H_sem, exact Code constructor and
  missing fixed-root emission head.
- [source generator](../design/2026-10-04-source-generated-callback-structural-theorems.md)
  §§2.1–2.4 and [semantic input realization](2026-10-08-call-semantic-input-realization.md)
  §§2–3 and the previously reviewed R/E results imported through the source-base
  note: independent decorated kernel and actual-provider semantics.
- `tasks/current.md`, Immediate work order item 2 and the exact source-base
  residual: scheduling context only. Its dirty contents are not Authority.
- `rules/compiler-engineering.md`, proof-obligation economy: retain insertion
  evidence if an owning emitter already knows it; do not invent membership
  through metadata.

Retain H_form and H_sem of the reviewed source-base note unchanged. In
particular, H_sem supplies independently justified original environment,
hereditary same-value membership, VIncl, reify/whole-carrier typing, challenge
assembly, original kernel and lawful live-event actions. It is not generated
from raw source syntax, IF slots, a checking origin, Q, or the desired result.

The additional **candidate input H_rules** is stated precisely:

1. The independent original kernel has a finite *schema presentation* for
   each operator used here: Name, Result, inert Delay, dependent Bind and
   actual-provider invocation. A schema may quantify over providers, carriers,
   observations and independently admitted histories; it does not enumerate
   these infinite families.
2. Each schema has its independent constructor-image meaning, original
   premise telescope, original typed conclusion, original scope and lawful
   whole-witness action. The prefix/continuation cases in §4 are part of that
   original meaning. Original primitive and provider contracts remain inputs.
3. Each finite source derivation has a last original schema instance; every
   instance carries the original operand occurrences and operation witness.
   Kernel equations supply the Bind/Call decomposition and reconstruction.

H_rules is **not** a supplied E inventory, a source-to-E map, a finite emission
certificate or a global descriptor soundness assertion. It is a finite
presentation of the independently interpreted local operators. The cited
source documents specify the operator inventory and sequencing equations,
but do not print every concrete decorated inference rule. Consequently this
note does not establish H_rules for a sealed foreign kernel or production.
If such templates do not exist, their exact independent meaning must be
supplied before applying this theorem; the builder cannot create it.

The theorem's new output is rule *installation*, with exact incidence and
inventory proof. The semantic typing work from H_sem is reused, not solved
by installing a rule. H_rules separates that real dependency from the old
conformance premise rather than concealing it inside a renamed certificate.

## 3. Source-owned construction and retained certificate

Keep `j=(B,X,xi,Delta_c; all incidences)`, the original binder tree and
`xi=(nu,K,D)`. A root occurrence includes its original constructor origin,
declared whole telescope and typed source occurrence. `rho` maps these
occurrences to **allocated presentation slots**, not to a new provider or
world. Distinct occurrences stay distinct, and shared registered references
remain shared. A symbolic original root handle can be retained literally;
the presentation containing it is nevertheless the newly built `E^att`.

The builder has two finite passes, extending Theorem IF's registration pass:

1. Allocate one root slot per registered original data/code/contract
   occurrence, preserving binder identity and the original declared telescope.
   Allocate dependent operand and suspended-suffix slots from the selected IF.
   References terminate at registered slots; recursive bodies are not unfolded.
2. Visit each formation record in the registered inner envelope once. For its
   constructor tag, insert the instantiated original operator schemas of §4,
   with child references fixed by its actual typed operand occurrences. At a
   contract declaration, insert its actual original clauses, including all
   W/Z/Option 2 clauses. Preserve existing union/conjunction/binder structure,
   not an arbitrary union of every slot. Insert the independent history schemas
   at their genuine response/raw-handle/future ports. Return a record for each
   actual insertion.

The elementary builder operation is the following *proposed representation
constructor*. `append_at` is actual graph construction, not an IF inclusion:

```text
registered r:T at its original binders in the owned presentation under construction
schema s from the independent operator/declaration, typed substitution m
actual operand handles a, with their original origins and dependent shared telescope
------------------------------------------------------------------------ EM-Insert
E' := append_at(E,r,s[m,a])
i  := (presentation-version E', root r, clause address, s, m, a, origins)
lookup_rule(E',i) = s[m,a]
```

Each record includes the entire rule and operand substitution, not just a tag,
effect endpoint or row ID. IF-Insert/IF-Use are emitted alongside it from the
same formation record; no inference converts their slots into rule presence.
The insertion equality follows from the definition of the owned graph append.
It assumes exclusive ownership of that graph construction, not insertion
authority over an independently sealed `E_c`.

At finalization, freeze the finite clause table and root table. Remap insertion
addresses to that final table, preserving their exact clauses; this is a
deterministic address map, not semantic freshening. The output certificate is
the list of these final records, typed root registrations, schema origins,
operand edges, branch tags and binder/reference maps. It is available before
any observation, carrier challenge or subtype query. A mere detached list
without the lookup equalities would not be this output.

## 4. Actual local rule families to insert

For an original schema

```text
P_1(a_1,z_1), ..., P_k(a_k,z_k), G_K(z_1,...,z_k; original indices)
------------------------------------------------------------------------ s
Obs_K(n, J_s(z_1,...,z_k); original indices)
```

insert the same constructor-image rule with its **source child** predicates
replaced by references to their allocated roots. Primitive/operator guards
`G_K`, dependent result maps `J_s`, original witnesses and original admitted
history predicates remain independently interpreted. The resulting head is
the graph's data or computation membership at `rho(n)`. This is schema
instantiation, not a new operational transition. Descriptor membership is
not a premise for manufacturing source membership.

These are heterogeneous data/computation/carrier roots of the same original
typed rule graph; they do not introduce a new semantic coordinate. Insert the
following cases, including their original administrative prefixes:

| Owner | Actual operands and rule families retained |
| --- | --- |
| Captured/local Name | Original resolved binding reference and actual scoped capture substitution; lookup prefixes and completed lookup use that same binding/provider/current configuration. Captured f references the outer root; x references the local formal. |
| Result | Its data child, original Return delimiter and same returned descriptor/provider/state; initial and unfinished data-evaluation prefixes remain unfinished, without an invented Return. |
| Delay | Inert formation at the original reify origin, referencing the **whole** q_x and original capture telescope. Formation requires no execution of q_x. Its latent designated one-layer developments reference q_x and use original independent admission. |
| Bind | Initial suspended computation/suffix; first-child administrative/finite-prefix lift; actual Return followed by typed same-value/state rebind and suffix derivation; pending Request/raw handle with ordered suffix; admitted response/resume development at its live state. |
| Call | Initial and callee-prefix cases; actual callee Return at its original result interface; subsequent actual inert whole-argument formation; actual-provider dispatch/receipt; actual entry, body, native return, consumer and invocation return; pending and admitted future developments through those original dependent interfaces. |
| Response / raw Resume / FutureUse | The four original admission constructors, at the exposed operation, original raw handle or actually returned provider. Membership developments reference the original suspended continuation or latent interface, at the independently admitted live event. |

Call is the ordered Bind image with suffix

```text
S(actual_f,C1) = form_actual_Delay(q_x,original_capture,C1);
                ExecuteCallable(actual_f,that_whole_carrier,C1).
```

The `form_actual_Delay` operation denotes the original inert formation case;
it does not Force q_x. The receiver suffix is a finite dependent schema on
the **actual** returned provider, with that provider's actual role and entry.
Its complete original declaration/operation witness is required when this
schema is instantiated. No provider implementation theorem follows from
allocating a root.

Bind retains exactly the independently supplied equations:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S).
```

An initial Call prefix contains suspended source/Bind information, not a
constructed Delay or d. A callee lookup prefix is lifted with the unreached
receiver suffix. At actual callee Return, bind the same `(v_f,U_f,r_f,C1,w1)`;
only actual carrier formation and independent challenge assembly introduce
those later fields. Pending receiver entry retains past receipt and the
remaining entry/rebind/body/consumer/return suffix. Resumption does not replay
receipt or bind a result before its actual Return. Value entry has its one
designated Force; retained entry has none. A native return precedes its
declaration-derived consumer. Infinite divergence needs no Return, while each
finite prefix uses a finite instance of these rules.

Future-use schemas retain the actual result provider's dependent port. The
schema quantifies over independently admitted finite uses; no list of all
future clients is enumerated or supplied at formation. A separately supplied
finite source client graph can be registered at that actual use. An arbitrary
opaque provider/client still needs its complete independent original contract;
this construction does not establish all-provider source adequacy.

The carrier slot stays the original open whole-carrier hole. The actual source
Delay is its diagonal filling. No rule equates every independently admitted h
with that Delay, demands that h return, or narrows D_c. For a different filling,
the same receiver schema uses h's own original whole-carrier/admission evidence.
The structural derivation theorem below concerns the source diagonal and its
independently admitted developments, not an assertion that every filling has
q_x's source derivation.

All original clause alternatives are retained at their actual declaration
roots and use occurrences. W preserves its original input/output relation,
changed-provider/future fields and domain certificate; it does not equate
those two tuples. Z may have no source observation anchor. Union keeps its
actual branch map; conjunction keeps one shared tuple. No arm is rerouted
through structural U_f or removed for an unavailable primitive typing proof.
Source-base inventory certification is tagged separately from retained
production alternatives; it asserts no source-tight production policy.

## 5. Inventory certificate is an output: constructive induction

For a finite formation graph with N occurrence nodes, L original contract
clauses, I incidence fields and k finite operator schemas per node (maximum
over the supplied local signatures), the builder visits N nodes and L clauses
and emits finitely many schema instances and address records. The record count
is bounded by `k*N + L` plus finite history/reference records. This is a
structural finiteness observation, not a measured complexity claim.

Prove by induction on the builder's second pass:

1. Every completed source node has exactly the required local source families
   for its constructor, at its allocated root with the original ordered
   operands. Its record contains lookup equality at that root.
2. Every emitted clause is attributed to that actual source constructor,
   original declaration alternative or original admission schema. There is no
   unexplained emission route: the builder has no fourth emitting branch.
3. Registered references, scopes and shared middle telescopes are those
   allocated in the first pass. Every edge uses the original typed substitution.
4. Inserting later nodes never invalidates previous clause records; final
   address remapping preserves their lookup equalities.

Initialization gives empty source inventory over typed registrations, not
source membership. Each loop step chooses the finite schema list solely by
the original constructor tag, constructs its exact references from that
formation record and appends precisely those clauses. This proves items 1–4
for that step directly. References to a later or cyclic node use its already
registered interface; no semantic recursive unfolding is required.

At termination every node in the registered inner envelope and each included
contract/declaration has been visited exactly once; the table in §4 proves
inventory coverage for that bounded envelope, and the append records prove
output-clause accounting. The four history cases prove independent admission
inventory accounting. Thus the syntactic inventory/incidence portion of
§§3.1–3.4's source-base conformance certificate is **generated**, not assumed.
For this untransformed output the transformation list is empty. A later
generalizer/use must provide its own lawful whole-map certificate; this note
does not generate it by identity of printed roots.

Local semantic DescMem is supplied separately by §6, not by these syntactic
records. Together these give the relevant local conformance premises of §3.5
for this constructor output. Full conformance of a larger enclosing graph
still requires its remaining source nodes and complete local typing lemmas.

## 6. Finite derivation translation and local typing

Induct on an actual finite decorated source observation derivation pi. Its
last rule is an independently interpreted original schema s by H_rules.
Recursively translate source-child premises. Look up the retained insertion
record for s at the same source occurrence and instantiate its unchanged
guard, maps and joint evidence with pi's operands. Apply that emitted rule.
This constructs delta_pi at E^att, without querying descriptor membership,
successful Q or a finite emission-certificate input.

For Name, use the original environment projection/capture evidence; for Result,
use the same child and Return delimiter. Delay formation uses its original
inert witness and reference, without recursively deriving an execution of q_x.
A later actual latent development uses the q_x child derivation at the original
live scope. Bind prefix cases translate only the reached child and retain the
suspended suffix; Return uses the one dependent middle witness. Request uses
the original handle and suffix equation, and admitted resumption uses the
same operation witness at C'. Call uses the actual callee derivation and its
same-provider receiver witness through this Bind construction. FutureUse uses
the actual result provider and original admitted use. Recursive reference
translation is on finite pi, never infinite graph unfolding. Conversely,
last-rule lookup reconstructs a source-base derivation under the same schemas;
this converse excludes independent production W/Z derivations.

For the initial observation pi0, the emitted **Call-initial** schema yields

```text
original formed q_c, independent valid initial event/env, original initial-prefix witness
---------------------------------------------------------------------------------------
M_E^att(rho(c),h,O_initial,w_initial;xi).
```

There is no carrier/challenge/receiver execution premise in this rule. Its
initial-prefix meaning is an H_rules input; presence at rho(c) is a builder
output. This is the smallest finite target derivation: one Call-prefix rule
application after graph construction. It is not an empty-root witness at E_c.

For local typing, H_sem and the reviewed R theorem supply Name/Return/Delay
typing. For each actual structural observation, callee inversion retains the
same v_f/U_f/r_f. At the right stage independent assembly yields d; contextual
membership eliminates at that actual provider, and E supplies P_F_c(d) through
all receiver developments. Before that stage retain only the suspended
prefix obligations. The selected identity ReadInvoke-Desc introduction gives
DescMem at exactly O_pi,w_pi,xi and the same scopes. It does not use delta_pi
to prove receiver typing. Combining this with delta_pi supplies the active
constrained-root conjunct without filtering generated observations by result
success.

Original W/Z alternatives need their own complete local typing, final guards,
introduced-provider/future and changed-admission laws. Rule preservation alone
does not prove these. The theorem does not promote full C0, CompleteMem or
any aggregate gate.

## 7. Exact attachment to a separately fixed E_c

An applicable attachment is a root/typed-rule map a, with a(rho(c)) the
original E_c root, satisfying for **each used inserted schema**:

```text
lookup_rule(E^att,i) = s[m,original operands]
lookup_rule(E_c,a(i)) = the same independently interpreted s
                      under one lawful whole-index action a
```

It preserves original source occurrence, declarations, operand order,
provider/role/entry, whole carrier, xi, binder position, scopes, guards,
dependent maps and joint witnesses. If the target sequent requires literally
unchanged tuples, the action must be identity on those original fields.
A map for renamed/hid tuples additionally requires the original certified
transport; projection equality alone does not suffice.

Induction on delta_pi then proves M_E_c at the mapped root/tuple: map child
derivations, look up the identical target rule and apply it with the same
witness. Only the source subgraph needs this embedding for forward membership;
extra E_c alternatives can coexist. Converse source-base correspondence
requires exhaustive accounting of the target's designated source base.

Existing IF-Insert records certify *contextual clause slots*, not these target
lookup equalities. The selected sources furnish no such attachment for an
independently fixed E_c. Two precise representation choices remain for the
primary to adjudicate within the authorized missing-definition scope:

1. **Construct at the owner:** define the relevant source presentation to be
   the builder's actual output, and retain EM-Insert records as phase output.
   M_E^att is then constructively available. This chooses E's construction;
   it is not a theorem that a previously sealed E_c had those rules.
2. **Keep an independent fixed consumer:** its owning emitter returns actual
   rule lookup/insertion records satisfying a, or a separately reviewed
   rule-preserving translation. Then §7 derives M_E_c. If a required prefix
   rule is missing, the forward theorem does not apply and adding it changes
   the presentation; an approved repair must be made at that owner.

These alternatives need not change the approved observable source meaning if
their templates are the same original operator relations. A choice of new
primitive meaning, prefix transition, admission condition or source restriction
would be a semantic decision and is not authorized by this proposal. No such
choice is made here. The production emitter is a third distinct object:
neither its inventory nor its attachment was inspected or proved in this job.

Owner classification: if a real source emitter already inserts these clauses,
the missing retained lookup facts are D reconstruction debt and should be
returned by that emitter. If the selected interpretation has no such emitter,
E^att is a forward semantic/representation construction on the A/B dependency
route. The certificate is compiler phase evidence about an actual append; it
does not add a duplicate membership relation to compensate for absent rules.

## 8. Evidence limits, failures and frozen manifest

One constructive documentary attempt; no executable oracle, tests, builds,
probes, mutations, formatting, children, interactive questions or Git mutations.
Seeds/ranges are not applicable. The original schemas and reviewed R/E/IF
results are shared assumptions; the induction proves conditional construction
and translation, not those schemas' independent source selection. A checker
reimplementing them would not establish that selection or production attachment.

Coverage: the exact captured Name/Name inner Call, its original entry/capture
telescope, implicit whole-argument Delay, staged prefixes, ordered Bind,
actual receiver, admitted resume/future schemas and retained original abstract
alternatives. Raw-source initial typing, arbitrary effectful/computed callees,
foreign kernels, full primitive validity, all provider/client source graphs,
world inhabitance, generalization/use, production correspondence and cutover
remain unverified. No repository-wide absence search was performed.

Failure conditions: missing independent finite original schema presentation;
untyped original formation/environment/primitive inputs; wrong prefix staging;
scope/witness/provider recombination; replayed receipt; forcing Delay during
formation; changed admission at a W output without its own certificate;
lost Z/Option 2 alternatives; absent target lookup; or changed dependencies.
None is a proposed source rejection rule.

Resource budget: documentary reasoning only; at most four lightweight reads
per batch, zero heavyweight processes, one leased output. No numerical CPU,
memory or wall-time cap was supplied. Peak CPU/RAM and elapsed reasoning time
were not instrumented. Some early aggregate tool returns were truncated;
the governing constructor and contract sections were reread in bounded chunks.

Frozen direct semantic/workflow dependencies (SHA-256):

```text
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
1a588c2a9920f39b2d49a06525dc482bf455029bd52de23f754204d4ae1ff1f5  notes/theory/2026-10-08-readinvoke-sourcebase-construction.md
568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe  notes/design/2026-10-04-source-generated-callback-structural-theorems.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442  rules/compiler-engineering.md
```

The final artifact hash is supplied in the frozen handoff packet.
Scheduling-only `tasks/current.md` was read with
hash `54c3d821d78dde275fae308ca62492af695a5f5b29be4351e322819a9485f6fe`;
its unrelated dirty state is preserved and not a proof dependency.

Recommended next action: independently review the finite H_rules requirement
and this constructor/attachment boundary, then choose the actual presentation
owner and retain its rule insertion records. The artifact needs no additional
receiver/phase probe. Any implementation needs its own exact authorization.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-08-readinvoke-emission-attachment-proposal.md`.
- Baseline SHA: `c4a22471680223856da7fae16a11bc2f969a0834`.
- Changed dependency hashes: none assumed; final dependency recheck accompanies
  the frozen report. Shared dirty paths were not edited.
- Review status: independent compiler-referee and spec-auditor review passed;
  the scope clarification was delta-reviewed; no semantic
  selection, fixed-E_c membership, production conformance or gate closure.
- Checks: governing-section documentary analysis, read-only baseline/status,
  dependency capture/recheck and exact leased output inspection; zero tests,
  builds, probes or Git mutations.
- Proposed one-line checkpoint message: `research: construct retained ReadInvoke emission inventory`.
- Shared deltas intentionally left to primary/curator: record the conditional
  E^att constructor, original H_rules dependency and separate fixed-root
  attachment; adjudicate representation selection and independent review.
  Keep M_E_c, primitive/full-C0, production and aggregate gate status open.
  No task/index/authority/theory-map/question-board edits are included.

Writes stop at the frozen handoff; later review repairs require an explicit
renewed lease.
