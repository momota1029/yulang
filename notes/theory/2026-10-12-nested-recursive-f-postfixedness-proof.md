# Nested recursive f: direct postfixedness attempt

Date: 2026-10-12
Status: frozen unreviewed research; conditional clause derivations and a local obstruction
Original L4 / complete Call / inference A/B gates: OPEN
Primary-issued baseline: `988ef4ae1`
Primary-issued branch: `research/simple-sub-intrusion`
Producer: leaf `/root/nested_f_postfixedness_proof_retry1`; no delegation
Exclusive output lease: this file only
Budget: one direct construction attempt, 30 minutes, static mathematics only

## 1. Frozen statement and original scope

The unchanged source is

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

The target is the original local clause

```text
H_f subset Phi(S).V
```

where H_f contains the actual f closure at its original complete endpoint
A_f, root r_f, initialization event b, and independently lawful restrictions.
The relation S must contain the actual event-indexed g and drop closures,
their jointly correlated worlds, and all required observations/carriers.
Putting a tuple in S is a permitted coinductive premise; proving its Phi(S)
readout is the obligation. Membership of recursive f is not an axiom.

Fix the original resolved graph, binder tree, `xi=(nu,K,D)`, initialization
event and one entire assignment/strategy. The source roots r_f, r_g, r_drop
and formal origins q_x, q_y, q_z are distinct. The inner callee f resolves
to r_f; both its argument y and drop's body y resolve to q_y. Neither is z.
For each actual f-body construction event a retain one actual v_g[a]. For
each actual g-body construction event d below a retain one actual
v_drop[a,d], capturing that event's returned y. Static root names do not
identify different allocations or event witnesses.

Quantify over every independently admitted f challenge, every retained
actual-provider decomposition, every finite zero-step, administrative,
pending and complete development, and all compatible future demands.
Descriptions precede their challenges: A_x at f's original type scope;
A_y below the f-body dependencies but before g's challenge; A_z below the
g-body construction dependencies but before drop's challenge. EventProof
choices depend only on preceding event inputs. Shared fields are assigned
once, aliases retain the same complete certificate, and different incoming
description frames retain their originally permitted proof fields without
rerunning initialization or changing runtime objects.

Independent primitive, profile, formation/license, entry, checking, hard
guard, context/action and W/Z laws remain at their original scopes. Their
truth is neither assumed collectively nor inferred from stored constraints.
No body/invocation port equality, termination assumption, manufactured Return,
successful query rule, source restriction or ordinary-inference change is
allowed. The broader parent quantifiers remain unchanged.

**Result class.** This note constructs a candidate relation and expands its
source clauses until a specific original checking premise is needed. It also
gives a bounded raw-operational no-finite-Return argument for the structural
source branch. Neither result establishes the desired postfixedness, a
source-qualified falsifier, source rejection, compiler correspondence or a
closed theorem. The exact independent laws still need their actual evidence.

## 2. Governing source constructors and consumers

The frozen [predecessor](2026-10-12-nested-recursive-l4-proof.md) §§1–3,4.3
pins the source/event scopes and original H_f target. Its failed pair/Step
instantiations are retained evidence, not repeated here.

The [selected contextual definition](../design/2026-10-08-contextual-function-membership-definition.md)
§§2–3 supplies same-provider Function realization and the positive operator.
[Simultaneous introduction](2026-10-08-simultaneous-immutable-root-introduction.md)
§3 displays Phi's V/W/T/Car clauses, mandatory fixed-domain positivity and
relative background lift; §4 supplies the pair proof pattern. Its exact
two-closure theorem is not applied to this source.

The [selected complete closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
§§2–4 and [captured introduction](2026-10-08-captured-call-closure-introduction.md)
§§3–6 supply generic Strict composition and the separate raw
Lambda/Name/Result/Delay/Bind/Call prefix constructors. Step §6's ordinary
captured-f checking argument is inspected as a consumer, not imported as an
introduction theorem for this source.

[Source Generalize](../design/2026-10-08-source-generalize-definition.md)
§§2–3 selects [its proof](2026-10-08-source-generalize-definition-and-proof.md)
§§3–5. L3 requires genuine local same-value/Function checks; L4 requires
actual simultaneous member/world introduction. §3.1 Call owns callee,
whole argument, receiver, entry, designated consumer and invocation return.
§3.2(4) requires checked-domain and whole-observation inclusion by an actual
finite local proof. §3.3 retains MemberEntry/Internal/Event records;
their existence does not establish the semantic law.

[Input realization](2026-10-08-call-semantic-input-realization.md) §§2–4
is the actual semantic consumer: PhiT Return uses the same value and world;
whole checked-challenge assembly precedes actual receiver acceptance;
Theorem F consumes a genuine whole comparison and ordinary source
realization. The [complete f-y inventory](2026-10-12-fy-complete-call-construction.md)
§§3,5 separates checking-origin records from their required semantic action.
The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
govern native inference and prohibit eager solving or source restrictions
introduced for proof convenience.

## 3. Candidate relation, with the holes and dependencies exposed

Define H_f to contain only the decorated actual `(A_f,v_f,r_f,e)` tuples
at independently compatible original events. It contains no g/drop value,
world, carrier, continuation, registration, receipt, guard or authority hole.
For this attempted proof device define

```text
Phi_Hf(Y).V = Phi(Y).V union H_f
Phi_Hf(Y).W/T/Car = Phi(Y).W/T/Car
B_Hf = greatest fixed point Y. Phi_Hf(Y).
```

This is a mathematical relative relation for the same Phi, not a selection
of new semantics for the independent challenge domain. The algebraic lift
from simultaneous-introduction §3 generalizes verbatim to this exact H_f:
if B_Hf is contained in S and H_f is contained in Phi(S).V, one unfolding
and positivity give B_Hf contained in Phi(S). All non-hole sorts already
unfold through Phi; only the exact f value holes need replacement. No
world-validity assumption is hidden in H_f.

Ordinary complete certificates embed in B_Hf by monotonicity. However,
uniformly interpreting every independent punctured challenge proof field
in B_Hf is a separate correspondence obligation. The exact pair and Step
background selections do not automatically prove it for these nested event
families. In particular a field checking f at another endpoint needs its
actual original checking derivation. We do not discard such challenges.

Construct S as the componentwise union of B_Hf and these proposed source
cases, retaining all decorations:

- V: H_f; the actual g[a] and drop[a,d] tuples at their original complete
  endpoints, all original checked-use endpoints when required, and their
  lawful future restrictions. A checked-use tuple added here creates another
  Phi(S) obligation; it supplies no checking proof.
- W: actual initialization, entry, construction, rebind, Call and future
  worlds, with every installed external/background binding. Parameter values
  enter only after their actual carrier Return; g/drop enter only after
  their actual Lambda construction/result binding. Shared capture projections
  keep their dependency-closed incidence maps and one original world witness.
- T: every actual finite original prefix and development, carrying its
  precise remaining entry/body/consumer/invocation-return suffix, including
  requests, raw resumptions, current configurations and future-provider ports.
- Car: actual whole source carriers at their Reify origins, with separate
  inert and universal designated-execution clauses, and their original open
  fillings when the independent interface supplies them.

The event index set is all independently compatible original events; it is
not the events whose safety is already proved. S includes actual families
without presuming their validity and does not define the observation domain.
Ground values and arbitrary latent argument results stay in B_Hf at their
own endpoints; they are not replaced by f/g/drop. An actual compatible
history is shared by all fields, rather than chosen independently for each
membership test.

## 4. Direct source-clause expansion

### 4.1 What coinduction removes from the predecessor's obstruction

For f's capture inside g, the PhiV capture premise can refer to
`S.V(A_f,v_f,r_f,e)` at that same construction event. This is precisely
the coinductive hypothesis being tested, not an ordinary established
certificate. Lambda formation still needs every original independent
registration/profile/formation guard. No fixed sibling g is invented.

For each world in S.W, PhiW demands every binding's S.V/S.Car projection
and all joint registry, scope, authority and incidence guards. The actual
typed Return/rebind edge adds its exact returned tuple and retains old
projections. This gives a clause derivation conditional on those actual
guard/action inputs, rather than a completed JointWF assumption. In
particular q_x has no value before f entry Return, q_y has no value before
g entry Return, and q_z has no value before drop entry Return.

Thus the raw capture recursion is representable in the positive clauses.
The direct attempt no longer tries to obtain an ordinary f certificate
from x entry or to fit the fixed pair/Step bodies.

### 4.2 Drop's body and complete entry

Take an actual drop[a,d] and an arbitrary independently admitted drop
challenge. Its raw Value entry is receipt, designated Force, actual
z Return/rebind if present, then `Result(Name y)` and invocation return.
The captured y is the same actual result supplied at g entry, at A_y,
restricted to this original event. Its S.V premise comes from that
complete entry/background field; it is not z and is not a marginal witness.
Name/Return has a PhiT readout from that S.V premise, the same S.W world
and the original Return incidence. Generic Strict/Bind composes these
clauses at the original complete drop ports. Membership at a different
original A_drop still needs its actual complete comparison; it is not
identified with a printed Strict skeleton.

During a pending drop entry the suffix is exactly

```text
typed-rebind-z; Result(Name y); original-drop-invocation-return.
```

Force's arbitrary admitted requests, typed responses and raw resumes
retain that suffix and their actual current world. No z, body result or
Return is fabricated for a divergent Force. In a later independent use
of this same drop, its incoming carrier may actually return; the captured
y body then returns that same y. This later use cannot be omitted because
drop's source-diagonal argument below does not return.

This is a conditional positive clause expansion for drop's constructed
interface, carrying its independent guard, entry and comparison premises.
It is not ordinary drop membership or the full g/f proof.

### 4.3 G's delayed whole argument and the first recursive checking seam

The actual outer Call first returns this drop value, inertly forms the
whole carrier `t_c = Delay(Call(Name f,Name y))`, and invokes drop.
Only drop's designated argument Force executes the inner f-y computation
on the source diagonal. During that Force its unfinished drop suffix is
the one in §4.2; neither drop body nor z rebind has run yet.

For an actual inner event e, Name/Return can use f's original H_f/S.V
premise and the proposed S.W current world to form a **relative** callee
Return at A_f. The y Name carrier can similarly be expanded at its genuine
Reify origin using that same y/world, provided its independent license
and original whole-carrier checking clauses are established.

Now the owning Application rule requires the same actual f at checked
complete Function F_c, not only at A_f. This is the first recursive use
where a mere positive capture reference is insufficient. The original
checking-origin record does not supply the semantic action. An ordinary
pointwise inclusion has the form

```text
V*_A_f(v_f,r_f,e) -> V*_F_c(v_f,r_f,e).
```

Its antecedent is the conclusion still being constructed. It cannot be
applied to `S.V(A_f,v_f,r_f,e)`, and merely inserting the F_c tuple in S
does not give its Function readout. Step §6 avoids this issue by first
checking its independently ordinary captured-f certificate and unfolding
that ordinary certificate. This source has no such input.

An existing finite complete-Function checking proof could supply a lawful
route here. At the same original scoped assignment it must provide

```text
(D)  d in D_F_c(e) -> that SAME d in D_A_f(e)
(P)  o in P_A_f[S](d) -> that SAME decorated o in P_F_c[S](d)
```

with all provider decompositions, worlds, hard guards, actual inlet/receipt
preconditions, return/future ports and dependencies retained. (D) is fixed
independently of S. (P) must be derived from this check's actual local
proof constructors; truth of inclusion only at V* is insufficient. Then
the f source readout at its original interface can be tested on that same
challenge, and its entire positive observation family transported to F_c.
This is the ordinary complete comparison argument applied within a
postfixed proof, not a new source typing rule.

**Minimal unsupplied premise.** No actual finite checking derivation with
these original input and output maps is supplied for c in the frozen
f-y inventory or the selected exact pair/Step results. The inventory
explicitly leaves VIncl and WholeArgCompatible truth separate from their
origins. Source Generalize §3.2 supplies the grammar and requirement,
not this source's proof. At the very least (D) must transport F_c's same
whole-carrier admission to f's actual original entry interface I_x,
with its real receipt/path/context guards. It is needed before recursive
output typing; divergence does not make admission vacuous.

This is an unconstructed specified local checking premise, not a proved
false law or evidence of source rejection. If its actual finite proof is
available, the producer should expand that proof, rather than postulate
parametric checking for every S. Identity/conjunction/composition cases
permit direct positive lifting; nonpositive children retain their actual
equality/domain premises under Source Generalize §3.2(4). No blanket
monotonicity of VIncl is inferred from monotonicity of Phi.

The attempt stops at this seam. It does not complete g's carrier validity,
g's Function readout, f's first-call/annotation/final-call clauses, or
H_f replacement. Complete original interface identification/comparison,
background-domain correspondence and every independent guard/primitive/arm
premise remain explicit. None is absorbed into the displayed checking map.

## 5. Raw finite-return argument and its limited use

Within the same source expansion, inspect the raw structural branch under
the selected Value-entry and ordered Bind/Call equations. A finite completed
f invocation must finish its first `g 0` before continuing to the final
`g ()`. Finishing that g invocation must finish its Call of drop; drop's
Value entry must finish Force of the whole `f y` carrier before rebind-z
and Name-y Return. Thus any finite completed f invocation contains a
properly nested, completed invocation of that same actual f before its
own completion.

Choose a completed f derivation with the least finite number of raw
transition-rule applications. Its required nested f completion has fewer
applications, contradicting minimality. Hence this raw structural branch
has no finite completed f invocation. A completed structural g invocation
would require such an f completion, so it likewise has no finite Return.
This argument uses the unchanged code and strict Value-entry/ordered Bind
rules, not recursive semantic membership, a type query or a termination
assumption. A divergent or pending incoming carrier cannot create the
missing body completion. A control development that exits the invocation
without completing its remaining suffix is not that invocation's Return.

Its exact scope is the supplied raw source equations, conditional on their
faithful operational identification. It is not an execution/parse result
for the current compiler. It covers no independent whole-Call W/Z arm or
opaque provider alternative. Those can have different actual outcomes and
retain their own complete contracts.

This establishes why source-diagonal recursive result Return/rebind
premises cannot be fabricated. It does **not** license replacing original
result descriptors by bottom, identify body and invocation ports, prove
the int annotation's full local relation, discharge initial admission or
check arbitrary effects/pending/future envelopes. It also does not erase
the latent g/drop family or the later g call from the original source
rule program. Their interfaces/checks remain present even if this raw
structural execution cannot reach their later completed phases.

## 6. Precise obstruction, economy audit and next evidence

This is a materially different attempt from the predecessor's exact
constructor-fit audit: it introduces an event-indexed coalgebra, expands
world/result and drop clauses, and encounters source checking during
positive recursive use. Neither attempt resolves the same parent L4
premise. The generic relative lift and raw no-Return argument are useful
bounded reductions, not parent proof closure.

Apply the required proof-obligation-economy audit before another variant:

- A/B: valid accepted recursive membership, complete checked Call and
  ordinary nested inference remain necessary. They are not downgraded
  to an optional all-model characterization.
- Construction owner: the actual Application at c owns the complete
  same-value/whole-carrier checking origins and operand telescopes;
  recursive Lambda/installation owns f's original complete interface,
  captures and simultaneous world law. Source Generalize already retains
  those clauses and their event dependencies.
- D: reconstructing the check from a successful query, solved endpoint
  shape, numerical level, or a stored edge would lose evidence. Preserve
  the authentic finite local check proof/native constructor output when
  available. Retention alone still does not prove its semantic action.
- Method change required: expand that exact local check and original
  interface/entry law, then resume this coalgebra. Another pair/Step fit
  audit, a larger prefix checker assuming (D)/(P), or another renamed
  postfixedness target will not supply the missing premise.

**One next action:** the primary assigns the source-checking proof owner
the original Application c's finite complete comparison/whole-carrier
derivation, starting with (D)'s same-carrier map to actual I_x and deriving
(P) from its local constructors at the original scopes. Return its exact
shared assignment and genuine primitive/guard dependencies to the recursive
introduction owner. Do not silently select new interfaces or an inlet
restriction. The parent recursive owner remains responsible for H_f and
for the independent background/complete-interface and remaining source
clause obligations; the check packet cannot promote that parent gate.

## 7. Verification, runtime and frozen dependency packet

Performed bounded `cat`, `sed` and `rg` reads, one static coalgebra attempt,
the raw finite-derivation argument, SHA-256 snapshots and leased-file
whitespace/local-link checks. No compiler edits, tests, builds, parsing,
executable inference/probes, measurements, Git operations, child launches,
question-board writes or external communication. Lightweight read/check
processes only; at most four independent read commands batched, zero heavy
processes and zero inference samples. CPU/RSS were not instrumented; the
work stayed within the assigned 30-minute wall allocation.

Requested routing: normal gpt-6.1-sol/high leaf under the primary packet.
Observed worker identity: `/root/nested_f_postfixedness_proof_retry1`.
Effective model/effort runtime metadata: **unknown**. The inspected config
registers prover, defaults to gpt-6.1-sol/high for subagents, and omits prover
model/effort pins; these are configuration facts, not execution evidence.
No Astra, hot reload, delegation or independent review is claimed. The
yulang-proofs skill was applied under the explicit leaf-only assignment.

Frozen current semantic dependency SHA-256 snapshots, rechecked at handoff:

```text
657ccdf993aca04085de6857520d05bd26f207e5cf04146dcd98f39465c83540 notes/theory/2026-10-12-nested-recursive-l4-proof.md
3bcc290f0fab01f08272d83c358f491df377da46f2022412c176184533d9f872 notes/theory/2026-10-12-fy-complete-call-construction.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6 notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f notes/theory/2026-10-08-captured-call-closure-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0 notes/design/2026-10-08-contextual-function-membership-definition.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38 notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd notes/design/2026-10-08-captured-closure-constructor-definition.md
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389 notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

No dependency was written. Baseline-to-blob equality is the primary's
integration check; no Git read was performed. Unverified: original full
challenge/background embedding, all checking/primitive/guard/annotation
truths, complete local postfixedness, actual source admission/runtime,
effects/alternatives, native source-to-implementation bridge, qualifying
extrusion/intrusion, generalization and required principality. No stored
constraint activation or complete replay result is established.

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-nested-recursive-f-postfixedness-proof.md`.
- Baseline SHA supplied by primary: `988ef4ae1`.
- Changed dependency hashes: none between the before/after snapshots.
- Claim/review status: frozen unreviewed candidate coalgebra, conditional
  source-clause derivations and bounded raw-operational argument; original
  H_f postfixedness and parent gates OPEN. No source-qualified falsifier.
- Checks already run: static source/constructor reads, dependency hashes,
  whitespace/fence/local-link integrity; no executable compiler checks.
- Proposed checkpoint message: `research: expose nested f coinductive checking premise`.
- Shared-record deltas left to primary/curator: attach this direct attempt
  and its exact c checking dependency to the existing recursive-introduction
  owner; retain parent L4, complete Call and inference gates OPEN. No task,
  theory map, index, authoritative definition or question bundle changed.

Writes stop at handoff; independent review and integration remain primary-owned.
