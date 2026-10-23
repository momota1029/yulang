# R336 — finite K0 algebra and the definition-output obstruction

Frozen producer artifact: `R336-K0-ALGEBRA`, revision 1. Author:
`/root/r336_k0_algebra_prover`; no contributing descendants. Outcome:
candidate mathematics and source/native evidence, with an exact algebraic
counterexample to revision-2 D1 when its output is the native definition-root
component, and the bounded revision-3 repair check appended below.
This is not independent review, production authority, or full-theorem closure.

## Parent and frozen dependencies

The original parent remains the unchanged Yulang Simple-sub A/B, source/native,
catalog and full-language goal. The immediate parent is the frozen R336 D1:

```text
ValidK0(s) ∧ CompleteK0Construction(s,C_s)
∧ ρ ⊨ H(C_s) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ s : ρ(v_s) ! ρ(ε_s).
```

No quantifier, K0 form, witness hypothesis or ordinary inference operation is
removed here. In particular arbitrary finite symbolic effect valuations remain
quantified; finite witnesses do not imply finite witnesses for every cyclic graph.

| Frozen dependency | SHA-256 | Provenance |
| --- | --- | --- |
| `tasks/agent-loop/sprints/r336-k0-d0-d1-20261023-rev2.md` | `175057184a9eac3850cc7d697e5336fb2b478e5d8f96892a7411becb2e564737` | Luna `/root`, contract revision 2 |
| `notes/theory/2026-10-23-r336-k0-d0-d1.md` | `978dbcf56510dbcec52d51c4eae7e0ab33ea29e5305d944ee69fa1380aa97bb8` | Luna `/root`, parent proof candidate |
| `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` | user-supplied audit; individual author UNKNOWN |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | authoritative user inference policy |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` | compiler baseline below; individual authors not inferred |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` | same |
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` | same |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` | same |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` | same |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` | same |

Compiler baseline supplied by Luna: `17e57af2c4605d7084c7d76792b115674776bbe2`.
The audit's distinct baseline is `18d10b95942fbb8775b92542884e5a55860670bc`.
No Git operation was used to establish either baseline; current bytes above
were hashed directly. The audit §§4, 6, 9–10.3 and 12 and the frozen parent are
reused only for their stated construction/model premises. No historical hygiene,
FreshUse, Call, F1/FK1 or FieldTail theorem is used to certify this result.

## Independent algebra, without source or runtime premises

Use exactly the finite value-term grammar and the effect carrier
`P_fin(Ω)` fixed by D0. “Finite” describes each witness term/set; it does not
make the value carrier finite. The least preorder exists as the intersection
of all preorders closed under the displayed bounded-lattice and Function rules;
the universal relation is one such preorder. Its equivalent definition is finite
derivability from those rules. Quotienting by mutual comparison gives a bounded
lattice; no decidability, normal form or recursive-type interpretation is needed.

For effects, union and intersection preserve finiteness; inclusion is reflexive
and transitive. `EffectBottom = EmptyEffect = ∅`, so the pure interval forces
exactly `∅`. This argument applies to a row with that interval. It does not force
an unconstrained latent entry, return or invocation row to be empty.

Function is monotone on `Vᵒᵖ × Eᵒᵖ × E × V`. In explicit order:

```text
A' ≤ A, EA' ⊆ EA, ER ⊆ ER', B ≤ B'
  imply Fun(A,EA,ER,B) ≤ Fun(A',EA',ER',B').
```

Reflexivity follows from four reflexive premises. Composition follows by
transitivity in each port, reversing the first two. This proves the sufficient
variance rule. No converse/inversion, Function distributivity, optional-record
law or native propagation-preservation theorem is claimed.

To see the lattice axioms do not collapse `⊤V` into `Int`, interpret values in
the powerset lattice of four distinct base tokens, atoms as singleton sets,
joins/meets as union/intersection, and every Function as the whole token set.
Assign variables arbitrarily. Every algebra rule is valid in this model,
including Function variance, while `⊤V ≤ Int` is false. Therefore that
comparison is not derivable in the least preorder. This separation argument is
used below; it is not proposed as runtime semantics for Function.

## Endpoint and four-port correspondence

Write `V(e)` for the authentic `endpoints[index]` endpoint, and `E(e)` for
`positions[index].effect`. These are not uniformly the pair returned by the
occurrence-component query. The collector allocates a component pair for every
expression (`candidate_source.rs:1093`), then sets a parameter Name's `V(e)` to
`CandidateEndpoint::Parameter` (`1131–1137`). Its separately allocated Value
component has no alias edge to that formal (`1724–1764`).

The corresponding binder environment must map the exact `HirParameterId` to
the same formal-row valuation. `candidate_endpoint` translates Parameter using
`parameter_live_base + position` (`shadow_apply.rs:3925–3940`). Lambda body,
Apply operands and Group children use `endpoints`, including Name endpoints;
the Lambda recipe explicitly retains `endpoints[body_index]`
(`candidate_source.rs:2056–2061`). An induction at every allocated Name Value
component would be invalid, even though an induction at `V(e)` has the needed
Name premise.

Ordinary `CandidateInference::solve` enters `solve_mode(hir,false,false)`
(`shadow_apply.rs:1584–1585`). Its source collection passes
`candidate_values=true, candidate_graph_effects=true, scoped=false,
operation_v1=false` (`1823–1824`). Thus the effect-enabled branches below
apply. The pure-effect fallback is not a replacement construction for K0.

| Constructor | Positive Function children | Negative Function children |
| --- | --- | --- |
| argument Value | negative | positive |
| argument Effect | negative | positive |
| return Effect | positive | negative |
| result Value | positive | negative |

`term.rs:1230–1271` checks precisely these kinds/polarities in this port order.
Positive and negative occurrences of one row both interpret as its one `ρ`
value; signs determine their constructor position and constraint direction,
not independently selectable witnesses. Distinct raw rows or occurrences are
not identified merely because their valuations happen to agree.

For a K0 Lambda, annotation absence registers `FormalRole::Value`
(`candidate_source.rs:1100–1113`); no unit/record/formal-annotation action is
scheduled (`1274–1342`). The only inspected `formal_domains` insertion owners
are `candidate_record_parameter`, `candidate_unit_parameter` and
`candidate_formal_annotation` (`candidate_effect.rs:1563–1680`), all excluded
by the unchanged K0 contract. Thus `admit_lambda_fact` uses the negative
formal row, the positive `V(body)` endpoint, fresh entry/return Effect rows,
and includes both entry and body effects in return (`lib.rs:11557–11689`).
The admitted relation is

```text
Fun(ρ(formal), ρ(entry), ρ(return), ρ(V(body))) ≤ ρ(V(lambda)),
ρ(entry) ⊆ ρ(return), ρ(E(body)) ⊆ ρ(return).
```

Creation has both pure bounds (`shadow_apply.rs:3610–3619`). Given the body
induction hypothesis, these are exactly the frozen Lambda-rule premises.

For Apply, the recipe carries authentic operand endpoints and effects
(`candidate_source.rs:1820–1829`). `admit_candidate_fact` checks its source
registration against those operands (`shadow_apply.rs:3948–3971`), constructs
the negative demand with a fresh invocation row (`4085–4116`), and includes
callee/invocation effects in the application effect (`4207–4224`):

```text
ρ(V(f)) ≤ Fun(ρ(V(a)), ρ(E(a)), ρ(invocation), ρ(V(app))),
ρ(E(f)) ⊆ ρ(E(app)), ρ(invocation) ⊆ ρ(E(app)).
```

These are the frozen Apply-rule premises for arbitrary finite effects. For a
positive Function compared with that demand, the four variance premises are
`A_actual ≤ A_formal`, `E_actual ⊆ E_entry`, `E_return ⊆ E_invocation` and
`B_body ≤ B_result`. The native Function-child orientations at
`lib.rs:14800–14827` match those directions. Inspecting these children does
not prove the whole propagation algorithm preserves the independent algebra.

Finally, literals have **both** atom bounds and **both** pure effect bounds
(`candidate_source.rs:1558–1573`). Interpreting only the lower atom bound
would fail to match the frozen literal rule.

## Explicit nontrivial finite witness

Consider the authentic-shaped K0 constructor tree
`Apply(Group(Lambda(x,Name(x))), Integer("7"))`, with all occurrences distinct
and the Name resolving to that Lambda's parameter. This is a construction
schema following the inspected source constructors, not a claim that a test
or native runtime trace was executed.

Choose **any** finite `S ⊆ T ⊆ U ⊆ Ω`. Set `F = Fun(Int,S,T,Int)`.

| Row/endpoint | Assignment |
| --- | --- |
| formal `x`; `V(Name(x))` | `Int` (one shared formal row) |
| separately allocated Name Value component | `Bool` (unused; not the formal row) |
| Lambda Value; Group Value | `F` |
| Integer Value; Apply Value; definition-root Value | `Int` |
| Name, Lambda, Group and Integer evaluation Effect | `∅` |
| fresh Lambda entry Effect | `S` |
| fresh Lambda return Effect | `T` |
| fresh invocation Effect; Apply evaluation Effect | `U` (distinct rows) |

Literal and Name pure intervals hold. Lambda creation is pure, `S ⊆ T` and
`∅ ⊆ T`, and its Function inclusion is reflexive. Group forwards reflexively.
Apply demands `Fun(Int,∅,U,Int)`; Function variance establishes
`F ≤ Fun(Int,∅,U,Int)` using `Int ≤ Int`, `∅ ⊆ S`, `T ⊆ U`, `Int ≤ Int`.
Its outer effect edges are `∅ ⊆ U` and `U ⊆ U`. The annotation-free
definition link is `Int ≤ Int`. All rows in this construction schema have
finite witnesses, including the unused Name component. There are no extra
default-field, annotation or computation-formal rows in this K0 tree.

When `Ω` has two labels, for example `S={a}`, `T={a,b}`, `U={a,b}` gives
nonempty latent/invocation effects. The family is valid also for an empty `Ω`;
no particular labels or finite upper bound on `|S|` are imposed. This witnesses
one nontrivial shape and its whole finite-effect family. It neither establishes
all-source witness existence nor excludes cyclic K0 constraints.

## Historical revision-2 obstruction: body result versus definition output

The frozen parent leaves the symbol `v_s` insufficiently distinguished from
the native definition-root component. The native API explicitly exposes the
latter through `ConstraintBatch::root_value_component`
(`lib.rs:1823–1835`). `add_definition_root` allocates that distinct component
without equating it to the body (`1836–1858`). Ordinary authentic collection
uses `emit_candidate_source` (`1220–1243`). For an annotation-free Definition,
the final action is only

```text
Action::Link { endpoint: endpoints[body], target: root }
```

(`candidate_source.rs:2168–2171`). `execute_candidate_action` admits it as
the inequality `V(body) ≤ root` (`2423–2426`), not equality.

Take one authentic nonrecursive K0 definition whose body is the canonical
Integer literal `7`, with the empty outer environment and no annotations,
parameters, imports, local bindings or other forms. Its initial generated
relations, including the definition link, are exactly

```text
Int ≤ V(body), V(body) ≤ Int,
∅ ⊆ E(body), E(body) ⊆ ∅,
V(body) ≤ root_definition.
```

Assign `V(body)=Int`, `E(body)=∅`, and `root_definition=⊤V`.
Every displayed relation holds and every witness is finite. Under the native
definition-root reading `v_s=root_definition`, D1 would require
`∅ ⊢₀ 7 : ⊤V ! ∅`. Inversion on the frozen literal rule requires
`⊤V ≤ Int`, disproved by the separating algebra model above. No other frozen
rule concludes a typing for a bare literal. If `s` instead denotes the whole
Definition syntax, the frozen judgment supplies no Definition introduction
rule at all. Neither reading supplies the missing step.

Thus the original displayed D1 cannot be certified at the exposed native
definition output by the frozen proof. This is a counterexample to that
root-output interpretation of **construction** soundness, not a compiler
rejection, execution failure or counterexample to full Simple-sub soundness.
There was no native-run experiment; the evidence is the actual source
constructors plus the explicit model assignment. If `v_s` denotes `V(body)`,
this particular contradiction disappears, but choosing that different output
is Luna's authority decision. This artifact does not substitute that theorem,
add general subsumption or a Definition rule, weaken the literal upper bound,
or alter the source domain to evade the obstruction.

## Revision-3 amendment and bounded repair check

Before this artifact/handoff was frozen, Luna issued and authorized these new
frozen dependencies under the same two leases and original 700-second cap:

- Contract `tasks/agent-loop/sprints/r336-k0-d0-d1-20261023-rev3.md`, SHA-256
  `595ef83b5a0ac94e0dc57e1ce424e503132ab98b71464a709d4bdf903b724d2b`.
- Parent `notes/theory/2026-10-23-r336-k0-d0-d1-rev3.md`, SHA-256
  `e7ae95a9287586eb44628c45e3c4456be4d8a89ccf91b05110ad2f5591ee6b24`.

Both were read and hashed directly. Their author is Luna `/root`; the
Value-subsumption/root-interface repair is Luna's contribution, not an
independent review of this producer's evidence. Old revision-2 input bytes
remain historical dependencies, not the active claim. The old obstruction
above does **not** refute the corrected revision-3 claim:

```text
ValidK0(s) ∧ CompleteK0Construction(s,C_s)
∧ ρ ⊨ H(C_s) ∧ Reifiable₀(ρ)
  ⇒ ∅ ⊢₀ e_s : ρ(v_root) ! ρ(ε_body).
```

Revision 3 explicitly adds the independent rule
`Γ ⊢₀ e:A!ε, A≤V B ⇒ Γ ⊢₀ e:B!ε`, and requires the authentic
`v_body≤V v_root` Link in `C_s`. This rule depends only on the previously
fixed value preorder and preserves the exact effect. Repeated Sub steps
compose by transitivity; it adds no algebra axiom, runtime-success premise,
effect widening or claim that every row assignment has a witness.

Given the constructor induction at semantic body endpoint `V(e_s)`, satisfaction
of the inspected native root Link supplies
`ρ(v_body)≤Vρ(v_root)`. One Sub step therefore derives exactly the new
root-output conclusion. The root has no allocated Effect component, so the
effect remains `ρ(ε_body)`. In particular the old assignment now has the
valid derivation `⊢₀ 7:Int!∅`, then `Int≤V⊤V`, then `⊢₀ 7:⊤V!∅`.
Both literal bounds remain in the initial literal derivation and graph.

The earlier Function matching and arbitrary finite-effect witness are unchanged
under this extension. This check discharges the particular root-output bridge
obstruction conditionally on the expression induction; it does not independently
audit all K0 constructors, contexts or allocators in the new parent. No claim is
made that this producer proved the whole revised D1 or reviewed it independently.

## Parent application, TODOs and stop receipt

The algebra and four-port lemmas discharge the algebraic Lambda/Apply
matching subproblem at semantic expression endpoints. They expose the
definition-output step missing from revision 2; the authorized revision-3 Sub
and authentic Link repair that step as shown above. The parent remains OPEN
pending full coverage and fresh review. Full K0 source coverage, L0/all allocator cases, ordinary context
identity/no-Allowance, propagation N, model existence W, runtime M and Z/S0,
G-completeness, principality and full-language A/B remain unproved here.
Independent foreign-continuation quantifiers F1/FK1 are untouched.

`R336-K0-OUTPUT-1` — original request, now answered by Luna's revision 3:
adjudicate the exact output component and
source-judgment domain against audit §6 and native `root_value_component`,
`emit_candidate_source` and `execute_candidate_action`. Required input is the
frozen D0/D1 statement and these source bytes. Proposed output is an explicit
authority decision and, if needed, a versioned contract/theorem revision
before new proof writing. Falsifier for the present root-output D1 is the
literal assignment above. A repair must account for this assignment without
silently dropping the atom upper bound or importing runtime success. The
revision-3 repair passes this exact falsifier by the explicit Sub derivation;
fresh review of the combined claim remains Luna's next action.

`R336-K0-ENDPOINT-1` — owner Luna/integration: retain `V(e)=endpoints[e]` in
the induction and distinguish unused Name components. Falsifier: assign that
unused component `Bool` and its formal `Int`; no source-generated equality
licenses replacing the formal endpoint by that component. The witness above
contains this discriminating assignment already.

No production-code defect or safe implementation slice follows from this
research-contract obstruction. No implementation TODO is authorized here.
Fresh review belongs to Luna; this producer cannot certify the combined proof.

Checks: manual rule derivations, exact constructor/consumer reads and direct
SHA-256 checks. No tests, Cargo, compiler execution, executable probes, network,
Git, external contact, scratch files or descendants. Requested model/effort:
`gpt-6.1-sol` / `high`; observed model/effort: `UNKNOWN` / `UNKNOWN`.
Grant: at most 700 active seconds, no carryover; precise active duration is
UNKNOWN and the full grant may be charged conservatively. Work stops at the
frozen revision-3 artifact/handoff after the bounded amendment. Only this artifact and
`tasks/agent-loop/inbox/20261023-r336-k0-algebra-prover.md` are new paths.
Worker state on handoff: STOPPED; all writes stop after freezing that handoff;
no unresolved descendant leases. Review/integration pending, parent not closed.
