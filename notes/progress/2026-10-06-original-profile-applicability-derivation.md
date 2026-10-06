# Original profile applicability: source inventory and the signature-formation cut

Date: 2026-10-06
Baseline: `0a28c92cce9f469856b5f8776426bb6a2c53eb81`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: independently compiler-referee-reviewed bounded derivation; profile formation remains open
Claim class: exact bounded source-constructor inventory; conditional complete-profile
assembly; unresolved original-signature applicability/contribution formation
Semantic and implementation authority: none
Exclusive lease: this note only

## 1. Objective, dependencies and result

Construct the COMPLETE original applicable-position/profile judgment for
the approved nonrecursive source, continuing the source-profile/admission
construction's handoff:

```text
my apply f = { my step x = f x; step }
```

The source-to-profile route constructs every original binder, read, capture,
source Call and directional upper-introduction occurrence in this exact
component. It constructs one tagged directional introduction, its carrier
result lift, and the pointwise no-annotation policy. It does **not** construct
the independent signature-formation law whose inversion accounts for every
original applicable position and original contribution. Accordingly, neither
a complete singleton `Slots(beta)` nor a nonempty complete-row solution family
is concluded. No alternative language meaning is proposed.

The new reduction is the explicit separation of three inventories: source
nodes/exposures; original signature slots/contributions; transported receiving
incidences. Only the first has exhaustive source-constructor inversion here.
The precise missing last rule is specified in §5, including the forward and
reverse obligations needed to extend that inversion to the second inventory.

Governing clauses, read directly:

- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5: shared inferred contract, static `beta`, Q-independent formation,
  actual-role separation and still-open complete source judgments.
- [Directional decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: protect the original upper output; no lower backflow or automatic
  result traversal. Its user instruction governs; its formalization is Draft.
- [Nested-block meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: exact sequential binding, returned step value and same outer capture.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3,6–9: independently interpreted whole-tuple primitives, conditional
  source grammar, bounded allocation-view class and retained Option A/2 extras.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–9: source constructors, actual entry, complete invocation, independent
  descriptor/inclusion obligations and all-challenge comparison law.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6: original profiles supplied by elaboration; typed transport introduces
  neither a new boundary nor an unrelated nested incidence.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–4: B ordering and original slot invocation view; existing callable
  introduction and entry remain its own.

Reviewed research dependencies are the source-call, joint-source and SV
constructions listed in §9. Their conditional envelopes remain premises.
The frozen profile/admission handoff is independently reviewed research,
not source semantic authority. Its hash in the assignment was `bb29863…`;
the primary explicitly replaced it with `add4197…`, identifying only completed
review/status metadata changes and an unchanged derivation/dependency body.
No conclusions below depend on its old unreviewed header.

## 2. Hypotheses and one original row

Fix the selected resolved source graph `C` and its original binder tree.
Let `sigma_f` denote the outer formal's binding scope and `sigma_x` the step
body scope importing that same outer binding. Use one joint
`xi=(nu,K,D)` with every original provider, world, continuation, role/entry,
constraint and dependency incidence retained at those scopes. Logical local
witnesses stay beneath their original rigid dependencies.

The reused constructor premises are:

```text
H_source: approved exact nested-block core correspondence and lexical resolution
H_core:  ordinary parameter/Name/Result/Lambda/Bind/Call rules at original scopes
H_call:  reviewed unsolved complete Function-demand and ElimOrigin constructor
H_seed:  selected unannotated higher-order formal's original protected-variable seed
H_dir:   selected upper-output introduction and no-backflow law
H_view:  independent typed correspondences for an original realization, when used
```

`H_call` emits independent semantic obligations; it is not their successful
solution. `H_view` supplies transport of a given row; it cannot supply original
profile formation. There is no assumption that current production accepts the
source, no Oracle-derived premise, and no complete Function/profile witness
hidden in `H_source`.

## 3. Exact source inventory and constructive derivation

Label the approved core term once:

```text
L_A = lambda(d_f,
        B_s = bind(d_s,
          R_s = result(L_s = lambda(d_x,
            C_fx = call(R_name_f = result(N_f = name d_f),
                        R_x = result(N_x = name d_x)))),
          R_out = result(N_s = name d_s)))
```

There are 11 constructor occurrences: two Lambda, one Bind, four Result,
three Name and one Call. There are three binders and three resolved reads.
`L_s` has exactly the one free binding `d_f`; `d_x` is local, and `d_s` is
read outside `L_s`. The final read of step is not a Call. No operation,
annotation, explicit elimination, recursive reference or raw resumption node
occurs in this component. These counts refer to this approved core term,
not runtime activations or unknown complete type children.

| Original occurrence | Constructor consequence | Profile-formation consequence available here |
| --- | --- | --- |
| `L_A,d_f` | Before body generation, `d_f:Value(A_f)` with its ordinary Value-entry skeleton | Selected binder absence supplies seed `k` on the still-inferred shared `A_f`; it does not give all applicable positions |
| `L_s,d_x` | Before step body generation, `d_x:Value(A_x)` | No independent higher-order upper exposure of `x` occurs in this source; solved latent shape supplies none |
| Capture of `d_f` in `L_s` | Same lexical root, endpoint and inherited packet at `sigma_x` | Typed identity transport; no new beta origin or public closure-field exposure |
| `N_f,R_f` | Return the same captured provider; ordinary source interface `Value(A_f)` | Preserve `k,R_f` and original scope correspondence; no new seed on Name lookup |
| `N_x,R_x` | Actual returning Name computation `J_x` on rebound `A_x` | No whole-carrier domain inferred from printed `Comp(empty,A_x)` |
| `C_fx` | One dependent COMPLETE demand `U_u`, original upper occurrence `u`, `ElimOrigin` and complete output address `p_out(C_fx)` | One designated upper-output occurrence `p0=outEff(U_u)` |
| `R_s,B_s,N_s,R_out` | Inert local closure creation, sequential bind of its actual result and return of step | Retain captured packets; these constructors create no additional source upper exposure of `f` |

Write the shared inferred contract root as `R_contract`, retaining the
original `R_f` contract identity used by the dependencies. It is distinct
from the syntax occurrence `R_name_f = result(N_f)` displayed above.

Registration and the one same-root captured read yield:

```text
Seed(k,d_f,A_f,R_contract,sigma_f)
beta = (d_f,R_contract)
SourceUpperUse(u,A_f,U_u,sigma_x)
ProtectedVarAt(k,A_f,sigma_x,u)   [original scope transport of the same seed]
-------------------------------------------------------------- H_dir
a0 = (k,beta,u,sigma_x,p0),  NewProtection(a0)
```

Keep the original source checking conjuncts on the same row:

```text
VIncl(A_f,U_u;xi)
WF_Dec(U_u;xi)
WholeArgCompatible(J_x,CarrierContract(U_u);xi)
CompleteCallImage(J_f,Delay(J_x),U_u,actual_entry,consumer,world;xi)
    fits the original Comp(E_c,A_c)
TypedCallCert_Dec(C_fx,U_u;xi)
```

There is no need to solve these conjuncts to construct `a0`; there is also
no implication from their emission to satisfiability. An actual supplied
callable keeps its introduction role, entry and lower-origin packet.
The source-specific `NonHandlerFormal` refinement preserves the original
seed consequences; it produces no annotation grant.

**Bounded source-exposure result.** Within `H_core/H_call/H_seed/H_dir` for
this exact graph, the catalog of directly derived beta upper-introductions
is exactly `{a0}`. Proof: the only Call node is `C_fx`; its callee read is
the sole read of the seeded formal. All other last rules in the 11-node
inventory are parameter registration, inert introduction, identity lexical
transport, Return or Bind. They cannot derive another original source upper
occurrence. Applying Dir-Protect to this sole exposure produces `a0`.
This is constructor-relative source-exposure completeness. It asserts no
exhaustiveness of all independently interpreted signature-slot rules.

## 4. Position sorts: origins, slots and receiving images

| Address or index | Original source justification | What it cannot establish |
| --- | --- | --- |
| `a0=(k,beta,u,sigma_x,p0)` | Same original seed and complete upper-output occurrence | Every contribution governed by the COMPLETE signature, or every static slot |
| `p0` in `U_u` | Function elimination's complete invocation effect port | Empty outward support, actual role, receipt or capture grant |
| `argument.result.(u,p0)` at apply receipt | Outer source Value-entry result prefix; reviewed SV dependent lift | Protection at `argument.effect` while manufacturing/forcing the factory carrier |
| `(u,p0)` on rebound f | Actual Return/rebind removes exactly the known result prefix | A rebound f before the carrier actually returns |
| Captured/read f occurrence | Same typed binding, capture and read correspondences | A new source slot, new receiver beta, or a public latent step-result mark |
| `p_out(C_fx)` | `ElimOrigin` maps the original upper complete-call position | A map to unrelated result-latent paths or the provider's own lower output |
| Other dependent signature paths | Only an independently supplied signature/exposure constructor could license them | Existence or applicability from solved `A_c` shape alone |

Repeated actual invocations and raw resumptions can produce many receiving,
view and observation occurrences for the one original origin. Conversely,
several origins can refer to one static slot. Thus an origin count and a
transported incidence count do not determine `|Slots(beta)|`.

The incoming factory carrier, apply's body return of step, step's own
incoming carrier, and the inner returning Name `J_x` are distinct complete
computations. Their entry/control dependencies remain jointly scoped.
Keeping these distinctions removes no original provider or world predicates.

## 5. First missing constructor, with its exact coverage interface

Attempt the original judgment at the shared inferred contract:

```text
C,d_f,R_contract,U_u,beta,original scope tree; xi
    |- OriginalSignatureFormation(S_beta,Gamma_beta,Contrib_beta)
```

This names the missing independent judgment, not a definition by this
note's emitted catalog. Its output must have the following source meaning:

1. `S_beta` is the complete original static applicable-slot inventory;
   its dependent position identities survive generalization/use.
2. `Contrib_beta` independently relates each slot/position to the original
   contribution it governs in the complete upper contract. This includes
   complete invocation/whole-carrier dependencies; it is not outward support.
3. The original `a0` has a source-justified slot/contribution correspondence.
   The constructor must specify whether distinct witnesses share a slot;
   equality of endpoints does not decide this correspondence.
4. For **every** original beta-owned applicable slot/contribution witness,
   inversion gives its original introduction/exposure constructor, operands,
   seed when required, scope and signature-position correspondence. All
   other formation cases must be specified and accounted for. A blanket
   absence assertion about unnamed cases is not a proof.
5. For every such licensed original witness, forward construction returns
   its applicable slot/contribution at those same scopes. Inherited provider
   and result packets retain their own origins and cannot become beta-owned
   merely by arriving at the same typed path.
6. Both directions concern the same whole row `X` containing original
   `xi,U_u,providers,world` and all independent semantic obligations. They
   must not choose a row or signature completion separately for each slot.

Items 3 and part of 5 are constructed for `a0`. Items 1–2 and exhaustive
item 4 are not supplied by the approved direction or the reused constructors.
The first missing last rule is therefore **original inferred-signature
applicability/contribution formation and its inversion**, after registration
and complete upper-demand formation, before full profile assembly or SV
receipt instantiation. This is a mathematical construction gap. No claim is
made that an additional user semantic vote is necessary to fill it.

### Why the available last rules cannot discharge it

| Attempted last rule | Available premise/conclusion | Exact unchanged premise |
| --- | --- | --- |
| Dir-Protect | One justified seed/exposure gives its output occurrence | Does not classify every original applicable slot/contribution or supply its inversion |
| Lambda/interface synthesis | Builds body/result skeleton and unknown complete obligations | Profiles/typed paths are retained or supplied; complete invocation admission is not the bare body result |
| Name/Capture/Bind/Result | Typed identity/result correspondence on existing packets | Needs the original source packet/profile that would be transported |
| Typed-boundary introduction | Source slot plus supplied original profile introduces receiving boundary | Assumes the profile inventory; cannot construct it from the received type's solved shape |
| Callback B | Known instantiated slot/profile selects literal context before synthesis | Takes `Slots(beta)` as input; this exact step lambda is created locally rather than directly supplied to a known callback literal slot |
| `VIncl/CIncl` or whole Function comparison | Checks original whole interfaces under independent admission | Checks do not allocate source slots, introduce protection or enumerate their source origins |
| Allocation coverage (§6 of source contracts) | Conditional output-contributor coverage inside a supplied non-coverage kernel | Finite `V_alloc` alignment is an extra premise, not exact original-profile licensing over every permitted view |
| SV erase/reflect | Exact selected fragment on independently typed original rows/completions | Such complete rows/completions exist and have independently complete inventories |

This last-rule derivation cannot be closed by inducting again on the same
11-node graph: that induction has already exhausted the direct source
exposures, while the necessary signature-formation rules remain unspecified.
No second equivalent toy model or larger probe was attempted.

## 6. Conditional theorem and whole-row nonemptiness residual

**Conditional policy/coverage theorem.** Assume an independently interpreted
OriginalSignatureFormation constructor satisfying all six obligations of §5
for a fixed original row `X`, and satisfying the governing no-annotation
policy. Then the beta-owned profile is uniquely assembled on its complete
applicable inventory: every licensed position is protected, with no concrete
grant from beta; outside that inventory beta supplies no incidence. Its
forward/reverse coverage has the same original witnesses and scopes as the
formation constructor.

Proof: traverse its formation derivation, preserving the independently
identified slots/contributions. At every licensed unannotated position the
approved policy fixes protection and absent grant. Formation inversion covers
every beta-owned position; forward formation supplies each licensed one.
Typed transport then preserves the original tags by indexed relational image.
Any other beta-owned profile satisfying those same inventory/policy premises
agrees pointwise. Inherited provider/result packets are separate inputs and
are retained without modifying their grants. This is a conditional theorem,
not a constructor of its own formation premise.

Even after that cut is discharged, producing an actual complete witness
requires one original row satisfying all generated constraints, all descriptor
and provider checks, independent import/world admission and every permitted
finite development. For a Function this includes every independently admitted
whole carrier/current-world challenge and the matching complete invocation
observations, retaining Option A/2 production-only members. A trace on a chosen
identity provider is not those universal predicates.

The present result consequently establishes neither
`exists X. OriginalSignatureFormation(X) and CompleteOriginalRow(X)` nor a
nonempty `Completions(delta;xi,w)`. It does not refute either existence claim.
It leaves all-view principality, production admission/observation inclusions,
recursive formation and generalization lifecycle unverified.

## Independent review

A compiler referee reviewed this frozen derivation and its direct input
hashes; no blocking, major or minor finding remained. The review confirms the
exact 11-node constructor inventory, the single justified upper-output
introduction, and the distinction between direct source-exposure completeness
and a complete `Slots(beta)` inventory. It accepts the stop at independent
original-signature applicability/contribution formation. Complete-row
nonemptiness, universal carrier/world validity, principality, and production
inclusions remain open. This does not close the opening objective's full
profile-construction demand.

## 7. Rule-grounded failure discriminators

These are derivation mutations, not executable search results:

- Equate `{a0}` with complete `Slots(beta)`: the signature correspondence and
  exhaustive original-formation inversion in §5 disappear from the proof.
- Mark an additional latent result because `A_c` solves to Function/Thunk:
  no original seed/exposure/contribution constructor supplies that mark.
- Paint the provider lower output because its endpoint equals `p0`: distinct
  original occurrences are collapsed and the selected no-backflow is violated.
- Paint `argument.effect` with the prospective result incidence: the known
  result-prefix map supplies no such edge.
- Regard a capture image or later receiver view as a new original slot:
  transport is substituted for introduction, contradicting typed-boundary §6.
- Prove complete-row validity from one silent identity trace: universal whole
  carrier/world and pre-dispatch routing obligations remain unchecked.
- Solve each slot independently and join witnesses: original `xi`, provider,
  operation/continuation and binder correlations are lost.

Each mutation fails at a named source or proof premise. None constructs an
Authority-consistent additional latent-slot countermodel, an actual rejected
source example or a production acceptance result.

## 8. Checks, independence, resources and recommended next action

Method: bounded static source construction and last-rule inversion. Reference
meanings came from the named source clauses; no production output or Oracle
behavior was read or run. The derivation shares the reused source-kernel,
Call and typed-transport assumptions with its dependencies, so it is not an
independent validation of those source rules. The new conditional theorem
explicitly assumes independent signature formation, rather than defining that
formation to equal the emitted catalog.

Commands: bounded `cat`/`sed`/`rg` reads, `sha256sum` on the 11 direct inputs,
and a note-only whitespace/link/dependency check recorded at freeze. One initial
read-only `git rev-parse HEAD` confirmed the packet SHA before the no-Git-command
constraint was applied strictly; no Git mutation occurred. No test, build,
solver, executable model, enumeration or Oracle run was performed. No seeds,
ranges, numerical case coverage or runtime mutations apply. Constructor
coverage is exactly the 11 nodes, one capture, one source Call and one derived
directional introduction described above.

Resource budget consumed: one lightweight shell process at a time, no Cargo
or heavyweight process, no output/log files beyond this lease, no children.
Commands completed without a timeout; aggregate CPU, peak RSS and total
wall time were not measured. Some initial combined captures truncated;
the relevant clauses used in the proof were reread in bounded section captures.
This is a bounded search of the assigned sources, not a claim that no possible
original formation law exists elsewhere or can be derived with further work.

Recommended next action: assign construction/review of the independent
OriginalSignatureFormation law at this exact nonrecursive root, requiring the
§5 forward/inversion obligations and original whole-row scope. Use the source
catalog as its constructor input. A singleton output, source-only membership
restriction or larger support checker cannot discharge that assignment.

## 9. Frozen dependencies and commit packet

| Direct input | SHA-256 |
| --- | --- |
| `notes/progress/2026-10-06-source-profile-admission-construction.md` | `add4197a6e4e047db7d71d746c97b771e03ffad83be6aa75cb204c20ad350ff2` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-directional-joint-source-judgment.md` | `fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1` |
| `notes/progress/2026-10-06-directional-source-view-instantiation-construction.md` | `462d792e518409199f77bb20a41aaa54d64898fe30363f98f0afff7ab3f805e3` |

Exact leased/changed path:
`notes/progress/2026-10-06-original-profile-applicability-derivation.md`.
Baseline: `0a28c92cce9f469856b5f8776426bb6a2c53eb81`.
Changed dependency: primary-authorized profile/admission metadata replacement
`bb29863cb679ef5b286ef8432f828a72f23efae1a466da8c2458d33a5622bcd7`
→ `add4197a6e4e047db7d71d746c97b771e03ffad83be6aa75cb204c20ad350ff2`.
Other listed hashes unchanged against the reused recorded dependencies.
Review status: independently compiler-referee-reviewed bounded derivation;
no main P/A closure or production authority.
Checks already run: direct source clause reads, constructor/position count,
last-rule/quantifier audit, dependency hashes, note-local integrity check.
Proposed one-line research-checkpoint commit message:
`research: derive original profile applicability formation cut`.
Shared-record deltas intentionally left for the primary/curator: record exact
source-exposure inventory separately from complete signature-slot/contribution
inversion; preserve complete-row nonemptiness and Option A/2 admission gates
as open. No shared task/index/theory/authority file was edited. Integration
baseline/dependency equality and any Git operations belong to the primary.
