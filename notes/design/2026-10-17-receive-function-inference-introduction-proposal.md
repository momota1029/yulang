# Candidate source inference introduction for the original c2 Function view

Date: 2026-10-17
Status: unselected decision-ready source-rule proposal; preservation proof pending.
Scope: one complete inferred Function description at the original `g(Unit)` Call of the contracted `receive` route.
Author: Luna, under sprint `receive-function-introduction-proposal-20261017`, revision 1.
Semantic / implementation authority: none.

## 1. Original obligation and proposal boundary

The original source is unchanged:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

The target is the one Call-introduced complete Function description `F2` at
its original result-binder scope `sigma2`, dependency telescope `Delta2`, and
shared `xi=(nu,K,D)`. The original theorem still quantifies over every
`alpha`, actual provider/decomposition, compatible punctured context, current
world, pending response/raw continuation, and finite future development. The
displayed `alpha+` only contracts this one Call's type shape.

The reviewed source audit shows that initial Call allocation and its symbolic
ReceiveSchema do not construct the complete descriptor. This proposal
specifies a candidate source introduction and the exact point where it must
map into an existing complete Function interpretation. It does not promote
that map to a theorem or select a new meaning. The accompanying preservation
packet is authorized to test the clauses, not to treat them as adopted.

## 2. Existing selected constructor and the missing inputs

The current selected complete Value-entry constructor is
`Strict(I, formal:A, R, IF)`, fixed by the captured-closure definition §§1–2
and its selected constructor record §§3.1–3.2. It constructs one complete
dependent `ContextualFunction(Pure, ValueEntry(I), ...)` from an independently
specified whole-carrier inlet `I`, dependent body descriptor `R`, and complete
entry/return/future interface `IF`. It retains receipt, Force, actual
Return/rebind, body invocation, original return, every pending raw handle and
suffix, and all independent future/extra-arm contracts.

This is a real constructor in the existing universe, but its selected scope
is actual Pure/Value-entry closures. It does not produce `I`, `R`, or `IF`.
At original c2, `g` is a result binder from an arbitrary actual first Call;
the selected source facts do not establish that `g` is a Pure Value-entry
closure. The Unit argument cannot determine its actual role or entry. Directly
setting `F2 = Strict(I2, g, R2, IF2)` would therefore either assume the absent
role fact or move the missing formation work into the chosen inputs.

The selected source Call-interface rules do provide IF-Insert/IF-Use
incidences when original declarations and uses exist. Native signature rules
provide the selected support/license/profile constructor from its actual
primitive, annotation and world premises. Neither package alone supplies the
complete descriptor interpretation or the missing input meanings at c2.

## 3. Candidate source judgment

The proposed judgment is a source-generation rule, not a successful-checking
predicate:

```text
Resolve(C, q); SourceArg(C, q, J_a, A_a);
SharedComponent(C, q, role-entry roots, source scopes, xi);
CallInterfaceGraph(C, q); OriginalProfileGraph(C, q);
LocalSourceLaws(C, q)
---------------------------------------------------------------- Gen-CallView?
C; sigma2; Delta2; xi |- q : CallView(F2, E2, beta2, Slots(beta2))
```

The question mark marks this as a candidate rule. Its premises are concrete
source objects and independently specified local constructor laws, not
`WF_Dec(F2)`, complete F2 fields, a desired descriptor equality, actual
membership, successful comparison `Q`, or prior execution. `SourceArg` is
the source derivation for the actual argument occurrence; it does not equate
the descriptor's whole-carrier domain with the one carrier observed in a
particular run. `SharedComponent` comes from declarations/definitions/uses
and retains role and entry as a relation on one shared inferred interface; it
does not select an actual provider role from argument shape. `CallInterfaceGraph`
and `OriginalProfileGraph` mean the selected source-owned IF and native
signature incidence constructors applied to their actual source occurrences
and their local premises, not arbitrary completed field packages.

The generated open tuple has these source outputs:

1. **Original description identity and telescope.** `F2` is the single
   existing descriptor occurrence allocated at `q`; all field declarations
   retain `sigma2,Delta2`. Captured/imported established contracts remain
   fixed. No new scope is chosen to make a field well-formed.
2. **Whole-carrier inlet source.** The argument derivation contributes its
   actual source endpoint, source path and typed maps. A complete inlet
   relation must be generated from the applicable source constructor and
   independent carrier-admission laws. The source argument's one returned
   carrier is only one instance; divergent, requesting, resumed and other
   independently admitted carriers remain in the original challenge domain.
3. **Role and entry relation.** The shared component graph relates all
   declarations, definitions and uses at original positions. Any still-open
   role/entry choice stays relational and jointly scoped. The candidate may
   not turn `Unit` into Pure, ValueEntry, or Handler evidence.
4. **Call interface and profile.** IF-Insert/IF-Use and the selected profile
   constructor contribute only their actual insertion/use/slot/path/license
   incidences. All original `beta2`, `Slots(beta2)`, typed `Flow`, owner and
   receiver relationships are retained at their own source scopes. Missing
   original clause inventories or primitive/profile laws remain explicit
   premises of those local constructors.
5. **Complete challenge and observation fields.** Their domains are fixed
   comparison-independently by the approved complete Function and
   punctured-context meanings. The pending `Q` cannot create, restrict or
   complete them. Their descriptor-local clauses must be interpreted on the
   same whole provider/observation tuple and original `xi`.
6. **Open source constraints.** Emit the ordinary unsolved component and
   source-use constraints before satisfiability. Keep source lineage,
   residuals and all dependent maps in one joint relation; never select
   independent per-port witnesses.

These outputs are not a claim that their source laws or descriptor
representation currently exist. The central candidate obligation is a single
joint representation at the original F2 occurrence:

```text
Gen-CallView outputs (I2, role/entry2, R2, IF2, E2, beta2, Slots2)
  -- one existing descriptor constructor and its proved local embedding -->
WF_Dec(F2; xi) and the exact projected field equations at F2.
```

No separate descriptor can be chosen for each field or each challenge. If
`Strict` is applicable only to a source-proven Pure/Value-entry subset, its
theorem remains available on that subset but cannot serve as the general c2
rule. The generic existing descriptor predicate `DescMem` cannot be cited as
an embedding theorem: source-contract §2.2 calls active interpretation an
additional hypothesis, and the source-base realization uses local descriptor
typing premises.

## 4. Relation to approved production meaning

The candidate retains the approved Option A complete typed-observation basis
and separate comparison-independent admission. It retains Option 2: an
observation need not carry a source-constructor witness, provided it meets the
independently fixed complete descriptor and hard-envelope conditions. No
source-only `P_ref` becomes production membership, and no W/Z grammar is
selected here.

For a future embedding proof, source-generated clauses can be retained as
ordinary conjunctive constraints on the same complete typed tuple. They may
not filter actual challenges by provider success, erase an independently
licensed non-source observation, or replace the descriptor's existing
membership. An embedding statement must account for both sides: every
generated tuple is interpreted at the original incidence, and every tuple
admitted by the selected descriptor universe remains governed by its complete
guards and Option 2 alternatives. The exact law that makes these equations
true is still open. Stating the obligations does not prove them.

## 5. Candidate bridge alternatives and consequences

These are design alternatives, not selections:

| Candidate | Added rule | Consequence for original c2 |
|---|---|---|
| **Existing-constructor reuse** | Instantiate `Strict` only when the original source component independently derives its `Pure,ValueEntry` role, complete `I/R/IF`, and all local guard/transport laws; prove the joint map at `F2`. | Reuses an already selected complete constructor without new semantic meaning. Current c2 premises do not establish the role or complete inputs, so this route cannot yet derive `WF_Dec(F2)` and cannot restrict c2 to such providers. |
| **Role-indexed CallView bridge** | Add a source-local constructor mapping the complete relational CallView output above into one existing descriptor while retaining every actual role/entry arm and Option 2 observation. | Could address arbitrary source-typed call results without guessing an actual role, but the source/descriptor embedding clause and its exhaustive guards must be specified and shown to respect the existing universe. Any different behavior needs explicit adoption. |

The first route is a valid constructor specialization but not a proof of the
original c2 premise. The second is the bridge under investigation, not a new
carrier declaration hidden in the word “view.” If the existing descriptor
universe has no constructor satisfying its equations, the exact missing
meaning and observable difference must return to user adjudication. Neither
route licenses compiler code before a selected rule and its source/consumer
correspondence are established.

## 6. Preservation obligations for the bounded proof lane

The preservation author receives the frozen clause set and attempts:

1. source-order and scope correctness for every declared field, including
   `sigma2,Delta2` and the distinction between Shared, Desc, ViewLogic,
   EventField and EventProof records;
2. joint `WF_Dec(F2;xi)` and field equations using the one named existing
   constructor, with no opaque whole-F2 field premise;
3. preservation under the selected legal source substitutions/grafts,
   Generalize and use-time instantiation, retaining actual event keys,
   fixed imported/one-shot dependencies, shared binder witnesses and current
   challenge domains;
4. application at the original c2 tuple with the remaining obligations
   classified separately.

If one of these requires a missing local source or descriptor law, freeze that
exact first law and its owner. The author may not silently add a premise,
select an alternative, prove only one chosen provider, or narrow the original
domains. A conditional preservation result is useful but is not a selected
semantic rule, source/native `T`, production conformance, or parent theorem.

## 7. Exact parent application and still-open gates

The previous reviewed packet at artifact SHA
`7cb867df64f1d931b1667f33a6c323448d687c5d0d7fdcf9bac7535577f72590` already
preserves the original A1, F2 and xi. This proposal adds only the candidate
formation clauses above.

Even if the bridge establishes `WF_Dec(F2;xi)`, the following remain
independent obligations:

- actual-provider membership and full `VIncl(A1,F2)` over every A1 value;
- whole-carrier inlet compatibility for every original challenge;
- complete invocation-image `CIncl` into the original c2 result descriptor;
- enclosing Bind image, source residual, joint world/import and profile/path
  joins;
- the original universal-alpha parent, all independent contexts/providers,
  current worlds, responses, raw continuations and future developments;
- source `T`, anchored native MODEL, production Option 2 conformance,
  principality and cutover.

No actual c1 return, selected provider trace, comparison success, Unit-based
role inference or new A1/xi is used. The result of this packet must identify
what follows at the exact original c2 incidence and leave every unproved gate
OPEN.

## 8. Direct dependency hashes

Contract revision 1 pins the exact current bytes of all governing inputs. In
particular the selected `Strict` constructor is pinned both through its
authoritative scope document and the current selected producer record; the
producer's historical frozen theorem body hash is also retained there. No
Git-history reconstruction is needed to use the current reviewed selection.

This proposal is unselected. Any later correction to its candidate clauses
requires a new proposal revision, a fresh proof against that revision, and
independent review of the resulting frozen bundle.
