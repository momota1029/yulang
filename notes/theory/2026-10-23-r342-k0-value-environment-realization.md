# R342 — K0 finite-return value and environment realization

Status: **frozen producer candidate, revision 1; independent review required**.
Assignment `R342-K0-VALUE-ENVIRONMENT`; sole author
`/root/r342_value_environment_prover`. This is a bounded hand derivation and
source/native correspondence argument, not independent certification,
machine checking, a whole M theorem, or production authority.

## 1. Parent, quantifiers and result

The parent remains the user-directed audit's full Yulang2/Simple-sub
source/native theorem and original A/B, with its original quantifiers and
accepted source domain. The immediate application is audit §§4, 6 C/M and
10.3: supply the actual-value and captured-environment premises of R340's
authentic Value-entry prefix. R341's accepted S0 implication keeps its exact
four premises and supplies independent source typing only when those premises
are separately available. Neither R341 nor R340 supplies runtime success.

The candidate result covers **all seven authentic K0 expression forms**:
literal, parameter Name, Value Lambda, Apply, else-complete If, Group, and
binding-free Block/StatementBlock. For every independently typed expression
and realized lexical environment at an authentic reachable evaluation boundary,
every finite evaluation segment that actually reaches its matching value-return
boundary has an independently typed source value related to that exact runtime
handle. There is no existential assertion that such a segment exists.
Function canonical form follows from the actual independent value derivation,
including subsumption and arbitrary finite joins/meets. The same argument and
capture witnesses give the exact environment at R340's body entry.

This result concerns representation and independent source-value typing. It
does not interpret the native Function ports as complete runtime receiver,
result or future interfaces. Normal return, result/future-port realization,
effect/continuation preservation, progress, unavailability exclusion and full
M remain OPEN. No F1/FK1 or foreign-continuation quantifier is discharged.

## 2. Frozen inputs and authority

Contract revision 1, baseline `research/simple-sub-intrusion` /
`ab58f80b7652dd26c75c1da293cf3b1ff33a3938`. No Git command was used.
All following byte pins were checked before this candidate was written.

| Input | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/r342-k0-value-environment-realization-20261023.md` | `deffbf0301cef182a208420856804896a412f51a4adc14d94bafc96621d98b64` |
| User audit, `docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` |
| R336 rev4, `notes/theory/2026-10-23-r336-k0-d0-d1-rev4.md` | `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R339 D3, `notes/theory/2026-10-23-r339-k0-machine-call-simulation.md` | `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666` |
| R340 proof, `notes/theory/2026-10-23-r340-k0-apply-continuation.md` | `7ae75ef26d6bfa441989e9655dda89fbed2927d0061f5d8445246d587a0d7737` |
| R340 final source census, `notes/theory/2026-10-23-r340-k0-machine-continuation-source-census.md` | `de3902d834a68f0d4f5b269f4bddac7d900d44bfe8dc118b05b451372cf24078` |
| R341 proof, `notes/theory/2026-10-23-r341-k0-source-constraint-retention.md` | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` |
| Luna's R342 source census, `notes/theory/2026-10-23-r342-k0-value-environment-source-census.md` | `18a4eef622ee8feacc8db48d4360321fdcbd8d5f330636866705f42b8551b1b5` |
| `tools/inference-playground/src/runtime/machine.rs` | `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840` |
| `tools/inference-playground/src/runtime/program.rs` | `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0` |
| `tools/inference-playground/src/runtime/dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |
| `tools/inference-playground/src/runtime/literal.rs` | `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f` |
| `tools/inference-playground/src/runtime/receiving.rs` | `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551` |

Use exactly R336 rev4's finite Value algebra, least bounded-lattice preorder,
four-port Function variance, finite Effect subsets, independent D0 rules and
authentic K0 membership. No distributivity, recursive type interpretation,
optional-record transitivity or general Effect subsumption is added.
`DecodedString` is not an additional standalone K0 constructor. All exclusions
in R336 remain, including Comp formals, local bindings, imports/other roots,
annotations, operations, handlers, members and operators. No constraint
generation, accumulation, propagation, levels, extrusion, qualifying intrusion
or generalization operation is changed or bypassed.

The primary briefly held the census dependency while checking its start-method
locator, then restored its original bytes and reverified the displayed hash.
The hold consumed the existing grant; it did not reset resources. The relevant
method is `RuntimeProgram::start`, inside `impl RuntimeProgram` at
`machine.rs:367`; the constructed evaluator is a Machine.

## 3. Independent source objects and representation relations

These definitions precede and do not mention successful execution, native
completion, unresolved obligations or model existence.

Source values are finite objects `Lit(site,c)` and
`Clos(siteλ,x,b,σc)`. A literal carries its authentic allocation occurrence and
decoded Unit/Bool/decimal/String payload. A closure carries the authentic
Lambda occurrence, its exact parameter ID/body occurrence, and its actual
immutable source capture-environment object σc. Source environments are
persistent parameter frames, with lookup returning the most recent equal
parameter ID. Extension creates a new frame over the exact previous object;
it does not replace σc by a pointwise-equal map. A closure and its capture
values are finite; this is an inductive source-value domain, not an assertion
that arbitrary recursive native solutions have finite witnesses.

Define `TypedVal₀(v,T)` and `TypedEnv₀(Γ,σ)` mutually on these finite objects:

* `TypedVal₀(Lit(site,c),T)` holds if `Atom(c) ≤V T`.
* `TypedVal₀(Clos(siteλ,x,b,σc),T)` holds if there exist Γc, Ac, EAc,
  ERc, Bc and EBc with `TypedEnv₀(Γc,σc)`, an actual independent D0
  derivation `Γc,x:Ac ⊢₀ b:Bc ! EBc`, `EAc ⊆ ERc`, `EBc ⊆ ERc`, and
  `Fun(Ac,EAc,ERc,Bc) ≤V T`. The Lambda/formal/body occurrences are the
  authentic ones named by the value. This is the D0 Lambda introduction
  with capture values substituted for the environment, not a callable-handle
  premise.
* `TypedEnv₀(Γ,σ)` holds when σ's visible parameter domain is Γ's domain
  and each lookup value has `TypedVal₀` at its Γ type.

Transitivity gives value subsumption: `TypedVal₀(v,T)` and `T ≤V U` imply
`TypedVal₀(v,U)`. Conversely, an actual D0 literal or Lambda derivation has
the displayed introduction witness: strip its final Value-subsumption rules,
invert the remaining constructor rule, and compose its subtype premises.
There is no separate expression meet/join introduction rule in D0. All meet
and join cases therefore occur in the pinned preorder, handled in §4.

Fix the same authentic HIR and constructed RuntimeProgram P. `CodeReal₀(e,k)`
requires the constructor-derived label for e, exact source root/occurrence
and range in `Code.site`, and the instruction obtained from e's actual child
indices. It includes the exact Lambda parameter, false unit flag, absent
record pattern, Value role, absent root schema, and authentic body label.
It is not recognition of an eventual handle by provider site.

Define `Repr₀(v,h)` and `EnvRep₀(σ,η)` mutually on finite source objects:

* A literal requires `values[h].source` to be its authentic literal site and
  `values[h].kind` to contain exactly its corresponding decoded payload.
* A closure requires `values[h].source=siteλ`, kind Closure, and the actual
  executable entry at key `h.0` to be
  `Closure(x,false,None,Value,None,kb,ηc)`, with `CodeReal₀(b,kb)` and
  `EnvRep₀(σc,ηc)`. The witness names the numeric saved ηc read from this
  exact entry. It does not permit replacing that saved field with any other
  environment that happens to have equal lookups.
* `EnvRep₀(σ,η)` requires, for every visible source parameter x, that actual
  `lookup(η,Parameter(x))` returns a cell containing a record r with Value
  interface, a valid existing view satisfying `matches_value(r.view,r.value)`,
  and `Repr₀(σ(x),r.value)`. Dispatch metadata is retained, not equated to
  lexical identity. Extra runtime cells are irrelevant to source parameter
  lookup; shadowed parameter frames still use most-recent-ID lookup.

Now `ValReal₀(T,v,h) := TypedVal₀(v,T) ∧ Repr₀(v,h)` and
`EnvReal₀(Γ,σ,η) := TypedEnv₀(Γ,σ) ∧ EnvRep₀(σ,η)`.
`RecvReal₀(T,v,r)` adds Value interface and that exact view/value match to
`ValReal₀(T,v,r.value)`. `ClosureReal₀(T,v,h,ηc)` is `ValReal₀` with the
displayed closure clause and that particular saved ηc exposed. No future
behavior is part of these predicates. In particular an opaque view's unknown
coverage is not interpreted as a negative protection certificate.

Different evaluations of the same Lambda may allocate different h and ηc.
The proof below carries each actual pair and the same immutable σc from its
construction; it never identifies handles by `SourceSite` or equates captures
by spelling. Representation witnesses persist when the machine appends new
values, executables, views, parameter cells or environments: K0 does not
overwrite these existing entries. Its selected-definition cache writes are
not parameter-cell writes. This storage extension fact justifies retaining
the same capture witnesses across later evaluation.

For finite source evaluation use the following independent proof notation
`σ ⊢ e ⇓ v`: literal decoding returns its literal value; parameter lookup
returns the exact stored value; Lambda returns the closure with current σ;
Apply evaluates f, then the whole a in the caller σ, then the saved closure
body under σc extended with that argument; If evaluates ordered tests until
the first true test, or its else branch after all false tests; Group forwards
its child value; expression-only blocks evaluate prefixes in order, discard
their values and return the final value. No rule says a non-Bool selects a
branch or a nonclosure enters an Apply body. Zero-test If uses its else.
These are finite derivation clauses over source syntax and values, independent
of Machine traces. They spell out the existing bounded lexical Value behavior
used in R339/R340, not an approval of a new global operational semantics.
Luna acknowledged this interpretation during the assignment before writing.

## 4. Preorder lemmas and canonical form

### Four-port inversion without normalization

Define Value maps on raw finite terms, with any fixed constant, say `⊥V`,
for every atom/type variable not covered by the following clauses:

```text
πA(Fun(A,EA,ER,B)) = A       πB(Fun(A,EA,ER,B)) = B
πA(⊥V)=⊤V, πA(⊤V)=⊥V       πB(⊥V)=⊥V, πB(⊤V)=⊤V
πA(S∨T)=πA(S)∧πA(T)         πB(S∨T)=πB(S)∨πB(T)
πA(S∧T)=πA(S)∨πA(T)         πB(S∧T)=πB(S)∧πB(T).
```

Induction on every generating preorder derivation proves
`S ≤V T ⇒ πA(T) ≤V πA(S)` and
`S ≤V T ⇒ πB(S) ≤V πB(T)`.
Reflexivity/transitivity compose directly. The bounds reverse/preserve by the
displayed constants. Join injection/least-upper-bound and meet
projection/greatest-lower-bound are exactly exchanged for πA and preserved
for πB. In a Function-variance step the required conclusions are precisely
its original argument and result premises; the projections do not recurse
into or alter those port terms. This covers every rule of the least preorder.

For Effects use the same construction into the complete lattice `P(Ω)`:
πEA extracts the argument Effect, reverses join/meet to intersection/union
and sends `⊥V,⊤V` to `Ω,∅`; πER extracts the return Effect, preserves
join/meet as union/intersection and sends the bounds to `∅,Ω`. Other
atoms/variables map to ∅. The identical rule induction uses the exact
`EA' ⊆ EA` and `ER ⊆ ER'` premises. `P(Ω)` is only a proof target;
no possibly infinite Ω is introduced as a D0 finite Effect witness.
Consequently

```text
Fun(Ac,EAc,ERc,Bc) ≤V Fun(A,EA,K,R)
  ⇒ A ≤V Ac ∧ EA ⊆ EAc ∧ ERc ⊆ K ∧ Bc ≤V R.
```

This proof uses neither distributivity nor an unproved syntactic subtyping
normal form. Meets/joins in any port and any intermediate subtype term are
covered by the induction.

### Value canonical form from its actual introduction

Interpret the entire Value algebra in `{0<1}`, with lattice operations min/max,
bounds 0/1, every base atom 1, every Function 0, and arbitrary fixed variable
values. Every generating preorder rule is valid, including Function variance
whose endpoints both become 0. Therefore no base atom is below any Function.
If `TypedVal₀(v,T)` and `T ≤V Fun(A,EA,K,R)`, invert its actual value
introduction. A literal would give
`Atom(c) ≤V T ≤V Fun(A,EA,K,R)`, contradicted by this interpretation.
Thus v is the exact source closure and its introduction exposes Γc, σc,
the independent body derivation and intrinsic Function type from §3.
Composing its intrinsic subtype with `T ≤V Fun(...)` and using four-port
inversion gives the exact formal and body-type comparisons above.

For Bool canonical form map Bool to 0, other base atoms and all Functions
to 1. This is another valid bounded-lattice interpretation. Inversion excludes
every literal other than Bool and every closure whenever `T ≤V Bool`.
Similarly, mapping all base atoms and Functions to 1 excludes any inhabited
`TypedVal₀(v,⊥V)`. Variables, bottom and join/meet branch types therefore
cannot be silently assumed inhabited. The first `{0,1}` interpretation alone
would not prove a theorem about an unvalidated parameter environment.

These are canonical forms for independently typed source values, **not**
canonical forms for arbitrary expression shapes. A Function-typed Name or If
is connected to them only by the typed finite-return induction in §6 under
the independently defined `EnvReal₀`. A bottom-typed parameter/branch is
handled by that same invariant, not removed from the source language.

## 5. Lexical lookup, capture and substitution owners

`program.rs:544–603,962–979` establishes the label/site crosswalk;
`748–879` gives the K0 instruction constructors. The later field/operator
rewrite loop has no K0 case. For an unannotated formal,
`receiving.rs:35–44` returns no root schema. These facts establish CodeReal
from the authentic source, not from a fabricated instruction transition.

**Parameter Name.** Roles/lowering at `program.rs:709–747,756–808`
select the exact parameter ID and Observe. `evaluate:773–834` calls lookup
with `Binder::Parameter(id)`. `lookup:2488–2498` walks immutable parents and
finds the most recent equal binder. EnvReal gives this exact populated cell,
source value and received record. `dispatch_name` preserves handle/view and
interface; in authentic K0 it preserves the whole record as shown below.
`consume:2372–2388` validates that view against that same handle and Observe
returns that record. A Name receipt is not a new source or runtime value.

**Lambda.** `program.rs:818–842` retains exact formal/body/Value role.
`evaluate:856–877` calls data/allocate at `2589–2617`. The new handle is the
old `values.len()`; its executable entry has exactly the constructor fields
and **the numeric current environment η**. `data` creates an opaque view for
that new handle. Pair the independently constructed source closure's current
σ with that same η and retain the input EnvReal witness. This proves
ClosureReal with exact body/formal/capture; no call has occurred.

**Environment substitution and dictionary Name.** Both generic branches are
inspected; their exact conclusions differ:

1. `substitute_environment:2509–2513` returns exactly η if dictionaries are
   absent or substitution is None. No substitution equation is needed.
2. With dictionaries present and substitution present, its actual successful
   result η' is a fresh binder-free wrapper whose parent is exactly η.
   Its dispatch substitution is `then(old,new)`; `dispatch.rs:78–94` returns
   the existing nonempty operand if the other is None, or allocates the
   ordered `Then(a,b)` node. For every binder predicate, lookup through η'
   reaches the identical cell it reached through η. Cells and their records
   are untouched. Thus EnvRep and EnvReal for the same source σ are preserved,
   although `η' != η` and dispatch may change.
3. With dictionaries present, `dispatch_name:2520–2528` copies the received
   record and changes only `dispatch`. `dispatch::name:161–185` optionally
   appends a symbolic `Assign(cell,replacement)` for a dictionary Name step,
   then composes the current substitution once in order. On any successful
   return the handle/view/interface are identical. No equation asserting
   inert, commutative or idempotent substitution is used. If a helper fails,
   this generic identity lemma makes no successor claim.

For authentic K0, RuntimeEvidence starts with contextual dispatch false.
Its only enabling assignment is the ambiguous field-tail selection at
`program.rs:402–412`; that loop checks the authentic field-tail/generated
selection occurrence. The single K0 source and its admitted dependencies have
none. Therefore `program.rs:1231–1248` constructs dictionaries=None and no
dictionary Name steps. These are constructor facts about this actual P,
not an assumed property of every runtime program. The reachable K0 path uses
case 1 and the record-identity Name branch. The generic present-dictionary
lemmas establish lexical/value identity only, not broader dispatch adequacy.

**ValueEntry binding and source substitution.** At the actual matching
argument return, `return_value:1382–1410` binds
`r'={value:r.value,view:r.view,dispatch:r.dispatch,interface:Value}`.
`bind/extend:2529–2541` allocate a fresh populated cell and a new environment
over exactly the saved/substituted capture ηc'. Lookup of the formal x finds
this cell first; every distinct parameter ID retains its previous cell.
Source extension `σc[x↦va]` uses the identical source value va, not an
evaluated copy. If `RecvReal₀(Ac,va,r)` and
`EnvReal₀(Γc,σc,ηc')` hold, pointwise lookup and source value subsumption give

```text
EnvReal₀(Γc[x:Ac], σc[x↦va], bind(ηc',Parameter(x),r')).
```

This handles repeated dynamic activations of the same source parameter ID by
shadowing. Other parameters' cell/value identities remain exact. Subsequent
append-only K0 allocation preserves this witness. This is lexical
substitution/environment extension, not type instantiation or a claim that
ordered dispatch substitutions are idempotent.

## 6. Finite-return supplier: all authentic K0 forms

Let `RetSeg(e,η,κ,ω;r)` mean an **actual finite** sequence of Machine steps,
starting at reachable `Evaluate(k_e,η)` with frames κ and owner ω, and ending
at the first matching `Return(r)` with those frames, before consuming κ's
waiting frame. Pauses may split the sequence; count actual steps, not run
calls. CodeReal identifies e/k_e. This is an observation of a segment,
not the definition of source evaluation, typing or realization.

**Candidate finite-return theorem.** For every authentic independently typed
`D:Γ ⊢₀ e:T ! E`, every source σ/runtime η with
`EnvReal₀(Γ,σ,η)` and every actual RetSeg above, there exists a source value v
such that `σ ⊢ e ⇓ v` and `RecvReal₀(T,v,r)` holds at its endpoint. The
source value retains its allocation occurrence and the actual capture objects;
the runtime witness is exactly `r.value`, not an existential port replacement.
No termination, successful invocation allocation or endpoint existence is a
premise of D or of realization. A stopped or nonreturning trace supplies no
RetSeg, and this theorem has no conclusion about its future behavior.

**Proof.** Strong induction on the number n of actual steps in RetSeg,
simultaneously for all D, σ, η and actual waiting stacks/owners. Strip final
Value-subsumption rules from D to expose its constructor; at the end reapply
value subsumption. This stripping does not change the trace length. For each
recursive evaluation below the segment is strictly shorter than n.
Use R340 §3's constructor-based protected-prefix and owner invariant: actual
K0 steps do not scan or replace lower frames; nested Value calls delimit their
owner changes. This fact is independent of value canonical form. Stopped
segments cannot later reach Return; thus errors are not erased by induction.

* **Literal.** The corresponding evaluate arm creates the exact source-site
  payload and a ground matching view (`machine.rs:688–703,2543–2557`).
  Decoder validity is part of authentic K0. `literal.rs:1–9` removes leading
  zeroes, preserving the decimal value; `12–58` gives the pinned quoted-string
  decoding. Independent literal inversion gives `Atom(c) ≤V T`.
  The source literal rule and exact allocated h give RecvReal.
* **Parameter Name.** D's constructor assigns Γ(x) to the exact resolved ID.
  EnvReal gives `TypedVal₀(σ(x),Γ(x))` and the actual cell record.
  The Name/Observe path in §5 returns that same value/view/interface and,
  because this P has no dictionaries, that same dispatch. No new value is
  chosen and no assertion that arbitrary Γ is inhabited is needed.
* **Value Lambda.** D exposes its independent body derivation, intrinsic
  four-port Function and subtype to T. Source evaluation returns
  `Clos(siteλ,x,b,σ)`. TypedEnv comes from the input invariant. The exact
  allocation/capture proof of §5 gives RecvReal for the new actual h.
* **Group.** Its Forward step enters exactly the child under the same η and
  κ. The remaining finite segment is shorter. Apply induction to its actual
  child derivation `A ! EA`, obtaining the same source value/received record;
  D's `A ≤V T` and value subsumption give the conclusion. No group site
  replaces the child's allocation site.
* **Binding-free Block/StatementBlock.** `begin_local:2403–2449` goes directly
  to the final expression for an empty binding list. For an expression prefix
  it pushes exactly BlockExpression with the same η, in source order; its
  return arm at `1529–1530` discards that value and begins the next prefix.
  The protected-prefix invariant decomposes the given finite RetSeg into
  shorter returning prefix segments, followed by the shorter final-expression
  segment. Induction supplies a finite source derivation for each; no binding
  changes σ or η. The final result/record is forwarded unchanged and D's
  final-value subtype gives TypedVal at T. Prefix effects remain premises of
  D; no runtime effect interpretation is inferred.
* **Else-complete If.** `evaluate:903–917` starts the first authentic test or
  the else branch if the test list is empty. Each reached Condition frame
  stores the same source If and η. The actual finite segment decomposes into
  shorter test segments and the selected branch segment. Test induction gives
  independently typed values at their test types. D supplies test type≤Bool;
  §4's Bool canonical form gives Boolean source values and Repr gives the
  identical actual Boolean payload tested at `1482–1528`. Thus source and
  machine choose the same ordered branch, including the all-false else.
  Apply induction to that branch's actual D premise; its type≤T gives the
  result. A bottom-typed reached test would require an inhabited bottom value,
  already excluded by value inversion; no constant-folding source rule or
  loss of an unselected branch typing is introduced.
* **Apply.** Invert D to obtain fixed premises
  `Γ⊢f:F!EF`, `Γ⊢a:A!EA`, `F ≤V Fun(A,EA,K,R)`, and the stated outer
  effect inclusions; final subsumption may give `R ≤V T`.
  The authentic Apply push and R340's distinguished Callee prefix decompose
  the given finite segment at its actual callee return. Induction yields
  `TypedVal₀(vf,F)` and Repr at **that returned h**. Section 4 canonical form
  exposes `vf=Clos(siteλ,x,b,σc)` with its actual independent body derivation
  `Γc,x:Ac⊢b:Bc!EBc` and `Fun(Ac,EAc,ERc,Bc) ≤V F`.
  Four-port inversion gives `A ≤V Ac`, `EA ⊆ EAc`, `ERc ⊆ K`,
  `Bc ≤V R`. No port is chosen independently.
  Repr exposes the executable at h and its exact saved ηc. R340 §§4–5,
  applied with that ClosureReal, gives the whole Delay for a in caller η,
  fresh actual invocation i, preserved Callee/ValueEntry payload and matching
  owner at both return boundaries. The argument segment is shorter; induction
  gives `RecvReal₀(A,va,ra)` for its actual return. Value subsumption at
  `A ≤V Ac` and §5's capture/substitution/extension lemma give EnvReal for
  `σc[x↦va]` and the exact body ηbody used by that ValueEntry.
  Since the original full segment actually returns, its remaining structure
  contains a shorter matching body segment, followed by that invocation's
  ReceiverReturn. Apply induction with the **exposed body derivation** and
  this newly established environment invariant. Its source value vb has type
  Bc; compose `Bc ≤V R ≤V T`. Source Apply's finite clause uses precisely
  vf, va, σc and vb. `ReceiverReturn:1370–1382` keeps the same
  handle/view/dispatch and sets interface Value; its successful owner check
  follows from R340's protected prefix. Hence the final actual r realizes
  this vb at T. This conditional use of a body-return segment does not assert
  that the body will return or establish a future/result interface theorem.

These exhaust authentic K0 and every generating D0 expression rule.
Subsumption is reapplied to each returned TypedVal; no other Effect rule is
used. The smaller-segment induction is well founded even if nested calls
revisit the same Lambda, parameter ID or Apply site. No recursive evaluation
is justified by source-tree size alone. ∎

For the actual closed selected-definition start, σ is empty, Γ is empty and
EnvReal is vacuous at the constructor's initial lexical environment. Runtime
root/source-schedule bookkeeping is the selected-definition path already
identified in R339/R340 and the census. Restricting the theorem to expression
segments before a waiting-frame pop avoids equating whole-module completion
Unit with the selected body's result. The selected cache retains the actual
body handle; this packet asserts no new root-completion/progress theorem.

## 7. Apply the supplier to R340's authentic body entry

Start with R340 ApplyCfg for the same D, caller σ/η, labels, entire actual κ
and owner ω. R340 creates and protects the distinguished
`Callee(whole_argument,ηcaller,siteApply)`; it is not supplied as an assumption.
If its actual callee segment returns, §6 gives ValReal at the derivation's F,
and §4 gives ClosureReal for that exact h and its actual capture ηc.
This supplies R340-VREAL as a candidate at this boundary for **every authentic
K0 callee form**, including Name, If and Apply results. It is not limited to a callee
whose source syntax is Lambda or whose type was already syntactically Fun.

R340's actual-handle executable lookup and whole Delay then enter the whole
argument in caller η if those operational entry steps are available. Its
invocation remains the actual fresh i, with previous owner ω. If the matching
argument segment returns, §6 gives its actual ra/va. Four-port inversion
subsumes that same va to Ac; no different argument witness is introduced.
The Lambda construction establishes the saved EnvReal, and §5 preserves it
through the actual substitution (ηc'=ηc on authentic K0). Exact ValueEntry
binding therefore gives

```text
state = Evaluate(kb,ηbody)
frames = κ · ReceiverReturn(i,ω)
owner = Invocation(i)
EnvReal₀(Γc[x:Ac], σc[x↦va], ηbody),
ηbody.parent = ηc',
lookup(ηbody,Parameter(x)) = the fresh cell containing ra's same handle/view.
```

Here kb, x and ηc came from the executable entry at that one h. The saved
source capture is the same σc object carried by vf, and the Delay uses the
original caller η and whole argument label. This supplies R340-CAPTURE at
the exact typed body-entry boundary. Operational resource failures retain the
same conditional boundary as R340; no entry or normal return is promised.

Before R342, R340 needed separate unproved callee-value, captured-environment
and argument-value suppliers. Subject to independent review, the candidate
finite-return theorem supplies them for all authentic finite returning K0
segments and the exact call entry. This is a concrete application to the
parent C/M obligation, not a new parent claim or a replacement of S0's four
premises.

## 8. Remaining obligations, falsifiers and handoff

| Stable request | Disposition and exact remaining premise/owner |
| --- | --- |
| `R342-K0-VREAL-FINITE` | Candidate supplied by §§3–7 for all named K0 forms at actual finite matching returns. Fresh review must test the typed-environment induction, four-port projection rule cases, occurrence/capture identity and actual segment decomposition. No additional K0 constructor is knowingly omitted. |
| `R342-K0-CAPTURE-ENTRY` | Candidate supplied for authentic K0 saved/substituted capture and same-value ValueEntry body entry. Generic dictionary-present statements preserve lexical/value identity only; broader contextual dispatch semantics remain OPEN at `dispatch::name/then/word` and dictionary construction. |
| `R342-M-REST` | OPEN: same-witness native result/future-interface realization, effect/continuation interpretation, whole preservation/progress and unavailable-step exclusion. Owners include `candidate_call.rs` complete Function/Call producer and consumer, `Machine::return_value`, `Receiving`, and the audit C/M interpretation. A finite typed returned value alone does not settle these independent obligations. |
| `R342-VREAL-OUTSIDE-K0` | OPEN: Comp/record/default/operation/handler/module/local-let and recursive model cases are outside the unchanged accepted K0 domain of this packet; future allocation belongs to Luna. The broader parent source domain is not narrowed by this local theorem. |

The exact proof falsifier is an authentic typed K0 environment/actual finite
returning segment whose reconstructed source value cannot be typed at the D0
type, or whose returned handle/view, literal payload, allocation occurrence,
closure formal/body/capture, or parameter lookup differs from these clauses.
A subtype derivation violating one displayed projection implication also
falsifies §4. A fabricated runtime entry, merely bottom-typed uninhabited
environment or omitted independent runtime-interface premise is not such a
source-qualified counterexample. Missing evidence must instead be reported
with its constructor/consumer and retained as OPEN.

Next in-scope step: freeze this candidate and the one assignment inbox for
Luna's fresh non-contributor review with the primary census; producer writes
stop. Mutual TODO for Luna: adjudicate `R342-K0-VREAL-FINITE` and
`R342-K0-CAPTURE-ENTRY`, then apply accepted suppliers to the unchanged C/M
proof while assigning the precise `R342-M-REST` interface premise separately.
No implementation TODO is justified: **NO_SAFE_CODE_SLICE**, after direct
inspection of actual `program.rs`, `machine.rs`, `dispatch.rs`, literal and
receiving owners. An authentic handle/formal/body/capture or lookup mismatch
would be the falsifier needed for a minimal provisional code-evidence packet;
this packet authorizes no source edit.

## 9. Reuse, checks, resources and cessation

R336 rev4's algebra/source derivations are reused within their finite
reification domain. R339's pre-execution representation idea and actual-handle
trace are reused; its unproved value adequacy is proved here as a candidate
by induction, not imported as a fact. R340's actual Apply push, entire Delay,
protected stacks, owner and argument-return identity are reused under their
actual premises. R341's accepted conditional S0 is retained without reopening
or silently strengthening it. Rejected shortcuts: shape-only Function
canonical form, unvalidated parameter/bottom inhabitation, provider-site
identity, inert/idempotent dispatch and a local frame action standing for all
foreign continuations.

Checks: read-only authority/source inspection, all displayed dependency hashes
matched, manual derivation coverage of all D0 subtype/expression rules and all
named K0 evaluation/return constructors. This is not an exhaustive operational
search. No tests, builds, probes, code/tooling/config edits, external contact,
Git, scratch paths or descendants were used. The explicit packet forbids such
execution checks; the proof's test is fresh independent review.

Resource grant: 2,400 seconds, no carryover; charge the entire reservation
conservatively, including the census dependency hold. No budget expansion.
Requested Sol/high (`gpt-6.1-sol`, high); observed effective model/effort
**UNKNOWN** because no runtime metadata attests them. Actual worker identity
`/root/r342_value_environment_prover`; session supplied by the primary is
`4a30d8bc-cf58-442a-ac35-a6026b4e35b5`. No model-switch claim.

Only new paths are this note and
`tasks/agent-loop/inbox/20261023-r342-k0-value-environment-prover.md`.
Their exact frozen hashes accompany the handoff message; an artifact cannot
contain its own final byte hash. No scratch or descendant leases exist.
Revision 1 is immutable on submission. The inbox records final writer
cessation; after submission this producer is STOPPED, not a resident worker
waiting while marked RUNNING. Review, acceptance, central state and integration
remain Luna's responsibility. Original A/B, full N/W/Z, model existence,
principality, broader source completeness, export transport, whole M and
production remain OPEN.
