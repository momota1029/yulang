# c2 admission occurrence and phase rule — rooted candidate

Date: 2026-10-17  
Status: Draft / unselected candidate; no semantic adoption  
Sprint: `c2-admission-occurrence-and-phase-rule-20261017`, contract rev1  
Parent: original FORWARD-FIRST-CALL A/B OPEN  
Compiler-code authority: none

## 1. Root and ownership

The exact source is

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
```

Let `c1` be the RHS `Apply(Name(f), Unit)` and `c2` the body
`Apply(Name(g), Unit)`. The root is the single resolved c2 occurrence, with its
original argument `a2=Unit`, descriptor variable `F2@(sigma2,Delta2)`, fixed
`xi=(nu,K,D)`, and full incoming view `B_in`. The body remains under the same
`Bind(g,c1,...)`; `Name(g)` resolves to that binding, whose value comes from c1.
No new provider is chosen. The outer declaration/definition/use component is
owned by the selected source Function-view direction §2. That authority
selects shared inference from declarations, definitions and uses but expressly
does not supply a detailed introduction judgment. The F2 formation frontier
and exact open-check are recorded in the pinned parent notes.

The source implementation confirms only the operational occurrence:
`candidate_source` sees `LocalSourceForm::Apply`, retains its callee/argument
endpoints and `CandidateRelation::Apply`; `candidate_call::observe` authenticates
the same owner, expression, `Name(g)`, `a2`, scope and negative-function native
`Demand`. The native argument port and the semantic descriptor inlet are
separate objects. No inspected native constructor defines the latter.

## 2. One fully instantiated candidate predicate

Because no selected source rule introduces original F2 admission here, this
section proposes a new, narrow candidate leaf. It is not called an original
clause and is not identified with `I2`.

At the actual `Apply(c2)` occurrence, let `N2` be its retained native call
Demand and `arg(N2)` its native negative argument port. Let `Unit+` be the
positive native endpoint at the actual literal child `a2`. Instantiate the
candidate predicate at the original call telescope `tau2`:

```text
Aarg_c2^cand(tau2) := Unit+ <= arg(N2)
```

Here `tau2` retains, without projection, the original
`(sigma2,Delta2,xi, owner(c2), c2, Name(g), a2, N2, F2, h, k, C_e, w_e,
Dems(k,h), Obs(k,delta), K, D, licensed descriptions)` coordinates in their
original scopes. No actual provider is an input; it remains universally
quantified by the parent. The formula uses one actual literal, one actual
Apply Demand and one endpoint relation. It does not assert that the native
port is the whole inlet, that this leaf is exhaustive, or that the port
relation has a semantic interpretation at `F2`.

Candidate rule `C-AppArg` places this leaf at the c2-use slot only when the
source resolver supplies that exact `Apply(Name(g),Unit)` occurrence and its
native Demand record. Its proposed behavior is exact for this leaf: a tuple
satisfies it iff `Unit+ <= arg(N2)`. The unselected alternative leaves this
native relation as an ordinary call-check constraint with no claim that it is
an admission clause of `F2`. These alternatives could differ on a tuple whose
native argument relation holds while an independently fixed F2 inlet guard
fails, but no source-qualified tuple of that form is established here; the
difference is **UNVERIFIED**, not decision-ready. `C-AppArg` is not adopted.

## 3. Actual graph and phase behavior

The concrete source/occurrence graph is

```text
Scope(receive-definition,
  Lambda(f, annotation Unit -> alpha+,
    Bind(g,
      Call(c1, Ref(f@declaration), Unit),
      Call(c2, Ref(g@Bind-result), Unit))))
```

`Ref(f)` and `Ref(g)` retain distinct root/use identities. `Bind(g,...)`
keeps the c2 body beneath the actual c1 Return result; it cannot be hoisted to
the declaration, and the c2 provider/result fields stay under their actual
Return. The candidate leaf sits at `Call(c2)` and references `a2` and `N2` in
that slot. No source-level Union or Conj node occurs in this concrete HIR
subtree, so none is invented. The semantic descriptor graph for the inferred
`F2` is still absent; its Union/Conj grammar cannot be claimed as an actual c2
graph.

For any proposed descriptor graph containing this rooted leaf, use the
following **candidate staged residualization**, which preserves syntax rather
than flattening phases. Every primitive carries its original predicate,
complete telescope and source owner. `phase(q)` is supplied only by that
owner; a missing label yields `Unclassified(q)` and blocks admission use.

```text
split(Prim(q))       = Ready_A(q)                 if phase(q)=A and scope-ready(q)
                     | Residual_C(Prim(q))        if phase(q)=C
                     | Residual_P(Prim(q))        if phase(q)=P
                     | Unclassified(Prim(q))      otherwise
split(Conj(q,r))     = Conj(split(q), split(r))   same joint tuple/witness
split(Union(q,r))    = Union(split(q), split(r))  preserve original branch tag
split(Bind(x,q,r))   = Bind(x, split(q), split(r under the same x/result/world))
split(Scope(b,q))    = Scope(b, split(q))         bind b once, below original scope
split(Ref(t,m))      = Ref(t,m)                   classify at t; retain whole m
```

`scope-ready(q)` means every free coordinate of the original predicate is
bound at that exact node. Otherwise the whole node remains residual under its
original Bind/Scope. In particular a later Return/provider/live-authority
predicate cannot be promoted into A merely because it is stored. Conj retains
one correlated witness. Union admits through the selected tagged branch;
it does not require every branch. Bind's continuation remains dependent on the
same preceding Return and current world. Scope retains one hiding witness.
Ref does not duplicate or re-root the source predicate; its complete telescope
is instantiated by the authentic `m` at IF-Use.

This is a candidate graph operation, not an existing selected phase law. The
concrete source subtree has one candidate `Prim(C-AppArg)` beneath its actual
Scope/Bind/Ref/Call positions. There is no instantiated F2 descriptor graph on
which to demonstrate Union/Conj/Bind/Scope/Ref cases; those additional cases
are **unverified**, not claimed by this single occurrence.

## 4. Insertion, use, and current evidence

The actual source path is `declaration f -> c1 use of f -> Bind result g ->
c2 use of g`. IF-Insert may retain an actual declaration clause at its real
root; IF-Use carries an authenticated root and the whole original dependent
substitution. At c2, selected IF-Use applies only after a genuine typed
`g`-root/interface exists. Current evidence gives the resolved local reference
and native Apply endpoints, but not a semantic complete `IF(g)` or a
source-authenticated insertion for `Aarg_c2^cand`. Thus no IF theorem is
instantiated with absent semantic operands. The candidate use slot may be
written explicitly as

```text
Use_c2(Aarg_c2^cand[tau2])
  -- IF-Use(m_g) --> CallSlot(c2, N2)
```

conditional on a real `m_g`; `m_g` is not synthesized by the native port map.
The ground Unit carrier remains only its own supplied certificate and does not
prove all original `B_in` fibers.

For exact incidence accounting, distinguish these three maps:

```text
m_arg : source child a2 -> Apply(c2).argument
       = identity on the retained expression/occurrence; verified by observe.
m_callee : source child Name(g) -> Apply(c2).callee
          = identity on the retained expression/occurrence; verified by observe.
ins_c2^cand : CandidateLeaf(tau2) -> CandidateRoot(F2@c2)
            = id_tau2 (proposed local root insertion, not selected IF-Insert).
```

The resolver authenticates `Name(g)` against the existing `Bind` result root;
that root identity is not yet a typed `IF(g)` interface substitution. Name the
missing map `use_g^sem : IF(g)[m_g] -> CallSlot(c2)`: its source-side
root-resolution component is present, but its complete semantic telescope and
instantiation `m_g` are not supplied. Therefore `IF-Use` on the semantic
interface is not claimed. `C-AppArg` is inserted only into its proposed local
F2 candidate root by `id_tau2`; it does not masquerade as an imported clause
from g. This makes the missing source bridge an explicit proof obligation.

Original VIEW still requires the admitted `I2` tuple to produce complete
carrier evidence for every target `(delta,O)` in `B_in`, including the original
non-source, request/resume/future and independent-alternative cases. The
candidate leaf gives no such action. Original CHECK still requires actual
original clauses, correlated witnesses and an introduction into original `I2`;
`C-AppArg` cannot introduce `I2` by itself. Both remain OPEN at original c2.
No Q, membership, provider success, `I2=SAT`, `B_in=J_U`, or port equality is
used to bridge the gap.

## 5. Limits and next proof gate

This output instantiates one *candidate* predicate at the actual c2 Apply and
records the real enclosing source graph and scope behavior. It does not meet a
source-origin theorem by relabeling a native relation. Astra may proceed only
to prove the staged operation's graph-preservation consequences for the
specified graph, and to attempt VIEW/CHECK conditional on separately stated
candidate adoption. Every uninstantiated descriptor node remains out of scope.

Exact unresolved owners: original Function-view/declaration owner for a
semantic introduction and the full `F2` constructor graph; original inlet
owner for the total carrier VIEW action; original whole-argument-check owner
for original CHECK. No actual source-qualified tuple distinguishing
`C-AppArg` from those original rules is known. Parent FORWARD-FIRST-CALL A/B,
source `T`, native `MODEL`, `WF_Dec(F2)`, `VIncl`, whole-argument compatibility,
`CIncl`, F1/FK1, hygiene, soundness, principality and production remain OPEN.
No code lease or semantic adoption follows.
