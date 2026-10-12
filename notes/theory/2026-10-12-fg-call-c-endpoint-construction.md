# Bare f y: Call-constructor inversion for extrusion endpoint C

Date: 2026-10-12
Status: reviewed bounded constructor inversion; no parent proof closure
Baseline: `ed705d0ea121c775ce84e9cb694ada1aa0189889`
Producer: prover-equivalent generic leaf `/root/call_c_operand`
Exclusive lease: this file; one static pass, at most 60 minutes
Independent review: `compiler_referee` PASS, no findings; scope §§1–6,
2026-10-12
Requested/effective model and effort: unknown; no runtime metadata supplied

## 1. Question and result

The [publication-incidence obstruction](2026-10-12-intrusion-publication-incidence-bridge.md)
§§3–5 requires an authentic source realization of the actual positive
extrusion copy C. This note performs the missing **Call-owner inversion**:
which operand of the existing original Call rule could supply that realization
at the bare `f y` occurrence?

The Call rule constructs the actual Name-y whole carrier, retains the complete
checking demand, and inserts the actual callee, receiver and result interfaces.
Its interface constructors generate contextual occurrences of those original
fields. Inversion reduces a proposed realization of C to an independently
formed field/endpoint term in an original operand, or to that field under an
already supplied lawful whole scoped substitution. Neither the negative
Function's native argument port nor the scalar extrusion memo supplies that
source input. No supplied original constructor identifies C with any such
field or term at its scope. The derivation therefore stops at **field
formation and typed source incidence for C**, before Generalize can classify
it. This is distinct from the full carrier inclusion D, observation inclusion
P, and recursive f membership; none is assumed or attempted here.

This adds the precise elimination of Call/IF inputs to the earlier report's
unspecified C-realization cut. It establishes neither source rejection nor
impossibility of an owner-supplied realization. No semantic rule is selected.

## 2. Frozen source, scopes and contracts

Use the unchanged 116-byte [two-use witness](2026-10-12-two-use-exact-source-bridge.md)
§§1,3–5:

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

The Call c is Apply 13, with Name 14 resolving to the active recursive f
and Name 15 resolving to g's formal y. Keep Group 12, drop and its z formal,
the unused first/x bindings and both later g uses. G is the definition-root
origin and F the resolved callee receiver under the approved
[occurrence association and nested-origin selection](../design/2026-10-12-intrusion-value-type-association.md).
These Values do not classify a source description field.

The [native occurrence derivation](2026-10-12-intrusion-occurrence-source-proof.md)
§2 supplies the original Simple-sub constructor operation
`C = extrude(B,+,1)` inside the negative `Function(B,R)` demand. The
[original two-use trace](2026-10-12-extrusion-occurrence-intrusion-proof.md)
§3 uses that same argument-copy seam with the ignored-call wrapper. C here
denotes that actual native copy occurrence, up to coherent UID renaming;
it is not a row selected by shape. The Yulang witness's source levels are
f=2, g/c=3, drop=4. A native Scala target level 1 is not a source telescope
or a claim that these two source languages have identical complete semantics.

Let E_c be the original lexical telescope of c. Parameter's source A_y is
declared at sigma_y **before g's invocation challenge**, below the actual
enclosing f-body initialization/world dependencies, with its genuinely supplied
Delta_y. Its ValueBind is available inside g after y's original entry/rebind.
The inner Call code is in the whole argument of the enclosing drop Call;
when executed, its current event/world is supplied by that original latent
consumption path. It is not drop's Lambda body or z's scope. No returning
execution of either Call is assumed. Source formation precedes its challenges.

Retain the entire original `xi=(nu,K,D)`, assignment, roots, scopes, witnesses,
actual-provider/current-world dependence, receipts, pending suffixes, raw
resumptions and future fields. Every independent whole-carrier filling of the
Call hole remains present, including nonreturning/effectful fillings and all
original W/Z alternatives. The source Delay of Name y is only the diagonal
section. It neither defines the hole's whole contract nor exhausts its domain.

## 3. Original Call formation, projected at c

Use [Call input construction](2026-10-07-call-input-construction-proof.md)
§§3.1–3.4 and [Theorem IF construction](2026-10-08-call-source-interface-construction.md)
§§3–6, selected by the corresponding Authoritative definitions. The following
is a rule instantiation and elimination **conditional on authentic original
formation inputs**. The exact-input parser/candidate evidence does not supply
all these inputs, and no semantic membership is inferred from this inventory.

Name/Result elimination of the actual binding/capture origins returns

```text
q_f : Code(E_c, Name f, Comp(empty,A_f))
q_y : Code(E_c, Name y, Comp(empty,A_y)).
```

The f certificate is the same registered recursive binding transported along
the actual capture/reference path. There is no source polymorphic `new` at
that still-live reference. The y certificate refers to its one original
Parameter/ValueBind. Neither rule creates an independent argument descriptor.

The actual reify origin gives

```text
t_y = Delay(Return(lookup(the same y)),the original references)
J_y = the original whole carrier interface of that reification.
```

Code-Call inversion then returns precisely

```text
(q_f, q_y, t_y, original F_c/R_f,
 VIncl-origin(A_f,F_c),
 WholeArgCompatible-origin(J_y,CarrierContract(F_c)),
 original complete Comp(E_c_eff,A_c), o_c, Suffix_c(U),
 original resolved roots/scopes and operand incidences).
```

Here `E_c_eff` names an effect endpoint, distinct from the lexical telescope
E_c. F_c is a whole complete Function demand, not the native two/four-port
term. Its origin does not specify an extrusion substitution. The two check
origins record actual emission, not truth of inclusion. `Suffix_c(U)` uses
the original producer interface parametrically at its actual returned
provider; it supplies no already accepted actual f challenge.

Theorem IF places this inventory in the ordered FrameCall slots:

| Slot | Original field/interface recovered by projection | What would be needed to recover C there |
| --- | --- | --- |
| callee | The same f registration/interface under its authentic scoped reference use | A genuine field/endpoint term of that original interface and its incidence to the actual C copy |
| argument | WholeCarrierSlot with J_y and its latent/capture interface; generic hole retained separately | A genuine original field/term and C incidence; pure Name-y formation returns A_y, not a copy declaration |
| callee result / receiver | Actual returned provider/current world and that provider's complete declared phases | An authentic producer field/term and the typed occurrence map; I_x as an entire carrier interface is not the scalar C port |
| return / future | Complete original A_c/result and output-provider-dependent future schemas | An actual result/future formation record with C incidence; no argument-copy inference follows from result sort |
| original alternatives | Whole interfaces of actual clauses at their actual insertions/references | The clause's own complete formation and lawful maps; no arm is invented or discarded to supply C |

In particular, the independent demand variable F_c and native copy C are not
identified by the fact that both participate in Function checking. If an
original demand formation already has a suitable endpoint term, its authentic
formation and typed occurrence map would be sufficient static inputs to
resume this question. The displayed formation rule does not produce them.

## 4. Invert the only available interface transformations

Theorem IF §3.2 has explicit constructor cases, so the unresolved field can
be traced to its input rather than searched for in the final descriptor.

For an original clause insertion and a reference use, inversion is exact:

```text
IF-Insert(reg_t,q)  -> actual q at its original binders, whole IF(q)
IF-Use(reg_t,Ref(t,m)) -> actual reference occurrence, whole IF(t)[m],
                         original ordinary scoped substitution m.
```

The arrows generated by these constructors are contextual incidences. Their
field action preserves the original field and its dependent indices; they
are not endpoint-allocation or admission rules. Name/capture composition
retains the same original certificate. Scope retains its original binder.
Rename and Ref require their whole legal m as input. Bind uses its original
result/rebind/current-world equations. Call assembles those interfaces with
the original dispatch and return/future formation records. A Prim leaf
projects its original complete declaration and parameter instantiation.
Union/Conj retain their real alternatives/shared tuple. Delay retains its
whole child plus original captures.

Thus, following a proposed C field through the finite Call frame returns an
original operator/declaration field or endpoint term, together with every
actual substitution on that path. In the cyclic extension a Ref terminates
at its registered interface; it does not unfold recursion to synthesize a
new field. The constructors can generate a contextual *slot* for an input
field, but that operation cannot authenticate which native extrusion copy
the field realizes. If C is already in an authentic primitive/root input,
inversion can return that input; this note does not exclude that possibility.

Applying this inversion at c gives the minimal obstruction:

```text
native copy C and its signed B->C bound
    [no supplied source field/term formation plus typed occurrence map]
original field/term at (sigma_C,Delta_C), possibly under lawful whole m
    -> IF-Use / contextual insertion
typed C occurrence in the same complete FrameCall
    -> Source Generalize's dependency walk.
```

The missing input is the middle source formation/incidence, not the last
placement operation. Theorem IF already constructs placement when that input
exists. This requires neither assuming D/P nor obtaining f membership first.
It also cannot be discharged by labeling C with F's Value root: the approved
Value association activates actual pairs and does not select their source
description field, type scope or dependency edges.

The native polar memo is not itself the required whole m. Scala's extrude
returns a SimpleType, memoizes by `(Variable,polarity)` and adds one-sided
bounds; its interface has no original Call telescope or source typed action.
The same original variable can have separate positive and negative copies.
Providing a polar memo entry therefore supplies neither an ordinary whole
source substitution nor an action on the carrier/world/license/future
fields. A separately proved typed extrusion construction could supply such
formation or a different legitimate endpoint-term realization; no claim
that it must be an ordinary rename, or that it is impossible, is made here.

Complete contribution/membership inversion does not add the missing input.
The selected C-Call retains its authentic Q_c and independent complete C0;
CallMem elimination returns its exact original EvalCall witness. Their rules
have no extrusion-copy formation or occurrence-map output. Even granting
these original complete inputs hypothetically would still require the actual
native-to-source C incidence. No complete C0 instance is proved in this note.

## 5. Generalize consumer and precise next input

[Source Generalize](2026-10-08-source-generalize-definition-and-proof.md)
§3.3 permits an ordinary Desc declaration only at its actual Parameter/hole
or independently specified inference introduction. Existing fields and
derived endpoint terms remain possible realizations; no new source binder
is required merely because extrusion allocated a row.

For any such realization the rule must supply its actual component and
original telescope, plus the genuine Description/Internal/Established or
other owning field edges. The §5.1 fixed walk and §5.2 whole-frame allocation
consume these records. They cannot infer them from C's native level, the
G/F Value SCC, or a successful Function comparison. Consequently this
inversion supplies no `rho_i(C)`, no fixed/template choice, and no derived
`rho_i(B)=rho_i(C)=C_base` for the two uses. The earlier conditional
fixed-anchor falsifier keeps its exact original hypotheses and status.

One next action: at the Call-demand/extrusion owner, construct or obtain the
**single C field/endpoint-term formation and typed occurrence map**, with
its actual sigma_C/Delta_C and whole-interface action if it uses one. Freeze
its dependencies before independent review. Once supplied, existing IF
placement and the Generalize walk can be applied; no further full D/P tree
attempt is needed to answer this narrower producer question.

## 6. Verification and handoff

Checks: bounded static source/rule/skill reads, manual constructor substitution
and inversion, read-only baseline/status inspection and direct dependency
byte comparison with `git show ed705d0ea:<path>`. Every compared dependency
matched that baseline. Large combined captures sometimes truncated; decisive
Call, IF and Generalize windows were reread separately. A guessed glob path
in an early rg invocation was absent and supplied no evidence.

No compiler, parser, solver, build, test, probe, measurement, Git mutation or
delegation occurred. One reasoning lane, zero inference samples and zero
heavy processes; resource timing and RSS were not instrumented. The
yulang-proofs skill and prover role contract were applied under the explicit
leaf lease. Requested/effective model and effort remain unknown. Configuration
and role prose are not runtime execution evidence.

Unverified: original complete Call admission, recursive world introduction,
D/P, C's lawful source realization/classification, equality activation/frame
transport, soundness, required principality, normal progress and cutover.
The parent gate remains OPEN; independent review is primary-owned.

Commit packet:

- Exact changed path: this leased note only.
- Baseline: `ed705d0ea121c775ce84e9cb694ada1aa0189889`.
- Changed dependency hashes: none; direct compared inputs matched baseline.
- Status: frozen unreviewed constructor inversion, no new semantic authority.
- Verification: static derivation and dependency comparison; no executable checks.
- Proposed checkpoint message: `research: invert Call source inputs for extrusion endpoint C`.
- Shared-record delta for primary: refine the existing C-realization cut to
  original field/term formation and its typed occurrence map, before IF-Use;
  retain all parent scopes/statuses and separate D/P/L4 obligations.

Writes stop at handoff.
