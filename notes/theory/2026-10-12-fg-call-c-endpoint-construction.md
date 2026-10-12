# Bare f y: Call-constructor inversion for native extrusion correspondence

Date: 2026-10-12
Status: reviewed bounded constructor inversion with qualification-scope correction; native-to-publication bridge and parent theorem remain OPEN
Baseline: `ed705d0ea121c775ce84e9cb694ada1aa0189889`
Producer: prover-equivalent generic leaf `/root/call_c_operand`
Exclusive lease: this file; one static pass, at most 60 minutes
Independent review: `compiler_referee` PASS, no findings; scope §§1–6,
2026-10-12
Correction review: fresh `compiler_referee` and `spec_auditor` review confirm
the qualification/publication distinction; a fresh three-path diff review
confirmed this correction and the synchronized task record, 2026-10-12
Requested/effective model and effort: unknown; no runtime metadata supplied

## 1. Question and result

The [publication-incidence audit](2026-10-12-intrusion-publication-incidence-bridge.md)
§§3–5 identified a missing correspondence between native generated
constraints and the complete source relation. This note performs the
**Call-owner inversion**: which fields and interfaces does the existing
original Call rule construct at the bare `f y` occurrence, and does that rule
translate the native extrusion graph into its complete checking clause?

The Call rule constructs the actual Name-y whole carrier, retains the complete
checking demand, and inserts the actual callee, receiver and result interfaces.
Its interface constructors generate contextual occurrences of those original
fields. They do not, in the inspected rules, translate the native
`Function(C,D)` demand, its signed parent/copy bounds and approved event
equality into the complete source checking relation. This is the bounded
obstruction. It does **not** imply that C needs a separate source field,
endpoint term, binder or `Desc`: the approved event association directly
qualifies the native pair. This is distinct from the full carrier inclusion
D, observation inclusion P, and recursive f membership; none is assumed or
attempted here.

This adds the precise elimination of Call/IF inputs to the generation-to-source
correspondence gap. It establishes neither source rejection nor impossibility
of an adequate translation. No semantic rule is selected.

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

| Slot | Original field/interface recovered by projection | Correspondence question for the native extrusion graph |
| --- | --- | --- |
| callee | The same f registration/interface under its authentic scoped reference use | Show how the native `o <: Function(C,D)` demand and event provenance relate to the complete callee/checking clause |
| argument | WholeCarrierSlot with J_y and its latent/capture interface; generic hole retained separately | Preserve the whole argument contract and show the signed native bounds in the corresponding complete checking relation |
| callee result / receiver | Actual returned provider/current world and that provider's complete declared phases | Preserve provider-dependent ports while mapping native result coordinates; do not identify I_x with scalar C |
| return / future | Complete original A_c/result and output-provider-dependent future schemas | Show the native result demand's relation to these complete result/future interfaces without dropping dependencies |
| original alternatives | Whole interfaces of actual clauses at their actual insertions/references | Preserve every alternative and its lawful map in the correspondence; no arm is invented or discarded |

In particular, the independent demand variable F_c and native copy C are not
identified merely because both participate in Function checking. The
required result is a scoped relation between the complete source Call clause
and the native graph; it may carry C as an internal endpoint or identify it
with B after the approved quotient. A separate source endpoint term is not
required by intrusion qualification.

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

Thus, following a proposed source field through the finite Call frame returns
an original operator/declaration field and its actual substitutions. In the
cyclic extension a Ref terminates at its registered interface; it does not
unfold recursion. These constructors can place a complete source checking
clause, but the inspected rules do not establish that the native Call demand
and extrusion graph are represented by that clause. The missing item is this
generation correspondence, not a separately named C field.

Applying this inversion at c gives the minimal obstruction:

```text
native App demand, extrusion graph and approved event/pair record
    [no proved generation-to-complete-source-clause correspondence]
complete Call/checking clause with original carrier/result/effect/future fields
    -> IF contextual insertion / Source Generalize Build
same scoped constraints and equality in independent whole-use frames.
```

The missing input is the middle source/checking translation, not the last
placement operation. Theorem IF already constructs placement for a supplied
complete clause. This requires neither assuming D/P nor obtaining f
membership first. The approved Value association selects the actual pairs;
the separate source correspondence must retain their relation and scopes.

The native polar memo is not itself a whole scoped substitution. Scala's
`extrude` returns a `SimpleType`, memoizes by `(Variable,polarity)` and adds
one-sided bounds; its interface has no original Call telescope or source
typed action. The same original variable can have separate positive and
negative copies. A polar memo entry therefore does not establish the
generation-to-complete-Call correspondence or a whole action on the
carrier/world/license/future fields. The missing proof may retain the native
coordinates directly or use the approved quotient, provided it derives the
complete scoped relation; it need not invent a source term for every copy.

Complete contribution/membership inversion does not add the missing input.
The selected C-Call retains its authentic Q_c and independent complete C0;
CallMem elimination returns its exact original EvalCall witness. Their rules
have no extrusion-copy formation or occurrence-map output. Even granting
these original complete inputs hypothetically would still require the actual
native-to-source C incidence. No complete C0 instance is proved in this note.

## 5. Generalize consumer and precise next input

[Source Generalize](2026-10-08-source-generalize-definition-and-proof.md)
§§3.3–4 consumes source-produced clauses and their actual dependency records;
§§5.1–5.2 retains the whole relation and allocates independent component
frames. It does not need a new `Desc` solely because native extrusion
allocated C. The missing premise is that the owning App/Call/extrusion
generation is represented by a complete source clause with the original
carrier, result/effect/future interfaces and scope incidences. Generalize
cannot infer this translation from native levels, the G/F Value SCC, or a
successful Function comparison.

Consequently this inversion supplies neither a frame equation for C nor a
fixed/template classification. The earlier fixed-anchor falsifier remains
conditional because the native equality and its source-clause incidence have
not been transported through actual independent Yulang use frames.

One next action: prove the **native App/extrusion to complete Call-clause
correspondence**, including the approved event and actual signed pairs; first
try the quotient `C ↦ B`, preserve all complete interfaces and original
dependencies, then apply the existing Generalize allocation to independent
uses. Stop if that quotient requires a scope or sharing rule absent from the
selected constructors. No extra D/P membership derivation or C-specific
source binder is the goal of this next step.

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
D/P, native-generation to complete-source-clause adequacy, equality
activation/frame transport, soundness, required principality, normal progress
and cutover.
The parent gate remains OPEN; independent review is primary-owned.

Commit packet:

- Exact changed path: this leased note only.
- Baseline: `ed705d0ea121c775ce84e9cb694ada1aa0189889`.
- Changed dependency hashes: none; direct compared inputs matched baseline.
- Status: reviewed bounded inversion with correction, no new semantic authority.
- Verification: static derivation and dependency comparison; no executable checks.
- Proposed checkpoint message: `research: record native Call publication gap`.
- Shared-record delta for primary: qualify the bounded inversion as a
  generation-to-complete-source-clause gap; do not treat separate C term,
  binder or `Desc` formation as required by intrusion. Retain all parent
  scopes/statuses and separate D/P/L4 obligations.

Writes stop at handoff.
