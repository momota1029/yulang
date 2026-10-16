# Explicit Function formal: receiving profile and first-Call applicability

Date: 2026-10-16
Status: independently reviewed source-constructor construction and scoped proof;
the bounded constructor is selected by the linked definition below.
Independent review: mathematical capture_math_review and source/authority
capture_source_review, both CLEAN at producer SHA-256
`5fd4f6e49b0ffe92889bbe2419077863d167163a5175e4980abcc984200120e9`.
Selection: [known-Function first-call profile](../design/2026-10-16-known-function-first-call-profile.md).
Baseline: `9394ef04effea7b41b09c7da0886ca3cf65ce39c`
Exclusive lease: this new note only. No compiler or runtime authority.

## 1. Frozen statement and boundaries

Consider the authentic resolved source constructor class

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl] Unit) -> [ctrl] Int
```

These are semantic abbreviations for original source annotation and expression
nodes, not a new source spelling or an executed fixture. Fix its original
receiver Lambda `L`, formal `x`, annotation occurrence `a`, annotation scope
`S`, shared contract root `R_f`, first resolved Name `n_1`, Unit argument `v_1`
and first Apply occurrence `c_1`. The second Name/Apply of `g` remain distinct.
`ctrl` is the original resolved family declaration, not its spelling. Fix one
original joint assignment `xi=(nu,K,D)` and coherent original instance
substitution `sigma`. No original type/scope/receiver binder is reallocated.

The root annotation is an ordinary **Value(Function)** annotation, with no
outer computation row on the formal. Its outer Function argument is Unit;
its result is the explicit Function `alpha+`. The effect row on that outer
result is omitted. The two written `ctrl` rows occur inside `alpha+`, at its
argument and result positions. Omitted outer rows are open coordinates, not
empty inferred effects. The abbreviation `alpha+` is fixed here; this is not
profile inference from the eventual shape of an unknown type variable.

Construct from these original source operands:

```text
AnnotationProfile(beta, p_call, Protect, Permit = empty)
Applicable(beta, c_1, p_call, first-use correspondence and source origins)
```

Here `beta=(x,R_f)` retains its original owner/annotation/scope provenance and
`p_call` is the complete invocation position of the **outer explicit Function**.
The theorem constructs that profile component and its actual first-use
applicability; neither is a premise. It also constructs its actual receiving
boundary/Name/Call evidence when that source entry/use executes. All other
independently justified profile components, inherited evidence and unknown
dependencies remain separate. No assertion that this singleton exhausts
`Slots(beta)` is made.

Quantifiers include arbitrary compatible actual providers, actual entry
roles/contracts and inherited packets under the same `xi`, including unknown
native coverage. Static formation does not require provider membership or
successful Function comparison. Actual execution conclusions use an
independently valid source execution with its actual admissibility, entry,
typing and current-world premises. The theorem does not establish those
premises by creating this schema.

Excluded: OmittedFormal/ProtectedVarAt seeds, recursively marking every
position, reversing protection into a provider lower, equating AE with
complete invocation, closed input rows, handling from permission alone,
general profile completeness, second-Call eligibility, native realization,
soundness, principality and production cutover. The original all-source
profile parent stays OPEN.

## 2. Governing sources and definition permission

- [Receiver-relative clarification](../design/2026-10-15-callback-identity-forwarding.md),
  lines 56–80: receiving protects associated argument effects inside that
  original receiving boundary; independent protections and explicit local
  permissions retain their meaning.
- [Annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
  §§1–1.2,3: composed polarity, concrete local permission, no declaration-only
  inflow, unknown variables retained, and existing hygiene results reused.
- [Typed boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md):
  boundary introduction at applicable signature positions, independent
  profile/typed-flow/receipt/Observe edges, whole packets and current activity.
- [Typed core §§3,9](../design/2026-10-02-typed-computation-core-elaboration.md):
  complete producer invocation, including entry and designated result
  consumption; `J_call` differs from the whole carrier `J_arg` and body.
- [Existing Function construction](2026-10-15-function-callback-profile-construction.md)
  §3, especially lines 147–158, and §5: an explicit known Function has a
  complete executable call position; the coordinate theorem alone does not
  supply its independent profile/applicability constructor. This note
  supplies the named bounded constructor, not the source-wide remainder.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–3: no omitted-formal seed for an explicitly annotated formal and no
  backward propagation into existing provider lowers. Its rule is not used
  as the producer of the annotation component here.
- [Selected source-interface formation](../design/2026-10-08-call-source-interface-definition.md)
  §§2–3 and [construction](2026-10-08-call-source-interface-construction.md)
  §§3–5: actual registration/read, producer complete phases and Call-use
  insertion generate the required source correspondences.
- [Callback context](../design/2026-10-03-callback-context-delivery.md) §§2–4
  and [Function view formation](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–2: original static slot/profile versus dynamic boundary; existing
  provider role stays unchanged; source identity comes from formation.

The existing user permission to complete legitimate missing definitions is
recorded in [contextual Function membership §1](../design/2026-10-08-contextual-function-membership-definition.md)
and [source Generalize §1](../design/2026-10-08-source-generalize-definition.md).
The primary's read-only architect packet identifies this explicit-known-Function
case as an omitted constructor of already fixed receiving behavior. This
proposal received fresh independent reviews and the bounded selection above. It
does not rewrite a fixed foreign kernel or choose an observable alternative.

## 3. Positive formation rule at the original formal

Construct the outer complete-invocation position directly from the original
Function occurrence, not from a solved type or a set of effect-family heads:

```text
p_call = (a, outer-Function occurrence epsilon, CompleteInvocation)
```

The Function annotation exposes a callable interface. The existing producer
interface formation supplies its designated complete invocation constructor
`ExecuteCallable`: actual entry, body where present, native return and
designated result consumer. Typed-core §9 places their whole relational image
at `J_call`. Thus this original Function occurrence supplies `p_call` before
any provider is chosen. The annotation's AE/RE coordinates remain separate
source row operands of that interface. In particular, constructing AE does
not construct the complete invocation position, and `p_call` is not an AE
alias. No equality of `p_call` with one scalar native row is asserted.

Emit the following new explicit source-rule output:

```text
original formal (L,x,a,S,R_f), Role(x)=Value
original outer annotation value = Function(Unit, alpha+)
outer Function's source complete-invocation constructor at p_call
---------------------------------------------------------------- KnownFunctionReceive
AnnotationProfile(beta, p_call,
                  Protect = receiver-relative default,
                  Permit = ConcreteMembers(a.outerFunction.result.effects),
                  provenance = (L,x,a,S,R_f,epsilon,CompleteInvocation))
```

`ConcreteMembers` reads **only that original row occurrence**, retaining its
resolved family/type-argument operands. For an omitted row it returns no
concrete permission and retains the distinct open row reference. Here the
permission output is therefore empty. This does not assert the effect row
empty, deny unknown effects or add an effect occurrence. Protection is a
schema at the supplied function's complete executing view, independently of
which effects subsequently flow through it.

**Derivation of the rule.** The explicit source Function constructor identifies
the callable behavior associated with the received argument. Its complete
invocation position is constructed above from the independently selected
producer interface. The receiver-default policy applies to that associated
behavior at the receiver's original callback slot. Typed-boundary §6 then
provides the boundary-profile introduction at that position. The original
formal is negative; the complete invocation direction is preserved by
typed-core §9, so its direct written result row has the selected negative
permission meaning. Reading the omitted row yields no concrete family.
These premises prove the emitted component without an assumed
`Applicable(beta,c_1,...)`, desired `chi`, protected-variable witness or provider
lower. Applicability at this actual first source use is constructed next.

This is a syntax/source-directed specialization of the default, not a rule
that every function-shaped solver endpoint gets protection. Its source
premise is a receiving formal with this explicit Function occurrence and
its complete invocation constructor. The generic external Name case has
neither that formal introduction nor a newly generated boundary merely from
being a Name.

## 4. Construct first-use applicability from Name and Call

The first source Apply has authentic children `Name(x)` and Unit. Construct
its source upper-use demand `U_1` with its original argument, invocation-effect
and result endpoints. Unit formation contributes the original Unit value and
its pure source evaluation; it does not solve the whole invocation effect.
The actual source constraint is the formal endpoint used as callee below
that demand. The result endpoint `A_1` remains distinct from annotation
`alpha+`; ordinary constraints/checking relate them, rather than assignment
by this constructor.

Now construct the actual typed use inclusions:

| Original source operation | Generated correspondence |
| --- | --- |
| Resolved formal Name `n_1` | Reference the original binding `x` at `R_f`, preserving `beta` and its source signature; identity maps its complete call position into that Name's value view. |
| Source callee evaluation | Normalize this Value Name as Result, retaining the same actual value/view and complete call port; no Comp elimination or extra Force occurs at this Name. |
| Actual Apply `c_1` | Source-interface formation inserts that actual callee-result view into its receiver-use slot and surrounds the actual producer's `ExecuteCallable` by the corresponding complete executing view. |

Let `M_1` be that composed identity/read/result/invocation-use correspondence.
Its endpoints are generated by the original Name and Apply constructors:

```text
M_1((beta,p_call), (c_1, executing received-Function view, p_call))
```

Emit

```text
Applicable(beta,c_1,p_call,
           sourceUpperUse=U_1, map=M_1,
           origins=(L,x,a,S,R_f,n_1,c_1,v_1))
```

This is the source constructor's output. There is no premise that a native
Function inequality succeeded or that its scalar ResultEffect is already the
complete CallView. `U_1` authenticates the actual source upper-use, while the
executing view uses the received formal's own original complete call position.
Actual provider acceptance and checked-view comparison retain their separate
complete obligations. Forming the slot/map does not prove those obligations.

The map is independent of the actual provider's Pure/Handler role or entry
mode. The typed source Call inserts the provider's actual complete execution:
for Value entry the view begins before designated argument Force and spans
rebind/body/return; for retained entry it spans actual carrier binding/body;
for an operation it spans native return **and** its designated post-return
consumer. Those are the selected original producer clauses, not roles
inferred by this profile or a new wrapper invocation.

## 5. Actual entry, receipt and exposure: use the constructed component

At an actual `receive` invocation `r`, its ordinary Value entry receives the
whole carrier, forces its designated argument once and rebinds the actual
returned callable. Instantiate `beta`'s constructed component using that same
entry's fresh original boundary `b_r` and source endpoint references. Do not
use `L` or `beta` as a dynamic receiver ID.

The Value entry's typed rebind supplies the original result correspondence:
the formal's callable position is the whole argument's matching
`argument.result.p_call` position. The boundary can be retained there at the
original entry; result transport removes exactly that prefix when the actual
Function value is rebound. This allocates no second receiver/boundary after
argument evaluation and places no Function incidence at the argument's
unrelated current force-effect position.

For the rebound formal view `V_f`, the local component is

```text
chi(V_f) = inherited actual-value/result images
           union_tagged {(p_call,b_r) from KnownFunctionReceive}
Receive(r, original formal slot x, V_f, original entry/rebind map)
```

The inherited images include every actual returned packet and matching
carrier-result profile with their original `K,D,L`, contracts and unknown
dependencies. They are not replaced by this singleton, united with all aliases,
or asserted complete. The new component does not require unknown inherited
profiles to be enumerated or empty.

At the actual first Name read, let `w` be its current executable source owner
and `V_n` its typed read view. Name identity gives `chi(V_n)(p_call,b_r)` and
the actual read supplies `Receive(w,n_1,V_n,Id)`. The source first Call opens
that same received view at `M_1(p_call)`. Every fresh request `q` exposed
during that complete execution has its actual `Observe(q,V_n,p_call,o)`.
The profile, `M_1`, Observe and same-view receipt therefore construct the
typed Path witness. Exact current activity still determines `Inc_C`.

In the ordinary still-live `receive` body, `w=r`; a candidate installed there
has this receiver-relative protection component and **no local concrete
permission from this omitted outer row**. This does not decide eligibility
from the absence of Grant: other independent profiles/permissions remain.
If an original receiver has expired after control re-entry, transport retains
its identity and current filtering removes its inactive incidence; a fresh
executable owner/read does not revive the old boundary.

No operation need occur. If the first call diverges or requests indefinitely,
the theorem covers its finite executing prefixes and creates no `g` early.
If it returns, the original two-input result rule binds the actual returned
packet to `g`. This first-call component is not mapped from `call.effect` to
the returned callable's latent position. Its independently sourced nested and
actual-value incidences survive through their own matching result paths.
The second Call requires its own actual path/receipt/application evidence.

## 6. Nested Ctrl, no backflow and mapped support

The original finite coordinates are:

| Original path | Composed direction at the `receive` formal | Written operands |
| --- | --- | --- |
| outer Function AE | positive | omitted, distinct open coordinate |
| outer Function RE | negative | omitted, distinct open coordinate |
| `outer.result / alpha+.argument` effect row | positive | resolved `ctrl`; allowance at this position |
| `outer.result / alpha+.result` effect row | negative | resolved `ctrl`; permission at its own applicable position |

These rows are retained under the same source scope and assignment. Neither
nested row is the direct outer result row read by KnownFunctionReceive.
The nested negative permission is not an outer permission; its applicability
at a later view is not proved by this first-use rule. We neither discard it
nor manufacture blanket nested protection. No allowance proves actual Ctrl
inflow, and no permission performs handling.

**No backflow.** The only new dynamic incidence is introduced on the received
view at the original boundary. Its edges run forward through the formal
binding, actual Name and complete Call use. There is no reverse edge into
the unreceived provider `f_0`'s lower packet. Equal row representatives,
families or underlying value IDs supply no such edge. Thus the provider's
lower keeps exactly its independently present profiles. The new formal view
can observe a provider event through its actual complete execution without
rewriting the provider's introduction, role or lower.

**Finite/mapped support.** This constructor adds one original profile
coordinate and one bounded first-use path; the four annotation coordinates
are retained source operands, not an assertion of exhaustive profile support.
Construction takes constant additional records for this source shape plus
references to its original annotation/contract data. It performs no search
over effect assignments or future provider shapes. Under an original lawful
source instantiation/renaming, retain `beta`'s original provenance and apply
the same coherent substitution to all endpoint/row/binder references. The
Name/Call inclusions commute because they select the same constructor fields;
no map merges outer/nested paths or independently freshens shared variables.
Arbitrary graph equalities or nonidentity adapters still need their owning
typed-map law and are not certified by this bounded source mapping argument.

## 7. Actual native locators and retained closure boundary

Pinned source inspection authenticates accessible operands and first-use
constraint formation; it does not claim this new profile is implemented:

| Actual owner at the baseline | Established fact |
| --- | --- |
| HIR `module/source_annotation.rs:69–100` | Original owner/position, outer row, Function children, distinct row positions and resolved concrete IDs are retained. |
| solver `candidate_source.rs:594–608,650–656` | Formal registration retains Lambda/parameter/recipe/scope/Value role; each resolved parameter Name retains that same registration. |
| `candidate_source.rs:715–748` | Explicit annotation emits FormalAnnotation at its original scope. OmittedFormal is emitted only when annotation is absent, so this formal gets no such seed. |
| `candidate_source.rs:942–959,1008–1048` | Value-formal Name is pure lookup; actual first Apply retains the original callee/argument/result/checking/cause and formal-Name route. |
| `shadow_apply.rs:1553–1625` | The actual first upper Function demand uses original argument/result and separate invocation effect; native interface is retained before admission. Directional introduction requires the absent OmittedFormal record and does not produce this profile. |

The proposal completes the source annotation/receiving constructor for this
known first-Call position. It gives no native schema field, processing action,
runtime event implementation, all-source completeness or provider membership
proof. Native paired annotation support for these concrete negative rows is
not inferred from coordinate retention. No production guard or source domain
may be weakened because that implementation correspondence is still open.

The primary accepts both independent reviews and selects only this bounded
source constructor. Exhaustive profile supply and native/runtime handoffs
retain their own evidence and authority gates.

## 8. Pins, static checks and commit packet

All new source reads used `git show 9394ef04e:<path>`; no live choose-context-
and-catch or whole-context artifact was read. Direct SHA-256 pins:

| Linked dependency / source | SHA-256 |
| --- | --- |
| existing Function construction | `e4dbbf9cb4e15f460279647c5f4f1b8f8513dce01ea6a0d4a0a08e24f81a54cc` |
| receiver-relative clarification | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| annotation integration | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| directional addendum | `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73` |
| contextual Function permission | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| source Generalize permission | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| source-interface construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| source-interface definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| source Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| callback context | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| inferred Function views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| solver/candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| solver/shadow_apply.rs | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| HIR/module/source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |

Static checks: source-rule/constructor tracing, pinned hashes, note whitespace,
fence and local-link integrity. No Cargo, tests, builds, executable probes,
network, Git mutations, measurements or children. At most two lightweight
read commands per batch; one leaf, assigned 18-minute bound, CPU/RAM not
instrumented. Requested normal Sol/high; observed model/effort unavailable.

Commit packet:

- Sole lease: `notes/theory/2026-10-16-known-function-first-call-profile-construction.md`.
- Baseline: `9394ef04effea7b41b09c7da0886ca3cf65ce39c`; dependency edits: none,
  every read pinned. Primary revalidates any later dependency changes.
- Claim/review: independently reviewed bounded source-constructor proof;
  primary selection is limited to the linked definition, with no native
  conformance or parent closure.
- Checks already run: static source trace, SHA-256 and note integrity; no
  executable verification. Artifact frozen on handoff.
- Suggested checkpoint: `research: construct explicit Function first-call receiving profile`.
- Shared deltas left to primary/curator: after review, record exactly the
  first-use component and preserve general profile/provider/native/runtime
  and global hygiene/soundness/principality parents OPEN.
