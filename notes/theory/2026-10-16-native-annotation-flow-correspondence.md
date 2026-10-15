# Annotation permission, target type flow and native residual obligations

Date: 2026-10-16
Status: constructive local source/type-constraint correspondence; independent
review CLEAN. Original FIRST-RESULT-ADEQUACY remains OPEN.
Baseline supplied by primary: `cfded839e`; production source `35e87f844` stable.
Exclusive output lease: this note only; source hashes in §8.

Independent review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
at producer SHA-256 `a5dabe20e668069c370fb67e3cffd06e4cc407a07780cc78625c640f8cf726dd`.
Accepted claims are direct computation noninjection, declared-target type
formation/member correspondence and the simultaneous local consistency schema.
The last is not a proof for arbitrary surrounding assignments or of packet
identity. The complete all-xi,z source/native implication in §7 remains OPEN.

## 1. Original theorem and the actual new premise

Retain [native predicate adequacy §1](2026-10-16-native-source-predicate-adequacy.md#1-statement-fixed-before-the-derivation):

```yu
my receive (f: () -> 'a) = { my g = f(); g() }
```

For every original xi=(nu,K,D) and complete first-Call return witness z,
preserve the same actual returned provider/value, private captures, original
scope, whole carrier, receipt/receiver coordinates, pending Bind and future
obligations. Its two inputs remain jointly

```text
M_W* W_z union_tagged M_res* F_R,z.
```

The required native implication includes the actual same-parent Result,
ResultEffect, argument/entry and reached context predicates under this one xi.
Unknown obligations stay predicates; arbitrary xi is not asserted to solve
them unconditionally. No independently chosen provider, packet, marginal
effect assignment or fixture-domain restriction is introduced.

The consumed user correction is the exact
[approved answer](../../questions/2026-10-16-annotation-declared-envelope/approved-answer.md),
question1 / `annotation-declared-envelope-a1` revision1, approval OK; integration
`cfded839e`. It selects neither offered option1 nor option2. Permission,
constraint-derived inflow and subtraction result are different. Permission
alone does not re-add a declared io member to a residual with no io inflow;
unresolved variables, existing filters and dependencies remain symbolic. No
behavior-analysis refinement is needed or authorized.

Two previously selected source owners are decisive independent premises:

1. [Source annotation boundaries, approved §2–3](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md):
   compare the current endpoint directly with the annotation target; pass
   **that target** and local realization evidence outward; the next boundary
   uses that target without erasing earlier evidence or composing concrete
   comparison successes transitively.
2. [Concrete effect annotation implementation, Annotation checking and publication owner](../design/2026-10-10-concrete-effect-annotation-implementation.md#annotation-checking-and-publication-owner):
   check F_actual against F_decl−, then publish F_decl+ in the shared annotation
   variable/view environment. A covariant positive port retains declaration
   Support as a structural **type operand**, not an emitted contribution.

These are existing approved owners, not a newly supplied assumption that the
implementation is correct. The current correction does not revoke them or
require the outward callable type to be the most precise body effect type.
It requires showing which object is an annotation target, inflow or residual.

## 2. Separate the three source/type objects before interpreting code

For an actual annotation boundary b, fix the original source root, position,
scope and symbolic-variable environment. Write:

- D_b: its declared target type/interface, with its concrete covariant type
  members and original shared symbolic tail;
- I_b: the source computation's actual constraint-derived inflow type, which
  may be unresolved and need not equal D_b;
- R_h(I_b): the type after an actual authorized handling/subtraction operation
  h, retaining the original attachment, current scope and symbolic remainder.

The source target-exposure rule says the value passed outward after checking
is viewed at D_b with the original realization evidence. It does not say
that evaluating the body emitted every member of D_b, or that D_b equals
I_b or R_h(I_b). A later Call through that annotated callable view generates
type constraints using that view's declared ports. That is an actual source
type-use edge. It is different from appending D_b to an already computed
handler residual solely because b permits those members.

The correction's empty and io|write examples are equations on I_b and the
actual subtraction operation, not equations replacing every outward annotation
target by the set of events of one execution. We do not define residuals by
event enumeration or interpret an unknown variable as empty.

## 3. Actual direct computation annotation has no permission-to-inflow injection

### Local theorem

For every authentic supported source annotation reaching
`candidate_annotation_computation_effect`, its generated computation-effect
constraint checks the original I_b against the declared negative allowance
(or the original variable-only tail). That owner creates no positive
declaration Support bound into I_b, the initializer's effect or the local
value scheme. This theorem includes root, local and expression-ascription
callers and keeps every original symbolic coordinate.

### Derivation at the real constructors and consumers

`candidate_effect.rs:1432–1469` reads the original annotation row. If absent,
it emits no computation-row constraint. A singleton variable-only row uses
the scope-indexed existing tail as the negative endpoint, preserving future
flow through that row. Otherwise it calls candidate_signature_effect with
polarity Negative and composed variance Positive, obtaining a negative port
whose bound is Allowance(view). It then emits exactly

```text
original computation_effect+ <: this negative target.
```

It does not call the Positive signature-effect branch for this computation
check. The row, declared view and original computation component are distinct
objects. The source owner is precisely the covariant allowance policy and
the original boundary's check, rather than an observation-derived approximation.

For an EffectRow lower and a concrete upper, actual
`candidate_apply_effect` (`candidate_extrusion.rs:876–900`) installs the upper
as a Negative bound on that same row, then replays its opposite bounds. It
does not install the upper view's allowed members as Positive lowers. Replay
forms checks from actual opposite bounds, including future lowers; it cannot
manufacture an additional lower from an upper-only allowance. Direct atom
comparison either accepts the original resolved member, forwards that same
unmatched atom to an existing tail, or records a mismatch
(`candidate_effect.rs:971–1041`). None introduces a new atom from permission.

Consequently, in the concrete instance where I_b is established empty by its
source type constraints, this boundary does not add io. If I_b remains unknown,
it remains unknown with this upper check; no empty-inflow assertion follows.
If later constraints add write/io, those actual lowers face the retained
checks. This is a theorem about generated/propagated type constraints, not
proof from a pure execution trace.

The root annotation caller (`:1297–1310`), local annotation caller
(`:1243–1294`) and expression-ascription caller (`:1312–1317`) all pass their
actual computation component to this same owner. The local caller explicitly
leaves initializer effects on the block edge. Thus no separate computation
annotation path silently re-adds the permission list.

## 4. Positive Function Support is the declared TARGET type operand

At an actual value annotation boundary,
`candidate_annotation_pair:1319–1392` elaborates both targets with one original
scope/variable/view environment, admits

```text
F_actual+ <: F_decl−          check, original source boundary
F_decl+   <: destination−     target exposure, same boundary
```

The local constructor performs the same check and exposes the positive target
through its freshly installed local scheme root (`:1265–1290`). The expression
ascription can use its original peeled endpoint as the destination. These
choices follow the approved target-exposure rule; they do not follow by
transitivity from the first comparison's success.

`candidate_signature_value:1521–1563` reverses polarity and composed variance
for the Function argument and preserves them for the result. At a covariant
concrete port, `candidate_signature_effect:1632–1697` retains the resolved
declared members, same scoped tail and source-owned view. A positive port
gets Support(view) as its structural Positive bound; the negative companion
gets Allowance(view). The fresh positive declaration port and the body's
original effect component are not identified. View construction retains the
annotation root/position, not a fabricated contribution instance.

This establishes exactly the formation premise that was unavailable in the
earlier observation-only attempt: Support(view) at this constructor denotes
the exposed declaration's type operand. Its complete finite member list is
supplied by the independently selected target-exposure owner. No inhabitance,
request event or future execution by the original provider is needed to keep
those members in that comparison object.

### The member implication now comes from TYPE constraints

Let a reached actual type-use constraint have that positive declaration port
on its lower side and target T on its upper side, retaining its one original
Function parent/context. Under a source type assignment satisfying this
original constraint, the covariant structural operand

```text
declared concrete members plus the original symbolic tail
```

is what flows along that use edge. The native Support loop expands this exact
operand into its declared AnnotationMember indices and its same tail
(`candidate_effect.rs:979–996`). Against Allowance(T), the native consumer
checks the same resolved concrete identities and otherwise forwards the same
member to T's symbolic tail. Against EmptyNegative, a concrete member fails.
Thus each generated member/tail check is the corresponding component of the
original declared-target **type constraint**, at the same position/assignment.
It is not an inference from the absence/presence of events in z. Shared tails
are not instantiated separately per member or per Function port.

The actual Function dispatcher selects the declaration's actual fields, and
candidate_function_port_admit retains the parent and composed operation
(`lib.rs:12624–12665`; `candidate_context.rs:3001–3064`). These component checks
remain inside that one coupled comparison; their identity correspondence
does not license independent marginal witnesses or concrete-success
transitivity. Compiled context filters add their exact allowance constraints
to the actual lower type and preserve a residual, as already proved in the
reviewed predicate factorization. A discharge record is not a proof that
those type constraints succeeded.

This is a constructive source/type-operand correspondence at the actual
formation/use/check owners. It does not assert that every independent complete
semantic Function comparison has already been shown to imply its generated
source type constraints. That remaining adequacy direction is separated in §7.

## 5. Permission, operation flow and subtraction are different cases

The actual cases must not be conflated:

| Actual owner | Declared/type object | Inflow or residual effect |
| --- | --- | --- |
| Direct computation annotation `:1432–1469` | Negative Allowance/tail for D_b | Only checks original I_b; no positive declaration Support injected there (§3). |
| Published Function value target `:1358–1388,1632–1697` | Positive Support is the immutable declared covariant type operand | A later actual source type-use edge propagates this target's advertised port; it is not a claim that the body emitted every member. |
| Formal omitted/single symbolic ports `:1145–1164` | Same original shared row at both polarities | Unknown rows stay unknown; they are not closed from syntax or solved at generation. |
| Computation formal entry `:1176–1189` | Original concrete annotation grants local permission | Only an explicit symbolic tail is equated to entry; the concrete list supplies no closed input cap or positive inflow. |
| Resolved operation result `:1578–1586` | Declaration-owned operation family Support | This belongs to the actual primitive's declared result consumer; it is not merely annotation permission. Its source Call includes designated execution after MakeRequestThunk. |
| Actual Catch/subtraction | Source-derived inflow and legitimate handling/attachment | Must compute R_h(I_b) from that inflow, not append the declaration list after subtraction. General source subtraction remains an explicit open gate. |

The signature constructor still refuses unsupported negative concrete rows;
there is no proved general source subtraction operation hidden in that branch.
Ordinary Catch's conservative output constraints are not automatically the
precise subtraction theorem. Existing experimental handling scopes also do
not establish the full original source gate. This note neither certifies those
paths nor presents their incompleteness as a new annotation counterexample.

In particular, freshening/copying a declaration Support preserves that same
declaration operand, mapped tail and original owner. It is not a legal rule
for adding that operand to an unrelated handler residual. A proof must trace
the actual annotated target/use or actual operation source at each insertion.
No such residual add-back counterexample is established by this packet.

## 6. Application at the original first Apply under the same xi

The original f annotation has omitted AE/RE ports and one shared result type
variable a. Its actual formal owner constructs the paired targets at
`candidate_effect.rs:1124–1164` and admits both original formal edges at
slots43/44 (`:1191–1231`). Those omitted effect ports are shared unknown rows;
they are not declared empty and do not acquire concrete Support from this
annotation alone. The original first Apply has its actual Unit argument,
fresh invocation effect i and fresh result r. The actual annotation-lower /
Apply-upper meeting emits:

```text
Unit argument type <: declared Unit input type
d+ <: e_A−
e_R+ <: i−
a+ <: r−.
```

Here d is the actual Unit expression's effect type, established bottom by its
literal source constraints, not by observing a terminating run. Let A, E_A,
E_R be the original source type interpretations of these shared formal
coordinates under xi, retaining their symbolic/source predicates. The local
common assignment

```text
r has type A; i has type E_R; d has bottom type;
the Value-formal f Name's evaluation has bottom type; j has type E_R
```

satisfies this local table by identity, bottom inclusion and the generated
application-effect inclusions. It does not set E_A/E_R empty. When a real
annotation target supplies declared Support to one of these original type
coordinates through an actual use, §4 interprets that Support as source type
inflow; when only an allowance checks the coordinate, §3 does not add it.
This supplies the declared-member part that an actual-event-only valuation
missed, without changing xi, selecting another provider or postulating the
entire native graph satisfied. Other accumulated constraints stay conjuncts.

The original source Call/Return/Bind rules still provide the same z and both
tagged packet images, including operation-valued f after its designated result
consumer, original captures and pending response/Bind suffixes. Source hygiene
transport keeps K predicate identities and D incidences through the matching
typed maps; no type-support member itself grants handling authority.

The type assignment r=A is not equality of the two packets' typed views or
their profiles. The separate Result transport maps remove the matching
Result prefix and preserve both tagged inputs. Therefore the local type
valuation and these source packet equations cannot alone be promoted to a
complete native Result semantic interpretation.

## 7. Honest remaining claim and proof-obligation economy

Established local conclusions, pending review:

1. Direct computation/root/local/ascription annotation checking has no
   permission-only Support inflow; unresolved/future constraints remain.
2. Published positive Function Support is supplied by an existing approved
   target-exposure type owner, and its member/tail checks correspond to actual
   declared-target type-use constraints at the same composed polarity.
3. The original first Apply has a simultaneous local type valuation with the
   original symbolic AE/RE and a=r type coordinate; declared Support and
   actual inflow are correctly distinguished in that valuation.

Thus the prior request for a new declared-envelope/descriptor choice is no
longer the next prerequisite. Existing target-exposure authority supplies this
type-formation clause. No new user decision, emitted-event inhabitation proof,
behavior refinement or blanket Support deletion is needed for it.

The full original implication still needs the source/native semantic adequacy
step: the original complete same-provider Function/source obligation under xi
must imply satisfaction of its generated source type constraints and native
Result predicate **jointly with the two actual packet views**, entry/RE and
any reached subtraction/residual context. The local type valuation establishes
the original scalar/structural constraints' consistency and the annotation
member correspondence, not that complete implication for all original source
constraints and dependent K/D observations. No arbitrary full native I is
assumed to close it.

At the actual Result owner, the required remaining conclusion is that this
same source-derived type assignment and original witness interpret the
field3 comparison on the same W_z/F_R,z packet inputs, while the parent's
effect/residual predicates use that same assignment. Actual source boundaries
and their target realization evidence must be kept through this step; an
identity of raw rows or r=A type equality does not identify typed views.
General subtraction correspondence cannot be replaced by treating an allowance
list as the residual. These are existing semantic/consumer gates, not evidence
of a new bug or missing declaration metadata.

This is genuine progress at the formerly absent annotation owner: the earlier
event-only obstruction is bypassed by the existing **type** target-exposure
rule and actual asymmetric constraint propagation. It is not original parent
closure. Repeating a decoder/census or an event-only Support proof would leave
the remaining premise untouched. Next action is to combine these established
type constraints with the original dependent source Result/Function judgment
at candidate_function_port_admit, using the target realization evidence and
actual residual operation where reached. Full FIRST-RESULT-ADEQUACY, B,
hygiene, soundness/principality and cutover remain OPEN with the primary.

## 8. Dependencies, checks and commit packet

| Actual frozen source | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `a330100b418f14be1c8f600c62970efdb4859818b603190846796de39fa8cef2` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/lib.rs` | `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| Approved correction answer | `7c564a6e28c85059473b2c8498fdff72fd5f5e8f6378e9a8dce2780b63d69785` |
| Approved annotation-boundaries answer | `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` |
| Concrete effect annotation implementation authority | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| Annotation hygiene integration including §1.2 | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| Reviewed native predicate adequacy input | `718491c438ae566fb6fb552c9bb5063317de58ec64fdee63311b76e95586ead2` |

Method: actual source/type-constraint induction and constructor/consumer trace;
no event-based effect inference and no assumed native-G model. Read the
yulang-proofs skill, design authority and exact approved correction/older
target-exposure owners. Normal Sol/high requested; observed live runtime
metadata unavailable. No override or delegation.

One bounded 20-minute allocation; no tests, builds, executable probes, Git,
network, compiler edits or shared-record writes. Bounded rg/sed/cat/hash reads
only; zero heavy processes/measured samples, exact elapsed/CPU/RAM uninstrumented.
Only this leased file changed; independent review pending.

Commit packet: sole path
`notes/theory/2026-10-16-native-annotation-flow-correspondence.md`; baseline
`cfded839e`, stable source `35e87f844`, dependency hashes above. Proposed
checkpoint: `research: derive annotation target type flow without residual reinjection`.
Shared-record delta for primary/curator: consume exact positive annotation
formation/type-use and direct-computation noninjection results after review;
retain original same-witness Result/residual adequacy and parent gates OPEN.
No shared record was edited.
