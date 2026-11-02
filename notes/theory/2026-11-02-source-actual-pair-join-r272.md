# R272 — e9 source action, ordered Replay and actual extrusion Parents

Revision 1. **Candidate source-native witnessed finite-prefix derivation;
independent review pending.** Sole author:
`/root/sol_r270_source_qualification_auth`, no descendants/coauthors.
Contract `tasks/agent-loop/sprints/source-actual-pair-join-r272.md`, SHA-256
`ab10fbdae1cf7a78b8e6174f29cb95ac60e5f2b66a92528f940f4febf5cd93c5`.
Source bytes are the contract's exact manifest snapshot, inherited baseline
`8d646ac2ed171e13a529e25e035fc75f91678b0b` supplied by Luna; no Git inspection
was performed by this worker.

## 1. Result and exact acceptance boundary

The unchanged parent is full inference/effects soundness → R70 →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`, with its original source domain,
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, source/native correspondence, F1/FK1 and foreign continuations.
Parent/A/B delta remains **0→0**. This local instance does not replace that
parent statement.

The source-body derivation below joins the helper-body call e9 to an actual
negative Function extrusion at target level 2. The operation creates and
retains four actual polar Parents, completes, and its rewritten output reaches
the ordinary bound consumer. Its processing relation has the exact source set
`{event 2}`. Native qualification is false, so each Parent is appended but is
**not pending**; the group is inactive and settlement does not merge it.
This is stronger than an Apply event or a candidate graph/type-copy shape.

The claim is a **finite constructor/consumer prefix under ordinary successful
resource allocation and arithmetic**, derived from actual source owners. It
does not assume that a desired typing judgment holds, that an extrusion is
reached, or that the `unwrap`/test expectations succeed. It is not an observed
execution or kernel-checked Rust proof. It establishes opt-in carrier and
candidate-inference prefix construction, not final acceptance/publication of
the whole program by ordinary/default inference. Later independent semantic
equality paths and full inference termination are not proved absent.

R271's frozen theory/handoff are **unreviewed conditional candidates** and
serve as locators/notation only. Their conclusions and partial review are not
imported as accepted premises. The source equations used for this prefix are
reapplied below at the revalidated bytes; this artifact and its source prefix
require fresh independent review together.

The remaining implication toward a defect/parent result is:

```text
actual e9 extrusion + retained nonpending polar Parents at this finite prefix
  → the required accepted-source equality at the relevant successful consumer,
     accounting for any later independent approved equality path
  → a source-required canonical c / selected physical slot / witnessed
     raw-canonical continuation and actual ordered opposite Replay inputs.
```

The last arrow is not supplied by a nonpending Parent. `Need_D`, the R268
incidence square, R70's independent entry/drain premises and universal R71
coverage remain OPEN. No source-qualified parent counterexample, approved
production repair or full soundness result follows from this packet.

## 2. Source prefix reconstructed from constructors

The exact source is the following 87-byte ASCII string, without final newline:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

The selected constructor is the existing fixture's `parse_file` with the same
cloned source allocation passed through `scan_header`, empty syntax environment,
and `shadow::lower_module_with_local_source` with empty semantic imports. Its
FileKey is `("local-self-recursion-kernel", "source.yu")`. The candidate
collection configuration is true/true, unscoped, operation_v1=false under
`shadow-apply-candidate`; it is not default/ordinary carrier admission.

The concrete syntax facts are source-derived:

* `SyntaxIn::token` delegates to `chasa_recover::In::token`; Token's
  `run_once` checkpoints, invokes the raw scanner and restores the exact `&str`
  suffix on None. `with_str` only captures the consumed prefix. The cached
  reborrow implementation/templates preserve the live field reborrow.
* unicode-ident's ASCII branches use the two pinned u128 masks. Their Start
  bits include A…Z/a…z; Continue includes those plus digits/underscore. Every
  fixture letter is admitted, and space/`{ } = ;` terminate its identifiers.
  Thus failed continuation/suffix scans restore the actual separator rather
  than silently swallowing it. These are finite mask calculations, not probes.
* Header discovery's use/operator selectors reject `my outer` as a header;
  binding selection accepts it. Imports/operators are empty and coverage is
  `0..0`, FirstNonHeader. The empty effective-operator builder returns Ok(empty).
  The full parser's complete nonbinding selector chain rejects the following
  ordinary names, then Binding accepts all four declarations.
* Binding owns Equals; ordinary identifiers form IdentifierPatterns and the
  loop/helper formals each have one PatternMlApplicationTail. No annotation,
  unit/record formal, path or where clause is present. Inline bodies contain
  two correctly closed BracedStatementBlockExpressions. Their three explicit
  semicolons have following statements, with no trailing separator.
* Each of `loop x`, `loop y`, `helper x` has an Identifier head and one
  MlArgument; argument mode None ends at the actual semicolon/right brace.
  Nonquote literal mode is None. The root ends at EOF. No recovery-emitting
  alternative is reached. The inspected Rowan builder's balanced parent/child
  construction, exact cache equality predicates and ordered child adapters
  preserve this CST content; hashing is not treated as equality.

These equations identify the syntax/HIR prefix at its owning constructors
(`header`, `binding`, `pattern`, `operator_chain`, `statement`, local parser
engine and cached Rowan/classifier sources in the manifests). They are not a
proof of arbitrary third-party library inputs/unsafe allocation internals.
All availability failures retain their normal failure behavior; the argument
concerns this finite normal-return prefix and does not alter the source domain.

Let A be the actual minted HIR artifact; R is its outer DefinitionRootId and
SR=Definition(R). All following indices are owner-qualified with SR. The actual
LocalSource construction gives this complete table, with e_i the occurrence
in expression slot I_i:

| slot | retained form / children or resolution |
|---|---|
| I0 | Block, local binding L, final I1 |
| I1 | Name loop → Local L |
| I2 | Lambda parameter X, body I3 |
| I3 | Block, local bindings D,H, final I4 |
| I4 | Apply(callee I12, argument I13), source_form MlArgument |
| I5 | Apply(callee I7, argument I8), source_form MlArgument |
| I6 | Lambda parameter Y, body I9 |
| I7 | Name loop → Local L |
| I8 | Name x → Parameter X |
| I9 | Apply(callee I10, argument I11), source_form MlArgument |
| I10 | Name loop → Local L |
| I11 | Name y → Parameter Y |
| I12 | Name helper → Local H |
| I13 | Name x → Parameter X |

Here L/D/H are `HirLocalId(SR,0/1/2)` and X/Y are
`HirParameterId(SR,0/1)`. Initializer slots are L:I2, D:I5, H:I6. Builder::block
allocates the outer final/init slots, then inner final/D/H slots; processing D
first allocates I7/I8, processing H allocates I9/I10/I11, then the inner final
allocates I12/I13. No slot is left unfilled (`local_source.rs:1084–1375,
1484–1548,1887–2180,2677–2831`).

Initializer(L) pushes temporary self L before X. D sees that L/X and publishes
D. Initializer(H) pushes H then Y, while retaining the enclosing L; its loop/y
resolves L/Y. Publish/Restore installs H for the inner final, then restores the
outer scope and publishes L for the outer final. Thus e9 is **in H's own body**,
and e10 is its resolved use of the still-forming outer L. Neither is inferred
from spelling or from solver row identity. The source owner retains each
parse-branded key and occurrence; `lower_plan` stores this same carrier at R.
An UnsupportedExpression facade for older ordinary brace-body lowering does
not reject this opt-in carrier and is not a successful final ordinary typing.

Collection registers R/DefId, retrieves `local_source_for(SR)` and then
`emit_candidate_source:1043–1073` checks the same pointer and exact R/receiver
identity. Occurrence/parameter/local maps contain these exact entries.
The module has one static definition, no imports/providers/member carriers and
no pending module-definition uses. Its static SCC plan has one singleton.
This is the actual retained input to the native source scheduler.

## 3. Semantic source Values, planning levels and event identity

The source planner begins at I0 level 1, raises Block initializer level by one,
preserves final-expression level, and preserves Lambda body level
(`candidate_source.rs:1208,1249–1262,1340–1380,1546–1557`). Hence:

```text
slot:   0 1 2 3 4 5 6 7 8 9 10 11 12 13
level:  1 1 2 2 2 3 3 3 3 3  3  3  2  2
births: outer=1; L/X=2; D/H/Y=3.
```

Graph::retain_source switches declaration owner at each nested initializer and
keeps it through Lambda/body traversal. Its owner Names give

```text
outer→L; D→L; D→X; H→L; H→Y; L→H; L→X.
```

It also constructs seven Name helpers, three Apply helpers and three Apply
result Values. Thus there are 9 semantic vertices plus 10 helpers, 23 raw
edges, and exactly three events. Block/Lambda/Link/FreshUse metadata does not
invent another Apply event. Every helper entry preserves its planning level;
all births/levels are recorded before seal. The native same-level graph is
acyclic and its 19 components are singleton; the raw graph has the cycle L↔H.
The exact checking/event map is:

| event | checking identity | source owner / resolved receiver | native result |
|---|---|---|---|
| 0 | (e4,0) | L,H | false |
| 1 | (e5,0) | D,L | false |
| 2 | (e9,0) | H,L | false |

`Graph::seal:354–393` returns normally on the complete level/helper inventory;
its equal-level guards make the event endpoints distinct native components.
`qualifies:395–397` is false also for invalid event indices. The collection
and session constructors call this seal, not an unused test-only partition.
This establishes the native qualification input for the actual-pair join below.

This use of H/L concerns **the actual call-demand occurrence**. Y's parameter
Value, the Apply-result Value, the two Lambda coordinates and the copied type
row are different objects. None is identified with H or L, and no incoming
Value-reference edge into a type copy is demanded.

## 4. Native entrance and bounded state before e9

Use `InferenceSession::try_new_candidate(batch)` and its ordinary candidate
`run_candidate`/`execute` path, not a manually invoked extrusion helper.
`try_new` allocates distinct dense kind-qualified live rows; source-level
initialization assigns the recorded levels and native formal roots.
`start_candidate_graph` starts empty Parents/pending/forests/local routes and
sets scoped_enabled=false (`lib.rs:10410–10508`,
`candidate_source.rs:2294–2326`, `candidate_scheme.rs:2528–2552`).

`emit_candidate_source` sets active=true at :2259. Therefore `execute:10702`
skips global pre-admission of collected facts; source actions control their
order. `execute_scc_plan:17178` selects `execute_candidate_graph_plan`, whose
single-root/no-provider dependency order calls `execute_candidate_source_root`
before capturing/publishing the root (`candidate_scheme.rs:3151–3194,3369–3450`).

Let V_i/E_i be the **actual** Value/Effect live rows at the collected component
positions of I_i; let x/y be the actual parameter live rows, computed from
parameter_live_base + recipe_position. These are symbols for constructor
handles, not arbitrary native-state assumptions. Their pertinent levels are:

```text
l=V2 at 2; a=V7 at 3; b=V10 at 3;
x at 2; y at 3; d=V5 at 3; r=V9 at 3;
E7,E8,E5,E10,E11,E9 at 3; E3 at 2.
```

The relevant schedule order is:

```text
BeginLocal L; BeginLambda L;
  BeginLocal D; Name e7 Link(l→a); Name e8 effects; Apply e5;
  D initializer-effect→E3; Install D;
  BeginLocal H; BeginLambda H;
    Name e10 Link(l→b); Name e11 effects; Apply e9;
  [H Lambda construction/publication and inner-final e4 come later].
```

Each Name also has its explicit Bottom/Empty Effect facts before the Link when
applicable; no Value fact equates its parameter with the unused Name component.
Source Name e7/e10 uses the active_initializer[L] endpoint V2, so each is a
monomorphic Link. Source Call registration order is e5, e9, e4 (indices 0,1,2),
whereas event order is e4,e5,e9. Thus e9's Apply recipe/source_input are index 1,
and its checking identity is exactly (e9,0)→event 2. Its callee is Local L,
so formal_name=None, introduction=None; scoped-only local_callee routing is not
selected. The NativeInterface is retained before slot-0 admission.

`step_candidate_source:2396–2467` executes one action synchronously. Link,
Fact and Candidate actions run their typed drains to return before `next` is
advanced. The D Install is a two-step PublishLocal stage; its capture stack
top is D and it registers the actual d root at boundary 2, then pops D. It
does not freshen or execute a later use of D. The remaining active capture is
L; BeginLocal H/BeginLambda H are therefore valid. No unpublished/foreign
capture is borrowed (`candidate_scheme.rs:5079–5153`).

### Prefix obligations from the earlier direct call

The earlier call cannot be skipped just because the target is e9. Its actual
demand is

```text
U5 = NegativeFunction(x+, E8+, T5-, d-), birth(T5)=3.
```

The Link l₂<:a₃ stores l as a Positive lower of a. Apply e5 seeds (a,U5) with
event 1; its target-3 extrusion copies nothing, stores U5 as a Negative upper
of a and replays the lower l. The resulting (l,U5) has target 2 and copies
only E8+, T5-, d-; x is already level 2. Its output U5′ has all ports at level
2. The rewritten (l,U5′) stores U5′ as an upper of l and has no opposite lower.
These three Parents are nonpending because event 1 is false. No positive
Function lower of l has yet been constructed: both source Lambdas are finished
only after their bodies.

All preceding Effect facts are ordinary rows/Bottom/Empty. E7/E8 have one
Bottom lower and Empty upper. The direct call's later slots add E7→E5 and
T5→E5; its initializer-effect fact adds E5→E3. Copy source links add E8→E8′
and T5′→T5. These directed paths have no cycle, no Allowance/view, no Value
feedback, and no operation/member/annotation check. Their replay consists of
row/Bottom transmissions in this finite DAG; Bottom→Empty is accepted by
`candidate_check_effect_operand:1605`. No context filter consumes a Value
relation, since all Value source contexts are IDENTITY. Each fixed relation
and replay dependency is interned/deduplicated; queue admission preserves its
owned child. The finite direct-call drain and its following Effect drains
therefore return before H's schedule is entered. This is not a general drain
termination theorem.

No FreshUse, source H/L Lambda Function admission, equality merge, annotation,
operation, external provider or Function-port comparison precedes e9. In
particular y/r remain without Value bounds. E11 is introduced by its own Name
facts and has exactly one Bottom lower and one Empty upper. T9 will be fresh.
This establishes the selected-side facts used below, rather than inserting
them as arbitrary native-state premises.

## 5. Exact ordered Link/Apply/Replay ancestry

At e10, `execute_candidate_action` constructs the positive l term and negative
b component term and admits `(e10,30)` (`candidate_source.rs:2482–2486`,
`candidate_scheme.rs:5138–5153`). Terms are in the same branch, both Value,
the occurrence is owned and CauseId is made from that occurrence. The store's
actual admission guards are met (`lib.rs:4007–4032`).

Let ρ_L be the actual source seed relation for q_L=(l,b). Its sources are None:
the only checking keys are the three Apply slot-0 identities, so (e10,30) is
not one. The typed drain sets its actual current relation and task scope before
Context/Dispatch. `candidate_context_source` returns IDENTITY for Value pairs;
default unscoped flow has transformer=0 and no demand. Context execution returns
false and does not consume the Value task (`candidate_context.rs:3785–3813,
4186–4245`; `lib.rs:14291–14508`).

`candidate_apply_value:1115–1138` orients l₂<:b₃ toward owner b, Positive,
bound l (the b≤l-level guard is false). It appends the actual physical slot

```text
s_L = (RowKey::Value(b), ValueLowerRow, 0)
B_L = BoundKey(Value(b), Positive, Value(l)).
```

Constructor readback checks B_L. Its executable bound fiber ρ_lo inherits the
same source seed, context and flow. In fact interning yields ρ_lo=ρ_L, since
the bound's ordered pair is q_L itself; the Derived dependency remains distinct
evidence even when IDs agree (`candidate_context_bound_for:4317–4360`,
`attach:3702–3714`). b has no opposite bound yet, so no replay is generated.

At e9, `admit_candidate_fact:4159–4193` validates its retained source_input,
recipe occurrence, all callee/argument/effect/result fields, and checking.
It obtains y directly from the parameter endpoint I11; its callee endpoint is
b, **not l**. The application Effect row E9 has level 3; the constructor
allocates fresh T9 at 3 and builds

```text
U9 = NegativeFunction(y+, E11+, T9-, r-).
```

`term.rs:1251–1270,1390–1404` validates exactly those Value+/Effect+/Effect-/
Value- children in the same arena. Fresh T9 and distinct r make U9 different
from U5/U5′. Its exact checking `(e9,0)` seeds q_A=(b,U9) with σ9, the actual
interned source-set identity whose stored events are `[2]`. Let that actual
RelationId be ρ_A. The state has IDENTITY/default flow and no scoped demand;
there is no source-set union with the earlier direct call at this seed.

The first q_A dispatch is not a memo hit. It invokes negative extrusion of U9
to b's level 3 (`lib.rs:14827–14843`); every port is already ≤3, so it returns
U9 without a Parent. Ordinary application then appends

```text
s_U = (RowKey::Value(b), ValueUpperAtom, 0)
B_U = BoundKey(Value(b), Negative, NegativeFunction(U9)),
```

with attached fiber ρ_up=ρ_A. Both physical b prefixes and their full fiber
lists are now exactly singleton: the only earlier write to b was the Link;
no canonicalization/FreshUse copied l's older upper U5′ into b.

`candidate_replay_bound:1070–1112` enumerates that one opposite lower. Because
the inserted side is Negative, **lower_input=B_L, upper_input=B_U**, and task
q_Ω=(l,U9). `candidate_context_begin_replay:4411–4497` captures both heads;
the prior frontier is (None,None). Its new-lower×all-upper quadrant therefore
retains exactly this ordered dependency:

```text
Replay { child: ρΩ, lower: ρ_lo, upper: ρ_up,
         lower_input: B_L, upper_input: B_U }.
key(ρΩ) = (Value(l,U9), IDENTITY, Some(σ9), default-flow)
source_events(σ9) = [2].
```

`union_sources(None,Some(σ9))` returns that same σ9, not an invented source
owner. Both scoped inputs are default; the lower has no deferred demand, so
composition passes its real guard. This identifies the actual opposite input,
not merely a relation with equal endpoints. `candidate_context_drive_replay`
queues the sole child and retains its acknowledgement in the operation. It
does not pretend queued work has completed.

The outer typed drain next pops this exact child. Transport preserves it because
representatives are unchanged. Context sees its IDENTITY; Dispatch records
task scope q_Ω and actual context.processing=ρΩ. q_Ω is a new pair/relation,
since U9 is new; no prior typed memo or retained rewrite can suppress it. Its
lower l is a row and upper is a negative Function, so the same production
dispatch calls

```text
candidate_extrude(Value(NegativeFunction(U9)), Negative, value_levels[l]=2).
```

This is the reached occurrence Ω9, returned by begin_candidate_extrusion.
Ω9 is different from source e9, checking (e9,0), RelationId ρΩ and Parent
indices. No field is reconstructed by identifying these separate objects.

## 6. Actual Parents, successful whole extrusion and consumer

Let j be `parents.len()` at Ω9's entry. Its Function decomposition is exactly
contravariant Argument/ArgumentEffect and covariant ResultEffect/Result.
For Negative extrusion the four Visits are therefore:

| Parent offset | kind / original actual row | sign | original level | fresh row level |
|---|---|---|---:|---:|
| j+0 | Value y | Positive | 3 | 2 |
| j+1 | Effect E11 | Positive | 3 | 2 |
| j+2 | Effect T9 | Negative | 3 | 2 |
| j+3 | Value r=V9 | Negative | 3 | 2 |

Write their actual returned fresh rows as c_y,c_E,c_T,c_r. Each fresh ordinal
is the old kind-specific bounds.len(), larger than all existing rows in that
kind; no equality merge has occurred. These are actual distinct allocations,
not synthetic type-copy graph vertices. Function children are pushed in reverse
and visited in the table's order (`candidate_extrusion.rs:288–329`).

For each high-row Visit the actual code at :110–180 allocates the fresh row and
calls `retain_extrusion_parent` **before** adding its source link or scheduling
selected bound copies. At that call:

```text
context.processing = Some(ρΩ)
effect_algebra.processing = Some(Value(l,U9))
extrusion_sources() = Some(σ9)
source_events(σ9) = [2]
references.qualifies(2) = false.
```

Consequently `retain_extrusion_parent:305–365` appends the actual record

```text
Parent { copy: RowKey(c_port), parent: RowKey(original_port),
         polarity: port_sign, target: 2,
         sources: Some(σ9), comparison: Some(Value(l,U9)), occurrence: Ω9 }
```

and does **not** append its index to pending. Parent.comparison is a TypedPairKey,
not ρΩ; the proof retains their relationship from this actual call scope rather
than inventing a Parent.relation field. In particular Parent j+0 is the actual
positive type pair `(c_y,y)`, with its retained source event e9→(H,L). The
complete source prefix gives three earlier Parents from e5, so j=3 in the
fresh-session prefix; the constructor identity `j=entry parents.len()` is the
authoritative locator and no guessed raw row number is needed.

The operation completes; it does not stop at a speculative pair allocation.
At visit time y has empty selected lowers, T9/r have empty selected uppers,
and E11's selected lowers contain exactly Bottom. No source view/Allowance
exists, so positive Effect copying has no incoming-Allowance path. The source
links actually emitted are

```text
y  <: c_y        E11 <: c_E        c_T <: T9        c_r <: r.
```

E11's selected Bottom is anchored, installed on c_E, and transported with its
actual exact raw-bound antecedent/witness. No original high bound is silently
dropped, no canonical/ancestral fiber is substituted, and no Effect temporal
equivalence theorem is assumed. This finite case has one selected physical
Effect bound and no selected physical Value bound. The unscoped bootstrap may
retain its own relation; it is not identified with the exact transfer witness.

The Function continuation reifies the four copied ports with their actual
signs and returns the distinct term

```text
U9′ = NegativeFunction(c_y+, c_E+, c_T-, c_r-).
```

The pending-bound Bottom item is finished before operation return. With no
incoming Allowance, the final sparse replay loop is empty.
`finish_candidate_extrusion:368–386` retains the group [j,j+4), Ω9 and actual
`(comparison=Value(l,U9), output=U9′)` lookup; activated=false follows from
the same actual σ9 test. The outer source/processing relation is not changed by
these local insert/transport helpers. The operation returns U9′ normally
after its finite stacks and source-preserving bound transfer are complete
(`candidate_extrusion.rs:542–592`).

Dispatch consumes the actual returned output: it records original q_Ω,
retains the whole-Value rewrite, derives ρΩ′ from **ρΩ** with the same σ9,
and enqueues `(l,U9′)` (`lib.rs:14844–14870,15380–15396`,
`candidate_context_value_rewrite:3902–3927`). No permanent Value owner or
EndpointId equality replaces the occurrence/provenance. At the next dispatch
all U9′ ports are at level 2; its local extrusion returns unchanged with no
new Parent. `candidate_apply_value` appends U9′ as the actual negative bound
of l and retains its rewritten relation. l has no positive lower at this
frontier, so that insertion has no opposite replay product.

The real typed-drain consumer then reaches empty Transport, settlement,
Diagnostics, acknowledgement and ReturnReady. All pending tests have been
false; `settle_candidate_intrusion:568–596` takes pending_cursor==pending.len()
and does not call `merge_candidate_rows`. The replay child has one prepared/
completed acknowledgement and the source-drain completion retains the actual
selected seed/relation (`lib.rs:14394–14523,14986–15049`). The Apply action
then admits its actual Effect slots 1/2, E10→E9 and T9→E9
(`shadow_apply.rs:4421–4459`). E10 contributes Bottom; T9 has c_T as its
lower, so the remaining transmissions are Bottom→E9 and c_T→E9. E9 has no
upper at this frontier. These are finite row/Bottom Effect drains with no
Allowance, Value feedback or additional Parent. The complete Apply action
therefore returns before H's Lambda/publication actions. This is a finite
local drain argument for this action, not R70 eventual global drain closure.

## 7. Competing paths and what is not established

The finite-prefix audit covers the following actual alternatives:

| Potential alternative | Source-derived disposition before the reached consumer |
|---|---|
| Ordinary fresh Local/module use | e7/e10 are active L Links; D is unused; H and L fresh uses occur later; no imports/providers |
| An earlier canonical equality/alias | all graph events are false; pending starts empty; no pending push/activation succeeds; settlement performs no merge |
| Existing positive Function on l | both Lambda recipes are scheduled after their bodies; e9 precedes either Function admission |
| Prior U5′ demand | it is an upper of l, never a lower; it is not an opposite input to the b Replay and cannot compare two uppers |
| Memo suppression | b and U9 are fresh to this action; `(l,U9)` has never been admitted; ρΩ is a new retained relation |
| A different source set from old e5 | b has only this Link lower and this Apply upper; their actual source sets are None and σ9; the ordered union is σ9 |
| Scoped-demand/transformer refusal | the selected experiment is unscoped; all three involved flows are default, with no lower demand |
| Copy-generation from generalization | none before e9; the four pairs come from the actual high-row Visit branch |
| Hidden selected-bound cycle | y/T9/r selected sides are empty; E11 selects Bottom only; no Allowance/view or Function lower exists |
| A consumer already imposing y=c_y | y had no bounds before Ω9; afterward its only new Value constraint is y<:c_y, and c_y has no selected lower; no reverse equality was emitted in this prefix |

Thus a retained, nonpending Parent is established at a completed local consumer;
an independent equality path is absent **at this frontier**. This is not a
proof that every possible later source constraint, H fresh use or final typing
derivation fails to imply the same semantic equality. A whole-program defect
claim still needs that boundary resolved at its owning successful consumer.

The inspected canonical-merge API supports only the weaker structural
observation needed here: normal pending insertion occurs at qualified Parent
creation or qualified recapture, and merge_candidate_rows is called by pending
settlement. There is no such call in this prefix. No arbitrary all-history
rollback/alias theorem or semantic assignment equivalence is asserted.

The approved occurrence rule compares H/L for Ω9, whose raw source cycle was
constructed above. Native eligibility is false because of the level partition.
The actual-pair premise is now exhibited; a complete accepted-source semantic
violation has not been certified. No one may infer soundness failure, change
SCC semantics, discard the level/extrusion/generalization mechanisms, or grant
production edits from this candidate witness alone.

## 8. Parent application, prior evidence and next in-scope evidence

Before this packet, e9's event/qualification was not joined to an actual
extrusion. This derivation supplies the explicit spine:

```text
retained H body I9 / checking(e9,0)
  → NativeInterface(b,y,E10,E11,r,U9,T9,E9)
  → source seed ρ_A(b,U9), σ9=[2]
  → B_L/ρ_lo then B_U/ρ_up, ordered Replay to ρΩ(l,U9)
  → actual Ω9, Negative, target 2
  → retained Parents j…j+3 and actual U9′
  → actual rewritten negative bound at l / nonpending settlement.
```

This supplies a local source-to-Parent bridge, not an independently required
canonical descendant c. In this prefix the selected Value sides are empty and
representatives unchanged: no earlier EqualityCanonicalization `r:k→c:C(k)`
is instantiated. The R71 raw/canonical commuting square therefore remains
inapplicable. Neither an empty selected Value side nor a false qualification
proves a required fiber dispensable for the original source domain.

`R272-LATER-EQUALITY-AND-ACCEPTANCE-1` to Luna, same parent: review this exact
source/processing/Parent spine and establish what successful consumer requires
the Ω9 equality, accounting for later H/L Lambda admission, local FreshUse and
any independent approved equality path. Required inputs are R/SR/e9/e10,
ρ_lo/ρ_up/ρΩ, B_L/B_U, σ9, Ω9 and the four actual Parents/U9′. Falsifiers:
constructor rejection before this prefix; different schedule/polarity/source
set; no high-row copy; or a later independently justified equality path that
satisfies the claimed consumer. This requests evidence, not semantic authority.

`R269-SOURCE-NEED-CARRIER-1` remains to Luna: independently justify the named
canonical c-bearing source requirement and meet it with all selected physical
slots/history paths and actual ordered opposite Replay ancestry. If a change
of fixture or source/native input is needed, admit it at a new boundary rather
than silently enlarging this fixed witness. R70/R71 and all full-domain claims
stay unchanged.

Implementation remains **NO_SAFE_CODE_SLICE** under this packet. Exact inspected
owners for primary assessment are Graph::seal/qualifies, source Apply/Link,
candidate_context_begin_replay/value_rewrite, and retain_extrusion_parent /
finish / settle. An implementation TODO, only after fresh review and Luna's
approved-clause adjudication, is to address the owning qualification computation
if this completed actual-pair trace violates the approved successful-consumer
contract; its falsifier must remain the source-authenticated actual pair and
complete competing equality paths. No patch, test expectation, observer or
production semantic change is written/authorized by this leaf.

Reused: the reviewed R269-r4 LEVEL269/source-owner characterization within its
conditional premises; R268's approved-owner audit as an ownership map, not
proof of this instance. Their authors/reviews remain their frozen records.
R271 candidates by this same author were not treated as accepted or independent
support. R70 raw-prefix and R267 selected Function-slot results do not establish
Need_D or complete accepted-source ancestry. Test assertions, helper-only
states, endpoint equality as lineage, withdrawn type-copy-vertex qualification,
and legacy eager-solving bypasses were rejected as evidence.

ENTRY-WF, eventual drain/Diagnostics, Q262-EPISODE, Effect TEMP265/Z265,
permitted histories/rollback, diagnostic adequacy, complete Call, helper
coverage, full soundness, A/B, F1/FK1 and foreign continuations remain OPEN.

## 9. Dependencies, checks, resources and freeze

Exact dependency manifests: R271-r2
`dfab9720fea19807bca1ad386bffbe4bdb508bef222c5f6480001350be35569e`;
R271-r3 additive readiness
`ef2b3f4c51e383722b458483ba3f5cf05e35ee8e4d918545c94294d0734a7871`;
R271-r2 readiness
`c5d3d87a1b1c335bc0854f43be424407265087a5d380f5a54e68b74b3d613801`.
R269-r4 contract
`a5f3bd1f3bc701ce75191ec234b72264d0dd9e73d7dfd31b88f0b8da0c6009ec`;
R268 owner audit
`4c48c7efe37a90d122e2a1ded7fe0ba835842d8ec1f58f070edbc1ba2677ba13`.
The two unreviewed R271 inputs retain exactly their contract-specified hashes.

Initial gates before technical reads: all **207 manifest rows** and **307
distinct inherited/direct pins** matched, zero failures, observed 14:23:44 UTC
2026-11-02. Source reads were targeted to the exact manifested syntax/HIR,
local/cached parser/CST/classifier owners previously inspected and the native
source, session, term, scheme, context, extrusion, effect and intrusion owners
named in this note. No new source owner or unlisted dependency was accessed.
No R271 partial-review record is used. No exhaustive audit of every manifested
module, third-party library or later source action is claimed. In-file cfg(test)
declarations occasionally appeared in narrow reads/search results; test bodies
and expected assertions are not proof premises.

No executable checker, test, build, probe, Cargo, Lean, network, scratch/cache
or generated output, source/expectation edit, Git, nested CLI or descendants.
Only this theory and `tasks/agent-loop/inbox/source-actual-pair-join-r272.md`
are new/written paths. There are no Lean theorem types or axiom audits for
this source-native packet.

Requested registered prover Sol/high; observed effective model/effort and child
UUID UNKNOWN. Exact identity `/root/sol_r270_source_qualification_auth`, session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; this contract's independent hash matched
Luna's before fresh GO and RUNNING acknowledgement. Separate 3,000-second cap,
no reset/extension/refund. R270/R271 charges stay retained; the new full grant
is charged, while exact active duration/CPU/RSS remain UNKNOWN. Observed status
cuts include 14:23:44, 14:28:59, 14:32:38, 14:37:58 and 14:38:55 UTC.

Final pins/artifact hashes and cessation are supplied in the one frozen handoff
and terminal receipt. Fresh review, adjudication, central state and Git belong
to Luna. This producer does not independently certify its result.
