# Authentic ordinary seed reconstruction and the admission frontier

Status: candidate static source/native reconstruction; independent review pending.
Author: `/root/npair_authentic_seed_antecedent`, sole author, no descendants.
Assignment: `NPAIR-AUTHENTIC-SEED-ANTECEDENT-20261017`, revision 1.
Sprint: `npair-authentic-seed-antecedent-20261017`, contract revision 2,
SHA-256 `9556556e771c4d8bb666b771eb61dba0b926fdfc824ab51a2782ee912121a73f`.
Original contract revision 1: `41d4c4c47fc9a8eaecb4f4e34c5669d08656b6d645bc394f1e778a04e18b949c`.
Supplied baseline: `4685eef7efb59314dc9d96cfcae692d1e09000fe`;
additional-dependency snapshot supplied by Luna: `ecc3b46241203ec6779803e10907a30b80f1ef4d`.
No Git verification or operations. Requested Astra/medium; observed model/effort UNKNOWN.

## 1. Parent and result

Parent **CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017 remains OPEN**.
Keep every original provider, observation, assignment, world, typed position,
source occurrence, guard, continuation, interaction, demand and future. F1 and
FK1 remain independent. The original route is `f () -> install(g) -> fresh use
-> g ()`; this audit does not replace it with a direct operation call.

There is a concrete existing source seed whose identity can be reconstructed:
an operation signature's result interface member. Its physical lower is
`Support(v)` and its individual operand is `AnnotationMember(v,m)` with
`ViewOrigin::Operation`, not ordinarily a freshly constructed
`Contribution(u32)`. The retained view and emission/admission records recover
the source declaration, source operation occurrence and exact native member.
Actual FunctionPort and Replay dependencies supply a structural derivation
skeleton, including ordered replay inputs. This is more evidence than merely
an unlabelled family/row pair.

The reconstruction does not supply the original semantic provider/observation
tuple or an association to a negative Permission descriptor. Also, retained
relation identities do not generally identify a unique selecting source or
processing event. Section 4 proves that precise projection ambiguity, without
claiming a source-qualified counterexample or that every existential derivation
reconstruction is impossible. No execution, admitted receive example, completed
At judgment or production authority is claimed.

## 2. Existing source-owned seed and its physical emission

Take an already resolved operation declaration whose signature is a Function
with primitive argument/result values, no outer computation annotation, and
an omitted result effect row. This is an existing preflight shape:
`candidate_source.rs:428-432` checks resolved declaration, outer effects absent,
Function shape, and ordinary `preflight_annotation`. No negative concrete
formal is required. Resource availability and successful source registration
are premises; this is a static constructor trace, not a run receipt.

At `candidate_source.rs:923-939`, collection emits the operation expression's
bottom/empty computation links and retains `Action::Operation` containing the
resolved declaration, source owner O, exact HIR occurrence o, target and level.
The driver at :1381 calls `candidate_operation` (`candidate_effect.rs:806`).
That constructor builds the positive signature at level+1, then admits the
ordinary value link at `(o,42)`. `candidate_signature_value` recognizes the
outer declaration Function by pointer identity and passes its own family to
its result effect construction (:1557). For the omitted result row,
`candidate_signature_effect` (:1574-1585) creates:

```
v = View(allowed=[declaration.id.family], tail=None,
         owner=O, position=declaration.signature_position,
         provenance=Operation(declaration Arc, occurrence=o))
s = fresh effect row at the signature level
insert_bound(s, Positive, Support(v))
F+ = ordinary positive Function with result effect s
```

`candidate_signature_view` (:753-805) owns the copied family handles and
OperationOrigin. It does not give this operation view an annotation filter.
The operation expression's immediate computation effect remains distinct from
this latent signature effect.

`candidate_insert_bound` (`candidate_extrusion.rs:432`) records
`OwnerEmission { processing }`. The physical owner (:442-601) canonicalizes
owner/operand, admits the bound **before** physical append, reserves emission
storage, journals the effect row, appends `Support(v)` to
`effect_bounds[s].exact_non_variable_lowers`, then retains
`BoundEmission { admission=a, bound=b, physical=(Effect(s),EffectLowerAtom,i) }`.
Here `b=(Effect(s),Positive,Effect(Support(v)))`. The emission index i is the
actual vector length at append. This is physical lower evidence on successful
completion, not just a requested constraint. Partial failure is not a success
premise. The constructor need not have an active processing relation: a direct
signature construction can reach it outside a typed drain.

The admission a retains b, origin pair, optional relation r and cause.
`candidate_context_bound_for` (:3299) attaches b to a relation for its pair,
using a matching current parent when available or creating an origin relation.
It records Derived even when parent and child intern to the same relation;
therefore provenance traversal must not assume acyclicity merely from the
name “DAG”. OwnerEmission's three coverage gaps are still recorded (:684-702).

### A partial reconstruction that genuinely succeeds

For a retained, live successful emission e, validate its admission reference,
e.bound=a.bound, physical owner/lane/index, and that the referenced slot still
contains the expected Support(v) under the applicable canonicalization/version
premise. Resolve v to a view, check Operation provenance and m in range, and
return:

```
NativeSeed(e,a,v,m) =
  (view.owner, operation.occurrence, operation.declaration,
   view.position, v, m, view.allowed[m])
```

For the selected omitted-result branch m=0 and the family is exactly the
operation declaration's family. Correctness follows by the concrete constructor
assignments above and the physical append/emission linkage, not by comparing
family names. Distinct views/members/emissions are not merged by this result.
It is scoped to live references; rollback/reuse or later canonicalization
requires lifecycle validation, not an unconditional persisted index theorem.

`candidate_check_effect_operand` (:975 onward) splits Support into
AnnotationMember(v,m) tasks when checking an operand. The exported observation
`shadow_apply::effect_conflict` (:377-389) already resolves such a member to
`OperationInterfaceMember` with declaration, owner, position, occurrence,
member and effect. Thus reconstruction uses existing owned fields.

A repository-wide static call-site search found the only non-test call of
`candidate_effect_contribution` in `candidate_scheme.rs:1224`, copying an
already existing Contribution during FreshUse. The constructor itself retains
only effect, SourceNodeKey and a fresh instance. We do not invent an ordinary
source Contribution producer or require operation seeds to use that variant.
FreshUse crosswalks are reusable structural inputs, not authentication by
mere allocation of a new instance.

## 3. Actual processing skeleton and a bounded derivation reconstruction

The successful `(o,42)` value link is admitted and recorded with occurrence
and cause by `candidate_scheme::admit_candidate_value_link` (:1528).
`lib::start_typed_drain` (:12268) invokes `candidate_context_seed_with_formal`.
`candidate_context_seed` (:2872-2938) retains an Origin containing the exact
ConstraintOccurrenceId, relation, optional inferred entry and formal data.
Source occurrence is therefore **present**. Relation sources can additionally
refer to checking source events, and scoped demand data retains original Call
and use identities where supplied.

When an actual comparison is between F+ and a negative Function H-,
`lib.rs:12643-12711` produces all four child tasks. The result effect task is
`s <: J`, where J is H-'s result effect, and its result value child is separate.
`candidate_step_function_dispatch` (:12797) invokes
`candidate_function_port_admit`. The latter records
`FunctionPort { parent=p, child=c, field=ResultEffect, operation=Preserve }`.
Argument children instead use Swap. The parent is the active retained relation,
not a reconstructed row equality; a scoped Call demand checks its negative root
and supplies the existing result protection transformer. Typed drain dispatch
sets context.processing from the actual work item's relation (:12355).

For a comparison with the displayed endpoints (no intervening copy/rewrite),
and the simple level case level(J)<=level(s), `candidate_apply_effect`
(`candidate_extrusion.rs:876`) stores J as an upper row of s. Its replay owner
(:799-839) pairs that upper with the already stored Support(v) lower. The
opposite insertion direction is also replayed when that upper already exists.
`candidate_context_begin_replay` (:3401-3470) records ordered
`Replay { child=h, lower=r_seed, upper=r_port, lower_input=b_seed,
upper_input=b_port }`, preserves source sets and scoped composition, and owns
the child task `Support(v) <: J`. Processing h can then physically append the
Support lower to J, retaining another admission/emission. This concrete
orientation is enough for the bounded trace; other levels, extrusion and
canonicalization are not silently included.

Given these retained witnesses, one can reconstruct the structural proof tree
“seed b_seed; Function result comparison c; bound b_port; ordered Replay h;
arrival emission at J”, checking endpoints, field and input keys at each step.
If any referenced emission or dependency is absent, reconstruction fails.
When a visited relation has multiple origins/dependencies, retain alternatives
or require a separately justified selection; do not choose the first row.
Use visited identities when traversing, because interned Derived self-edges
can exist. This is a partial evidence-validation algorithm specified here,
not an implemented consumer or total source-adequacy theorem.

This branch traces existing constructors through an actual FunctionPort API.
It does not assert that the refused receive source produced those records, nor
that a bare equality s=J witnesses a Function incidence. General reachability,
all ordinary generations, and successful evaluation of a source program were
not tested or proved.

## 4. Minimal ambiguity of the retained admission projection

`RelationKey=(pair,context,sources,scoped)` is interned
(`candidate_context.rs:2569-2600`). It does not contain an Origin index or
processing-event index. `candidate_context_seed` appends an Origin even when
that key returns an existing relation. Dependency insertion likewise interns
identical edges. A completed typed drain pops its frame (`lib.rs:12783`), so
its current work-item occurrence is not a lasting admission selector.

Let two retained origin records o1 and o2 have the same relation p. This is
allowed by those producer APIs whenever pair/context/source-set/scoped-flow
coincide; for example their source-set may both be None and scoped-flow default.
Consider the two decorated processing explanations `(p,o1)` and `(p,o2)` for
an otherwise identical OwnerEmission admission. The exact stored projection is

```
pi(p,oi,b,origin,r) = (b,origin,r,OwnerEmission { processing: Some(p) })
pi(p,o1,b,origin,r) = pi(p,o2,b,origin,r).
```

The two existing Origin records remain available, but no field of this
projection chooses one. Physical emission identifies its admission and storage
slot, not the missing selector. This is a two-element information-loss witness
for the **admission-to-selected-origin projection**. It is not a claim that two
full source executions have identical complete solver stores, nor a
source-qualified counterexample to N-Ingress. Such a stronger claim would need
source construction and the rest of the retained store checked as well.

Consequently no total inverse selecting the actual origin can follow from
these fields alone. In the unique-origin subcase a source occurrence is
recoverable by lookup; in the multiple-origin subcase a set of candidates is
recoverable. Ordered Replay and FunctionPort records reduce uncertainty but
do not generally select a particular processing event from a multiply derived
relation. An existential source derivation may still suffice for the original
delta: this witness does **not** prove a new event ID is semantically necessary.
The unresolved choice is whether a validated derivation with all relevant
alternatives is sufficient, or an owning operation must retain a selector.
Luna must not turn that choice into an unreviewed representation decision.

## 5. Apply to the original receive obligation

The original adopted At(D,w,delta) requires actual ordinary arrival at D's
exact negative Function position, with the original w dependencies. The
partial reconstruction above supplies native source member identity and a
checkable structural arrival skeleton for the existing subcase. It removes
the need to guess that identity from a family or to fabricate a Contribution.
It does not identify w's original provider/observation tuple or dependent
assignment merely from an operation interface declaration.

A future Permission record is a separate construction. Its typed path, owner,
formal occurrence, scope, source row and concrete IDs must be tied to the
actual Function projection involved in delta. The current code has no such
negative concrete Permission producer. Even the proposed retained record has
no standalone row-to-descriptor registry; tying it to the actual construction
and position must be explicit. Neither shared row identity nor member-family
equality proves that association. Do not reuse the positive operation Support
as the negative Permission: they serve different source rules.

Apply the inherited pair calculation unchanged: the first Call constrains Y
into J1 and Inner into R1. The original install/capture/use must carry the
whole presentation before a second comparison can constrain rho_u(Q+) into
J2. Our existing operation subcase proves no complete rho_u, no receive
admission (current preflight still refuses it), no local subtraction and no
future-lower completeness. Mixed/multiple-symbolic C_sym, full original family
operands, authentic w/D association, N-Transport, J1/J2 futures, real consumer,
F1/FK1 and production all remain OPEN.

Owner-directed mutual TODOs:

- `NPAIR-SEED-INTERFACE-VALIDATION`: candidate_effect operation/signature owner
  and evidence owner. Input: this exact view/member/emission reconstruction.
  Required result: a validated live source member certificate without relabeling
  it as the full semantic w. Falsifiers: fabricated view/member, stale physical
  slot, missing emission, family-only matching, or Contribution-only coverage.
- `NPAIR-DELTA-ORIGIN-SELECTION`: candidate_context seed/replay/processing owners.
  Determine whether a checked existential derivation over retained alternatives
  meets original delta, or preserve the actual selector at its owning operation.
  Inputs: Origin, FunctionPort, ordered Replay, admission and lifecycle evidence.
  Falsifier: arbitrarily choosing one Origin or assuming a relation is a tree.
  No implementation/type choice is authorized by this TODO.
- `NPAIR-DESCRIPTOR-INCIDENCE`: future formal producer plus Function propagation
  owner. Tie exact Permission position to the actual reached projection and
  original w; cover existing and later lowers. Falsifier: association from row
  or family equality alone, or conflation of provider/use/residual lineages.

Reuse the frozen refinement proof only for its conditional pair calculation
and identified owner boundary. Refine its gap inventory with this constructive
source member trace; reject the stronger inference that all seed origins or
all processing structure are absent. Historical finite map/transport results
cannot close the remaining semantic association.

## 6. Checks, resources and frozen dependencies

Six stages: authority/pins; source producer; physical emission; Function/replay
reconstruction; projection ambiguity and parent application; freeze.
Static reads, call-site search and SHA-256 only. No tests, probes, builds,
Cargo, compiler execution, Git, network, code edits or descendants. Initial
skill lookup at a repository-local path failed; the available home skill was
then read. Truncated combined reads were followed by bounded decisive excerpts.
Conservatively charge 900 seconds; no remaining assignment authority.
Only this artifact and its one assigned handoff were written; no scratch paths.
Writer STOPPED after final freeze; independent review and integration pending.

All contract pins matched before reliance. Revision 2 extension was explicitly
acknowledged after Luna's grant and pin verification; no budget reset.
Dependency authorship remains the existing source authors (not reconstructed);
prior proof author is `/root/npair_concrete_producer_refinement`.

| Dependency | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-authentic-seed-antecedent-20261017.md` | `9556556e771c4d8bb666b771eb61dba0b926fdfc824ab51a2782ee912121a73f` |
| `notes/theory/2026-10-17-npair-concrete-producer-refinement.md` | `ad7a89545c7318f0c19402313c495663af49a51279ab6376bded260740006389` |
| `tasks/agent-loop/inbox/20261017-npair-concrete-producer-refinement.md` | `bbd3314e965224379648a4633f54c21a630b62598e34d31a6114593c1d2c4103` |
| `notes/design/2026-10-17-npair-native-port-code-contract.md` | `a6b6f37218408b334922c19ff6065bd8bd607294201ec2b371f1376e800c41ce` |
| `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md` | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
