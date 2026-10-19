# R130 — finite experimental case source/worklist correspondence

Status: candidate source-native evidence and conditional repair derivation;
independent review NOT_RUN. Author: `/root/r130_proof`, no descendants or coauthors.
This is revision 1 of the proof artifact, frozen for Luna intake.

## Parent, authority and exact claim

The parent is R130 rev3's fixed experimental outcome: confirm the two case
accounting defects, preserve arm binding and all constraints in a one-visit
repair, then carry the specified finite sources through candidate inference
and the public playground evaluator. Contract:
`tasks/agent-loop/sprints/case-source-progress-20261019-r130-rev3.md`, SHA-256
`f6acca90ba74abdebd6f851863eb6aaa76e00c5d523c6b2e70d5602f0b7cd2fe`.
Luna explicitly granted rev3 after CLEAN delta review; no resource reset occurred.
Rev2's baseline and exact proof output leases survive unchanged.

The source/worklist result below quantifies over finite retained case trees
whose expression forms are Integer, arm-resolved CaseBinder Name, Case, and
optional Group wrappers, with Integer/Binder/Wildcard patterns. It assumes
successful source formation and available collection resources. It proves
source push/pop facts and the proposed traversal invariant, not parser
completeness or solver soundness. The constraint-preservation argument applies
to every retained arm body once that body's own traversal succeeds, including
bodies outside this small induction grammar; it does not prove those other
forms' full correspondence.

The governing inference principles require ordinary generation, accumulation,
propagation, variable levels, extrusion, qualifying intrusion and generalization.
This argument bypasses none of them. The charter supplies no production
implementation authority. Original Simple-sub/evaluator A/B and their original
quantifiers, R85 adoption, all six effect-hygiene parents, broad case completeness
and production admission remain OPEN. No F1/FK1 or foreign-continuation
obligation is discharged by this local case argument.

## Retained construction and scope

The contract's conceptual `LocalSourceBuilder::case` is implemented as the
private `Builder::case` in `crates/yu-hir/src/module/local_source.rs:1222`.
It allocates a fresh scrutinee index, then a fresh body index for each arm;
integer patterns also receive fresh retained Integer expression indexes.
`LocalSourceCaseArm` retains its source identity, pattern and body index.
A non-wildcard identifier receives the retained binder ID
`(source root, arm source key, ordinal 0)`. `_` retains Wildcard without a binder.
Distinct arms therefore do not use spelling as binding identity.

The builder pushes reversed `Work::CaseArm` children, then Restore(depth),
then the scrutinee Expression. Its LIFO traversal constructs the scrutinee
outside the arm binding. Each CaseArm pushes its own Restore(saved depth),
installs `LocalSourceResolution::CaseBinder(id)`, then pushes its body Expression
(`local_source.rs:683`). All body descendants finish before that Restore pops.
Nested arm restoration preserves the enclosing arm binding; restoration after
the enclosing body removes it before the next sibling arm. Name resolution
therefore retains an arm-local ID even when spelling is shadowed or unused.
An unused binder remains in the pattern; the builder creates no synthetic Name
occurrence for it. `slot`, `push_binding` and `restore` supply fresh indexes and
lexical restoration (`local_source.rs:782`, `:815`, `:828`).

The value-reference graph independently interns each retained binder and maps
resolved CaseBinder names to that ID (`candidate_value_graph.rs:74`, `:120`).
This is evidence that the binder survives construction. It does not populate
the separate `case_positions` map used by candidate source collection.

## Old worklist: two independent reachable defects

Let Vx mean `Work::Visit(x, level, region)`, Fx mean Finish(x,level), and Ax
mean CaseArms(x,level,region). Lists below give pop/execution order; child
traversals run to completion at each listed child. No test was executed.

At `candidate_source.rs:981`, Visit pushes Finish. For a Case, the old code
then pushes reversed arm bodies (and integer-pattern Visits), the scrutinee
Visit, and finally CaseArms (`:987`). Consequently CaseArms pops first. It
installs binder maps and pushes all reversed arm bodies again (`:1110`).
For arms in source order, the resulting order is:

```text
Vcase, Acase,
  first body0, first body1, ...,
  scrutinee,
  integer-pattern0 if present, second body0,
  integer-pattern1 if present, second body1, ...,
Fcase
```

An exact binder-free retained witness is
`C0 = Case(s1=Integer7, p2=Integer7 -> b3=Integer11)`. Its trace is:

```text
V0 A0 V3 F3 V1 F1 V2 F2 V3 F3 F0
```

Thus both body paths are reachable without any binder lookup, and b3 has two
Visits and two Finishes. Its constructor constraints are constructed twice.
No claim is made that duplicate fact identities necessarily cause a particular
later error or that the full old implementation accepts/rejects this source.

Independently, `case_positions` is initialized empty and populated only by
resolved CaseBinder Name occurrences (`candidate_source.rs:936–945`).
For `my main = case 7: unused -> 11`, construction retains C0, s1 and b2, plus
the pattern binder ID, with no Name for that ID. The old prefix is V0,A0.
CaseArms requires `case_positions.get(id).ok_or_else(invalid)` and fails there,
before V1 or V2. Here `invalid()` is MissingDefinitionEndpoint (`:442`).
Preflight (`:451`) imposes no requirement that a Case binder be referenced.
No other write to case_positions supplies an unused binder position. This is
an exact collection obstruction for that retained source, separate from CLI
execution or a claim that a CLI check ran.

## Nested endpoint trace

For the positive nested witness, retained fresh-index structure is:

```text
C0 = Case(s1=Integer7, alpha -> C2)
C2 = Case(s3=Name(alpha), beta -> n4=Name(beta))
```

Write vx for positions[x].value, Ex for endpoints[x], and B[id] for
case_binders[id]. Initially E1=Component(v1), E3=Component(v3),
E4=Component(v4). The positions map has alpha->v3 and beta->v4.
The old complete structural trace is:

```text
V0 A0
  V2 A2 V4 F4 V3 F3 V4 F4 F2
  V1 F1
  V2 A2 V4 F4 V3 F3 V4 F4 F2
F0
```

A0 stores B[alpha]=E1. The first A2 stores B[beta]=E3=Component(v3)
before V3 resolves E3 from B[alpha] to Component(v1). Both first inner-body
Visits read the stored B[beta]=Component(v3). The first F2 therefore creates
the arm value action from Component(v3) to v2. Changing E3 does not mutate
the copied endpoint in B[beta] or an already constructed action.

The second A2 can overwrite B[beta] with the now-current Component(v1);
the second F2 can consequently construct another action from Component(v1)
to v2. This demonstrates the stale first binding and duplicate construction.
It does NOT establish the full old solver outcome: the later correct action
may also constrain inference. In particular, rev3's string-to-int negative
detects a stale-only repair, such as removing duplicates while retaining the
old binder-before-scrutinee order. It is not a proven detector of the complete
old duplicate scheduler.

## Minimal proposed repair and conditional one-visit proof

The required push order is:

```text
Visit(Case): after existing Finish, push CaseArms, then Visit(scrutinee).
CaseArms: install each Binder ID from the visited scrutinee endpoint;
          if case_positions contains that ID, retain its arm-level assignment;
          then for arms in reverse source order:
              push Visit(body); if Integer, push Visit(pattern).
```

Every binder ID is installed, including unused binders. The optional lookup
only controls level metadata for an existing representative Name component;
it must not make a missing Name a collection failure or create a fake endpoint.
The existing level and region arguments are retained. In particular a first
Name nested in a deeper initializer keeps the existing representative's arm
level when such a Name exists. Name Visits still assign their endpoints from
the retained binder ID. No body, integer-pattern, or constraint is discarded.

Proof by induction on the finite retained tree: an atom has one Visit and one
Finish; a Group schedules its unique child once. A Case Visit leaves its sole
Finish below CaseArms and the scrutinee Visit. The scrutinee subtree completes
first, so endpoint assignment is current when CaseArms copies it. CaseArms
is the only owner of arm-body Visits and schedules each body and integer
pattern once. Fresh indexes make their subtrees disjoint, and LIFO processes
them in source order, pattern before its body. The induction applies to every
nested Case. The unique Case Finish then runs after all its children.
This proves the proposed one-visit invariant for the stated finite grammar;
the implementation correspondence remains to be reviewed after Luna's edit.

For the nested example the repaired trace is:

```text
V0 V1 F1 A0 V2 V3 F3 A2 V4 F4 F2 F0
```

Now A0 stores B[alpha]=Component(v1), V3 first resolves E3 to that endpoint,
A2 stores B[beta]=Component(v1), and V4 resolves E4 to Component(v1).
For the unused-binder source the trace is V0,V1,F1,A0,V2,F2,F0;
there is no representative level entry to require, and no binder Name to visit.

## Constraint and runtime preservation

Leave `Finish(Case)` unchanged (`candidate_source.rs:1200`). It constructs:

| Retained child | Constraint/action retained |
| --- | --- |
| Scrutinee s | effect(s) <: effect(case), at occurrence(s), slot 51 |
| Every arm body b | endpoint(b) <: value(case), slot 50; effect(b) <: effect(case), slot 51 |
| Every Integer pattern p | endpoint(p) <: value(scrutinee), slot 52; endpoint(scrutinee) <: IntNegative, slot 53 |

All arms contribute, even when runtime selection will choose another arm.
Literal Finishes retain their value and empty-effect constructor facts.
The Case action/fact counters remain `2 * integer_patterns + arms` for value
actions plus the unchanged emitted effect facts. The repair removes extra
child constructor executions, not the single required parent constraints.
The existing action consumer resolves ValueConstraint's positive endpoint
and admits the value link (`candidate_source.rs:1744`); this packet proves no
additional propagation, extrusion, intrusion or generalization theorem.

Runtime construction preserves the source-order arm vector, each body label
and retained binder ID (`runtime/program.rs:559`). Integer patterns are decoded
from retained Integer expressions. `Instruction::Case` pushes Frame::Case
with the current lexical environment and evaluates the scrutinee once
(`runtime/machine.rs:690`). On return, the frame uses source-order `find`:
integer equality matches the corresponding integer, Binder and Wildcard always
match, and no matching arm returns NonExhaustiveCase (`:1223`). A selected
Binder extends the saved environment under its exact ID with the identical
`received.value` and `received.view`, and ParameterRole::Value. It then
evaluates only that arm's body. A CaseBinder Name looks up that same ID (`:584`).

Consequently the unused-binder witness has the candidate machine transition
to literal 11. In the nested positive, alpha and beta both receive the original
scrutinee's runtime value, so the selected Name returns 7. Wildcard adds no
binding. These are finite source-machine derivations under successful program
construction, not observed CLI outputs, full source/native equivalence, or
evaluator A/B. The negative's actual inference rejection remains Luna's
implementation/verification obligation.

## Application, prior evidence and remaining ownership

Both decisive old source facts are confirmed, and the nested stale-endpoint
premise is exposed. This removes R130's source uncertainty and supplies the
minimal repair obligation to Luna at `emit_candidate_source`'s Visit(Case) and
CaseArms. Fresh review must compare that edit to the push order above and the
unchanged Finish arm constraints. Actual public parsing/inference/evaluation
of the three rev3 probes remains unverified here. Luna owns the leased CLI
regression and final single verification command after the required reviews.

The prior case-pattern progress note and pinned browser examples are reused
only as experimental scope/history and concrete existing example sources.
Their old green checks do not establish unused-binder handling or one-visit
scheduling. R129's continuation probe is not a premise for this case proof.
No historical hygiene theorem is reapplied outside its actual premises.
No final solver conclusion is inferred from a transition model or test count.

Mutual TODO R130-CASE-REPAIR-1: Luna changes only the leased candidate source
owner to the schedule/optional representative lookup above. Falsifier: any arm
body or integer-pattern receives duplicate/missing Visits, a binder captures
an unvisited Name endpoint, or any listed Finish constraint is lost.
Mutual TODO R130-CLI-1: Luna supplies the three exact rev3 sources through the
leased public CLI regression; falsifiers are unused->11 failing, nested->7
failing, or the string-to-int negative succeeding. The CLI cannot certify
the visit count. Independent review and Luna adjudication own promotion.

## Frozen dependencies and resources

Baseline: `1f44d6087d696a2bf436c18cbb6c7446af9fa6f1`; no Git command was used.
All eleven rev3 pinned inputs matched their contract SHA-256 on initial read;
the five source owners and rev3 contract matched again immediately before
artifact creation. Exact source dependencies:

| Path | SHA-256 |
| --- | --- |
| crates/yu-solver/src/candidate_source.rs | 1c758cf1bff9eb2b304107f1511bcac442e9b09a165d57ba142888b50ca0365f |
| crates/yu-hir/src/module/local_source.rs | d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce |
| crates/yu-solver/src/candidate_value_graph.rs | 19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0 |
| tools/inference-playground/src/runtime/program.rs | 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d |
| tools/inference-playground/src/runtime/machine.rs | 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd |
| notes/design/2026-10-11-yulang-inference-top-level-principles.md | 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 |
| notes/design/2026-09-29-scc-intrusion-redesign-charter.md | 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed |

The remaining four pinned context inputs retain the exact hashes in rev3;
they are not proof premises. Supplementary read-only inspection of
`lib.rs::emit` and `shadow_apply.rs::candidate_component` was reported to Luna;
neither is an added dependency or a basis for a final solver-outcome claim.

Requested model/effort: gpt-6.1-sol/high. Observed model/effort: UNKNOWN/UNKNOWN.
Grant: 480 seconds aggregate, unchanged across rev2/rev3, no delegation.
Charge the full 480-second reservation conservatively; precise launch timestamp
and total active duration were not exposed to this leaf. First explicit clock
observation was 2026-10-19 14:13:20 UTC. No test, build, formatter, CLI execution,
network operation, heavy process or Git operation ran. Read/search/hash commands
provided provenance only. No implementation or test file was edited.

Only this artifact and `tasks/agent-loop/inbox/20261019-r130-proof.md` are new;
there are no scratch paths or unresolved descendant leases. This artifact is
frozen. The handoff records final write cessation; the assignment stops after
its two files and hashes are submitted, with review and integration pending.
