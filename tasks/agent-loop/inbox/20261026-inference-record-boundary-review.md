# Independent M3 review: record-boundary normal preservation

Date: 2026-10-26
Reviewer: `/root/record_boundary_review`, fresh nonauthor proof/spec auditor leaf
Decision: **ACCEPT** for the explicitly delimited record-local research component.
Blocking findings: none. Major findings: none. Mandatory repairs: none.
Baseline supplied by the assignment: `yulang3`, `bf81a1bd444b3bcbecca6b754ea6fb603262f368`.
No Git operation was used to inspect or modify that baseline.

This acceptance does not close `SourceProblem.InferenceSoundness`, establish the
native-to-plan bridge, or approve new production semantics. The original
whole-language domain and its shared scoped witness remain unchanged.

## Frozen inputs and audit evidence

The following SHA-256 values were independently recomputed and matched. The
three repository source inputs were rechecked immediately before writing this
receipt:

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean` | `1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056` |
| `notes/theory/2026-10-26-record-boundary-preservation.md` | `7d75b8876e1706a00eabdfb6960d17d67cfe219b82ed44d506ea5889e0148dc4` |
| `docs/yulang-whole-language-semantics-ja-expanded-20261023.tex` | `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |
| Producer `check-06-build.log` | `47e45f2edc5f25dfb410eac3424f093676e2b7bc9ca5907251684d924282a520` |
| Producer `check-07-audit.log` | `9b875fa0d6aadf27f488d80ea6332be31999388ff2f2a57e5094fd4f901559d6` |

Producer evidence is under
`/workspace/scratch/f98087c7ac1a/inference-record-boundary`.
Its copied Lean source has the same frozen source hash. The project pin is
`leanprover/lean4:v4.35.0`, with no external packages and `-j1 -M1024`.
The build log reports successful construction of the selected module, two jobs.
This is a selected-module build, not a whole-project integration build.

I read the originating-module audit implementation, every public root's complete
printed type and axiom result, and mechanically checked its complete inventory.
It selects all `.thmInfo` declarations whose module index is the exact originating
module, rejects project axioms, requires the fourteen named roots, and checks
transitive axiom dependencies against the standard allowlist. The log has 77
unique begin markers, the identical ordered 77 end markers, exactly one axiom
result for each name, and the terminal `YULANG_AUDIT_COUNT 77`. No audit diagnostic
or missing root occurs. The inventory independently recounts as follows:

| Complete inventory | Count |
| --- | ---: |
| No axioms | 62 |
| `propext` only | 11 |
| `propext`, `Quot.sound` | 4 |

For the fourteen public theorem roots, under `YulangClosure.RecordBoundary`:

| Axioms | Roots |
| --- | --- |
| None | `Witness.direct_comparison_nontransitive`; `Witness.accepted_paths_have_different_views` |
| `propext` | `compileField_sound`; `common_field_resolved`; `required_input_present`; `fieldRun_preserves`; `run_preserves`; `fieldRun_presence`; `run_survivors`; `execute_runs` |
| `propext`, `Quot.sound` | `compile_sound`; `outputTyped_visible`; `compiled_run_preserves`; `composed_survivors` |

The full log retains all 77 exact types and axiom lists, including private and
generated declarations. Source inspection found no proof holes, project axioms,
`native_decide`, kernel bypass or unsafe implementation override. The dependency
cone is this module plus `Std`; the transitive axiom audit supplies the indirect
check. Earlier diagnostics remain in `check-01.log` through `check-04.log`:
check 03 is a warning-only receipt, while checks 01, 02 and 04 contain actual
errors. The final source-check log 05 is empty, and the later positive build and
complete audit give the substantive success evidence. I did not rerun Lean or
Cargo: zero of the two optional reviewer Lean calls were consumed. No concrete
remaining checker risk justified repeating the frozen successful checks.

## Independent predicates and mathematical review

The original normal-record claim is at manuscript lines 360–402; its exact
non-resurrection equality is at lines 421–429. The Lean definitions and proofs
establish their delimited normal-result component rather than restating it as an
input assumption.

`SlotTyped` and `ViewTyped` (Lean lines 39–49) refer only to payload typing,
signature lookup and input visibility. They do not refer to compilation,
execution, successful checking or preservation. Required declared fields cannot
be absent; present optional payloads still have their declared type; undeclared
labels are absent from the visible view. This is the manuscript's
`Req(R) ⊆ dom(r) ⊆ Lab(R)` and payload condition. The payload predicate remains
independently supplied, as is appropriate for a component lemma.

`FieldPlan.Valid` records source lookup, the presence disjunction and actual
child-resolution equality. It does not require any output typing conclusion.
`compileField` constructs those conditions by cases, and `compile_sound` aligns
the complete target list with the constructed plan. `common_field_resolved`
extracts the selected child cast for every permitted common field. Optional
payload resolution is never bypassed on the ground that the input might be
absent. A rejected required-presence case may stop before payload resolution;
no accepted comparison thereby escapes the child obligation.

`PresenceValid known input` is an explicit, input-specific existence premise for
asserted known bits. It is not accepted as arbitrary trusted truth. In the
optional-to-required case it is exactly the additional premise allowed by the
manuscript. `required_input_present` derives the required visible lookup: the
absent-plan branch contradicts target requiredness, a required source follows
from input typing, and the remaining case follows from authentic presence.
Neither compilation nor a normal run is used as a substitute for that proof.

`FieldRun` reads only `input target.1`. Its constructors return absence, preserve
missing input, or invoke the retained cast on a present value and retain its
normal result. `Run` follows plan order and concatenates each actual child trace
before the remaining trace. There is no backing object, hidden lookup or default
value constructor. Arbitrary child traces are admitted; this proves neither
effect permission nor request/resumption safety.

`ChildSound` quantifies over payload source/target types, the resolver's actual
cast, a typed input payload and its actual normal child execution. Its conclusion
is only payload preservation. It does not assume record preservation, record
output typing, plan correctness, a successful record run, or termination.

The central theorem has precisely these premises:

```lean
compiled : compile source known resolve targets = some plan
inputTyped : ViewTyped typed source input
presence : PresenceValid known input
children : ChildSound typed resolve child
run : Run child input plan trace output
```

Its conclusion is
`ViewTyped typed (signature targets) (visible output)`.
`fieldRun_preserves` handles all three execution constructors, `run_preserves`
proves ordered slot typing by induction, and `outputTyped_visible` transfers that
independent slot meaning through matching first-name lookup. No desired record
conclusion is hidden among these inputs.

`run_survivors` derives exact Boolean presence equality without requiring child
payload preservation. `composed_survivors` first establishes intermediate typing
from first-run preservation, then applies the one-step equality twice. The
absence of a second `PresenceValid` premise is sound for this theorem: its
conclusion concerns presence only, not second-run output typing. It does not
silently claim that the final required fields are typed without that premise.

`signature` and `visible` both use first-name lookup. Duplicate target entries
remain separate ordered plan/output slots; the manuscript's finite-map
correspondence uses unique target names, as the companion explicitly states.
The generalized first-match theorem is sound and does not identify arbitrary
duplicate entries. A source signature may be a general map in Lean; finite-map
signatures are a valid specialization. These representation choices do not
weaken the manuscript's finite-map case.

`execute_runs` constructs a normal run of the pure specialization, so the
execution relation is not merely an uninhabited safety predicate. Both concrete
witnesses are checked by ordinary `decide`: the exact optional nontransitivity
shapes are retained, and the second witness includes all three successful plan
compilations plus the unequal direct/sequential visible results.

## Source and native mapping

| Source claim | Lean representation / theorem | Application boundary |
| --- | --- | --- |
| Manuscript 360–368: visible record typing | `SlotTyped`, `ViewTyped` | Payload typing is independent; no backing-object view. |
| 380–386: required presence, missing optional, common payload comparison | `compileField`, `compile_sound`, `common_field_resolved`, `required_input_present` | Boundary identity and owned presence/evidence metadata are not represented here. |
| 387–402: ordered normal record conversion and output typing | `FieldRun`, `Run`, `compiled_run_preserves` | Child normal preservation is explicit; full bind/effect/resumption contract remains external. |
| 406–419: direct nontransitivity and accepted path dependence | The two `Witness` theorems | Computed examples of this component, not native surface-cast execution. |
| 421–429: no resurrection | `run_survivors`, `composed_survivors` | Exact sequential visible intersection; no replacement by an endpoint comparison. |

The actual native record branch at `crates/yu-solver/src/lib.rs:14593` matches
the documented static shape decisions: first-source-name lookup, target-order
inspection, missing optional omission, missing-required diagnostic, and
`RecordAdaptationUnavailable` for optional-to-required. Every permitted common
field contributes its actual payload pair. The first-name and deferred-child
claims are supported by the existing
`f5b_record_comparison_is_local_and_retains_late_child_bounds` body, which was read
but not executed.

The retained `RecordDispatch` has lower and upper indices plus each typed pair.
Its candidate dispatcher takes children in reverse when prepending to the queue,
consistent with the source-order child vector; this scheduling observation does
not establish runtime cast evaluation order. No such operational equivalence is
claimed by the proof. The companion correctly distinguishes accepted shape
conditions from native success: a native `Ok` can carry diagnostics, and retained
child admission is not a selected successful cast. Taking all `known` bits false
matches the native static presence policy; the genuine-presence extension is a
research parameter, not a claim that native code already admits it.

## Parent application and remaining owners

This removes the record plan's own normal shape/payload-preservation and exact
survivor subproof once its honest inputs are supplied. It does not construct the
original `SourceProblem` instance or invoke `InferenceSoundness` with a concrete
native solver. I inspected `Contracts.lean:128`: that unchanged root still asks
for an original source judgment and the same scoped witness from every supported
successful generated solution.

The next application must come from the original source/native elaboration owner:
construct the actual boundary's plan and child evidence, authentic presence,
label representation, identity/scope/owner metadata and the corresponding run.
The child operational proof owner must supply `ChildSound` and separately the
stronger all-request-prefix and typed-resumption contract. Defaults, spread,
open rows, nominal projection/cast resolution, hidden dependencies, complete
Call/effects and joint source reconstruction remain original-language obligations.
The companion and progress contract preserve these boundaries explicitly.

## Resource and write cessation receipt

Review method: independent source/proof reading, exact frozen-hash checks,
native owner/test inspection, complete audit-log inventory validation and public
theorem-type inspection. No subagents, Git operations, compiler changes, native
tests, new Lean checks or shared integration were performed. No reviewer scratch
project was created. All producer proof, notes and logs were read-only.

Sole write:
`tasks/agent-loop/inbox/20261026-inference-record-boundary-review.md`.

**Final writes-stopped: true.** The frozen producer files remain unchanged.
