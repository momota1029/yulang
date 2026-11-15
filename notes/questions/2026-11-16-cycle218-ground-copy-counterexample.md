# Cycle 218: a ground source with a stale selected child

Status: checked refutation of the exact I40 EvidenceNode field; no language
semantics or operational definitions changed. 2026-11-16.

## Recommendation pending the owner's decision

Retain the refutation and delay the unrestricted EvidenceNode proof. Review how
historical generated occurrences relate to the parent's recomputed obligations.
Do not weaken Evidence, introduce a selection guard, or add model inhabitance to
the target to make this example disappear. No repair is implemented here.

## Exact result and stability scope

`Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation.not_evidenceNode` proves:

```lean
¬ B4SkeletonV7.EvidenceNode
    (GeneralDictionaryDefaultBoundary208.boundary
      GeneralDictionaryGroundCopy218Source.roles)
```

The separate `positive_premises` supplies the original checked registry,
InitialSource, point root endpoints, GroundRoots for every source model,
coverage, Initial, an actual corrected Steps trace, Reachable, generated child
membership, Stable at the original root and every generated occurrence (including
the selected child and its empty child list), selected Local,
a concrete journal model, and the empty ordered child-evidence relation.
`final_no_evidence` rejects the selected node in that same model. There is no
inhabitance assumption and no assumed constructor injectivity.

The final witness is after an actual corrected parent reinstall and saturation of
the entire original root. It satisfies more stability premises than EvidenceAt
requires. The earlier `GeneralDictionaryGroundCopy218Refutation` module also
records a smaller child-local witness; the main result here uses the stronger
`SaturatedRefutation` witness. The negation of EvidenceNode does not by itself
negate `B4TargetV7.Statement`; the cycle211 composition established a sufficient
implication, not an equivalence.

## Concrete source and operational account

The source has exactly the proposed eight slots, with seed 7:

| Slot | Meaning | Observation |
| --- | --- | --- |
| 0 | bottom | deferred |
| 1 | top | deferred |
| 2 | variant0(bottom) | variant0 with child 0 |
| 3 | variant0(top) | variant0 with child 1 |
| 4 | variant0(int) | deferred |
| 5 | variant0(bool) | deferred |
| 6 | Foo of the two actual arguments | two loose (2,3) nominal intervals |
| 7 | exact copy of Foo | point nominal intervals (4,4), (5,5) |

Ordinary equations fix 0–5 and equate 6 with 7. `Source.root_fixed` proves that
all source models interpret 6 as Foo[variant0(int), variant0(bool)]. The initial
observations at 2 and 3 follow from ordinary equations; no child-low refresh is
needed. The registry has only parent key0, `P[Foo[x,y]] where R[x,y]`, and terminal
key1, `R[T,T]`, with no named outputs. Both pass the actual declaration checker,
including Paterson and substitution-stable descent.

The checked path is initial → install parent → certified Reobserve → reinstall
parent → finitely many root-focused equate steps. The last sequence is obtained
from the existing termination theorem. The trace invariant exhausts all actual corrected Step
constructors; it is not an assumed transition checker.

The old child keeps two (2,3) intervals. Its centers remain the parent's distinct
purpose8 binder names. Every journal model of the stored parent gives those
centers inequivalent values. Raw top-level variable inspection starts with no
origins, so repeated-variable ProjectionModels impose no actual sharing there.
Two fresh candidate-private endpoint assignments witness the raw head test while
preserving every existing source identity. The selected child has no children.
Every possible evidence Frame would require equal centers, yielding a
contradiction, rather than merely failing one chosen Frame.

All root-generated occurrences in the final witness are enumerated: the parent,
the old loose child, and the new precise child. The two children have the same
identity and different argument intervals. The alias closure consequently also
makes the new child generated from the old one. Reinstall is an actual corrected
Step: its checked effect satisfies ChoiceCompatible, adds the precise child and
edge, preserves the model, and is not already committed beforehand.

After reinstall, every current parent Frame is committed using the stored precise
plan. This transfer remains valid as ordinary equations grow. The precise child
is pending because its lower slot 4 is deferred and cannot refresh in this
fixture. The old child remains known and selected, and evidence still fails.
Thus neither parent recomputation nor stability of the whole original root
removes the old occurrence from the unchanged EvidenceNode quantifier.

Other stability cases are closed as follows:

- Enqueue: all three generated occurrences are already registered.
- Both refresh constructors: the concrete journal model rules out any new head.
  Bottom/top have no head; variant-int/bool would require a raw slot representing
  the scalar payload, but this model contains no scalar at any source identity.
- Reobserve: all current nominal descriptors are point-valued.
- Equate: preserves the concrete model and source ownership; existing termination
  produces a finite terminal state for the original root.
- Install at the parent: any current Frame is already committed. Install at the
  precise child is excluded by pending status. Install at the old child: the common journal/packet model cannot exist because
  its actual centers differ in every journal model.
- Merge: exact finite site enumeration gives either different roles or reflexive
  aliases. Output requests are empty and no nontrivial alias edge exists.
- Local: known low endpoints, raw and actual cycle exclusions, administrative
  readiness, unique raw head, and both output-conflict exclusions are proved.

## Surface meaning and the specification question

Using `tick` for the fixture's numeric variant tag, the declaration/goal sketch is:

```yulang
impl P (Foo 'x 'y):
    where 'x: R 'y

impl R 't 't

// Ground demand at the use site:
// P (Foo (:{tick int}) (:{tick bool}))
// Its required child: R (:{tick int}) (:{tick bool})
```

This sketch uses the impl/where syntax from spec 6.2–6.3. Foo denotes the
invariant nominal constructor of this Lean fixture; this note does not specify
how variance is inferred for a new surface declaration. Role and method bodies
are omitted, and this is not a parser/runtime conformance test or a proof that
a Rust inference producer constructs these exact snapshots.

The behavior represented is selecting `impl R 't 't` for an old generated demand
whose two actual types are `:{tick int}` and `:{tick bool}`, because its historical
intervals still overlap. Sharing one named variable cannot provide the required
dictionary in the carrier. The initial root is already semantically ground;
Reobserve improves its cached descriptor, not the language-level root value.

The relevant established rule is [spec 6.3](../../spec/06-roles.md): siblings and
parents are rebuilt and recomputed after updates, and finalization waits for a
stable state at the end of the file (2026-11-08 decision). The same section's
same-input merging rule refers to actual argument identity, not just overlapping
interval endpoints. Its 2026-11-14 center rule also explicitly says that reusing
one type variable denotes the same actual argument; that is exactly the sharing
obligation for `R[T,T]`. The issue for the owner is how the formal boundary should
relate retained historical child occurrences to those recomputed obligations.
The current EvidenceNode field still quantifies over the stale occurrence after
the original parent is recomputed and the whole root is stable. This note does not choose
a new meaning for Yulang, delete historical demands, change matching, or weaken
the theorem.

## Verification and limits

All required fixture obligations are proved; none remain open for this candidate.
The permanent audit is `lean/Audit/GroundCopy218Check.lean`. The proof modules use only ordinary Lean
proofs; no sorry, admit, axiom declaration, or native_decide was introduced.

The proof skill's referenced prover configuration and role were absent in this
checkout. No prover agent ran. The primary constructed the final refutation and
raw leaf/subtree lemmas, complementary agents constructed disjoint support
modules, and a separate read-only review checked the primary's final derivation.
The review found no correctness issue. Build success and that review do not
establish a source-code producer bridge, runtime behavior, or the negation of
the B4 main Statement. Original-root stability is an explicit checked theorem.

## Full exported statements

The following names are in
`Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation`. These statements
use the exact module opens below; in particular `final` is the terminal state
of the original root starting from the actual parent-reinstalled state.

```lean
namespace Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model childSite model_forms low_high install_step)
open GeneralDictionaryGroundCopy218Reobserve (reobserved reobserve_step)
open GeneralDictionaryGroundCopy218Reinstall (reinstalled newChild newPacket reinstall_step reinstalled_reachable choice_compatible)
open GeneralDictionaryGroundCopy218SaturatedState
open GeneralDictionaryGroundCopy218Refutation (child_eq)
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalSaturationState (Generated)
open GeneralDictionaryGroundCopy218Stability (Supported)

theorem positive_premises :
    (GeneralDictionaryDefaultBoundary208.boundary roles).Checked sourceRegistry ∧
    GeneralNominalSourceFormation.InitialSource sourceRegistry context root ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] ∧
    GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation ∧
    (GeneralDictionaryDefaultBoundary208.boundary roles).Initial sourceRegistry root start ∧
    GeneralNominalCycleSteps.ChoiceCompatible reobserved.core.erased.current newPacket ∧
    GeneralDictionaryDefaultBoundary208.Step sourceRegistry root reobserved reinstalled ∧
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start final ∧
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final root ∧
    (∀ focus, Generated final.core.erased.current root focus →
      GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final focus) ∧
    Generated final.core.erased.current root childSite.occurrence ∧
    Generated final.core.erased.current root newChild.occurrence ∧
    (∀ focus, Generated final.core.erased.current root focus →
      focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence) ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final childSite.occurrence ∧
    (∀ child ∈ ([] : List (Occurrence roles)), GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final child) ∧
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry final childSite.occurrence (.selected 1 []) ∧
    Models final model ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralDictionaryDefaultBoundary208.boundary roles).Evidence
        sourceRegistry final model child dictionary) [] []

theorem final_no_evidence :
    ¬ (GeneralDictionaryDefaultBoundary208.boundary roles).Evidence sourceRegistry final model
      childSite.occurrence (.node 1 [])

theorem not_evidenceNode :
    ¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryDefaultBoundary208.boundary roles)

end Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation
```

## Final checks and file manifest

Commands ran from `/home/momota1029/rust/yulang-m1-sol/lean`:

| Command | Exit | Result |
| --- | --- | --- |
| `lake build --wfail Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation` | 0 | All new proof dependencies built, 1320 jobs. |
| `lake build --wfail` | 0 | Entire library including appended imports, 3191 jobs. |
| `lake env lean Audit/GroundCopy218Check.lean` | 0 | Only propext, Classical.choice, Quot.sound, or subsets; main three results use exactly those three. |

A development attempt at the first command exited 1 on a `rw` elaboration in
`SaturatedParent.frame_committed`; the explicit children-list conversion fixed
it, and the final command above passed. No unresolved build failure remains.
Fresh independent review of the completed parent commitment and final refutation
found no correctness issue and independently reran the permanent audit (exit 0).
The state-invariant module was also independently reviewed by a different agent
from its author. No configured prover role ran, as recorded above.

New proof files (all directly imported by appended lines at the end of
`lean/Yulang.lean`):

- `lean/Yulang/GeneralDictionaryGroundCopy218Cycles.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Install.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Leaf.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Obstruction.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Refresh.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Refutation.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Reinstall.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Reobserve.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218SaturatedParent.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218SaturatedRefutation.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218SaturatedState.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Source.lean`
- `lean/Yulang/GeneralDictionaryGroundCopy218Stability.lean`
- `lean/Yulang/GeneralDictionarySubtreeTermination218.lean`

Other new files:

- `lean/Audit/GroundCopy218Check.lean`
- `notes/questions/2026-11-16-cycle218-ground-copy-counterexample.md` (this note)

Only the root import file is modified among pre-existing Lean files, with
append-only imports. `lean/Audit.lean` and `lean/README.md` are unchanged. No
commit was made; the additions remain in the working tree. The prohibited-proof
construct scan found no matches in any new Lean file.
