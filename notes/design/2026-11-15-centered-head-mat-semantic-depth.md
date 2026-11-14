# Total semantic labels and successor ancestry

Status: checked local bridges and conditional ancestry, astra2-centered-25,
2026-11-15. `GroundDepthBound roles` remains open. The new result reduces it to
the explicit local producer `GroundHeadReadback roles` below. No reachable
unbounded-depth example was found or certified, and there is no owner question.
The Step, source contract, refresh certificates, boundary, and earlier files
are unchanged.

## Source authority and scope

Section 6.3 says that Paterson size and occurrence counts use the unnamed
arguments of where-children: 「名前なしの引数だけで数え、この出力専用の変数は数えない」.
It also requires counting after hidden record fields are removed and after
same-tag variant payloads are merged. The new normalization theorem interprets
both operations in the ordinary general carrier. `needed_unnamed`,
`needed_in_head`, and `needed_excludes_output` connect child captures to the
checked input variables and exclude output-only variables.

The current `DeclarationChecked.countsCovered` requires normalized heads and
unnamed where-arguments to be in the count-covered fragment whenever an impl
has a child. A residual multi-tag union is outside that fragment. This is an
existing declaration check, not a new restriction in this work. Associated
outputs, defaults, and leaf declarations can still contain multi-tag rows;
their size is not added to the ancestry budget.

Section 6.5's explicit center is an unknown argument identity, not a concrete
type chosen by execution. All labels here are retrospective witnesses for one
model. Different models can use different labels and captures. The proof
neither chooses runtime types nor refreshes cached heads from these witnesses.

## Proven bridges

`GeneralNominalCenteredHeadMatPatternSemantics` defines the meaning of every
Pattern: variables, applications, records with arbitrary tails, variants,
and joins. `normalize_sound` proves semantic equivalence before and after
normalization, including hidden-field removal, arbitrary record tails,
duplicate-tag payload unions, tag sorting, and multi-tag rows. Application
meaning is parametrized only by congruence under equivalent arguments.

`GeneralNominalCenteredHeadMatCompilerSemantics.algebra` instantiates that
parameter with the actual compiler's primitive and invariant-nominal meanings.
`translate_value` and `compiled_normalized` apply to successful translations
in actual mode. The total algebra has a fallback value on malformed or unknown
applications; these theorems do not claim those applications compile.
`child_normalized` reads the corrected packet's actual child-center equation,
not an equation from the superseded materializer.

`GeneralNominalCenteredHeadMatSemanticSubstitution` proves substitution,
congruence, closure, and normalized-substitution meaning. The semantic label
module then distinguishes:

- `Meaning`: a finite closed normalized Pattern equivalent to a carrier value;
  this relation permits multi-tag rows and total record tails.
- `CountedMeaning`: `Meaning` with the existing normalized `covered` condition,
  for unnamed-argument descent.
- `Inputs`: a list of `CountedMeaning` witnesses for a centered site's arguments.
  Endpoint bounds and inspection origins remain separate packet/site facts.
- `Captures`: all capture images are count-covered, and every name needed by a
  normalized unnamed child has a closed image equivalent to its actual binder.

`child_inputs` derives emitted child labels from corrected packet `Holds`,
`Captures`, clause membership/signature, and source constructor coverage.
`reachable_child_inputs` derives that coverage from the actual trace, source
WF coverage, and the installation frame. It does not derive `Captures`.
`label_descent` reuses `checked_normalized_descent` for these exact child labels.
`bounded_label_descent` additionally takes the instantiated-head comparison.

`GeneralNominalCenteredHeadMatInspectionSemantics.closed_value` connects every
old `ClosedTerm` to the new total algebra. Its record proof transports sorted
fields using the duplicate-free certificate already contained in `ClosedQuery`.
`GeneralNominalCenteredHeadMatSourceLabels.point_root_inputs` consequently
initializes the new relation from the original `GroundRoots` and point-root
premises. No stronger source condition, new root label, or root-model premise
has been added to the target. `old_inputs` also converts existing finite
center readbacks.

## Exact remaining producer

All names in this block refer to the actual total-materialization successor;
the definition is `GeneralNominalCenteredHeadMatSemanticAncestry.EnabledHeadReadback`:

```lean
EnabledHeadReadback registry context root :=
  ∀ state, Steps (Step registry root) (initial context root) state →
    ∀ effect, Installable registry state effect →
      effect.plan.packet.declaration.requirements ≠ [] →
    ∀ model, Models state model → Holds effect.plan model →
    ∀ parentLabels,
      Inputs (algebra registry.constructors context.interpretation)
        model effect.plan.input parentLabels →
    ∃ capture, Captures effect.plan model capture ∧
      mass (substArgs (images capture)
        (normalizeArgs effect.plan.packet.declaration.head)) ≤ mass parentLabels
```

`GroundHeadReadback roles` quantifies this producer over exactly the original
ground-source parameters: `Checked registry`, `InitialSource`, point arguments,
`GroundRoots`, and WF `Coverage`. Neither predicate is proved in this turn.
In particular, the local definition quantifies over every semantic parent-label
list, not only those chosen by an ancestry proof. These labels need no separate
syntactic WF certificate. The producer must recover the finite captured values
and establish the head-mass comparison from their meanings and the real guards.

This is the remaining representation bridge. The old head matcher still asks
for `ClosedTerm` inspection trees. The preceding exact-tail pattern compiles
under its coverage premise but has no old `ClosedTerm` for that literal pattern.
The new semantic relation represents that pattern, but semantic inversion of
the head schema and its finite projections, with the mass bound, is not yet proved.
No full-journal observation is substituted for a justified cache certificate.

## Retrospective reduction on the unrestricted Step

`sites_bounded` proves, assuming `EnabledHeadReadback`, that every recorded
centered site in every actual successor trace has retrospective labels with

```text
AtDepth registry initialSeed root.identity depth site.occurrence.identity
Inputs (algebra registry.constructors initialInterpretation) model site labels
depth + mass labels ≤ mass rootLabels
```

The theorem quantifies over every model of the endpoint. Model restriction
handles both refresh constructors, equating, reobservation, and merging.
Enqueue is impossible because generated demands are already registered.
Installation uses the corrected `install_models`, obtains its actual parent
site from the frame, constructs each child label from the total schema, and
uses checked normalized Paterson descent. No compatibility subrelation or
literal erasure simulation is used.

`installed_depth_bound` extracts a prestate model from an enabled installation's
common-model guard, so it does not require all reachable journals to be
inhabited. It bounds installed depth by `mass rootLabels`. The final chain is:

```lean
GeneralNominalCenteredHeadMatSemanticAncestry.ground_depth_bound
  (production : GroundHeadReadback roles) : GroundDepthBound roles

GeneralNominalCenteredHeadMatSemanticAncestry.progress
  (production : GroundHeadReadback roles) :
  GeneralNominalCenteredHeadMatStepExecutor.Progress roles
```

Thus the existing finite fact cover, missing-signature measure, and
administrative accessibility can consume the new labels once the producer is
available. Unconditional progress is not established. `CanonicalExitLifting`
is unchanged and remains open. General `Extension`, `SelectedCompletion`,
and exhaustive K2 projections are also unchanged.

## Hypotheses and review

The semantic theorems retain their displayed local hypotheses: congruent
application interpretation, successful actual translation, closed query/tree,
or capture substitution equivalence. Record permutation retains duplicate-free
field labels. Source-label conversion retains the original `GroundRoots`,
point inputs, and a source model. Child readback retains actual corrected
packet `Holds`, clause membership/signature, and constructor coverage; the
reachable variant derives the latter. Capture existence and the parent mass
bound remain exactly the producer above. Ancestry also retains `InitialSource`,
point roots, `GroundRoots`, and WF coverage; its global progress theorem
retains exactly `GroundHeadReadback`. No new scheduler or model-extension
hypothesis is hidden in that reduction.

No registered/callable `prover` role was available and no prover agent ran.
The primary constructed the bounded derivations. Separate read-only source
audit and fresh independent review found no defect; the reviewer checked all
seven modules directly with Lean, exit 0, and confirmed the conditional scope.

The exact public theorem inventory is in the new audit file
`lean/Audit/GeneralNominalCenteredHeadMatSemanticAncestry.lean`.

## Final checks

The following commands ran from `lean/`, each with exit code **0**:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadMatPatternSemantics Yulang.GeneralNominalCenteredHeadMatCompilerSemantics Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution Yulang.GeneralNominalCenteredHeadMatSemanticLabels Yulang.GeneralNominalCenteredHeadMatInspectionSemantics Yulang.GeneralNominalCenteredHeadMatSourceLabels Yulang.GeneralNominalCenteredHeadMatSemanticAncestry
lake build --wfail Yulang
lake build --wfail
lake env lean Audit/GeneralNominalCenteredHeadMatSemanticAncestry.lean
```

The full builds completed 2,838 and 2,839 jobs, respectively. The audit covers
all 55 new public theorems; its only reported logical dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. The reviewer independently ran
the audit with the same result. From the repository root, `git diff --check`
exited **0**. The append-only, frozen-file, import, prohibited-token and
dependency checks also exited **0**. Exploratory proof builds exited **1**
while elaboration errors were being fixed; one early build was run from the
repository root and exited **1**. All final commands above were rerun from
`lean/` after those errors were resolved. No git refs were changed.
