# Uniform source production through actual centers

Status: proved local producer lemmas and a concrete scalar elimination branch;
the universal unknown-hole source invariant remains open. This continues
[canonical hole transport, §5](2026-11-14-canonical-hole-transport.md#5-exact-remaining-work-and-center-dependence).
The owner's center decision, supplied by the supervisor, governs this work:
invariant arguments have actual names; a missing provenance proof is not a
semantic pending condition. No Step, boundary, or language rule is changed.

## 1. Uniformity and the exact source boundary

Fix the initial finite hole set H, its original origin map o, a current subset
R, a model predicate M, and a valuation v_m of those holes in each model m.
A source label consists of a retained Pattern p and a finite expression t,
with `Label context p t`. This asserts covered source syntax, exact translation
to `quote t`, and canonical tree structure. A labelled readback additionally
requires `Readback M o R root t`. All choices of p and t precede the quantifier
over models. Individual models may interpret surviving holes by recursive or
otherwise non-finite types.

The new results preserve this quantifier order. They do not infer a uniform
expression from a statement of the form "for every model there exists a finite
expression". Where one model is used to choose a subtree, the existing fixed
input expression makes the subtree syntactically unique, so the same subtree
works in every model. Consequently, the traversal and child-production lemmas
explicitly require an inhabited model predicate. Discharging that premise, or
handling inconsistent branches separately, remains part of source assembly.

The semantic and syntactic sides remain distinct. Uniform equivalence of two
actual origins does not by itself identify their retained Patterns or finite
expressions over R. In particular, it does not supply a common `Below` witness
for the historical packet presentation.

## 2. Nonpoint nominal arguments use their actual names

`GeneralNominalNamedArgumentReadback.Centers M parent name count identities`
asserts, for every argument position and every model of M, that the actual
nominal projection at that position is `Same` as the supplied source identity.
It is a positive center-provenance hypothesis, parameterized by the model
predicate so a centered relation can supply it directly.

For a recorded nominal descriptor whose TYPE parameters have arbitrary bounds
(l_i,u_i), `center_fits` proves that its actual named argument fits (l_i,u_i).
The proof obtains the descriptor's actual argument observation from the state
model, then transports both inequalities through `Centers`. Neither endpoint
is chosen as the actual argument, and the theorem requires no l_i = u_i.

`nominal_readback` assembles the nominal parent expression from the readbacks
of those named arguments. `labelled_readback` retains a supplied original
source Pattern; it does not reconstruct a catalogue key from a semantic name.

The graph side is separate. When `Centers` holds for every `Models state`
assignment, `named_argument` derives an actual `FeedbackK2.Argument` edge.
Together with source membership of the named arguments and child `Backed`
evidence, `nominal_backed` constructs the parent's graph backing. This is not
an inference from semantic readback alone. `nominal_discharge` then invokes
the established graph-backed occurs check: a represented old hole, represented
children, graph backing, an inhabited model set, and safety at the parent
produce a replacement over R with that hole removed. Occurrence of the hole
in a child would produce a real cycle and contradict the supplied safety.

For raw nominal reports with an absent inherited parent origin, the inspector
uses lower and upper endpoint parents. `nominal_fallback_parents` shows that
both parents have the same nominal root value as an explicitly supplied
actual root center fitting the interval. It uses nominal invariance via
`nominal_sandwich`. `nominal_fallback_centers` transports the same named
argument provenance to both parents. The parameter intervals themselves may
remain strict; no equality of their lower and upper bounds is concluded.
This handles the nominal reset mathematically, but it does not manufacture
the supplied root center or its fitting certificate.

## 3. Exhaustive report classification with source keys

The older open `Exposed` interface retained only capture and test inclusion.
At `origin = none`, a constructor report can have neither captures nor tests,
so those two inclusions alone do not locate its inspected interval in the
enclosing report. The additive `Fragment` relation instead records report
composition by visit, left/right append, and transitivity. `fragment_fields`
preserves captures, inspected intervals, anchors, and tests. No old definition
is edited and no execution guard is introduced.

`UniformReportDispatch.inspect_dispatch` and `many_dispatch` recurse together
over the actual `inspect` and `inspectMany` definitions. Given a represented
finite input forest with source labels, a successful report has either:

1. a fixed source-labelled subtree and uniform actual input meaning for every
   capture in the entire report; or
2. an existing hole in R at a successful constructor inspection fragment,
   retaining its interval, optional origin, and uniform leaf meaning.

The recursion visits both nominal endpoint reports. Structural descent keeps
the actual projected origin; nominal descent keeps the inspector's actual
inherited or fallback parent. Finished arity checks align the child forests.
Variables, including the terminal list-of-variables case, yield capture
labels directly. Constructor inspection of a leaf yields the second branch.
The result is a capture/exposure classification, not a head-wide `Matches`
theorem. In particular, the empty captures of a scalar query are not used to
assert a constructor match.

`SourceQuery context sources query` retains an original source Pattern, a
`Part` path to a subpattern, its coveredness, and its exact translation to the
query. `source_query_children` transports this evidence under each recursive
query descent, including record flattening and nominal endpoint traversal.
`source_report_dispatch` instantiates the full traversal for the actual
translated declaration forest. Thus the exposure branch has both a real
report fragment and an original source subpattern; it does not guess source
keys from the semantic constructor name.

`fragment_position` extracts the actual inspected interval. For a named
origin, `fragment_test` extracts its anchor and constructor test, and
`fragment_head` derives its uniform actual Head from `ProjectionModels` of
that exact full report. These are separate premises: classification does not
prove full-report model validity, recover every `none` origin, or provide
child graph backing.

There is one fully discharged exposure case. `scalar_source_trace` takes an
original scalar source query, a named actual scalar fragment, exact-report
model validity, and the old hole's uniform meaning. It derives the source
Pattern as `.app key []`, hence a zero-child labelled readback over the
surviving holes. It also constructs a one-elimination `HoleElimination.Trace`.
No child readback, replacement-variable scope, or numerical growth bound is
assumed for this scalar case.

## 4. Shared capture choices, child emission, and finite vocabulary

`UniformCaptureProduction.meaning_holds` converts a canonical finite meaning
and the original leaves' actual meanings into indexed readback.
`shared_candidate` transports one such capture to a positively supplied
shared actual origin. `simultaneous` selects one Pattern/expression pair per
required name before the model quantifier, with identity images elsewhere.

`packet_substitution` connects that uniform report result directly to the
actual packet interface. From positive `GenerationGuard` evidence and packet
branch models it constructs a single substitution and finite tree assignment
whose needed images have the source scope and hole closure, and whose meanings
satisfy the real `CaptureValue` predicate in every model. `needed_names`
identifies the needed-variable set with the finite list extracted from actual
normalized where-clauses. Unused images are explicitly the identity. This
uses the guard's positive shared-origin certificates; it never reasons that
a missing certificate causes pending.

`UniformChildProduction.quote_injective` proves that a finite query tree is
uniquely determined by its quotation. Thus `label_unique` gives uniqueness
for a fixed retained source Pattern. The existing real child-emission theorem
supplies that same Pattern in every model. `child_uniform` therefore chooses
one finite child tree once, then proves its `ArgumentValue` in every model,
including the emitter's second normalization. `child_readback` additionally
uses real structural containment to read back every positively retained
child input origin. Its retained-origin premise is explicit; it does not
claim to allocate or recover every fresh center.

`SourceLabelVocabulary.collect` and `collectArgs` extract the finite syntax
key list. `Scoped` and its theorems preserve those keys under subpatterns,
record-tail hiding, substitution, and normalization of covered templates.
`encoded_bounded` extracts a finite depth for a scoped Pattern's actual
inventory code using only its surviving-hole variable scope.
`replacement_trace` derives the corresponding Trace witness without a
separate numerical growth assumption. The code vocabulary is the existing
source-syntax codec vocabulary, not a list of semantic nominal tests.

This closes the finite-enumeration interface for replacements already
produced from scoped templates. The intended global vocabulary is the union
of keys collected from the finite initial label forest and checked registry
templates. Proving that every actual newly relevant replacement is generated
from this forest is still a source lifecycle obligation, not a consequence
of finiteness alone. Qualitative phase termination allows a locally extracted
finite depth at each genuine elimination; the existing Trace counts at most
the initial number of holes. A fixed numerical iterated bound would require
an additional uniform growth estimate.

## 5. Remaining source construction and transfer to centers

| Required source fact | New proved part | Still open |
|---|---|---|
| Uniform source labels over surviving original holes | Uniform full-report capture extraction; shared packet substitution; uniform real child trees and retained-origin readbacks | A reachable-state invariant providing the input forest and every newly relevant actual center, materialized origin, and settled output-only binder |
| Every relevant exposure | Full inspect/inspectMany classification, both endpoint fallbacks, original source subpatterns, actual positions/tests, complete named-scalar elimination | Recovery/center evidence for arbitrary absent origins; exact-report model validity; complete structural/nominal child labels and graph backing from actual source generation |
| Fixed vocabulary | Extraction from finite source syntax; closure under covered normalization, hiding, and substitution; derived replacement code depth | Source ownership of every generated replacement and initial label forest |
| Compatible new packet | One uniform semantic capture substitution and actual emitted child labels; prior exact history transport remains applicable | A canonical common expression or substitution-stable `Below` witness at every repeated capture, compatible with historical labels and new child label equations |

The last row cannot be replaced by a minimum-mass choice before refinement.
After global substitution, masses must be computed from the retained canonical
presentation, as in `CanonicalPacketTransport.filled_mass_exact`. Two finite
expressions may have uniformly equivalent meanings because the surviving
holes are constrained; that fact alone does not make them the same syntactic
tree or comparable by `Below`. A source invariant must unify those hole
representations, using genuine global elimination when necessary, before
constructing the new packet presentation.

Accordingly, universal `Simulation.next`, `ClassPHoleReadback`, and
unconditional unknown-root Class P Acc are not proved here. This is an open
producer proof, not evidence of a semantic counterexample. There is no new
owner question and no added pending rule.

The nonpoint nominal readback, fallback transport, report classification,
source-key closure, scalar elimination, and generic shared-choice lemmas are
parameterized by models and positive actual-origin data. They do not depend
on missing-provenance deferral. `nominal_backed` and `nominal_discharge`
specialize to the current carrier's `Models` and actual K2 edges. The packet
and child wrappers use positive `GenerationGuard`, `InputCoherence`, and the
existing emitter. A centered Step can reuse the generic lemmas by providing
its center, model, and graph facts; retargeting those concrete wrappers has
not been claimed or undertaken here. Boundary work remains with the other
worker.

## 6. Verification and independent review

Seven new modules are imported by appended lines in `lean/Yulang.lean`.
The separate audit is `lean/Audit/UniformCenteredProduction.lean`. Existing
proof modules, frozen files, specs, plan notes, and lake configuration are
untouched. No commit, push, or ref change is performed.

The configured `prover` role and launch configuration are unavailable in this
checkout; no prover agent ran. The primary performed the bounded derivation.
The separate available `settled_review` worker independently reviewed the
seven modules read-only. It found no blocking issue and specifically retained
the None-origin, exact-report model, common-presentation, and Simulation gaps.
Its suggestion to expose identity images for unused packet variables is
included. Final command results are recorded below after verification.

| Exact command, from the repository root | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalExposureSources` | 0 | All seven new modules are in this target's import closure; 810 jobs |
| `cd lean && lake build Yulang` | 0 | Aggregate build; 2322 jobs |
| `cd lean && lake env lean Audit/UniformCenteredProduction.lean` | 0 | 27 results; dependencies contained in `propext`, `Classical.choice`, `Quot.sound` |
| `git diff --check` | 0 | No tracked whitespace errors |

The final module, aggregate, and audit checks include the exported identity
branch of `packet_substitution`. Development elaboration attempts exited 1
before fixes to dependent indexing and mutual-recursion bookkeeping; these
are not the final proof state. The independent reviewer separately reran the
exact audit command with exit 0 and confirmed the same dependency set and
the scope of the final design note.

A separate successful scope check verified byte-prefix preservation of the
two existing appended files, all seven aggregate imports, the forbidden-token
scan of the new proof modules, exactly the intended new files, and unchanged
HEAD `cfa5d2611`. The earlier scope-check attempt read the audit log while it
was being regenerated; rerunning after audit completion passed. Existing
proof-module lines, frozen aggregate audit and README, specs, plan notes,
configuration, and git refs are unchanged.
