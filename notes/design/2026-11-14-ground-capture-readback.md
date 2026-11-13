# Ground capture readback: recovery, source syntax, and record mass

Status: partial proof companion, 2026-11-14. Continues
[ground factorization progress](2026-11-14-ground-factorization-progress.md).
Authority remains `spec/06-roles.md` §6 and the approved B4 statement with
addenda 1–7. The Step relation, guards, and all previously integrated
definitions remain unchanged.

**Result:** an actual installing packet's retained and missing constructor
roots have a finite forest preserving their original closed Pattern labels.
Source-key-preserving reification is proved along finite constructor paths.
Canonical record and variant projections yield closed source Patterns with
strictly smaller checker mass. Record normalization and exact record counting
are proved at separate syntax boundaries. The general Acc reduction now
needs factorization only on states reachable from the fixed initial source.

**Still open:** `GroundCaptureFactorization` and the new
`ReachableCaptureFactorization` are not discharged for arbitrary Checked
registries. This change does not add an unconditional ground-root Acc theorem
or widen the previously closed Show theorem. The exact missing connections
are listed in §6; none is silently supplied by source formation.

## 1. Retained roots, missing roots, and actual recovery

The existing `Inputs context model site labels` supplies a closed canonical
Expr for every input label, containment between the input endpoints, and
exact readback for every origin that is actually retained. It does not assert
that all inputs have origins. Compound input emission can legitimately store
`none`, and subsequent recovery can add a source endpoint origin.

`InspectionOrigins.inspect_counted` and `many_counted` prove for every actual
recursive inspection report that the number of recorded constructor tests
is at most the number of inspected positions. This follows through every
inspector branch, including two-endpoint nominal inspection. A constructor
visit with no origin adds one inspected position and no test. Hence
`missing_root` proves a strict deficit for a scalar, structural, or nominal
query inspected with `none`. Additivity gives `many_complete_component`.

The actual `Safe` guard requires equality of these total counts on the
**recovered** report. `complete_root` therefore forces a recovered origin
at each constructor root with located bounds. `GroundForests.safe_missing_root`
uses the real argument-location result to supply those bounds, then unfolds
`recoverOrigin`. If the stored origin was `none`, recovery can succeed only
through `EndpointEqual`. Thus it derives, rather than assumes,

    forall m satisfying the current state, lower_i(m) ≈ upper_i(m).

This applies to every unnamed input position, independent of its role arity,
head family, or registry recursion. Unused variable and deferred query roots
are deliberately outside the constructor-root conclusion. There is no
declaration rejection or additional runtime guard.

`missing_constructor_meanings` combines this equality with the already
supplied finite input meaning V. Since lower <= V <= upper and lower ≈ upper,
both endpoint source origins have exact meaning V. This does not choose a
value inside an interval: V came from the parent input invariant, while the
guard proves the endpoint collapse.

`retained_forest` and `recovered_forest` produce finite lists of entries
`(origin, original Pattern label, closed Expr)`. `GroundPacketForest.packet_forest`
combines retained roots with **both** endpoint source roots at missing
constructor positions. Its `roots_meaning` theorem proves every listed entry
has the original input meaning. The forest is obtained by finite enumeration
of the role's input positions, so it needs no assumption that every old input
is present. It is a local per-packet forest, not a fixed future signature cover.

The two endpoints matter. The original inherited report uses lower-source
and upper-source nominal fallback origins separately. Recovered inspection
uses the recovered lower origin for both. They need not be the same syntactic
path. The new forest supplies both original roots; it does not rewrite one
report into the other or identify distinct intervals by their endpoints.
Recursive transport of these meanings through the entire original report
remains to be assembled.

## 2. Source-preserving finite reification

`SourcePatternParts.Part` follows actual Pattern arguments, record payloads
and tails, variant payloads, or join branches. It retains constructor keys
from the source syntax, even when several catalogue keys share a semantic
nominal name.

`child_source` derives source-pattern provenance for a nonvariable child of
an actual translation. In a record, translation flattens the tail and sorts
field/query pairs. Membership through the sorting permutation shows that
every child query came either from the current payload or from a tail
payload. No inverse lookup of a nominal name in the constructor catalogue
is performed. A variant plain-variable capture is excluded when the child
quotation is closed; it cannot represent a leaf-free Expr.

`closed_child_source` and `followed_source` extend this to the existing
`Follows` relation, which selects genuine constructor positions of a finite
Expr. They initially produce a raw Pattern whose translation is the required
subterm quotation. The next theorem closes the normalization gap in that result.

`ClosedPatternNormal.translated_normal` proves:

    ClosedQuery (translate constructors interpretation p)
      -> normalize p = p.

Here `ClosedQuery` excludes variables and deferred queries, requires matching
structural arity, and requires distinct record labels. `quote_closed` derives
it from a closed canonical Expr. The record proof recovers the original
unsorted field membership and distinctness through the sorting permutation.
The tail cannot contain the new field label, so `hide_absent` proves hiding
does nothing. Payloads and tails are normalized recursively. Successful
closed translation rules out joins and merged plain-variable payloads.

`closed_reification` now concludes, from a `ClosedTerm` and a `Follows` path,
that the selected Expr has a normalized closed Pattern witness which is a
`Part` of the **normalized original label**. This covers scalar, pair,
canonical record, variant, exact-empty, and invariant nominal terms of the
existing finite Expr carrier. It assumes no injectivity or surjectivity of
catalogue names. The remaining task is producing all required `Follows`
paths from arbitrary real reports, not finding fresh constructor keys.

## 3. Actual record and variant inversion

`RecordInversion.field_presence` proves that the carrier field/trivial probe
on a finite record succeeds exactly at its listed labels. From carrier
equivalence, `record_membership` therefore derives equality of label sets.
With sorted canonical signatures, `record_signatures` derives equality of
the label lists themselves. Payload equality then follows from the existing
general structural projection theorem.

`record_projection` applies this to an actual `Observes` derivation. The
source record and inspected record initially have independent canonical
label lists. The theorem recovers their equality, a valid finite position,
and the exact finite payload meaning. `variant_projection` similarly
recovers the tag and the unique payload position from actual observations.

`SourceProjection.actual_record_pattern` and `actual_variant_pattern` combine
this inversion with source-preserving reification and the mass results below.
They return an actual readback, a closed Pattern from the normalized source,
and strictly smaller **existing checker mass** for that Pattern.

These theorems already handle independently specified record signatures or
variant tags. They still assume the source finite term is in the same
constructor family as the observed projection. A complete inspector induction
must first rule out other source families. In particular, exact-empty and
the empty-record shape are distinct carrier meanings; their distinction has
not been proved in this new inversion layer. Arbitrary noncanonical record
projection shapes are not covered: duplicate labels could expose shadowed
payloads. Successful structural inspection must supply canonicality from
its match with the snapshot's canonical shape.

## 4. Normalized substitution and the exact counting measure

`PatternRecordSubstitution.hide_commute` and `hide_substitution` prove the
record-spine identities for every Pattern and every capture substitution.
The latter explicitly retains the outer hiding after substitution, because
a captured tail can introduce a newly shadowed field.

`normalize_template` proves, when the raw template p is covered,

    normalize (subst sigma p) = normalize (subst sigma (normalize p)).

Records and variants are allowed throughout the template. Captured Patterns
are unrestricted, including captures that introduce record hiding or variant
joins. `counted_template` and `mass_template` transport this equality to the
existing checker. This is broader than the earlier application-only result.
It is not the general raw-declaration theorem: Checked supplies coverage
**after** normalization, while this theorem requires coverage of the raw
template. Raw joins that normalize away still need a separate argument.

`ClosedPatternMass.queryMass` charges 1 for a scalar, pair, variant,
exact-empty, or nominal constructor, plus its child costs. A record with k
fields costs k+1 plus the payload costs. This is the actual binary record
spine and its empty tail, rather than a single structural node.

`record_sort_mass` proves that flattening and sorting fields preserve this
cost. `translated_mass` then proves that a closed canonical translated raw
Pattern's encoded size is exactly its query cost. `closed_mass` obtains the
existing normalized Paterson mass for every `ClosedTerm`:

    mass [label] = weight term.

`child_weight` proves strict descent for every genuine finite child position,
and `followed_pattern` gives source syntax, actual readback and a nonincreasing
mass bound along any `Follows` path. The actual record/variant results above
strengthen it to strict descent for their single observed edge.

This reconciles source reification with canonical record counting. It does
not yet bound the sum of all instantiated head positions under one shared
substitution; per-capture descent alone is insufficient for that sum.

## 5. Reachable-only factorization and Acc

`GroundReachable.ReachableCaptureFactorization roles registry context root`
retains the old local factorization conclusions but adds an actual finite
trace from `initial context root` to its state premises. It still quantifies
over installable guarded packets with children, a current and packet model,
and finite `Inputs`. It must return one Pattern substitution with:

* instantiated head mass at most the simultaneous input-label mass;
* closed instantiated child labels of the checked arities;
* each child's existing `ArgumentValue` capture/template evidence.

`packet_production` derives actual emitted-child input meanings using the
existing emitter theorem. The new `sites_bounded` induction uses the trace
premise at each installation. Every actual constructor is handled; no Step
is replaced by an abstract transition. At child birth, checked strict
Paterson descent gives the usual invariant

    ancestry_depth + mass(site_labels) <= mass(initial_root_labels).

Labels remain retrospective: the final model of a finite trace is restricted
backwards, and local finite labels may depend on that model. No common model
of an infinite trace is assumed. `installed_depth_bound` and the existing
finite allocation/report/signature-cover result then yield:

    Checked registry
    InitialSource registry context root
    PointSource context root
    GroundRoots context root rootLabels
    ReachableCaptureFactorization roles registry context root
      -> Acc actualStep (initial context root).

This is `accessible_of_reachable_factorization`. `all_states_suffice` proves
that the old all-states hypothesis implies the new one. The new hypothesis
contains no depth bound or termination conclusion. It is still unproved.

## 6. Updated obligation table

| Obligation | Standalone progress | Remaining connection |
| --- | --- | --- |
| Retained/missing root forest | `complete_root`, `safe_missing_root`, `packet_forest` | Recursive original-report transport from these roots, including structural descent before nominal endpoint fallback |
| Record/variant inversion | `record_signatures`, `record_projection`, `variant_projection` | Cross-family exclusion and extraction of every required canonical finite path from the full report |
| Source-key-preserving reification | `closed_reification`, `followed_pattern` | Feed it the paths from the preceding obligation; no catalogue inverse is required |
| Normalized substitution | `hide_substitution`, `normalize_template`, `counted_template` | Raw joins that disappear during normalization; complete normalized translation/substitution into child templates |
| Head mass and termination | `closed_mass`, strict actual record/variant Pattern descent, reachable-only Acc reduction | One simultaneous substitution and its head-wide mass bound, with all child `ArgumentValue` evidence |

The single explicit remaining premise of the strongest general Acc theorem
is `ReachableCaptureFactorization`. The table decomposes its unfinished
construction; it does not present the new local lemmas as a proof of the
whole premise. The prior closed Show theorem remains available unchanged.
No new counterexecution, implementation obstruction, or semantic gap was
established. No additive Step repair or owner question was needed. Roots with
unknown holes and general strict-interval initialization remain outside the
conditional ground-root termination result.

## 7. Review and validation

The primary constructed these bounded proofs. The configured prover role
is unavailable: the checkout lacks `rules/agent-orchestration.md`,
`rules/research-lab.md`, `rules/design-authority.md`, `.codex/config.toml`,
and `.codex/agents/prover.toml`; the live collaboration schema has no prover
role. No prover agent ran. Separate read-only review checked the root-count
argument, recovery/endpoint distinction, source-key provenance, normalization
scope, record signatures, mass correspondence, and the reachable Acc
quantifiers. No blocking issue was found. The review confirmed the remaining
raw-template coverage and full-report alignment gaps.

Final commands from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalSourceProjection Yulang.GeneralNominalGroundReachable Yulang.GeneralNominalGroundPacketForest Yulang.GeneralPatternRecordSubstitution` | 0 |
| `lake build Yulang > /tmp/yulang-ground-readback-build.log 2>&1` | 0 |
| `lake env lean Audit/GeneralNominalGroundReadback.lean` | 0 |

The focused entrypoints build all ten new modules (746 jobs); the full build
completed 2222 jobs. All 30 audit entries use only `propext`,
`Classical.choice`, `Quot.sound` or fewer. Intermediate elaboration failures
were corrected before these final checks. No new parser or dictionary
execution fixture was constructed or tested.

From the repository root, `git diff --check` and
`python3 /tmp/yulang-ground-readback-scope.py` exited 0. The scope check compares
existing files byte-for-byte against HEAD prefixes, verifies the ten imports,
and scans the new modules for prohibited proof tokens. The only changed
existing files are `lean/Yulang.lean` and `notes/design/INDEX.md`, both with
appended lines. Frozen paths and earlier Lean modules remain untouched.
Branch and HEAD remain `astra/ground-factorization-2`,
`2433dc974cc71201cf22bd15782b977e112f1f4a`. No commits or ref updates were made.
