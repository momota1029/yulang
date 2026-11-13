# Normalized capture assembly: closed children and matched head mass

Date: 2026-11-14. Status: proved local bridges and conditional accessibility;
general ground-root accessibility remains open.

This extends [the capture-assembly note](2026-11-14-ground-capture-assembly.md)
on integration head `e83e521dd9e629c91d00d3529032576d5b43fe59`.
The relation is still `GeneralNominalActualInspectionSteps.Step`. No guard,
producer, source restriction, declaration check, or earlier definition changed.

## 1. Exact boundary and result

`NormalizedCaptureAssembly` has two conclusions for **every** `Ready` capture
substitution, model, and list of finite input labels at an enabled reachable
packet. This turn proves its entire second conclusion:

* `GeneralNominalChildAssembly.children` constructs, for every emitted clause
  and every input position, a closed finite term for the normalized substituted
  argument and the existing `GeneralNominalGroundProduction.ArgumentValue`.
* The theorem uses actual `Installable`, the shared generation certificate,
  `packet.Holds`, configuration agreement, and `Ready`. It has no independent
  quotation, materialization, finite-cover, or termination assumption. Its
  local statement does not need reachability or point-source premises.
* `GeneralNominalMatchedAssembly.head_mass` proves the entire first conclusion
  from the structural matching relation `HeadMatches`, including repeated
  variables and all head arguments. It does not yet construct that relation
  from successful inspection.

Consequently `assembly_of_matching` constructs `NormalizedCaptureAssembly`
from the single remaining hypothesis `ReachableHeadMatching`.
`ground_accessible_of_matching` proves accessibility for Checked registries,
InitialSource, PointSource and GroundRoots under precisely that hypothesis.
This is not an unconditional ground-root Class P theorem.

## 2. Matching and head-wide counting

For a query Q, let W(c,Q) be its weighted size. A singleton variable n has
weight c(n); a scalar has weight 1; pairs, variants and nominal applications
have weight 1 plus the sum of their children's weights. A record with k
fields has weight k+1 plus the sum of payload weights. The k+1 includes each
record spine constructor and the empty-record tail, exactly as the checker
counts them.

`Matches R Q t` preserves the constructor, its ordered positions, and arity,
and relates a singleton query variable n to its finite matched subtree by
R(n,t). Every occurrence is represented, including repeated occurrences of
one declaration variable. There is no deduplication of head positions.

Structural induction on this derivation proves:

1. If R(n,t) implies c(n)=weight(t), then W(c,Q)=weight(t)
   (`matched_mass_eq`).
2. If R(n,t) implies c(n)≤weight(t), then W(c,Q)≤weight(t)
   (`matched_mass`).
3. For any covered supported template p, substitution into the checker's
   encoded p has exactly W of its translated query (`translated_count`).
   Flattening a record and sorting its fields preserve the sum by a list
   permutation; the added spine constructor contributes exactly one.
4. The existing conservative normalization bound places the normalized
   syntactic substituted mass below this encoded substituted mass.

For the actual shared substitution, R is `CapturedPart`. A needed name has
a usable origin, a closed source Pattern for the matched subtree, and its
actual meaning at that origin. `Ready`'s minimum-mass clause bounds the chosen
label at **each** occurrence separately. An unused name keeps its identity
variable, which costs one; the matched subtree is closed and therefore has
weight at least one. `recorded_capture_part` obtains this relation from actual
membership in the inherited report and a finite positional readback, using
agreement with the usable representative.

`HeadMatches` aligns the complete normalized declaration-head list with the
input-label list. Applying the preceding inequality at each aligned position
and summing proves the exact requested whole-head bound. No multiplication
by head arity or total-variable-count approximation is introduced. Multiple
nominal endpoint reports do not authorize counting a syntax position twice;
constructing a single matching derivation per syntax position remains part
of the inspection bridge below.

## 3. Actual child production and both normalizations

Let a be a raw where-child argument, p=normalize(a), and σ a `Ready` capture
substitution. The checker's `countsCovered` gives coverage of p; it need not
give coverage of a. The emitter stores p in each compound input request and
the schema generator translates normalize(p).

For a compound argument, `emitted_requests` puts that exact request in the
actual packet requests. `Installable` supplies `Prepared`; its existential
bounds agree with the packet's located bounds. `RequestReady` then supplies
`generated.unknown=false`. Inverting schema concatenation and generation
proves that the exact twice-normalized query has no deferred subquery
(`GeneralNominalRequestCompleteness.input_complete`). Ordinary model
satisfaction alone would not prove this fact.

Coverage of p implies recursive normality of normalize(p). Record hiding
removes earlier occurrences of a field label, so its record spine has distinct
labels. Successful translation flattens this spine and sorts by label. Its
permutation preserves both distinctness and payload-variable identities;
sorting and distinctness give strictly increasing labels. Supported variants
have one payload, including the singleton-variable shortcut. Thus the query
is the quotation of a finite canonical open tree q, with leaves drawn from
variables of normalize(p) (`translated_good`, `quoted`).

Normalization and hiding introduce no variable, including through raw variant
joins and their merging (`normalize_variables`). Hence every leaf of q is
Needed for the packet. The declaration's lexical output-only check therefore
excludes every such leaf from the output-only binders (`needed_input`). The
shared generation certificate supplies a usable origin for each needed name.
`Ready` supplies a closed finite capture meaning. These combine with the
actual branch to yield `CaptureValue`, simultaneously for all leaves.
Unused substitution names retain variable syntax and are never substituted
at a leaf of this particular open tree.

Translation commutes with filling a supported covered template, including
sorted record spines (`translate_substitution`). Substituting the finite
capture trees into q gives a closed canonical tree. Its translated syntax is
already stable under normalization, by the existing closed-query theorem.
Finally, the existing covered-template substitution theorem gives

    normalize(p.subst σ) = normalize((normalize p).subst σ).

This identifies the child's intended normalized label with the schema's
second normalization. It uses coverage of p, not a global normalizer
idempotence assumption and not a commutation claim for arbitrary raw joins.
The closed bound tree and the original open tree q with its capture values
supply exactly `ArgumentValue`. The variable-only emitter branch is handled
directly using the same `CaptureValue` and usable origin. The existing
`child_inputs` theorem consumes this result and `InputCoherence` to obtain
actual child Fits and retained-origin meanings.

## 4. Endpoint inversion proved on the actual carrier

A structural inspection can descend between distinct endpoints even when
its source has point intervals. Therefore a constructor-wise equality lemma
about two already equal values alone cannot establish head matching.
`GeneralNominalFiniteBracket` supplies the directed facts needed here:

* `subtype_head` identifies the coarse constructor family from a directed
  subtype comparison using the carrier's role probes.
* `record_fields_below` transports field presence in its correct direction.
  Applying it to both sides of a bracket recovers the full canonical record
  signature (`record_signature_bracket`), independently of payload values.
* `record_exact_empty_bracket` separates an empty record from `exactEmpty`
  using optional/impossible probes, and nonempty records using field probes.
* `test_bracket` combines these results: a canonical finite constructor
  between two values of the same canonical test has that exact test.
* `shape_payload_below` gives directed payload comparison for pairs, variants
  and canonical records. Record payload probes use distinct field labels.
* `structural_interval` connects these carrier results to **actual** recorded
  lower/upper structural heads, `GeneralNominalState.Models`, and `Fits`.
  It extracts the finite input's structural children and proves each fits the
  corresponding real pair of endpoint slots, including different shape IDs
  that denote the same shape. It requires no point-endpoint equality.

These are unconditional local inversion theorems. They do not by themselves
construct a matching derivation for a whole recursive inspection report.

## 5. Exact remaining producer work

The sole hypothesis of the new ground-root accessibility reduction is
`ReachableHeadMatching roles registry context root`. It retains the old
universal quantifiers over reachable states, enabled guarded packets,
models satisfying current facts and the packet branch, and arbitrary valid
closed input-label lists. Its conclusion is only `HeadMatches`; it assumes
neither a numerical budget nor child output semantics nor accessibility.

To construct it, the remaining proof must recurse over `inspect` and
`inspectMany` with the following simultaneous invariant:

1. The current query is aligned with a finite subtree and an actual interval
   containing its meaning. Retained origins, when present, denote that same
   subtree. The finite Pattern reification retains source constructor keys.
2. `Finished` provides exact arity alignment and excludes blocked branches.
   Structural descent uses `structural_interval` and closed source-subtree
   reification. Scalar and nominal branches need their respective producer
   inversions and transport to the same subtree.
3. Each recursive capture occurrence is included in the original inherited
   report. Needed variable cases use `recorded_capture_part`; unused variables
   consume only positive finite subtree weight.
4. A nominal reset uses its real inherited origin or the correct endpoint
   fallback. Both endpoint reports must be related to the same finite input;
   one syntax position contributes once to `Matches`, while shared-origin
   agreement controls all repeated capture occurrences.

The existing full-report path/fallback theorems supply bounded individual
readbacks; they do not already assert this simultaneous position-preserving
invariant. No semantic counterexample or implementation mismatch was found
in this turn. No additive repair or owner decision was required. Roots with
unknown holes have not been advanced: the general elimination simulation is
still downstream of the unfinished ground-root producer.

## 6. Proof ownership and validation

The yulang-proofs skill was used. The host has no callable registered prover
role; the checkout also lacks the prescribed prover routing files. The primary
constructed these bounded derivations directly. An existing independent
reviewer inspected the theorem boundaries and producer connections, including
the expanded child and structural interval results, and found no blocking
issue. No prover agent ran. Review did not certify unconditional accessibility.

All additions are new modules; their imports are appended to `lean/Yulang.lean`.
The standalone audit is `lean/Audit/NormalizedCaptureAssemblyProgress.lean`.
The frozen audit and README, prior Lean modules, specification, planning notes,
and git refs are unchanged. Final validation results are recorded below.

Final checks, executed with working directory `lean/`:

| Exact command | Exit code | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralNominalFiniteBracket` | 0 | All ten new modules built transitively; 765 jobs. |
| `lake build Yulang` | 0 | Aggregate build passed; 2264 jobs. |
| `lake env lean Audit/NormalizedCaptureAssemblyProgress.lean` | 0 | All 17 audited declarations use only propext, Classical.choice, Quot.sound. |

A separate Python scope/proof-token check exited 0: exactly ten new imported
modules, only ten appended aggregate imports among tracked Lean changes,
no prohibited proof tokens in the new modules, and unchanged integration HEAD.
Exploratory elaboration attempts failed while developing the new files and were
corrected before these final checks. Earlier checked files were not edited.
