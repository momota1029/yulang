# Ground capture factorization: actual paths and closed branching Acc

Status: partial proof companion, 2026-11-14. Continues
[ground input production](2026-11-14-ground-root-production.md).
Authority remains `spec/06-roles.md` §6 and the approved B4 draft, including
addendum 7. The actual-inspection Step and all existing definitions are unchanged.

**Result:** the existing inhabited point-source fixture
`Show (pair (list int) int)` is now accessible with no factorization or depth
premise. A general branching constructor class also has unconditional
accessibility under the explicit restrictions below. Actual capture-path
extraction, simultaneous finite semantic values, substitution facts, and
semantic mass uniqueness advance the local bridge. They do **not** discharge
`GroundCaptureFactorization` for arbitrary Checked registries. General
ground-root Class P Acc and `ClassPProducer` remain open.

## 1. Closed branching theorem and exact restrictions

`GeneralNominalBranchingAccessibility.Branching roles registry context active`
requires:

* Every active role has one unnamed input.
* Each active declaration with children translates to exactly one query:
  either a nominal with any finite number of direct singleton-variable
  children, or a pair with two direct singleton-variable children.
* Every where-child has an active role and one bare-variable argument.

The theorem also takes `Checked registry`, `InitialSource registry context
root`, an active root role, and a retained root source origin. That source
identity must have, in every initial source model, the meaning of one fixed
finite `Tree`: a scalar, pair, or nominal with finite tree arguments.
`Tree.mass` counts all constructor nodes. No nominal bodies are traversed.

Associated equations and output-only binders have no extra restriction beyond
Checked. Active leaf declarations may have arbitrary heads. Other registry
roles are unrestricted. The proof allows later strict observation intervals;
the root-origin premise in this result selects a point root. It needs no
global initial-pointness premise beyond that. Its ground tree class excludes
records, variants, rows, unions, and unresolved leaves.

This class adds branching and mixed constructors to the earlier single-spine
results. It is not the requested arbitrary-registry ground-root class:
multi-argument roles and compound where-child arguments are still outside
this unconditional theorem, even though the capture lemmas below cover
multiple input positions and nested nominal/pair queries.

## 2. Actual producer and termination proof

`BranchingCaptures.nominal`, `.pair`, and `.usable_path` unfold the real
recursive inspector. For the query shapes above, every usable capture has
an actual origin exactly one nominal-argument or pair-component edge below
the retained input origin. The nominal proof includes inspection of both
endpoints when the interval is not a literal point.

`BranchingAccessibility.child_path` uses the actual generation guard to
obtain a usable capture for each child variable. It follows the chosen
`SharedEmission` origin witness, rather than assuming that the emitted
child kept some preferred representative. Its conclusion is the actual
child-site input entry together with that one-edge path.

`sites_paths` inducts over all actual Step constructors. Every stored site
has an active role, literal allocation ancestry depth d, and a retained
origin reached by exactly d such edges from the original source identity.
The source-formation invariant excludes external enqueue events.
Refresh, reobservation, equating and merging keep the site list. Installation
preserves old paths and adds one edge to each new child's path. Aliasing
does not identify two literal birth paths or let an installation skip an edge.

`BranchingReadback.observed_path` supplies the semantic bound. If the root
has finite meaning T and the endpoint of a d-edge path is actually observed,
there is a finite tree U at that endpoint with

    d + mass(U) <= mass(T).

This theorem does not assume that the query path already matches T's syntax.
At each edge, nominal invariance or pair projection inverts the actual
observation. Shape-separating carrier probes rule out a nominal projection
from a scalar/pair and a pair projection from a scalar/nominal. Each valid
projection selects an actual finite child whose mass is strictly smaller.

For any finite trace ending in an installing packet, its installability
certificate supplies a prospective model. All actual steps restrict models
backwards, so this model satisfies the original source facts. `SiteHolds`
supplies an observation of the retained input origin. Apply `sites_paths`
and `observed_path` in that model to obtain d <= mass(T). No model of an
entire infinite trace, output-size bound, or hole-elimination history is used.

`installed_depth_bound` therefore produces the existing `InstalledDepthBound`
with N = mass(T). `accessible` feeds it to `ActualBudget`'s finite
invocation/allocation/report enumeration and signature cover. The remaining
signature count strictly decreases on fresh installations; the existing
passive accessibility proof handles steps between installations. This is
accessibility of the unchanged actual-inspection relation, with no assumed
termination premise for this subclass.

## 3. The Show fixture

The existing checked fixture is:

```yulang
impl Show (pair 'a 'b):
    where 'a: Show
    where 'b: Show

impl Show (list 'a):
    where 'a: Show

impl Show int:
```

Its root is `Show (pair (list int) int)`. `ShowGroundAcc.branching` verifies
the class from the concrete declaration data. `input_ground` derives the
finite tree from the source equations in every source model. The tree has
mass 4; `depth_bound` is closed, and
`show_pair_list_int_accessible` has no factorization hypothesis.

`inhabited_closed_example` combines Checked, InitialSource, PointSource,
a concrete source model, and Acc in one closed theorem. It reuses the
integrated source unchanged: identity 2 is initially a reserved identity
with an ordinary pair equation, rather than a preexisting structural slot.
The theorem covers every subsequent actual trace, including any certified
refresh. This change does not construct a refresh/install witness or a
successful dictionary execution for the Show fixture. Accessibility and
inhabitation are established; execution completeness is not claimed.

## 4. Standalone bridges towards the general factorization

`CompoundCapturePaths.inspect_paths` and `many_paths` extract paths from
actual reports for arbitrarily nested nominal/pair queries and multiple
input positions. `Projectable` explicitly excludes structural record,
variant, and exact-empty nodes. Scalar, variable, and deferred query leaves
are allowed. The theorem requires an actual retained origin for every queried
input position and closure of the allowed-origin predicate under projections.

`report_forest` specializes this to a finite list of origin/tree roots.
`explained_value` combines a generated path, an observable endpoint, and
root meanings to give an exact finite subtree meaning. `path_unique` shows
that all observations at that path are equivalent. Closedness is semantic
here: `Tree` has no unknown leaves. It is not yet a declaration `Pattern`.

`simultaneous_captures` uses the actual generation guard, usable-capture
membership, and `InputBound` to obtain the endpoint observation. It chooses
one finite tree per needed declaration name. Existing shared-origin
coherence transfers that value to every usable occurrence of the same name,
including occurrences in different head positions. There is no selection
of an interval center. The child-syntax premise is currently the application
fragment; it allows `needed_not_output` to use Checked's exclusion of
output-only binders from child inputs directly. The finite root forest and
its retained-origin entries remain explicit premises in this general lemma.

`BranchingMass.equivalent_mass` proves that equivalent finite scalar/pair/
nominal trees have equal constructor mass. `shared_capture_mass` applies
this to two meanings of the same usable capture. Thus changing a semantic
witness for a repeated variable cannot inflate its mass. This is not a sum
bound across all positions or a pattern-syntax reconstruction theorem.

`PatternGroundSubstitution.encode_subst` and `encode_substArgs` commute raw
Pattern encoding and substitution for **every** Pattern constructor.
`normalize_subst`, `counted_substitution`, and `instantiated_mass` additionally
handle normalization and the actual Paterson count when the original
pattern uses variables and applications. Substituted patterns may be
arbitrary; they are normalized before encoding. These statements do not
assume normalization commutes with substitution through open record tails
or joins. `covered_plain_names` also establishes that a covered pattern
with successful `plainNames` is a singleton variable capture.

## 5. Exact remaining work

| Link | Proved here | Remaining for GroundCaptureFactorization |
| --- | --- | --- |
| Finite input inversion | Observed nominal/pair paths, without assumed shape alignment | Records/variants and complete extraction from general input meanings |
| Dynamic report origins | Nested/multiple-position actual report paths given a retained root forest | Produce that forest for general reachable sites, including missing/recovered inputs |
| Simultaneous variable values | One finite semantic tree per needed name, shared across usable occurrences | Reify trees as closed Patterns with valid source constructor keys |
| Substitution | All-pattern raw encoding; application-fragment normalization and counted mass | General normalized translation/substitution, including record-tail hiding and variant normalization |
| Mass | Equivalent tree witnesses have equal mass; strict projection descent | One simultaneous substitution with the sum of instantiated head masses bounded by the input labels |
| Actual child meanings and Acc | Existing materialization/recovery reduction; new closed branching theorem | Supply the factorization evidence to that reduction for arbitrary Checked registries |

Reification must preserve source keys: a semantic nominal name in `Tree`
is not automatically a catalogue key whose interpretation yields that name.
The original closed Pattern labels contain suitable source information,
but these proofs do not yet propagate it through the entire factorization.
Similarly, a canonical record with k fields has Pattern mass
`k + 1 + sum(payload masses)`, not a single node plus its payloads. A future
head-wide mass proof must reconcile that count with canonical record
projection and hiding; semantic subtree mass alone does not establish it.

The original `GroundCaptureFactorization` remains the single named hypothesis
of the existing general ground-root Acc theorem. It has not been discharged
or replaced by a reachable-state version here. No new counterexecution,
implementation defect, or semantic gap was established, and no guard change
or owner decision is proposed. Unknown source holes and general strict
interval initialization remain beyond these results.

## 6. Review and validation

The primary constructed the bounded derivations. The configured prover role
is unavailable: this checkout has no `rules/agent-orchestration.md`,
`rules/research-lab.md`, `rules/design-authority.md`, `.codex/config.toml`,
or `.codex/agents/prover.toml`; the live schema has no prover role. No prover
agent ran. A separate read-only reviewer checked the actual path producers,
all-Step invariant, retrospective model argument, simultaneous capture
scope, mass uniqueness, and fixture quantifiers. No blocking issue was found.
The review explicitly leaves general factorization open.

Final commands from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalBranchingReadback Yulang.GeneralNominalBranchingCaptures Yulang.GeneralNominalBranchingAccessibility Yulang.GeneralNominalShowGroundAcc Yulang.GeneralPatternGroundSubstitution Yulang.GeneralNominalBranchingLabels Yulang.GeneralNominalCompoundCapturePaths Yulang.GeneralNominalBranchingMass` | 0 |
| `lake build Yulang > /tmp/yulang-ground-factorization-build.log 2>&1` | 0 |
| `lake env lean Audit/GeneralNominalGroundFactorization.lean` | 0 |

The focused build completed 771 jobs; the full build completed 2212 jobs.
All 27 audit entries use only `propext`, `Classical.choice`, `Quot.sound`
or fewer. Development elaboration failures were corrected before these
checks. No parser or dictionary-execution test was run for the Show fixture.

From the repository root, `git diff --check` and
`python3 /tmp/yulang-ground-factorization-scope.py` both exited 0. The latter
checks byte-prefix preservation against HEAD, the eight new imports,
prohibited proof tokens, and unchanged branch/head. Only `lean/Yulang.lean`
and `notes/design/INDEX.md` change among existing files, both by appending.
The frozen paths and earlier Lean modules are untouched. Branch and HEAD
remain `astra/ground-factorization`,
`b95d31b190f25633851ec805553bb57c792ffad7`. No commits or ref updates were made.
