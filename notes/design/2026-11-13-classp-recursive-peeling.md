# Class P producer work: recursive nominal peeling

Status: Draft proof companion, 2026-11-13. No semantic decision and no Step
definition is changed. This continues the table in
[actual capture depth](2026-11-13-actual-capture-depth.md), using the requested
recursive-subclass milestone when the full source simulation remains open.

**Result:** unconditional accessibility of the actual-inspection Step for
the recursive peeling class below. This includes the existing real
`Display (list int)` source and a source-formed, inhabited, point family for
every positive list depth. General `ClassPProducer` is not constructed.

## 1. The precise recursive class

Fix a checked registry R, a source-formed initial context S and root q, a
set A of reachable roles, and a nominal declaration identity N. Require:

1. q's role belongs to A. Every role in A is unary.
2. For every visible declaration with role in A and a nonempty where list,
   its translated head query is `N(v)` for one variable binder v. Every
   where clause has the single unnamed argument v, and its role is in A.
   Branching and cycles between roles in A are allowed.
3. The initial point site retains `.source i` as its argument origin, and
   the initial constraints entail `i ≈ N^n b`, where b is a scalar base
   type and n is finite.

These are the fields of `Peeling` plus the initial-origin and ground-source
conditions in `PeelingAccessibility.accessible`. The restrictions describe
declaration syntax and initial source meaning. They contain no property of
future traces, source refinements, accessibility, or finite signature covers.

Active leaf declarations have unrestricted heads. Associated equations and
output-only binders remain unrestricted subject to `Checked`. Unreachable
declarations are unrestricted. The ordinary journal, support guards, K2,
merging, reserved IDs and all observation transitions are the existing ones.
The proof does not impose a scheduling policy or require alias classes to
expand only once.

Only the root's retained point origin is needed by this general theorem.
It does not require all later descriptor intervals to remain points. The
concrete sources below additionally satisfy the full initial `PointSource`
predicate, so they are a subclass of Class P. The result is not a theorem
for arbitrary output-free Class P programs: compound child arguments,
multiple inputs and arbitrary head shapes remain outside this class.

The source program family represented by the Display fixtures is:

```yulang
impl Display int
impl Display (list 'a) where Display 'a
```

with an initial demand `Display (list^n int)`, where the superscript denotes
finite nesting in this note, not surface syntax. For n=1 this is the
existing repository declaration registry and the existing `list int`
source. The registry also contains Wrap; it is unreachable from Display.

## 2. Dynamic report paths: general progress on row (a)

`GeneralNominalInheritedPaths` defines `paths(query, origin)` by following
the finite query syntax. A structural or nominal query adds its indexed
argument paths; variables and scalars contribute only their current origin.
`manyPaths` combines this construction for a head's unnamed arguments.

Mutual induction on the real `inspect` and `inspectMany` producers proves:

* Every captured variable has a retained origin in this list.
* Every anchor and tested position has its origin in this list.

The premise is that the relevant input origins are supplied. There is no
premise bounding endpoint IDs or invoking a finite allocation pool.
The same result applies to the inherited report and to the actual-inspection
report after recovery. With a retained parent, both endpoint traversals of
a strict interval use that parent; neither traversal substitutes the
endpoint identity for the actual origin. Nominal bodies are never traversed.

This is a syntactic path-extraction theorem, not a proof that the paths
denote finite source terms. Producing missing roots after compound
materialization and interpreting the resulting paths over H remain open
for general Class P. In particular, the theorem does not cover a missing
root by silently choosing an endpoint.

## 3. The local producer for recursive peeling

Write p(0)=`.source i` and p(d+1)=`.nominal p(d) N 0`.
`PeelingOrigins.nominal_captures` proves, for an arbitrary snapshot and
arbitrary endpoint bounds, that every capture in inspection of `N(v)` at
retained origin o has origin `.nominal o N 0`. The inspector may produce
captures from either endpoint descriptor; their origins still coincide.

`PeelingAccessibility.child_projection` then uses actual producer evidence:

1. `emitted_clause` extracts the original clause from an actual packet child.
2. The clause's argument v makes v `Needed`.
3. The existing `GenerationGuard` supplies a usable retained capture.
4. Every possible `OriginAt` witness has the projected origin just proved.
5. `SharedEmission.retains` therefore puts that exact origin in the emitted
   site's input list, independently of which witness its choice selects.

This is a theorem of the existing emitter, not a supplied child-origin
property. It does not require captures to have point endpoint bounds.

Induction on every actual Step now proves `sites_paths`: every registered
site has an active role and some d such that its allocator identity is at
ancestry depth d and its retained input is p(d). An installation adds only
the emitted children just analyzed. Refresh, equality feedback,
reobservation and merging preserve the old sites. Source formation excludes
an administrative enqueue of an unregistered generated occurrence.

Repeated expansion of an aliased site does not reset d: every literal child
extends its parent's retained path and allocator ancestry once. Alias
transitions do not rewrite either stored object.

## 4. Finite source readback and the bound

Let T(0)=b and T(k+1)=`N(T(k))`. The carrier theorem
`observed_path` states, for any full-carrier model m:

    m(i) ≈ T(n) and Observes(m, p(d), value)
      imply ∃ k, n = d+k and value ≈ T(k).

Induct on d. At zero use the source equation. At a successor, invert the
observed nominal projection and apply exact nominal argument invariance.
At scalar depth zero, a nominal-head probe rules out another projection.
The argument uses actual nominal arguments, never descriptor endpoints or
nominal bodies. In particular, d≤n.

`PeelingReadback.expression` is the corresponding finite symbolic term.
`expression_holds` proves the carrier readback; `expression_closed` proves
that it has no leaves. For every registered site's p(d), `site_readback`
uses the fixed term T(n-d) from the source-fixed list
`[T(0), ..., T(n)]`. Every current model satisfies this readback and d≤n.
The depth assertion is under the model premise: it is not a claim about
arbitrary sites in an inconsistent state.

These are closed readbacks, hence terms over any initial frontier H without
using an eliminable hole. The input representation cannot gain structure
when an ordinary constraint, an associated equation or a refreshed
observation is added: successor models remain source models, and the same
closed expression still represents the retained origin. Thus this subclass
needs no genuine hole elimination to bound its head-relevant inputs.
This does not classify every newly reserved/output identity over H.

`equal_paths_equal_depth` additionally proves that actual `Same` of two
such origins forces equal depths and hence equal finite readbacks. This is
proved by nominal inversion and tower injectivity. It is not an assertion
that an arbitrary syntactic Alias edge, by itself, proves `Same`.

## 5. From the actual installing packet to unconditional Acc

Consider any prospective installing packet at a reachable state. Its
existing `Installable` certificate supplies a model of the entire current
journal. The current state's `SiteHolds` gives an observation of the
packet's retained input p(d). Model restriction along the trace supplies
the original equation `m(i) ≈ T(n)` in that same model. Section 4 gives
d≤n. This proves `InstalledDepthBound R S q n` without a producer premise.

No theorem asserting global consistency preservation is used. If a state
has no models, it cannot supply the prospective installation certificate.
The finite signature-cover proof already handles the remaining
administrative transitions there.

The existing chain now applies without an open quantitative premise:

    source spine length n
      → InstalledDepthBound n
      → finite invocation and allocation pools
      → finite report/packet codes and SignatureCover
      → Acc of the unchanged actual-inspection Step.

The final measure is the count of missing signatures in that finite cover,
combined with the proved accessibility of administrative steps. We do not
require the total size of the journal to decrease at each transition.
Settled-output growth need not be bounded separately here: any output
equation capable of changing the fixed input spine would contradict the
source equation in the prospective installation model. Outputs are still
retained and may constrain other IDs; the finite installation/allocation
bound accounts for them.

## 6. Concrete end-to-end statements and remaining general work

`PeelingExamples.display_accessible` is a closed theorem for the existing
`Display (list int)` fixture. `real_recursive_step` uses the existing actual
installation and its actual emitted Display child. Accessibility also holds
after that step. It is not merely an inaccessible or initially blocked
example.

`PeelingSources` constructs, for every k, an explicit source with k+2 slots,
k+1 point nominal edges and an ordinary final-slot equation `= int`.
It proves `InitialSource`, `PointSource`, model existence, the initial root
equation `list^(k+1) int`, and accessibility. The terminal scalar observation
may initially remain deferred in this family; all allowed observation
updates are covered. We have not constructed a successful complete
dictionary execution of length k+2 for every k. The new claim is termination.

| Earlier table row | Proved here | Remaining for arbitrary Class P |
| --- | --- | --- |
| (a) Dynamic paths and finite labels | Query-directed report path extraction with supplied roots; exact retained peeling paths and finite closed labels | Construct missing dynamic roots and source interpretation for arbitrary compounds |
| (b) Producer over H | Every peeling site's actual input has a closed term in one source-fixed list; actual origin agreement implies equal labels | Full new-ID representation, shared variable/facet production and general Alias coherence |
| (c) Local refinement simulation | Actual-step induction preserves old paths and produces each new peeling child; the fixed closed readbacks survive all refinements | Extract general global hole eliminations from actual steps |
| (d) Output-binder trees | No output-tree hypothesis is needed for the fixed-spine termination theorem | General binder-to-settlement-tree correspondence and growth budget |
| Acc | Unconditional for the precisely stated recursive peeling subclass and concrete families | `ClassPProducer`, general `SourceBudget`, unconditional general Class P Acc |

No new implementation obstruction or semantic gap was established, so no
additional guard or owner decision is proposed. The path lemmas and the
peeling theorem already allow strict intervals after initialization; they
do not establish the full strict-interval source/facet invariant.

The primary constructed these bounded derivations directly. The checkout
has no registered `prover` configuration or callable prover role; no prover
agent ran. An independent read-only reviewer checked the source/model
quantifiers and theorem scope, including the model premise on site depth
and the unrestricted observation transitions.

## 7. Validation

Final commands from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalInheritedPaths Yulang.GeneralNominalPeelingSources Yulang.GeneralNominalPeelingReadback` | 0 |
| `lake build Yulang > /tmp/yulang-classp-build.log 2>&1` | 0 |
| `lake env lean Audit/GeneralNominalRecursivePeeling.lean` | 0 |

The standalone audit reports only `propext`, `Classical.choice` and
`Quot.sound`. `git diff --check` from the repository root exits 0. All six
new modules are imported by appended lines in `lean/Yulang.lean`; the design
index also gained only an appended entry. Byte-prefix checks verified the
append-only constraint on those two existing files, and no other tracked
file changed. Frozen paths, branch and HEAD are unchanged. The new Lean
files pass prohibited-token scanning; no commits or ref updates were made.
