# Item 4j: generation-budget checks and the actual sibling prefix

Status: **Partial. The generation budget and unconditional termination remain open.**
Date: 2026-11-13. Baseline: integration dc145d71f.
Scope: the unchanged GeneralNominalDownstreamSteps.Step and
GeneralNominalDownstreamBoundary.boundary roles. No new boundary or language
restriction is introduced.

## Outcome

The two Item 4i regression gaps are closed: Container has a full installation
proof, and the source-formed P → Container → Wrap prefix is an actual sequence
of downstream steps. Its complete retained support ledger proves the subsequent
downstream head is blocked. The earlier compressed journal is used as a model
comparison, not assumed to be reachable.

The positive L5 contribution is transport of every support-depth certificate
through any finite sequence of certified refreshes and descriptor replacements.
The requested transport through all updates is not proved. Actual installations
refute two tempting substitutes: persistence of producer grounding and a
non-increasing bound on the recorded producer pool. Neither result refutes a
bound on the minimum explanation depth of each persistent needed head.

A third checked obstruction excludes taking a maximum denotation size over all
models: the same two-slot, non-K2 initial state permits arbitrarily tall finite
nominal models. This does not exclude a symbolic source-term measure with opaque
leaves. Finally, a real same-input merge retains distinct occurrence identities;
a finite quotient does not automatically bound allocated diagnostic identities.

**No InstallationOrder, unconditional progress, or unconditional
whereAccessible is constructed. The V5 count remains 6/14.** In particular this
item does not prove that the downstream transition relation is nonterminating.

## L5: precisely what transports, and what fails

[GeneralNominalBudgetObservation](../../lean/Yulang/GeneralNominalBudgetObservation.lean)
proves the following for arbitrary roles, registries, tracked states, producers,
and natural depths. View is the existing finite certified observation closure.

~~~lean
depth_nonincreasing (state : Tracked roles) (view : View state.current after)
    (known : AtDepth registry state depth producer) :
    AtDepth registry {state with current := after} depth producer

grounded_preserved (state : Tracked roles) (view : View state.current after)
    (grounded : Grounded registry state producer) :
    Grounded registry {state with current := after} producer
~~~

The journal, sites, generation edges, and aliases remain fixed. Discharge and
waiting paths therefore transport in both directions. Every Need after the
view was already a Need before it: the inspection constructor already
quantifies over all further certified views, and the closures compose. Induction
on depth then transports the selected support explanations without increasing
their depth. Source formation is unnecessary for this observation-only result.
The refresh_depth and revision_depth corollaries specialize it to the two
implemented constructors. It supplies no merge or installation transport.

[GeneralNominalBudgetDepthObstruction](../../lean/Yulang/GeneralNominalBudgetDepthObstruction.lean)
contains three distinct checks of proposed measures:

1. **Producer persistence fails at the first R installation.** The producer has
   depth one in the empty-journal source state. The installation emits a child
   whose newly entailed list head requires that same unresolved producer. The
   trap theorem excludes Grounded afterward, at every finite depth. The update
   is a real Step, its declarations are Checked, its start is SourceFormed,
   and its result has a finite model. The lazy guard is doing its intended job;
   losing this certificate is not a semantic error or an infinite execution.
2. **The recorded-pool maximum increases at the first P installation.** Initially
   its dependency pool is empty, so bound zero holds. After installation P is
   recorded, grounded but unresolved, and the least bound is one. This is an
   exact update increasing the snapshot-bound predicate of Item 4i. The initial
   zero is vacuous; it is not evidence of unbounded growth of minimum head
   explanations.
3. **A maximum over all denotations is already unbounded initially.** Fix R's
   two-slot initial source, with source 0 equal to list of unknown source 1.
   For every n, finiteModel(n+1) is a model of that same state and gives source
   0 the type list^(n+2) int. Root K2 is absent. A size uniformly dominating all
   these heights cannot be a natural-valued source budget. Choosing one model
   introduces the separate model-loss problem already recorded in Item 4i;
   leaving unknown leaves opaque is still a possible approach.

No new language choice follows from these three results. They are failures of
particular proof proposals. The missing L5 statement is still a *source-derived
bound on future useful input structures/explanations*, compatible with losing
old certificates and with newly added heads. Monotonicity of each currently
chosen certificate is stronger than necessary and is false for producers.

## L6 and L7: merging is not an allocation bound

[GeneralNominalBudgetMergeRetention](../../lean/Yulang/GeneralNominalBudgetMergeRetention.lean)
uses the existing checked Display(list int) declaration with two Display int
where obligations. It proves its actual downstream installation and subsequent
same-input merge. Both sites remain; their entire demands are equal, their
occurrence IDs differ, and the IDs are aliased. The state remains SourceFormed
and has the existing model. Invocation-indexed allocation gives distinct child
source IDs for these two invocation IDs.

This is consistent with lossless diagnostic trees and spec §6.3's same-input
rule: aliases share constraints and associated outputs, while source obligations
remain identifiable. The theorem does **not** show that both aliased sites can
subsequently expand, nor an infinite allocation trace. It invalidates the
counting shortcut “equal requests merge, hence the list of occurrence IDs is
injective in input signatures.” A proof must separately bound expansion events
or establish sharing of expansions across equivalence classes, while retaining
all diagnostic identities.

Consequently no finite set of all future normalized signatures has yet been
derived. Finiteness of initial identities, a finite registry, fixed-capture
Paterson descent, and snapshot grounding are insufficient *as proved lemmas*
to assemble that set. This is a proof gap, not a demonstrated impossibility of
such a set. Raw cached packets also contain contexts; L7 must bound semantic
packet deltas and emitted edges, rather than count those raw structures. No
finite-basis premise is inserted into SourceFormed or Checked.

## Closed regression gaps

[GeneralNominalBudgetContainer](../../lean/Yulang/GeneralNominalBudgetContainer.lean)
checks all transition premises for the real Container packet after P:
location/capture, associated schema, Fresh, Prepared, unique Local selection,
ordinary and journal K2 exclusion, joint applicability, both merge-closure
conditions, satisfiable branch, novelty, and empty source support. The leaf
packet becomes Discharged. This is a full installation, not only a guard proof.

[GeneralNominalBudgetPrefix](../../lean/Yulang/GeneralNominalBudgetPrefix.lean)
then constructs the actual Wrap packet against that updated context. It proves
its full installation premises and the sequence from the empty-journal initial
state. The associated schemas have precisely the shared named target and the
Container child output target from the existing general emitter.

The actual final ledger retains every alternative from installedFacts. A cut
model validates every fact whose dependencies exclude Wrap, but not the newly
entailed list head at source 2. Together with the unresolved Wrap child, this
proves the downstream block on the actual prefix. It closes the old fixture's
missing transition-to-certificate bridge.

The observed_certificate and observed_downstream_blocked corollaries retain
this obstruction under observation-context replacement with the same journal.
The latter assumes every recorded head at source 2 has the intended list tag.
They apply to a certified refresh when one is supplied; they do not construct
that refresh or assert SourceFormed/model equality for arbitrary replacements.
The actual prefix in this item contains the three installations only.

## Updated lemma ledger

| Plan lemma | Status on the downstream relation |
|---|---|
| L1 formed-step decomposition | Proved on integration: GeneralNominalDownstreamOrder.formed_step_cases |
| L2 administrative accessibility | Proved on integration: GeneralNominalDownstreamSteps.passive_accessible |
| L3 fixed-capture Paterson descent | Proved on integration; unnamed inputs only, output-only binders excluded |
| L4 interval-sensitive finite cost readback | MISSING; retained origins/projection soundness are not such a readback |
| L5 source-derived generation budget across updates | MISSING; new observation-only depth transport proved; exact producer/pool substitutes fail |
| L6 bounded future identities and input signatures | MISSING; actual alias retention now makes the extra expansion-count obligation explicit |
| L7 finite semantic packet signatures | MISSING; no source-derived bounds on all future reports, materializations, or emitted edges |
| L8 persistence/novelty | Existing fixed-packet persistence inherited; coverage by a finite signature set missing |
| L9 decreasing missing-fact count | Conditional fixed-basis counting exists; the basis is not derived |
| L10 InstallationOrder implies Acc | Proved conditionally on integration; no InstallationOrder supplied here |
| L11 reachable root child accessibility | MISSING without Readback; unchanged whereAccessible_of_readback retains that premise |
| L12 bounded complete rejustification | MISSING; no new replay or rejustification transition introduced |

The exact remaining termination contract is
GeneralNominalDownstreamOrder.InstallationOrder: a well-founded order and rank,
passive updates weakly decreasing, every novel guarded installation strictly
decreasing on SourceFormed states. The existing accessible theorem consumes
this contract; it is not its construction. The task's primary goal remains open.

## V5 field table

Boundary: GeneralNominalDownstreamBoundary.boundary roles. Definitions and the
Remaining structure are unchanged. “Open” means not supplied unconditionally
for this exact boundary, even where another boundary has related results.

| V5 field | Status |
|---|---|
| progress | OPEN: InstallationOrder not constructed |
| execution | Conditional solely on Progress, existing downstream executor |
| halted | Conditional solely on Progress, existing downstream executor |
| closure | PROVED |
| stepModels | PROVED |
| frontierLocal | PROVED |
| localIdentity | PROVED |
| whereAccessible | OPEN: existing theorem requires Readback |
| treeExecution | Conditional solely on Progress, existing downstream executor |
| canonicalLocalOrder | OPEN |
| dictionaryRefl | PROVED |
| evidenceNode | OPEN for this boundary |
| generatedChildren | OPEN for this boundary |
| initialReorders | PROVED |

Count: six unconditional fields, eight remaining; three of those eight follow
from Progress for the chosen executor. No score is gained by the regression or
measure-obstruction theorems.

## Principal theorem statements

Below, names resolve in the named new module's namespace and its imported
fixture namespaces. These are the full hypotheses/conclusions of the principal
new results; the source files contain helper statements and proofs. All 120 new
public theorem declarations are included in the separate audit part.

### GeneralNominalBudgetDepthObstruction

~~~lean
theorem actual_grounding_loss :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalDownstreamSteps.SourceFormed registry (root 0) start ∧
    GeneralNominalDownstreamSteps.Step registry (root 0) start added ∧
    AtDepth registry start 1 (root 0) ∧
    ¬ Grounded registry added (root 0) ∧
    Models added.current (finiteModel 1)

theorem not_grounded_step_monotone :
    ¬ (∀ (reg : GeneralDeclarations.Registry) (d : Occurrence roles) (before after : Tracked roles),
      GeneralDeclarations.Checked reg → GeneralNominalDownstreamSteps.SourceFormed reg d before →
      GeneralNominalDownstreamSteps.Step reg d before after → ∀ producer,
      Grounded reg before producer → Grounded reg after producer)

theorem actual_pool_bound_increases :
    GeneralDeclarations.Checked GeneralNominalSupportSiblings.reg ∧
    GeneralNominalDownstreamSteps.SourceFormed GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.start ∧
    GeneralNominalDownstreamSteps.Step GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root
      GeneralNominalSupportSiblings.start GeneralNominalSupportSiblings.afterP ∧
    PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.start 0 ∧
    ¬ PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 0 ∧
    PoolBound GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.afterP 1

theorem source_arbitrarily_tall (bound : Nat) :
    ∃ model : GeneralNominalCommonBridge.Assignment, Models start.current model ∧
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower (bound+2))

theorem no_uniform_model_height :
    ¬ ∃ bound : Nat, ∀ model : GeneralNominalCommonBridge.Assignment,
      Models start.current model → ∀ height : Nat,
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower height) → height ≤ bound

theorem checked_off_cycle_unbounded_models :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalDownstreamSteps.SourceFormed registry (root 0) start ∧
    start.current.context.state.base.slots = 2 ∧
    ¬ GeneralNominalFeedbackK2.RootK2 start.current (root 0) ∧
    ¬ ∃ bound : Nat, ∀ model : GeneralNominalCommonBridge.Assignment,
      Models start.current model → ∀ height : Nat,
      CommonNominalFullCarrier.Equivalent (model 0).1 (tower height) → height ≤ bound

~~~

### GeneralNominalBudgetMergeRetention

~~~lean
theorem actual_merged_duplicates :
    Checked registry ∧ SourceFormed registry displayRoot finish ∧ Models finish.current model ∧
    (child 10).demand = (child 11).demand ∧ (child 10).identity ≠ (child 11).identity ∧
    Alias finish.current (child 10).identity (child 11).identity

theorem identities_retained : finish.current.sites = before.current.sites ∧
    finish.current.edges = before.current.edges ∧ finish.current.packets = before.current.packets

theorem not_literal_demand_injective :
    ¬ (∀ first ∈ finish.current.sites, ∀ last ∈ finish.current.sites,
      first.occurrence.demand = last.occurrence.demand → first.occurrence.identity = last.occurrence.identity)

theorem invocation_allocation_distinct (snapshot : GeneralNominalState.State) (reg : Registry)
    (key purpose owner position : Nat) :
    GeneralNominalAllocation.source snapshot reg (child 10).identity
      (GeneralNominalAllocation.origin (child 10).identity key purpose owner position) ≠
    GeneralNominalAllocation.source snapshot reg (child 11).identity
      (GeneralNominalAllocation.origin (child 11).identity key purpose owner position)

~~~

### GeneralNominalBudgetContainer

~~~lean
theorem enabled : GeneralNominalFeedbackSteps.Installable reg afterP.current cpkt

theorem step : GeneralNominalDownstreamSteps.Step reg root afterP afterC

theorem formed : GeneralNominalDownstreamSteps.SourceFormed reg root afterC

theorem actual_prefix : B4Target.Steps (GeneralNominalDownstreamSteps.Step reg root) start afterC

theorem container_discharged : Discharged afterC.current kidC

~~~

### GeneralNominalBudgetPrefix

~~~lean
theorem enabled : GeneralNominalFeedbackSteps.Installable reg afterC.current wpkt

theorem step : GeneralNominalDownstreamSteps.Step reg root afterC afterW

theorem actual_prefix : B4Target.Steps (GeneralNominalDownstreamSteps.Step reg root) start afterW

theorem formed : GeneralNominalDownstreamSteps.SourceFormed reg root afterW

theorem certificate : PrefixCertificate afterW

theorem actual_wrap_not_grounded : ¬ Grounded reg afterW kidW

theorem actual_downstream_head_blocked (support : List (Occurrence roles))
    (supported : Supported reg afterW support) : ¬ HeadSupported afterW support 2 (.nominal 0 1)

theorem observed_certificate (context : GeneralNominalCandidates.Context) : PrefixCertificate (observed context)

theorem observed_downstream_blocked (context : GeneralNominalCandidates.Context)
    (recorded : ∀ test observation, Head context.state 2 test observation → test = .nominal 0 1) :
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg (observed context) nextP support) ∧
    (¬ ∃ support, GeneralNominalDownstreamSupport.DecisionGuard reg (observed context) nextW support)

~~~

## Unverified stress test: dependencies hidden below a captured variable

Counterexample review found the following further program to investigate.
**This section is a conjectural stress test, not a proved obstruction to Acc.**
It is not used to justify any theorem or to declare L5–L7 false. The exact
checked obstructions in this item are the bounded results above.

Use three-input roles P/W/G, two-input roles C/D, and unary Extract; W/G have
out, and C/D/Extract have item. The illustrative declaration spelling is:

~~~yulang
impl Extract (list 'x):
  type item = 'x

impl W (list 'x, 'y, 'm) where C('y, 'm, item = 'u):
  type out = list 'u

impl G (list 'y, 'x, 'm) where D('x, 'm, item = 'v):
  type out = list 'v

impl C (list 'q, box int):
  type item = 'q

impl D (list 'q, box int):
  type item = 'q

impl P (list (list 'a), list (list 'b), 'm):
  where Extract(list 'a, item = 'z),
        W(list 'a, list 'b, 'm, out = 'z),
        Extract(list 'b, item = 't),
        G(list 'b, list 'a, 'm, out = 't),
        P(list 'a, list 'b, 'm)
~~~

Start with the demand P(list(list A₀), list(list B₀), box U), with A₀/B₀/U
unknown. Ordinary counted sizes are 7 for P's head and at most 5 for its
children, and 4 for W/G's heads versus 2 for their children. All introduced
output binders occur only in named equations or own associated definitions.
Full DeclarationChecked, including capture-stable descent, has **not** been
proved for this registry.

The candidate schedule installs P, discharges its Extract siblings, then
installs W/G. At stage n its intended equations are

~~~text
z_n = A_n,       z_n = list A_(n+1)
t_n = B_n,       t_n = list B_(n+1)
~~~

These would ready the recursive P child for another stage. C/D would stay
inspection-pending on U. Their list arguments capture the other tail without
inspecting its constructor. At the level of whole input values, C's output
would feed A through W and Extract, and A occurs inside D's unnamed input;
D's output would similarly feed B inside C's input. That is the suspected
unresolved output/value cycle. Current Need records head observations and
visible inspection reads, which do not include the contents of variable
captures. It may therefore miss these edges.

The Extract siblings are essential to even this proposal: directly writing
out = 'a where 'a is an input binder creates a fresh target linked by the
parent's provisional named equation. The existing ancestor guard blocks that
simpler proposal. This was checked against the actual outputTarget and
materialization definitions before retaining the revised test.

Unverified obligations remain substantial: the concrete checked registry and
initial snapshot, interval materialization and retained origins, actual
Installable/Joint/MergesClosed/Admissible/novelty/freshness proofs, certified
refreshes, separating models, and a uniform induction over stages. No Lean
counterexecution or parser/inference validation is claimed.

If the revised schedule is realizable, the likely classification is an
**implementation gap in output provenance under spec §6.3 / addendum 6**:
track alternative-sensitive dependence of full unnamed input values on named
outputs, including blocked requests, while preserving independent source and
discharged explanations. This is a proposed diagnosis, not an implemented
repair. No new owner decision is requested from an unverified counterexample,
and no stronger “all siblings must discharge” restriction is adopted.

## Checks, scope, and review

| Command | Exit code | Result |
|---|---:|---|
| cd lean && lake build Yulang.GeneralNominalBudgetObservation Yulang.GeneralNominalBudgetDepthObstruction Yulang.GeneralNominalBudgetMergeRetention Yulang.GeneralNominalBudgetContainer Yulang.GeneralNominalBudgetPrefix | 0 | Five new modules, 698 jobs |
| cd lean && lake build Yulang | 0 | Aggregate build, 1836 jobs |
| cd lean && lake env lean Audit/GeneralNominalBudget.lean > /tmp/yulang-budget-audit.log | 0 | 120 new public theorem entries |

A separate Python scope/dependency check exited 0: all 120 audit entries cover
the public theorems, their dependencies are limited to propext/Classical.choice/
Quot.sound, the old Yulang.lean byte prefix is unchanged, frozen Audit.lean and
README.md match HEAD, new Lean files contain no prohibited proof constructs,
and local document links resolve. The whitespace check also passed.

The new audit is [Audit/GeneralNominalBudget.lean](../../lean/Audit/GeneralNominalBudget.lean).
Development builds exposed ordinary elaboration errors; the final commands
above pass. Full legacy audits, tools/verify-lean.sh, Rust/parser tests, and
inference-to-snapshot validation were not run. The unverified stress test is
not a regression theorem.

Added: five Lean modules, the new audit part, this note, and the small
[module guide](2026-11-13-general-nominal-budget-module-guide.md).
Changed: five appended imports in Yulang.lean, an Item 4j pointer in the main
general-boundary note, and entries in the design INDEX. Existing Lean
implementation lines, Audit.lean, README.md, spec, plan inbox, lake configuration,
and git refs are unchanged.

Workflow: the registered prover configuration and callable prover role are
unavailable in this worktree. The primary constructed bounded transport and
measure-obstruction derivations; a separately leased regression agent built
the two actual installation modules. A fresh read-only reviewer checked the
statements, source-transition links, and limits, and ran the focused build.
A separate counterexample review inspected the speculative schedule and caught
the parent-output-target problem in its earlier form. No registered prover run
or closure of termination is claimed.

Assessment: the actual prefix and observation transport use the general
carrier and the exact downstream transition relation. They close real source
bridges rather than another scalar fragment. They do not close the decisive
budget. Repeating a finite-basis or InstallationOrder wrapper would not improve
that result; the next derivation must supply an interval-sensitive source
budget or establish and repair the suspected missing value-provenance edges.
