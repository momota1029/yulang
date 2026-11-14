# A required merge can empty the journal before completion

Status: additive proof record, astra2-centered-30, 2026-11-15.

The requested unconditional completion route is false for the repaired Alloc
boundary. A checked, constructor-covered, ground-point source first installs
its parent with an inhabited full journal. Its two generated same-input R
demands then merge, equating incompatible output requests. Every terminal
continuation still classifies R as selected, although the full journal has no
model. The raw candidate slice remains inhabited.

`GeneralNominalCenteredHeadAllocMergeConflict.not_headBaseline` and
`GeneralNominalCenteredHeadAllocMergeConflict.not_selectedCompletion` are closed
negative theorems for the fixture's concrete role declarations. No caller
supplies reachability, stability, source coverage, or the conflicting merge.
This satisfies the requested counterexample stop condition. There is no new
Step, Local, target, source restriction, refresh rule, or language decision.

## Source and actual execution

The fixture has unary P and zero-input R with associated output `out`.
Its schematic Yulang shape is:

```yulang
impl P int:
    where R(out = int), R(out = :tick int)

impl R:
    type out = int
```

The source demand is `P int`. Zero-input roles use the same ordinary
same-input rule: the list of unnamed inputs is empty in both R demands.
They are the same role, so their output requests must agree.

The Lean registry has P declaration 37, R declaration 38, where-clause IDs
42 and 44, and a local output-equation ID 43 in each clause. Purpose-5 targets
are the repaired, distinct identities keyed by `pair(42,43)` and `pair(44,43)`.
There is no allocation collision. The total emitted schema is exactly

```text
aTarget = int
bTarget = :tick int
```

`GeneralNominalCenteredHeadAllocMergeSource.source_checked`, `coverage`,
`ground`, and `initial_source` establish the actual boundary contract.
`GeneralNominalCenteredHeadAllocMergeInstall.install_step` is the real Alloc
Step from that source, and `installed_models` supplies a full model after it.
Its two child edges and distinct output cells are computed in Lean.

`GeneralNominalCenteredHeadAllocMergeState.merge_step` is the next actual
Step. `same_inputs` proves its input guard, and `not_aliased` proves novelty.
The step records `aTarget = bTarget`. Together with the stored total packet,
this requires `int` and `:tick int` to be equivalent; the full carrier rules
exclude that. `empty_models` proves the resulting absence of models.

The merged state need not yet be terminal: equality feedback can add ordinary
equations because its semantic equality premise quantifies over the empty
full model set. `step_stage` checks every successor constructor and proves
that all continuations only add such equations. The uniform-int assignment
continues to satisfy their raw slice. Neither fresh installation, another
required merge, improving reobservation, nor justified cache refresh can run.
The cache exclusion uses a genuine trusted-ledger model assigning bottom to
all identities outside the initial source; no P output is settled while its R children lack
packets. Thus this argument preserves the 2026-11-15 refresh decision.

Existing unconditional Alloc progress supplies a terminal continuation;
`trace_stage` preserves the exact journal and the raw-model invariant along
it. `final_trace` is a finite Steps witness from the literal initial state,
and `final_stable_focus` proves stability of the generated R focus. This
reuses the earlier progress theorem; it adds no general progress or depth
proof. The terminal is not asserted to be the canonical executor's chosen
terminal from the original source: the completion premises quantify over
**every reachable state**, so that stronger claim is unnecessary.

## Why Local remains selected

R has a unique visible declaration and no unnamed inputs. Its head report
is empty; `chosen_head_model` supplies the raw candidate model. `fresh` proves
allocation freshness from ownership and distinct invocation identities.
`merges_closed` supplies the administrative selection guard.

The current diagnostic does not recognize this merge-created error:

- `GeneralNominalCenteredHeadCandidates.Prepared` uses the raw slice, which
  is inhabited (`final_raw`).
- Semantic K2 explicitly requires an inhabited full journal; the fixture
  also has no structural or nominal raw cycle.
- `GeneralNominalCenteredHeadMatStepLocal.OutputConflict` requires an
  inhabited full journal satisfying the chosen head before it checks that
  the chosen effects have no common model. After this merge, that first
  conjunct is false (`final_no_outputConflict`).

Consequently `final_selected` proves V6 Local selected with key 38 and no
children. `final_no_leaf_packet` proves that no R packet is recorded, and
`final_no_installable` rules out every enabled installation at the terminal.
The aggregate `stable_selected_counterexample` includes checkedness, Initial,
inhabited initial and post-install states, the actual trace, generated focus,
stability, selection, inhabited raw slice, and empty full journal.

## Diagnosis and exact limits

The source contract is satisfied. This is an **implementation/proof-interface
gap in merge-created conflict reporting**, not a new language-semantics
question. Spec §6.3 says 「同じ入力の需要はまとめる」 and
「二つの関連型の出力を等しいとし、需要を一つにまとめる」, explicitly
「impl を選ぶ前、保留のままでも行う」. Its associated-type rule says
「それまでに積まれた制約と合わなければ、その時点で型エラーになる」.
The named-output/input distinction supplied in the turn-15 owner decision
also forbids resolving this by filtering candidates with output requests.
This program has incompatible requests for one R class and must be a type
error. The full Models predicate already represents the inconsistency;
the local conflict predicate and unconditional completion premise do not
account for it.

The exact false claims are

```lean
¬ GeneralNominalCenteredHeadAllocCompletion.HeadBaseline
    GeneralNominalCenteredHeadAllocMergeSource.roles
¬ GeneralNominalCenteredHeadAllocCompletion.SelectedCompletion
    GeneralNominalCenteredHeadAllocMergeSource.roles
```

Both predicates demand a full current model for every reachable selected
state. The final R state has none. Restricting completion to a positive
baseline would avoid this witness but would not discharge the original
unconditional premise or establish generated-child production. A future
repair must treat merge-created inconsistency explicitly, retaining the
head-only candidate rule and ordinary merging. No repair is installed here.

This fixture does **not** refute `GeneratedSelectedChildren`, V5's
`GeneratedChildren`, or `B4TargetV6.Statement`: R has an empty child list,
and semantic `Committed` can hold without a recorded packet when the full
model set is empty. The distinction between `final_no_leaf_packet` and
`Committed` is essential. The twelve existing Alloc laws remain unchanged.
`PacketAssembly` and `ChoiceFromCommon` are neither discharged nor refuted;
their common-model premises exclude this final state. No
`EvidenceNode → Statement` composition is claimed. The evidence obligation
reserved for dot remains exactly

```lean
B4SkeletonV5.EvidenceNode
  (B4TargetV6.prior
    (GeneralNominalCenteredHeadAllocBoundary.boundary roles))
```

## Verification and review

All five new modules are imported from `lean/Yulang.lean`. The new audit is
`lean/Audit/GeneralNominalCenteredHeadAllocMergeConflict.lean`, with dependency
checks for all 114 new public theorems. Main result theorems have no additional
hypothesis; `Good` and `Supported` in internal family lemmas are constructed
by the actual trace, not assumptions on the final counterexample.

The registered prover role/configuration and a callable prover launch surface
were unavailable. The primary constructed this bounded derivation directly.
A separate reviewer checked the source/Step/terminal invariants and the final
Local and negative theorems, and independently ran Lean successfully. The
review specifically confirmed the limitation concerning GeneratedChildren.

Final commands and their exit codes are recorded after verification below.

| Exact command from the repository root | Exit |
| --- | --- |
| `cd lean && lake build --wfail Yulang.GeneralNominalCenteredHeadAllocMergeConflict` | 0 |
| `cd lean && lake build --wfail Yulang` | 0 |
| `cd lean && lake build --wfail` | 0 |
| `cd lean && lake env lean Audit/GeneralNominalCenteredHeadAllocMergeConflict.lean` | 0 |
| `git diff --check` | 0 |

The audit reports only `propext`, `Classical.choice`, and `Quot.sound` across
all 114 declarations. The append-only check preserves every previous byte of
`lean/Yulang.lean` and `notes/design/INDEX.md`; the remaining changes are five
new modules, one new audit, and this note. The new modules contain no forbidden
proof construct. The branch and HEAD remain `astra2/centered` and
`c8e57f5f3d3b292d249d6768516e72c3d97b5f03`.
