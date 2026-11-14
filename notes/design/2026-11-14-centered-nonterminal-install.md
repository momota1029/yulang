# Centered nonterminal installation: a counterexample to the preservation contract

Status: Lean-certified counterexample to the frozen
`GeneralNominalCenteredSourceConstruction.NonterminalInstallPreservation`.
Unconditional `ClassPSourceProduction` and Class P accessibility remain open.
The proof attempt stopped at this counterexample, as requested. No transition,
boundary, source semantics, or existing target was changed.

## Result and exact scope

The new module `Yulang.GeneralNominalCenteredInstallCounterexample` proves,
without additional hypotheses:

- `not_newly_relevant_origins`
- `not_nonterminal_install_preservation`
- `not_class_p_install_preservation`
- `counterexample`

These names have the common namespace
`Yulang.GeneralNominalCenteredInstallCounterexample`. The last theorem packages
a concrete `Checked` registry, `InitialSource`, `PointSource`, an actual centered
`Step`, and the negation of the original preservation contract. The separate
theorem `unknown_input` proves that source `2` has no known initial head.

This is an invariant/quantifier obstruction. It is **not** a counterexample to
termination, nor a proof that a simulation cannot be constructed using a stronger
invariant. The initial runtime state is reachable; the auxiliary inventory is
permitted by the preservation contract but is not the inventory produced by the
intended full-frontier initializer.

## The three obligations and their composition

`Yulang.GeneralNominalCenteredInstallObligations` defines:

1. `NewlyRelevantOrigins`: every real nonterminal installation has an
   `OriginFrame` over the current inventory. An origin frame preserves old site
   forests, selects the new plan's trusted input fact, and covers all relevant
   input and output-binder origins under that same coarse trusted ledger.
2. `FullReportExposures`: positive global hole eliminations produce
   `IndividualHeadMatching`, with the earlier journal's labels transformed by
   precisely the recorded replacements.
3. `CaptureReconciliation`: further global replacements produce one
   `CommonCaptures` certificate. The certificate contains one presentation,
   uniform readbacks at the explicit stored binder centers, capture scope, old
   site preservation, and historical packet agreement. Its earlier-state journal
   also has exactly the transformed labels.

These are sufficient staged obligations, not a proved equivalence with the
original contract. In particular, `OriginFrame.selected` selects exact input
trust, and origin coverage is required before the exposure stage.

The following standalone theorems are proved in that namespace:

- `Installation.step`
- `Changes.prepend`
- `Changes.trace`
- `Changes.transport_journal`
- `CommonCaptures.finish`
- `nonterminal_install_of_three`
- `simulation_of_three`

`CommonCaptures.finish` constructs the final journal and every field of
`Coverage`; the capture obligation does not assume that final coverage.
New child forests use `GeneralNominalCenteredChildSourceValues.child_site`, with
the same capture trees at every child. `nonterminal_install_of_three` composes
the two elimination histories and yields the exact frozen case.

## Origin production proved before the obstruction

In namespace `Yulang.GeneralNominalCenteredOriginFrameProduction`:

- `input_recorded` derives the recorded raw input fact from the actual guard.
- `models_subset` and `frame_inputs` expose the precise coarse-model premises.
- `frame_inhabited` derives an inhabitant of every candidate frame's coarse
  models from the installation guard, the real post-install model, and trusted
  soundness. No inconsistent model predicate is used to manufacture values.
- `actual_binder` transports an actual schema use to the explicit stored
  `plan.binder` center; it does not recover missing provenance.
- `head_origin` and `needed_value` extract the corresponding labelled values
  from an origin frame.
- `source_snapshot_readback` proves exact readback when the packet snapshot is
  the source snapshot; `initial_snapshot_readback` specializes it to an initial
  installation.
- `of_input` constructs the frame from exact snapshot readback and values for
  the new input origins.
- `newly_relevant_origins` derives the first obligation from the explicitly named
  `InputReadbackAndOrigins` premise.

The counterexample already occurs at the initial snapshot. Its failure is the
missing child value, not a missing provenance rule or an unproved exact-readback
claim about a refresh.

## Concrete source shape

The checked declarations have the following schematic Yulang role shape
(notation here describes the formal declarations, rather than serving as a
parser fixture):

```text
impl P[Pair[A, C]] where R[C, Out = B] { Out = B }
impl R[Pair[X, Y]] where S[X]         { Out = X }

root demand: P[Pair[Pair[?u, ?u], ?u], Out = ?u]
```

`?u` is initially unresolved. The formal source slots are:

```text
0 = Pair(1, 2)
1 = Pair(2, 2)
2 = ?u
3 = Int                  -- an unused source slot
```

The first installation is legal and emits `R[?u, Out = B]`. Its child has the
explicit center `2`. The source fixture proves the report, captures, source
support, candidate selection, installability, novelty, all raw/feedback/centered
cycle exclusions, and the complete centered guard. It then proves `stepP` using
the real `.install` constructor. No transition or guard is a supplied premise.

The named declarations are in namespace
`Yulang.GeneralNominalCenteredInstallExample`; in particular:

- `checked`, `initial_source`, `point`
- `witness_source`, `packetP_holds`, `planP_holds`
- `enabledP`, `guardP`, `novelP`, `stepP`
- `childP_center`

The model used to certify the branch assigns `?u = Int` and gives the output
center the same value. It does not assert that the unknown source is ground.
The pending child is merely registered; no expansion depends on unfinished
implementation output.

## Why the contract is false

The frozen case quantifies over **every** valid inventory and journal with
`Coverage` at a reachable runtime state. It imposes neither complete original
frontier coverage nor a history of semantically justified replacements.

At the initial state, keep only the original frontier index `h` of source `0`.
Use the root forest `[var h]`, and choose empty trusted ledgers. This is a valid
inventory and satisfies all fields of the current `Coverage`: the only
registered site is the root; no trusted input or output-binder origins have yet
been selected. The general construction is proved by
`Yulang.GeneralNominalCenteredInitialInventories.initialized`; its supporting
declarations are `root_value` and `initial_site`.

The new child needs a value at source `2`, but only `h` remains. The declaration
test menu consists of two copies of the pair head. In the actual branch model:

- a leaf must refer to `h`, which denotes `Pair[Pair[Int, Int], Int]`, not `Int`;
- a constructor node must have the pair head, which cannot hold of `Int`.

Every finite value has one of these two outer forms. Therefore no labelled
value for source `2` exists over this inventory. This refutes the first named
obligation directly.

More strongly, any `HoleElimination.Trace` can only remove holes. The same
separation therefore applies to every proposed final inventory. The actual
post-install model satisfies every trusted ledger by the existing trusted
soundness theorem, so changing ledgers cannot avoid the contradiction. The
new child's required `Coverage.sites` value refutes the original
`NonterminalInstallPreservation`, independently of the strengthened origin-frame
staging.

The generic separation proofs are in
`Yulang.GeneralNominalCenteredOriginSeparation`:

- `source_equal`, `no_value`
- `no_origin_frame`
- `no_value_of_heads`
- `no_frame_of_input`
- `no_preservation_of_child`

The concrete module additionally proves `root_origin`, `tests_pair`,
`start_exists`, `witness_initial`, `missing_leaf`, `missing_head`,
`input_relevant`, `no_origin_frame`, and `child_member`.

## What remains

No universal proof of any of the three staged obligations is claimed.
`NewlyRelevantOrigins` and the frozen remaining case are refuted for the
concrete checked source above. `FullReportExposures` and `CaptureReconciliation`
remain unproved. `InputReadbackAndOrigins` remains the explicit premise of the
conditional origin producer; it requires both exact readback and new-origin
values. The latter cannot hold in this example's root-only inventory.

`CommonCaptures.finish` still requires a `CommonCaptures` certificate.
`simulation_of_three` requires `InitialSource`, `PointSource`, and all three
staged propositions. The old `simulation`/`accessible` reductions retain their
`NonterminalInstallPreservation` premise. No unconditional `Simulation`,
`ClassPSourceProduction`, or accessibility result was obtained.

A future additive invariant can retain uniform readbacks for every original
frontier origin, or retain a history of semantically backed replacements.
Syntactic `Trace` ancestry alone is insufficient: `Trace` itself does not require
semantic replacement readbacks. This is a proof-invariant issue, so no new owner
decision about language deferral or rejection is requested. No repair was made
after the counterexample, in accordance with the stop instruction.

## Rename, validation, and review

The branch-owned source trace module is now
`Yulang.GeneralNominalCenteredSourceTrace`, at
`lean/Yulang/GeneralNominalCenteredSourceTrace.lean`, with the matching namespace.
All imports, qualified references, the prior branch audit, and the prior design
note were updated by exact module-token replacement. Each changed dependent
file was created after base `f196a37fd`; the only changed older-file line was the
branch's own appended aggregator import, as expressly authorized. Other changes
are new modules/audit/note plus appended imports and this index entry.

Final verification commands, run from `lean/`:

| Command | Exit code |
| --- | --- |
| `lake build --wfail Yulang.GeneralNominalCenteredInstallCounterexample` | 0 |
| `lake build --wfail Yulang` | 0 |
| `lake env lean Audit/CenteredNonterminalInstall.lean` | 0 |
| `lake env lean Audit/CenteredSourceContinuation.lean` | 0 |
| `lake env lean Audit/CenteredSourceInvariant.lean` | 0 |
| `lake env lean Audit/SourceSyntaxRefinement.lean` | 0 |

The new audit prints 102 declarations, including all example theorems and all
concrete counterexample theorems. Dependencies are limited to `propext`,
`Classical.choice`, and `Quot.sound`. The three earlier audits were rerun after
the rename. The aggregate build completed 2,399 jobs.

The `yulang-proofs` skill was used. No registered `prover` launch surface was
available and no prover agent ran. The primary constructed the staged reduction
and final falsifier; complementary counterexample work constructed the concrete
guarded fixture. A separate fresh reviewer checked the reduction, generic
falsifier, complete fixture, and final quantified conclusions.

Scope checks verify exact rename replacements, appended aggregator/index
changes, imports for every new module, allowed source tokens, and unchanged
HEAD `dd65e427c5d5f93b2da859a0b5705511c144fbcf`. No git refs were changed.
