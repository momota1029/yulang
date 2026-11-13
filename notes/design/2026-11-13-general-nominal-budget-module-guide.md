# General nominal generation-budget modules

Status: navigation for Item 4j's partial result, 2026-11-13.
No unconditional generation budget or termination proof is provided.

| Module | Purpose |
|---|---|
| [GeneralNominalBudgetObservation](../../lean/Yulang/GeneralNominalBudgetObservation.lean) | Support depth is preserved through the existing certified observation closure |
| [GeneralNominalBudgetDepthObstruction](../../lean/Yulang/GeneralNominalBudgetDepthObstruction.lean) | Actual producer grounding loss, pool bound 0→1, and unbounded model heights at one two-slot initial source |
| [GeneralNominalBudgetMergeRetention](../../lean/Yulang/GeneralNominalBudgetMergeRetention.lean) | Actual equal-input alias merge retains distinct lossless occurrence identities |
| [GeneralNominalBudgetContainer](../../lean/Yulang/GeneralNominalBudgetContainer.lean) | Full Container installation and discharge after P |
| [GeneralNominalBudgetPrefix](../../lean/Yulang/GeneralNominalBudgetPrefix.lean) | Actual P→Container→Wrap prefix, full-ledger downstream block, and fixed-journal observation corollaries |

Read the [design and ledger](2026-11-13-general-nominal-budget.md) for exact
quantifiers, proof limits, V5 count, and check commands. All public theorem
audit entries are in [the new audit part](../../lean/Audit/GeneralNominalBudget.lean).
Existing Step, Stable, Committed, and evidence interfaces are unchanged.
