# C368: separate release support from the ordinary K2 graph

I-65's frozen interfaces and all-state/all-model goal are unchanged. This is a source-level proof plan and algebraic argument, not a Lean-checked result or a change to which programs the language accepts.

## Actual data and a representation obstruction

`GeneralDeclarativeI65.State` carries the current ordinary state, declaration modes, original typed observations and their routes. It does not carry an independent ordinary source/produced/released table. In `GeneralDeclarativeWitnessOrigins350`, `Attached s t` verifies that a table's authored and produced equations occur in `s`; it does not constrain the released IDs. `visible_iff` reads input support from that independent table.

Consider an exact produced pair `(row, owner)` in an attached table, with `row` neither authored nor produced by any previously released owner. Keeping the ordinary state, all rows, and the producer table unchanged, compare the same table with and without that owner in the released list. Both attachments are valid because their membership obligations are unchanged. The old table has no source or released provenance for that row; the augmented table names its exact producer and has a released origin. Thus ordinary truth and all I-65 fitting-model premises are identical while input support differs. This is a general conditional representation argument, not a claim of two reached solver states or permission to alter real release data. Recovering the correct one therefore needs an independent source/completion fact, not another deduction from an ordinary equality.

## Use two graphs, not one

The older `restriction` in C321 filters equations but retains all ordinary normalized bounds. Its `Alias.bounds` can therefore prove a logical alias with mutual bounds whose support has not been independently established. This is fine for ordinary recurrence, but is not by itself a proof that a head lookup through that route is independently authorized. For the positive ordinary prefix, track a chain of explicit backed alias equations (and later independently backed normalized bounds), plus the backed original head row at each inspected ancestor. Each edge lifts into the full ordinary structural graph; the cycle at the actual reached site is checked in that full graph, so unfinished equations can still cause K2 there. The root K2 check remains before pending. A rival prefix can veto a selected or ambiguous outcome without proving that rival has a completed head. Off-prefix recursion, bare aliases, and capture-only visits are not automatically K2. The current normalized named view is not complete for inline/open or native typed paths.

## Exact route disagreement

For a written declared application, scan all actual routes of the requested endpoint for the required original tag. An independently recorded incompatible tag plus *absence of that required tag on every actual route* excludes a genuine matching native-head witness without a fitting-model hypothesis. If the required tag is also present at another physical original site, keep both; do not overwrite either. An empty route set alone is not a positive miss. This yields a fact about one exact candidate lane, not a whole-rule verdict, and no semantics of conflicting routes was added.

## Next ordered proof cuts

1. Tie ordinary source/release facts, including normalized alias steps, to the actual declarative input before using any existing prefix or pending judgment. Preserve the full ordinary graph for the independent K2 veto. Connect source-native endpoint paths to their real logical positions before drawing the analogous typed conclusion.
2. From the exact selected source row and spans, keep the literal ordered compiler children and ordinary plus typed fixed writes at original ordinals and targets. A previously fixed typed observation in the current state has same-model meaning; it is not downstream release authority. Postselection repeated-center equations come from the actual body, never from endpoint equality.
3. Only then connect the complete local rules to the frozen recursive dictionary theorem. No unified checker or top-level checker theorem yet; no new fixtures, old `Local`, termination, or completeness.
