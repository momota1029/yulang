# Cycle138: current-context meaning of the entire packet journal

Status: proof plan, 2026-11-12. Target: reduce B4 V4 evidenceNode residual.

Cycle137 transports an old packet only when a separate ordinary Extension connects
its original context to a chosen start state. That does not cover a packet after
multiple alternating installations and descriptor refreshes. We instead induct on
actual `GeneralDictionaryFinishedTrace.Step` traces from an empty initial journal.

Invariant: for every recorded packet and every model of the current journal, its
source Instance holds at the **current** context, with the same registry, key,
occurrence and exact children. Old packets use the finished-inspection transport;
a newly installed packet uses Installable and its private-context extension.
This is proved from actual transitions, not assumed as a B4 field.

Refreshes retain the existing same-carrier/fixed-view restriction of cycle137.
We do not change Astra's Step, Stable, source grammar, or any Evidence definition.
The final theorem does not assert that every stable selected node is recorded,
nor that all finite dictionary witnesses exist. These remain explicit B4 gaps.

Yulang2: reviewed existing x-oracle X1/X2/X8/X9; these provide no execution oracle
for journal reconstruction or certified observation refresh. This is a proof of
existing Lean model operations, not a new claim about old runtime behavior.
