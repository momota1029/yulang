# Cycle169 selected node assembly

Target: shrink the Evidence/evidenceNode assembly obligation without claiming V5 closure.
For every SourceFormed Shared state, recorded packet and structural Relocates witness,
compare its interpreted Instance with an explicitly supplied exact-occurrence Local
selection. Their keys and ordered children coincide. Consequently the selected key
and current-model child Evidence assemble the parent in the same current snapshot.
No finite MixedTree of the children is required. Local selection is not derived from
Shared Stable, and structural relocation/packet coverage remain open.

A second route generalizes the earlier terminal-only Shared stability theorem:
for every Stable state, genuinely Generated and Installable packet, actual full
Shared PacketGuard, and model satisfying the current journal, derive the current
Instance and generated children; arbitrary same-current child Evidence then yields
the parent. The full PacketGuard is retained (including I26 DecisionGuard and
GenerationGuard). No claim that SafeKnown/Unique alone yields guarded installability.
These are soundness/assembly helpers, not completeness or principality.

## Guard gap / nonvacuity review

`SharedSteps.At.install` requires Installable, novelty and full PacketGuard. Actual
Stable excludes that exact action, hence implies Committed only when all these
remaining guards are supplied. Legacy `FeedbackK2.Local.selected` does not by
itself give Shared DecisionGuard, GenerationGuard, InputCoherence or source-support
ledger certification. Accordingly `relocated_selected` takes Local explicitly and
never identifies it with a future Shared boundary frontier.

A search of existing Shared example modules found no concrete theorem establishing
`GeneralNominalSharedSteps.Stable`. The Display one-step example has an inhabited
model and semantic nonterminal Evidence but explicitly no recorded terminal child;
its known facts do not certify Stable. The new general stability route therefore
has no newly proved nonvacuous stable fixture in this cycle. That is a limitation,
not a reason to weaken the guard or count `evidenceNode` as closed.

## Actual nonterminal route

The finite list lemma constructs payloads from separate per-child existential
Evidence, preserving the list order and repeated occurrences. The actual successor
assembly helper uses the existing Shared current-instance theorem, not stability.
The existing Display installation and its inhabited model instantiate current successor assembly
using independently source-derived Int child Evidence. The conclusion explicitly
requires a payload list of length one. This demonstrates a nonterminal
existential assembly route but is not a new dictionary or new source trace.

Follow-up within cycle169: `GeneralDictionary169SharedStable` now constructs a
concrete Shared Stable fixture by enabled-action contradiction from the existing
Value-stable initial fixture. It has a nonempty named output request but terminal
children and zero steps. The negative search above describes the starting point,
not the final cycle. It still does not instantiate the nonterminal stable helper.
