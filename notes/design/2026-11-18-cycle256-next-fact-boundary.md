# Next source-to-finite-fact boundary after cycle256

Status: design obligations, not a new operational semantics or an Acc proof.

## What the current proof actually buys

1. A real prepared Frame excludes empty input capture folds.
2. The exact lo/hi support obligation is per historical endpoint and side.
3. For the all-index, genuinely reachable I45 family, its actual lower-history
   projection passes the fixed two-atom check. Every base slot type reduces to
   one of five initial variables, but there remain n+5 slots.
4. General ordered elimination of a block actually included in raw.ordinary
   preserves complete public model projections (all unhidden components and all
   rows). This needs no SafeOrder because it is elimination of retained
   constraints, not construction of a fresh model for arbitrary equations.

## Candidate representation to investigate next

Keep source/public reference names literal. Replace private type definitions by
checked expressions over the fixed source/public basis, preserving old/current
roles before flattening. Store constraints as keys of normalized formulas rather
than by the number of old slot records or repeated journal entries.

For a tentative finite fact universe F, the useful order is ordinary subset on
stored facts. A new transition may add syntactically new normalized facts, even
if they happen to be semantically redundant; a finite F still bounds this.
It need not decide full semantic equivalence merely to exclude identical facts.
However, claiming a finite F now would be circular: all consumers, active rows,
origins/paths, template instantiations, and safe handling of cross-polarity
references must first be shown to range over a single source-defined universe.

## Three concrete next obligations

### A. PolaritySourceClosure

For the actual old/current environment supplied to every enabled install or
revision, derive EndpointSupported from source formation and operation guards.
Do not assume allocation purpose alone ensures the read side. Nonpoint revision
has no syntactic purpose-side restriction; semantic cache/raw-back obligations
must be used. The distinct-lower-endpoint plus cross-role revision test in the
main design note is the next finite-source stress test. A handwritten expression
or an arbitrary assignment is not a source-reachable counterexample.

A narrower independently useful extension is both-lower-and-upper retained
history elimination for the I45 family. The present history contains lower
entries only. Upper targets still occur in ordinary constraints. This must be
fixed before promoting its five-value slot theorem to whole-field finiteness.

### B. UsedConsumerAndInspectionPreservation

Treat these as separate obligations:
- raw Models/public model projection, now proved for retained ordered elimination;
- actual old versus current binder/capture/target values;
- Known/RootPending, head matching, PointDescriptor, K2 inspection, and cache trust;
- generated children/output identities and owner ancestry;
- active row terms and effect rows.

Model-set equality alone does not supply the latter four. In particular,
RawView.slot.row is inactive in current View.Models, but ordinary row atoms and
nominal row parameters are active and were not erased. Erasing inactive metadata
is not a proof that a reified source state or a future Step is preserved.

### C. CanonicalStrictProgress

Only after A and B give a fixed finite fact universe, prove that each permitted
successor step adds a fact not already present, or decreases a finite refinement
component. Literal duplicate revisions must be excluded by the new relation.
Then use the number of missing facts, together with the finite uninstalled-owner
component, for an accessibility measure. Existing I45 Step still has no-Acc,
while the new aggregate/slot representatives are constant/finite; the Usage file
checks both facts together. No contradiction is being concealed by normalization.

## Specification guard against an unjustified shortcut

Re-read spec/06-roles.md §6.5. It explicitly says invariant arguments are handled
as intervals rather than made points by type equivalence, and distinguishes
actual center identifiers from the matching endpoints. Therefore do not identify
public source names 2 and4 merely because some/all fixture models give them
Equivalent values. The present fixed representative remains (var2,var4), not
(var2,var2). Private elimination is justified by its retained defining equations;
public-name coalescing or changing matching/classification would require its own
faithfulness theorem and cannot be inferred from the current Models equivalence.

I50 output-depth/constructor-cycle rejection, all-source private nonescape,
operational Acc, mixed-time packet compiler, Permitted, twelve laws/regressions,
and EvidenceNode remain open. No semantic rule change or new language restriction
is proposed here. Do not start the packet compiler on the strength of this note.

## Do not turn the missing progress proof into a definition trick

Defining `newStep := oldStep and rank_decreases` would make its Acc easy but
would not show that the source algorithm can take every step it needs or reach
the required evidence. Likewise, putting a desired pool-closure property into
Permitted would move rather than solve the problem. The actual executable
normalization/check/canonical-fact producer must supply closure; a genuine
no-change skip must preserve matching, all required replay certificates, and
final classification. In particular a fact may be semantically redundant while
its historical/current certificate is still needed. Preserve that evidence
until a finite canonical certificate representation is proved sufficient.

## Next regression matrix

| Case | Already established | Still required before use in a successor claim |
|---|---|---|
| I45 duplicate lower replay | Actual source path for all n; actual retained lower history; fixed aggregate and slot-type values; current raw public-model projection | Both lower/upper full consumer normalization; index/certificate treatment; true strict-progress Step |
| Distinct lower atoms followed by upper read | Existing generic side-support check pinpoints the exact obligation; nonpoint guard does not itself tag polarity | Closed Initial/install/reobserve/cache/raw-back witness or source preservation theorem; do not use the abstract probe as that witness |
| Inactive slot.row private pointer | Actual raw metadata pointer retained; current View.Models ignores it | Any reification/future-transition use; ordinary and descriptor row consumers must be tracked separately |
| Active row inside a type/nominal parameter | Prior all-read collectors keep these reads visible | Source-derived finite row support and faithful rewriting, not metadata erasure |
| Old/current role collision (230/251 line) | Earlier regressions distinguish snapshot values from current targets | A real successor environment simultaneously handles body/default/nominal actual-mode switches and retained certificates |
| Associated output depth (252/254 line) | Old max bound refuted; conditional additive ground representative and raw-template bounds proved | Unconditional source producer/positive-cycle rejection needed for the all-state depth invariant |

This matrix records remaining proof work, not permissions to change semantics.
