# Cycle148 follow-up: point closure still leaves an actual refresh

`GeneralDictionarySupportPointRefresh.lean` continues the concrete source
path from `GeneralDictionarySupportRevisionStability.pointFinish`.

The point-closed snapshot is now proved **not Stable**, rather than merely
having unproved stability. Source2 is still unknown there. The installed
historical packet entails the nominal self-equation at source2 in every
journal model. A source-preserving `Refresh` can therefore add its explicit
point descriptor. The module constructs the refinement certificate and proves
an actual support `At` at the generated root. This is a fourth actual support
step from the initial source, and preserves the complete journal model set
in both directions for every assignment.

The old generated child is known after that refresh. Its explicit nominal
self-cycle yields an actual support `Local ... .rejected` judgment and excludes
any feedback installation of a packet focused at that child. A concrete model
is retained; this is not rejection manufactured by an empty model set.

This does not determine the root's current selector, prove global stability
of the fourth snapshot, or close general V5. Neither the cycle147 emission-gap
snapshot nor its point-closed continuation is a stable counterexample to
GeneratedChildren: both now have explicit enabled-step witnesses.

Focused Lean4.35.0 `--trust=0` succeeds. Ten exported proof/certificate statements
were individually axiom-audited and use only propext, Classical.choice,
Quot.sound. No existing semantics, transition, aggregate, or audit file was
modified; no full project build was run.
