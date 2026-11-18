# Finite substitution on already materialized journal views

Implement total finite map operations on Projection/Schema, Packet/Class/
Observed, then Journal. Reuse actual Origin.subst, Live.Site.subst,
Effect.Expr.subst and Raw.View substitution. Every type and row endpoint is
substituted; labels, indices, unknown flags and list membership remain fixed.
Prove each Models/Holds iff against the same RawView.read mapping assignment.
No alias-class enumeration is rerun: this operates on already materialized
lists. Ordered mapping then specializes via read_mapping = solve.

These operations are not a source transition, do not produce a fresh block,
and do not prove finite live-body growth, source progress, Acc or EvidenceNode.

Completed and verified: GeneralNominalProjectionSchemaSubst249,
GeneralNominalPacketSubst249 and GeneralNominalJournalSubst249 pass focused
--trust=0 -DwarningAsError=true. All proposed stages were reached. Journal
models_exact is for arbitrary mappings; ordered_exact specializes to actual
sequential solve without SafeOrder; repeated gives two-step exact readback.
These are semantic exactness facts, not a claim of syntax idempotence or
bounded-size repeated rewriting. Existing identifiers and unknown flags are
preserved by the definitions, with every listed semantic field transformed.

Further verified: GeneralNominalJournalSubstClosed249 proves literal absorption
of a second mapping whose target set lies within the first safe ordered block,
for the complete materialized Journal syntax, plus literal idempotence.
GeneralNominalJournalSubstSupport249 proves direct old-target elimination from
the full calculated typed support after subst on ANY materialized Journal,
not only an original compile result. Its within_protected supplies the metadata
half of an owner-frame protection certificate for subset-domain refresh;
OrderedExpansion249.protected_of_within supplies the consumer half.
Both files pass --trust=0 -DwarningAsError=true with all linters enabled.

The guarantee is for the fixed materialized fields and consumer list passed
through these substitutions. Additional observations/packets, changes of live
bodies, growing definitions, and an actual scheduler transition are not bounded
by syntax absorption. Materialized provenance is not source reachability.
