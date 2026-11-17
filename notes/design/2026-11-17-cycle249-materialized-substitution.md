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
