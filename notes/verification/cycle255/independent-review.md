# Independent read-only review
Checkpoint 9dc0b446f9ae653336996fea939c21e66bb435c6 was reviewed by a separate reader.
Scope: GeneralPresenceSourceSupport255, GeneralNominalSourceViewSupport255,
GeneralNominalSourceBasis255, GeneralNominalViewTypeImage255, GeneralNominalViewFixed255,
and the design note as published at that commit.
No claim-scope confusion found. Initial identity compile has unconditional source-pool
support; private separation needs InitialSource.below_seed and public purpose <= 1.
Field-private-free and finite candidates alone do not imply semantic preservation:
unsupported normalization may discard atoms. Rows, slots and journal are not finite here.
No independent rebuild was run. Later additions require a separate review.

A second read-only review covered checkpoint 87a36708384f177797028fe5fbd53c966f2e9f68:
TemplateCongruence255, TemplateNormal255, SourceTemplateMenu255, TemplateSupport255,
CanonicalBasis255 and NormalizedDepth255 (all GeneralNominal-prefixed), plus design.
No scope confusion found. Semantics needs used-(mode,name) support or prepare success;
finite menu/private-free/depth facts alone do not provide it. Menu is an overapproximation.
Canonical means duplicate-free selected-side atom lists, not a unique representative of
all semantically equivalent syntax. Depth is stored syntax, not ground readback.
No independent rebuild. DictionaryTemplateMenu255 and SourcePublicBasis255 were added later.
