# Selected-root usage by module
12 roots are listed in Audit/Cycle255Reach.lean. Counts include explicitly named def/theorem declarations only; generated/private traversal is used when reaching them. This is a structural dependency result, not a claim that outside-root APIs are unnecessary.

| Module | Reached | Outside selected roots | Total |
|---|---:|---:|---:|
| GeneralDictionarySourceAtom255 | 4 | 0 | 4 |
| GeneralNominalViewTypeTerms255 | 9 | 2 | 11 |
| GeneralNominalViewTypeMap255 | 11 | 0 | 11 |
| GeneralNominalViewNormal255 | 10 | 7 | 17 |
| GeneralDictionaryViewNormal255 | 2 | 2 | 4 |
| GeneralPresenceSourceSupport255 | 8 | 0 | 8 |
| GeneralNominalSourceViewSupport255 | 10 | 0 | 10 |
| GeneralNominalSourceBasis255 | 4 | 3 | 7 |
| GeneralNominalViewTypeImage255 | 14 | 4 | 18 |
| GeneralNominalViewFixed255 | 7 | 1 | 8 |
| GeneralNominalTemplateChoices255 | 5 | 1 | 6 |
| GeneralNominalTemplateCongruence255 | 2 | 1 | 3 |
| GeneralNominalTemplateNormal255 | 12 | 0 | 12 |
| GeneralNominalSourceTemplateMenu255 | 4 | 0 | 4 |
| GeneralNominalTemplateSupport255 | 8 | 1 | 9 |
| GeneralNominalCanonicalBasis255 | 9 | 1 | 10 |
| GeneralNominalNormalizedDepth255 | 8 | 0 | 8 |
| GeneralDictionaryTemplateMenu255 | 10 | 2 | 12 |
| GeneralNominalSourcePublicBasis255 | 5 | 1 | 6 |

Use the CanonicalBasis/SourcePublicBasis and source_prepared APIs when connecting the next closure invariant. The raw concatenated SourceBasis APIs remain support witnesses; do not confuse them with the duplicate-free basis. Some mutual wrappers are outside selected roots because their generated mutual implementation is already reached through another wrapper.
No files or declarations were removed.
