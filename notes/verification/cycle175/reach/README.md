# Cycle175 core declaration reachability

Read-only kernel dependency traversal through types and values, including opaque proof bodies. Six core modules, 100 declarations (definitions/private/generated included). Regression modules are separately checked, not loaded in this core reach report. This is not specification relevance, a deletion recommendation, or a proof of general B4.

|Module|diagnostic|nominal-inspection|table-certificate|whole-fixed|whole-flexible|
|---|---:|---:|---:|---:|---:|
|GeneralDictionaryAgreedCertifiedEvidence175|4|0|0|0|4|
|GeneralDictionaryAgreedCompletion175|0|0|0|6|5|
|GeneralDictionaryAgreedFlexibleCompletion175|0|0|0|0|2|
|GeneralDictionaryAgreedFlexibleTrace175|0|0|0|0|16|
|GeneralDictionaryAgreedTable175|22|0|23|0|22|
|GeneralDictionaryNominalOnlyRefresh175|0|9|0|0|12|

Exact roots are in adjacent .roots files. All five runs exit 0. Counts are not theorem counts.

- Fixed-history completion reaches the recursive evidence consumer, not the table certificate; successful independent Classify remains a premise.
- Flexible completed diagnostic also reaches the table equivalence and current-journal trace producer. It still assumes full actual halted and the restricted finite trace; reachability does not supply them.
- Nominal-only inspection is independent of the driver/certificate. No centered-state migration follows merely from this dependency fact.
- Certificate completeness/reordering and diagnostic exactness have distinct closures; an unreachable declaration in one group is not unused globally.

Additional Main-root run after loading compactTable: 3 roots, 0/131 declarations.
The earlier five TSVs were produced with six core modules (100 declarations),
before compactTable was added. Do not merge their denominators. Main's abstract
contract does not name these later producers; this is not a deletion argument.
