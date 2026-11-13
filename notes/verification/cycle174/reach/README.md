# Cycle174 declaration reachability (read-only)

This is syntactic dependency through types and opaque proof bodies, not semantic relevance or a deletion recommendation. The 261 module declarations include private/generated declarations; the namespace axiom gate uses a different 243-declaration selection. No files were pruned.

|Module|certificate-completeness|certified-diagnostic|conditional-b4|evidence-repair|history-obstruction|
|---|---:|---:|---:|---:|---:|
|GeneralDictionaryAgreedBounded174|0|11|0|0|0|
|GeneralDictionaryAgreedChecked174|0|1|0|0|0|
|GeneralDictionaryAgreedComposition174|0|0|10|0|0|
|GeneralDictionaryAgreedComputed174|22|8|0|0|0|
|GeneralDictionaryAgreedEdge174|2|5|0|0|0|
|GeneralDictionaryAgreedEvidence174|0|0|5|9|1|
|GeneralDictionaryAgreedExact174|0|4|0|0|0|
|GeneralDictionaryAgreedGround174|0|8|11|0|0|
|GeneralDictionaryAgreedHistoryObstruction174|0|0|0|0|7|
|GeneralDictionaryAgreedRefiningTrace174|0|0|0|19|0|
|GeneralDictionaryAgreedRefresh174|0|0|0|1|0|
|GeneralDictionaryAgreedRoleExamples174|0|0|0|0|0|
|GeneralDictionaryAgreedSearchOrder174|1|1|0|0|0|
|GeneralDictionaryAgreedUniform174|26|4|0|0|0|

Root files list the exact public declarations. Counts are not numbers of completed general-language theorems.

- The conditional B4 root depends on explicitly supplied Remaining obligations. Its reachability is not proof those obligations have producers.
- Certified diagnostic correctness uses certificate soundness; certificate-completeness/reordering roots separately test the producer proof closure.
- Evidence repair is the restricted actual ordinary/fixed-refresh history theorem. It does not prove every actual executor trace is in that subrelation.
- History obstruction is a negative result about a sufficient invariant, not a counterexample to B4/Evidence.
