# Cycle176 read-only dependency analysis

Roots and exact TSV tables are adjacent. Private and compiler-generated
constants are counted. No code is removed. A dependency edge is syntactic
proof/type use, not a specification-fidelity judgment.

|Module|Loaded|G composition|Conditional field|Nonvacuous tree|Seven roots|
|---|---:|---:|---:|---:|---:|
|GeneralDictionaryCenteredCandidate176|20|0|0|0|5|
|GeneralDictionaryCenteredFlexible176|22|0|0|16|16|
|GeneralDictionaryCenteredFootprint176|18|0|0|10|10|
|GeneralDictionaryCenteredInhabited176|17|0|0|14|14|
|GeneralDictionaryCenteredLedger176|9|0|0|0|8|
|GeneralDictionaryCenteredNonvacuous176|5|0|0|4|4|
|GeneralDictionaryCenteredReady176|6|0|6|0|6|
|GeneralDictionaryCenteredRecorded176|12|0|0|6|9|
|GeneralDictionaryCenteredRegression176|5|0|0|0|1|
|GeneralDictionaryCenteredRevision176|18|0|0|13|13|
|GeneralDictionaryCenteredSharedMerge176|6|0|0|0|6|
|GeneralDictionaryCenteredTree176|3|0|0|1|1|
|GeneralDictionaryHeadFootprintRegression176|21|0|0|0|18|
|GeneralDictionaryViewFootprint176|85|0|0|48|50|

G composition references zero new declarations because the general EvidenceNode
field is still supplied as a parameter. The conditional field consumer alone
uses six declarations and does not establish its unproved plan producer.
The nonvacuous finite-history theorem actually depends on112 new declarations;
its recorded-tree existence and restricted-history assumptions remain explicit.
