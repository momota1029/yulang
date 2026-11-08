# Named finite path allocation

A source path supplies one seed identity and a finite list of output identities. Its occurrence table is exactly `seed :: outputs`. The root is slot 0; the remaining slots are enumerated, not supplied by the caller. Source identity atoms equate repeated names before running the actual declaration-generated finite path.

For every named path and old state of the computed table length, the real run has exact final models: old constraints, source coherence, and str at each allocated occurrence. A source-level factorization follows from the executable descent theorem. This is a fixed named path carrier, not an allocator for arbitrary parser/nominal graphs or dynamically discovered children.

`success_domain` removes redundant source coherence from the success-domain formula: all allocated types equal str already implies coherence, while the real run still constructs identity atoms. Arbitrary old effects remain in `All values s.atoms`. `empty_success` proves all finite name lists (including duplicate names) succeed from empty old constraints; `rejects_inconsistent` proves old inconsistent state yields none. These are fragment results, not general source typing.
