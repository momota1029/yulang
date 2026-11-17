# Actual merge-entry domain change is not fixed by stable slot names

A representation-side regression uses one input name 7. Old bindings contain
one occurrence (0,1), so actual Definitions241.entries emits no merge entries.
Fresh bindings append another occurrence (1,0), so the same actual constructor
emits stable lo/hi entries. Consequently TargetsWithin fresh old is false,
although slot identities do not depend on the binding list. This isolates a
missing producer obligation for applying the ordered refresh theorem.

Both lists can be prepared independently; absence of a subset certificate
must not become a new source rejection. No source reachability, language
rejection, or semantic inconsistency is claimed by this finite regression.

Verification: GeneralNominalOrderedRefreshDomainLimit248 passed focused Lean
--trust=0 -DwarningAsError=true in cycle247-clean. In addition to stable_slots,
old_empty, fresh_entries and targets_not_within, old_prepares and
fresh_prepares certify that both entry lists prepare successfully separately.
The missing condition is cross-version target inclusion, not individual
ordering failure. No already published Lean file was changed.
