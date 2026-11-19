# Cycle 271: exact visibility for finite record-origin edges
The mixed recurrence checker excluded every record because a coarse record
tag does not determine a literal shape; cycle270 proved a shadowed second
position can never be semantically equal to a target. Keep the unchanged
old semantic judgment and derive the first-visible label contract:

1. Compute first payload by label in a finite list. Show every field probe
splits on that lookup; equal lookup tables preserve all probes and the full
type. Equivalent finite records have the same visible labels and equivalent
first payloads. Preserve the separate exact-empty meaning.
2. Given a noncanonical projected index and all-model equality to a target,
a single full model excludes hidden indices by changing the hidden
payload while keeping every first lookup unchanged. A visible index then
agrees with the corresponding canonical recorded child in all models.
Infer the actual unrestricted semantic Edge iff at least one recorded
child is equal to the target; unknown target equality remains unknown.
3. Combine this exact edge inversion with rigid/nominal closure and a
model witness. Synthetic journal fixtures should include nontrivial
record fields; no claim about surface reachability, general model
construction, or kernel termination.
