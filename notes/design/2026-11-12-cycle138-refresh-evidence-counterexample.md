# Actual feedback EvidenceNode: raw-journal counterexample

`GeneralDictionaryRefreshGap.no_evidenceNode` proves the negation of
`B4SkeletonV4.EvidenceNode (GeneralDictionaryFeedbackEvidence.boundary roles)`.
This uses the unchanged source Evidence, feedback Stable, and feedback Local
selection. No definitions in Astra or the target have changed.

The fixture is the existing `GeneralDictionaryJournalObstruction.journal`:
checked singleton registry key 40; a stale packet with invisible key 41;
a genuine selected terminal dictionary with an associated output requiring
source 1 to be int. The original state permits both List int/int and List
string/string models. The stale packet omits the requested output and hence
retains both models, while its alias-key conflict prevents installing key 40.

The missing stability step is now proved. `no_known` works for every nominal
state preserving both models. A normalized scalar head would identify int
with string. A structural or nominal head contradicts the int model by an
actual full-carrier role/nominal probe. Consequently an exact Refresh cannot
make source 1 Known. Singleton sites block enqueue/merge, the stale key blocks
install, and ContextComplete makes every feedback equality already raw.
The journal is therefore genuinely Stable, not merely installation-blocked.
The actual feedback graph is acyclic and key 40 remains selected.
`bad_not_evidence` supplies the source-evidence failure in its string model.

`not_sourceFormed` also proves this raw journal cannot be reached under the
existing source-formation invariant: its recorded invisible key would have
to be registry-visible. Thus the unrestricted raw-state evidence obligation
is false, but this does not refute a SourceFormed-restricted obligation or
the language. Any interface repair requires the appropriate owner; this
cycle does not weaken the target or replace evidence/stability.

Verification: all 12 public declarations passed direct Lean and `--trust=0`
with only standard propext/Classical.choice/Quot.sound dependencies. Combined
parent build and audit-shard registration remain separate verification steps.
