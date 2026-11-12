# Draft: stale-key obstruction to modeled Joint

Purpose: test the `ModeledSelectedJoint` sufficient condition, not change source semantics.
A raw journal may contain a checked but registry-invisible packet with the same root identity
and a different key. Choose a terminal len-like declaration on known List/int data,
so every context model satisfies the stale packet and the visible candidate branch and all sources are known. Such a journal
should be stable: installs blocked by stale key, no missing sites, no merges, no refresh,
and journal equality is already ordinary equality. Its selected source dictionary remains
valid, but Joint fails. This distinguishes the sufficient residual from EvidenceNode.
No SourceFormed claim, no changed definitions, no claim about reachable language states.

## Verified outcome

`GeneralDictionaryModeledJointGap` proves this example with the unchanged actual
`GeneralNominalFeedbackSteps.Stable` and `GeneralNominalFeedbackK2.Local`.
The registry has terminal key30 (`len (List a)`), all source slots are known,
and the journal contains key31 under the same root identity, invisible to that registry.
Its ordinary and journal models coincide. Both a concrete model and universal current
source evidence for key30 are proved. The example is also proved **not SourceFormed**.

Consequently `ModeledSelectedJoint roles` is formally false on the current unrestricted
state carrier. It is not a missing theorem to keep trying to prove. This does not refute
`EvidenceNode`, since the model-indexed dictionary exists in this counterexample.
The diagnosis is to separate alias-key coherence/formation from semantic dictionary
soundness, rather than impose Joint indiscriminately. No repair is applied to the target
or to Astra definitions here; a reachability-restricted residual would require an explicit
accepted target change, or a direct EvidenceNode proof avoiding this false residual.

Verification: direct Lean4.35.0 check and `--trust=0` audit of all26 public declarations
passed, using existing dependency oleans read-only. Only standard propext, Classical.choice,
Quot.sound occur. Parent must run its combined focused build and register the audit shard.
