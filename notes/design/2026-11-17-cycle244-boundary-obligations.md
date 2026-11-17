# cycle244: exact remaining boundary obligations
Status: Draft proof plan, not a successor boundary implementation.

## Representation versus actual observations

RawView243.Models covers ordinary atoms, heads, interval edges and nominal
argument constraints. Its View deliberately has no inspection graph, catalogue,
source ownership/provenance or mixed trusted cache. JournalSubst244's recovered
draft preserves all semantic View fields but cannot by itself preserve those
missing operational fields. Copying an old frame as metadata proves neither
that a new inspection is sound in the transformed assignment nor that the
candidate-selection support remains complete.

The next real state must expose, rather than hide, the correspondence between:
(1) actual source identity and I45 point-descriptor metadata;
(2) finite expression terms used by current and historical consumers;
(3) per-owner currently active private definitions; and
(4) the assignment readback used by the actual inspector, declarations, cache,
current journal and recursive evidence. Current and historical equations cannot
silently share a new interpretation of the same private name. A mere abstract
RetainedCongruent premise would not build this correspondence.

New244 core lemmas discharge part of(3): another owner's stored atomic definition
block can remain in definition form after physical RHS substitution when its
literal targets are disjoint. CrossRead plus prior External produces subsequent
External, and coherence is retained. It does not prove an actual reachable
report satisfies CrossRead, or update the current inspection graph correctly.

## Why Scheduler242 cannot yet be attached by a one-line simulation

Scheduler242.service calls Machine241.service, which changes only the chosen
owner's literal block and clears that owner's dirty flag. Its service_consistent
proof explicitly uses service_other to leave other clean owners' blocks equal
to compile(facts,other).

EscapedStore242.replaceAll instead physically substitutes the old owner into
EVERY other owner block and base consumer. Journal rewriting also changes its
retained expressions. Thus a real service cannot be called a Scheduler242 service
unless one proves that every touched other block is still literally its compiled
block, or constructs and proves a different simulation/representation invariant.
The current fixed-block idempotence lemma only handles repeating an unchanged
substitution; it does not identify compile outputs after changed definitions.

Blindly marking every owner dirty after every service is NOT a proved solution:
Scheduler242's existing rank decreases because service only drains dirty work
without reintroducing it. Re-dirtying clean owners may destroy that argument.
No such scheduler modification has been implemented or approved as a theorem.

## Required producer order

1. Adapt the new actual-Presence equations/substitution definitions to the
existing GeneralNominalAllocation/Inline241 names after restoring the required
cache. Prove those syntactic adapters, then combine CrossRead with the actual
finite owner table, not a caller-supplied arbitrary sequence. The six recovered
large-import drafts must first be rebuilt and audited, not imported on trust.
2. Establish real source dependency provenance from install, source promotion,
refresh and I45 reobserve. Check same-owner240-style promotion first. A decreasing
rank or the sufficient CrossRead check must be derived, not imposed as a new
language rejection. This may reveal a representation issue requiring a question;
no language decision is made in this note.
3. Define public monotone facts and prove a representation factorization through
those facts for ALL current/historical consumers, not just aggregate endpoint
candidates. Then give a simulation to a proven scheduler, including its dirty
work behavior. Finally prove terminal selected nodes yield actual certificates
and the full recursive EvidenceNode. A finite name pool and finite child pool
alone do not discharge this factorization or the terminal semantic theorem.

## Regression obligations, not claimed reruns

199/202/204/206/218: preserve their current intended accept/reject behavior and
whole output/sharing conditions.230: preserve its nonempty actual W/output O
completion while permitting a changed private aggregate value.239/240: their old
versioned-boundary nontermination remains true; stable representation is not a
renaming-based embedding of those transitions. The new successor must prove its
own operation premises and termination. No regression was deleted or weakened.
