# Cycle249: reservation bookkeeping versus actual model support

Cycle248 established two actual limits: singleton-to-many changes the active
entry domain, and all State.sources includes the owner's already reserved keys.
Do not change accepted source programs or hide promoted public coordinates.

Continue stable-owner rebase rather than semantic quotient versions (I47).
First define actual model support using a view of State with its reserved list
empty. State.Models ignores that bookkeeping list definitionally; this does NOT
remove reservations from the actual operational state. Prove exact model
invariance and derive a smaller sufficient support for preserving raw Models.
Then connect protected actual merge construction to that support plus explicit
binding endpoints. Slots may already be reserved but must be absent from actual
model reads and endpoint reads. This is not automatic privacy of live metadata.

In parallel remove the blanket fresh-target-subset-old-target requirement from
ordinary consumer rebase. Instead require the rewritten consumer typed reads to
avoid fresh targets, and public coordinates to avoid both old and fresh targets.
Old and fresh SafeOrder remain explicit. Use the same forward fresh solve and
backward old solve witnesses. This handles genuinely new unobserved targets
without pretending that arbitrary raw model or packet fields are unaffected.

Next compare finite support of actual compiled raw/live/packet views. Complete
metadata enumeration, live-body growth and a finite-work termination measure
remain essential before Acc. Static support facts do not prove source progress.
