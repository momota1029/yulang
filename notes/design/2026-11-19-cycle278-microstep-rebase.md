# Cycle 278: microstep-semantic rebase of the checked 239 and 240 loops

Cycle 259 checks full models at round boundaries and a report-driven finite
write. It does not relate the actual states *inside* each raw round. The
present target is the actual install, refresh, and reobserve microstates,
including where the fresh upper name first becomes constrained.

Use a three-phase source presentation (enter / installed / refreshed), with
reobserve crossing into the next round, and the existing normalized
write as successor. The same explicit source-boundary-preserving assignment
must satisfy all intermediate old states as well as the new state. Every
old microedge either lifts to the unique new write or has literally the same
normalized state and no corresponding new write. Check this on both fixtures;
the old raw infinite paths remain real. Arbitrary old branches, the complete
source compiler, and arbitrary-state termination are outside this boundary.
