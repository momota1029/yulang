# Cycle250: remember owner handles instead of reseeding

Status: Draft finite registry component, not a source scheduler.

Key a handle by (demand identity, declaration identity). The first request
chooses one seed and reserves all lo/hi slots. Later requests with the same
immutable input-name list return the existing handle and frame unchanged,
even if support or the public-name list has since grown. A changed input-name
list is an internal mismatch, not a language rejection. Keep actual registry
identity uniqueness and source declaration correspondence separate.

Maintain Registered: every remembered handle's slots are still targets of the
frame. Fresh reservation extends this invariant; persistent refresh and finite
metadata-install traces preserve it via exact target-list equality. Therefore
remembered owners supply raw target coverage on later uses. This removes
per-refresh reseeding in this component, but not unlimited distinct owners,
term growth, new source name collisions, public escape, or source Acc.
