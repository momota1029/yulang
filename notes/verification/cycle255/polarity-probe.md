# Side-sensitive closure probe

Strict Lean4.35.0 command: `lean --trust=0 -DwarningAsError=true` against the four examples below. Exit0 at2026-11-18T12:21 UTC. This is an abstract representation probe, not an actual sourceStep trace or nontermination counterexample.

```lean
import Yulang.GeneralPresenceCheckedNormal252
open Yulang
example : GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1] (.inter (.var 0) (.var 1)) = none := rfl
example : GeneralPresenceCheckedNormal252.prepare .upper [.var 0,.var 1] (.inter (.var 0) (.var 1)) = some (.inter (.var 0) (.var 1)) := rfl
example : GeneralPresenceCheckedNormal252.prepare .upper [.var 0,.var 1] (.union (.var 0) (.var 1)) = none := rfl
example : GeneralPresenceCheckedNormal252.prepare .lower [.var 0,.var 1] (.union (.var 0) (.var 1)) = some (.union (.var 0) (.var 1)) := rfl
```

These checks explain why future closure cannot be inferred solely from public-name membership.
An intersection of supported variables is an opaque atom for lower normalization, and conversely
a union is opaque for upper normalization. Initial source-atom collection covers the original
fixed fields but not every future cross-side composite. Next inspect actual old/current capture
construction and prove the relevant side-specific atom closure, or preserve such fixed structured
consumers outside the aggregate normalizer. Do not turn a prepare failure into language rejection,
and do not assume distributivity or flatten one connective through the other without proof.

The existing RoleModeRegression251 also separates positional default inputs from named
explicit binders and records nominal-argument actual mode and output-name override.
The next closure proof must retain all of these roles. Its `unknown_not_known` regression
is another reason not to identify an empty/dropped equation list with successful compilation.
These existing modules were inspected, not edited, and their runtime counterpart was not run.
