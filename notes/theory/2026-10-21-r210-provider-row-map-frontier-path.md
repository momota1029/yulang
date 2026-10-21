# R210 — Relay route graph and Effect-row image

The targeted test passed once. Captured stdout SHA-256: `cb092f7ef9589b34e03ca1d8f53399af34d82559d869597200744794b5393ac9`; stderr SHA-256: `1f97b3d3e80b42218786e48198dc4a535de6065b00d050cc494b2a1f967b9efe`.

The exact route is local route 1 for Apply occurrence 19, binding `relay`. Its Capture graph has root node 0, live root 8, boundary 1, and empty source frontier. The positive Function node's child rows are:

| Function port | Captured source row | Capture decision | Fresh image |
|---:|---|---|---|
| 1, argument effect | Effect(23) | level 2, boundary 1, local | Effect(33) |
| 2, result effect | Effect(31) | level 2, boundary 1, local | Effect(32) |
| 3, result value | Value(12) | level 2, boundary 1, local | Value(30) |

The graph also retains nonlocal rows Effect(28) and Effect(9), both at level 1/boundary 1 and unchanged by FreshUse. It contains no Effect(10) row. The source Lambda slot-4 bound remains Effect(10) ≤ Effect(31), relation 71, with completed Origin, admission 64 and physical emission 61 at Effect(10)'s upper-row lane. Thus this Capture graph does not contain the source slot-4 relation as a captured fiber, and its result-effect row 31 is mapped to 32.

The one retained Replay dependency reported for this local route is source relation 95, child 96, with Value inputs on rows 18 and function terms 324/338. It does not itself identify the Effect(10) ≤ Effect(31) source slot-4 edge. This is not an exhaustive negative for other relation, canonical-alias or shared-anchor paths.

## R183 application

This is a concrete source-emitted and completed slot-4 constraint on the exact local binding whose Function is captured by a provider route. Its physical owner Effect(10) is absent from the Capture row table, while Effect(31) is local and remapped to Effect(32). The direct local Capture graph therefore does not itself transport this edge.

A source-qualified counterexample still needs the owner representative of Effect(10), an exact same-provider source path or proof that none exists, and the actual lower input/consumer reached by the same use. R211 checks whether Effect(10) aliases to a retained shared row and whether any captured bound supplies an authentic path after mapping Effect(31) to Effect(32). R183 remains OPEN.
