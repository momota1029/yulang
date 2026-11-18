# Read-only selected-root reachability check (T7b-style)

Cycle255Reach.lean traverses each selected constant's type and proof/body constants,
including generated/private helpers, within the19 cycle255 module namespaces.
142 of168 explicitly named declarations are reached from12 selected final roots.
The other26 names are listed in reach.txt. No declaration was deleted.

This is not a global Main/M1 theorem reachability report. It deliberately excludes old
module traversal: frozen old modules cannot import the newly introduced namespaces.
An outside-root declaration is not proven redundant. Some are alternative API theorems,
regression entry points, or mutual-definition wrappers whose generated implementation
is reached through another wrapper. All168 explicit and245 generated/private declarations
remain included in the separate axiom audit; reachability does not replace that audit.
