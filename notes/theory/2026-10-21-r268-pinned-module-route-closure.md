# R268 — Y3 source locator reaches the pinned 40-module set

The primary-only probe reauthenticated all 40 embedded source blobs and
parsed each comment-projected source with the current Y3 parser. It recorded
direct `ModDeclaration` and `UseDeclaration` nodes in source order. Each of
the 39 external module declarations names a child file present in the pinned
set. Each of the 108 `std::` use bases resolves by longest existing module
prefix. The four non-`std` bases are same-source host-act reexports from R267.

The resulting route graph has 147 edges (39 module declarations and 108
standard-library use prefixes). Breadth-first reachability from implicit
`std` reaches exactly 40 module paths: no unresolved module declarations or
`std::` routes, no missing paths, and no excess paths. The temporary Cargo
probe completed in 0.31s and was removed. The exact edge closure is useful for
the sample's source graph, but it is not an observed Y2 ModuleMap: Y3 CST
`ModDeclaration` nodes carry Missing recoveries for Y2's external `pub mod
name;` form, and route-prefix classification does not prove Y2 import or
reexport behavior.

R260's empty imported-initializer conclusion remains conditional, and R149
runtime publication, accepted types, Request reachability and output remain
open. See R268 contract.
