# Cycle 293: direct CST shape to an unresolved role

Start from the documented Rowan role topology and the actual Rust emissions,
not from preclassified binder/member DTOs. Verify a narrow topology: plain
or explicitly visible role, one TypeExpression head, ordered simple
TypeApplyArgument nodes, and an indented role body under an actual colon.
Every direct statement must have exactly one selected child; recognize
ordinary TypeDeclaration and a clean ordinary BindingStatement only.
A nested declaration must never be mistaken for a direct role member;
unrecognized topologies fail the adapter, not the language.

Keep raw mixed child indices before ignoring trivia, so path handles are
anchored to a single supplied parse/tree and lost positions are detectable.
Separate a raw exported tree from the Rust SourceNode that could emit it.
The existing public parser exposes CST but the current environment has no
Rust toolchain. No Rust execution, production export or name resolution is
claimed. Scope and parse identity are independently supplied.
