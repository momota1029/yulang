# Cycle 292: where source occurrences stop and resolved identities begin

The active Rust workspace has syntax, recovery, and xtask, but no HIR/name
resolver. The relevant public producer is `ParsedFile::source_root` and descent
via `SourceNode::children`. Its opaque key is parse-branded and includes a
green allocation and byte start. This is source occurrence evidence, not a
semantic role ID, parameter slot, associated name ID or default manifest.
An independent reparse uses a new brand; a clone reuses the brand. Do not
reinterpret ranges or hashes as semantic IDs. The same name and scope can
acquire new occurrences across reparses.

The first executable Lean fragment works downstream of a future CST projection:
one flat role head with named binders, and an associated body that is required,
a single reference to a head binder, or a nullary constructor spelling. This
is not a Rust parser binding or a general type-expression compiler. Role /
associated / constructor IDs are supplied by independent namespaces. The
declarative witness records positional membership `binders[index]? = some s`
and uniqueness of binder spellings. It must not derive a semantic ID from an
occurrence. A closed witness will keep the same symbolic role/body fixed while
swapping two admissible resolver maps, yielding different exported IDs.

The experiment checks separately (1) ambiguity of source-only numeric ID
reconstruction across resolver maps and (2) absence vs required vs default.
No old resolver, CST, spec, runtime journal or kernel is changed.
