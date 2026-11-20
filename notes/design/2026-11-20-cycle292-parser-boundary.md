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

## Trace of the current implementation (static)

- `crates/yu-syntax/src/full_parse.rs`: `parse_file` calls
  `cursor::parse_root_with_depth` and creates a fresh private parse brand.
  `SourceNodeKey::eq` compares brand, green allocation, and start offset;
  `owns_source_key` compares only brand. Existing
  `source_node_keys_preserve_clone_brand_and_reject_reused_green_root`
  even reuses an identical green root under a foreign brand and requires
  inequality. Neither byte equality nor source ownership proves resolution.
- `declaration/role_decl.rs` routes the head through the ordinary type-expression
  parser and the body through shared statement machinery. The architecture
  map `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, RLD-S/T
  (around lines 23170–23200), shows a documented `RoleDeclaration` with
  `TypeExpression` occupying the role head; its `Index` primary and
  `'container`, `'key` applications are ordinary type expressions.
  Read the ordered simple head arguments, not `DeclarationTypeParameterList`
  here, and reject a recovered or unsupported head in this restricted bridge.
- The direct block statement `type value` contains an ordinary
  `TypeDeclaration`. RLD's design explicitly does not relabel it as
  associated. The same kind outside that role body is not evidence of an
  associated output. Preserve parent ownership; do not collect all descendant
  TypeDeclarations (e.g. declarations inside nested blocks or roles).
- `declaration/type_decl.rs`, `type_form` /
  `definition_from_item_normalized`: a complete bare form can hand off at a
  nominal boundary without an equals; an equality emits the actual Equals
  token and enters RHS parsing. Recovery may contain a TypeExpression even
  when the separator was missing, or a real Equals with a missing RHS.
  Therefore neither a missing node nor the absence of an RHS alone is a
  required declaration. Validate the actual token, complete name, structural
  diagnostics, kind of RHS and absence of unsupported attachments for this
  first subset. The existing `type_schema_equality_rhs_missing_uses_direct_rowan_order`
  and `type_c14_commits_complete_nominal_headers_at_the_owned_terminal` are
  explicit source-code test witnesses for these distinct shapes (not run here).

Design split: a future Rust producer must derive and attach ordered clean
shells and prove the projection accounts for **all** direct type members,
including unused roles; separately bind those names to the semantic resolver
environment and revision. Rejecting a shaped input in the Lean experiment
means this adapter does not cover it, not that the language rejects it.
No default can be credited to exact source bytes without these two bridges.
