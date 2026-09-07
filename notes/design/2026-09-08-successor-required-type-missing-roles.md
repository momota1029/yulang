# Caller-owned required-Type Missing roles

Status: Authoritative; private helper publication complete, caller conformance open

Date: 2026-09-08

Approved-by: user through the recovery-selection/simplification delegation in
`2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Scope and retained authority

Migrate the two raw Missing branches of
`type_expr::required_type_expr_inner_normalized` and explicitly supply the
owning mandatory slot from every production caller. This follows the
architecture's standalone-Type outer-missing override (around line 12725),
Pattern annotation PTA-O, Struct SD-T, TypeDeclaration TD-T and the existing
declaration role vocabulary. It does not select new accepted syntax or change
the currently implemented boundary/trivia/completion policy.

Only a fresh completely absent outer primary uses the caller role. The
existing nonempty malformed run remains Type::Primary and retains its exact
typed facts, extent and retry. Accepted nested Type recovery retains its own
role. A malformed run reaching a boundary does not acquire an additional
caller Missing. No eighth terminal or recovery-result carrier is needed.

## Explicit role transport

Each production required-Type entry takes one explicit `GrammarRole` value
for its missing slot. Forward it only into the current required-Type attempt,
never into accepted recursive Type parsing. There is no optional production
default, builder inspection, post-hoc remapping or role stored in Recover.

| current producer / caller | role for fresh Missing |
| --- | --- |
| Pattern annotation RHS | Pattern::TypeAnnotation |
| TypeDeclaration equality RHS | Declaration::Type(Rhs) |
| derives role reference | Declaration::Derives(RoleReference) |
| role head | Declaration::Role(Head) |
| standalone impl head / description | Declaration::Impl(Head / Description) |
| act head / source | Declaration::Act(Head / Source) |
| cast target Type | Declaration::Cast(TargetType) |
| Struct named / tuple required Type | Declaration::Struct(FieldType) |
| Enum/Error variant `from` Type | Declaration::Enum/Error(Variant(FromType)) |
| Enum/Error positional payload Type | Declaration::Enum/Error(Variant(PositionalPayload)) |
| Enum/Error named / tuple payload field Type | Declaration::Enum/Error(Variant(NamedFieldType / TupleFieldType)) |

The shared variant driver presently has no declaration identity. Add a small
Enum/Error owner enum whose role operation wraps an existing
VariantDeclarationRole. The enum/error shell selects it and the sequence
forwards it to the variant. At shared field-list entry, select the final
missing-Type role from owner and named/tuple shape, then forward only that
value through the existing field procedures. Struct's direct brace, tuple and
indented entries select Struct::FieldType. No other field/variant recovery is
migrated or reclassified by this transport.

The three isolated normalized required-Type harnesses explicitly use
Type::Primary as their anonymous mandatory-slot role, as allowed by the
standalone-Type contract. Make those harness wrappers test-only. Delete the
five zero-caller ordinary required-Type wrappers (including their internal
one-wrapper call) that supply a fabricated zero successor origin; all real
callers already use normalized coordinate-bearing entries. This is a narrow
required-Type API cleanup, not removal of other ordinary grammar entries.

## Publication and extents

Fresh Missing preserves the existing TypeExpression wrapper containing one
generic Missing node. Publish one record atomically: caller role, Missing,
zero-width range, empty unexpected facts, singleton expectation of
TypeExpression with the same role/range, COMMITTED_RECOVERY_RULE sources and
primary index zero. Generalize the existing Type-expression Missing draft to
accept GrammarRole; existing ArrowRhs/LeadingEffectTypeHead/BracketRowArrow
sites explicitly wrap their unchanged Type roles.

The insertion point is the inspected abstract boundary coordinate when
present, otherwise the current Item's remaining-start extent. Any leading
already emitted by the caller is excluded; still-pending leading remains
pending. Ordinary EOF callers that admitted trailing trivia therefore insert
at the successor; a caller that preserved EOF trivia inserts before it. Do
not emit new trivia or rescan source for the coordinate.

The two fresh boundary branches may share one guarded typed operation. Keep
the existing primary-found boolean and all terminal/Item/cursor behavior.
Normal accepted input gets no recovery allocation. The transport is a small
Copy value; extent work remains recovery-only.

## Pre-write verification contract

Add focused fresh/frozen/shifted/seeded tests for absent standalone required
Type (Type::Primary), with EOF, ordinary pending stop, pre-emitted leading and
an abstract fence. Exact output, Item, cursor, diagnostic allocation and
frozen cursor must agree. Existing standalone missing-Primary tests gain only
the now-published record; malformed Primary and nested-owner records stay
unchanged.

Actual statement/Pattern witnesses must assert caller roles without any
Primary Missing substitution: `x:`, `type T =`, `struct S {a:}`, missing
Enum/Error named-field Type and `from` Type, role/impl head and impl description,
act head/source, cast target and derives role. Use only the currently accepted
shell forms from existing tests. Bypass Missing sites still owned by a
declaration/list remain explicitly outside this helper gate; do not add
typed-node equality for a witness that intentionally includes such raw sites.
Include malformed and nested controls proving the override is not propagated.

M2, primary-only, one implementation pass and at most two batched repairs.
The pre-write binary inventory contains 347 Type/Pattern and direct declaration
tests. Run these known-small owner filters plus derives/variant, normalized
Type, output and recovery-output controls, one package check and scoped format/
diff checks. No broad workspace suite or independent certification. Benchmark
budget: zero samples/processes. Record the callsite mapping above and remaining
owner-local bypass sites before claiming the helper gate complete.

O3b's remaining Expression/Pattern/Statement/declaration/literal raw recovery,
complete typed-owner/RB ledger, actual embedded/header-full and public cutover
remain open. This gate supplies shared Type-callee publication, not independent
certification of those calling owners or the complete O3a/O3b boundary.

Static follow-up found while tracing the shared field caller: tuple field
sequence unconditionally admits a Type attempt, and a pending `=` can be
returned without consuming input and then retried unchanged. Resolve this at
the field-sequence owner in a separate forward-progress gate, with a bounded
witness before broadening validation. Ordinary empty/post-comma tuple Missing
sites bypass this helper and remain field-owned raw sites; role transport
alone must not be reported as their migration.

## Construction checkpoint and open caller checks

The shared helper now publishes every fresh Missing with its explicit caller
role. All production callers in the table are wired; the Type/PV implementation
files have no remaining raw Missing/Error construction. This is not O3a/O3b or
joint certification: calling owners still have their own raw bypass sites.

Five new tests cover seeded/frozen/shifted output, exact pending Items and
abstract boundaries, actual declaration and Pattern roles, non-propagation
into malformed/nested Type, and nominal TypeDeclaration's pending semicolon.
The latter witness retains `type T derives via key;`: its initial test harness
incorrectly demanded consumption of the semicolon, contrary to the existing
`type_c15_preserves_header_boundaries_and_nested_suspension` control. The
separate test now checks the complete pending semicolon rather than changing
the input or the parser. The quoted derives control gains only its
RoleReference Missing at `6215`; its separate raw ViaTarget Missing is retained.

Validation:

- `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`:
  191 passed, including all five new tests and retained malformed/nested/RB
  controls.
- `cargo check -p yu-syntax`, scoped `rustfmt --check --edition 2024`, and
  `git diff --check`: passed; existing 87 package / 38 test warnings.
- Reused `target/debug/deps/yu_syntax-b491637626fa8c73` with
  `--test-threads=1` and the following filters: 424 passed, **5 failed**.
  No tests were skipped and no wider caller-conformance claim is made.

```text
rewrite::tests::type_expr::
rewrite::tests::pattern::
rewrite::tests::type_decl::
rewrite::tests::struct_decl::
rewrite::tests::enum_decl::
rewrite::tests::error_decl::
rewrite::tests::role_decl::
rewrite::tests::impl_decl::
rewrite::tests::act_decl::
rewrite::tests::cast_decl::
rewrite::tests::derives::
rewrite::tests::declaration_variant::
rewrite::tests::normalized::normalized_type
rewrite::tests::normalized::ordinary_type_unmatched
rewrite::tests::output::
rewrite::tests::recovery_output::
```

Open failures, discovered when widening beyond the preceding Type-local
verification (not executed against an unmodified baseline):

| test under rewrite::tests | observed mismatch / next owning investigation |
| --- | --- |
| `declaration_variant::declaration_variant_contextual_pipe_stays_local_to_each_nested_type_owner` | `= A from F(\| T) \| B` has inner native Unknown rather than Pipe; check nested lexical policy and typed Error materialization |
| `impl_decl::impl_head_and_description_use_full_nested_type_surface` | `impl F (A -> B) 't;` recovers the spaced arrow as Error; reconcile inherited Type-ML/Parenthesized admission with formal accepted surface |
| `role_decl::role_head_is_one_full_type_and_nested_body_punctuation_is_suspended` | same `F (A -> B) 't` issue in role head; same owning fix, not a declaration-local workaround |
| `pattern::pattern_annotation_type_caller_close_matrix_preserves_pending_leading` | `x: '[A ) tail` consumes the protected space; audit P/E caller handoff before changing the expectation |
| `pattern::pattern_annotation_named_record_type_owns_its_first_same_kind_close` | record field no longer contains matching-close whitespace; reconcile this external control with the approved record Missing/leading policy |

These mismatches concern earlier nested-Type behavior, not the new
caller-role scalar; the diff does not alter those accepted/error/leading
branches. Their expectations are deliberately unchanged here. Resolve them
under their owning contracts before claiming the wider caller gate complete.
Also retain the tuple nonprogress follow-up above and inspect matrix D4e,
whose outer FieldType Error label conflicts with SD-T's Type::Primary malformed
role. Do not silently use either as a changed recovery oracle.

M2 primary-only, two bounded repairs: duplicate mechanical role forwarding
and the sibling Missing-draft conversion were caught in the first package
check; the new nominal-declaration harness was corrected in the second round.
No independent review or broad certification. Benchmark budget consumed:
zero samples/processes. No chasa-recover API change was needed.
