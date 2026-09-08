# Type caller conformance after owner-local recovery migration

Status: Authoritative conformance clarification; private caller controls complete

Date: 2026-09-08

Authority: the existing narrow owner contracts listed below; no new accepted
syntax or production recovery policy is selected here. The user delegated
recovery simplification and requested primary-only work.

Pre-write specification audit: primary, not independent review, under the
user's no-subagent instruction.

## Scope and causal adjudication

The required-Type role-transport checkpoint passed 191 Type tests but exposed
five failures when expanded to 429 caller/output tests. The implementation
change does not alter these nested Type branches. Preserve each original
source literal and reconcile its expectations with its owning authority,
rather than treating either current output or old recovery as an oracle.

1. `declaration_variant_contextual_pipe_stays_local_to_each_nested_type_owner`:
   T3 §3.2 explicitly emits malformed CallArgument payloads as `Unknown`,
   retaining native trivia boundaries. The later P/E/B/Forall/record/PV
   current-Item rules instead retain the native payload kind. For the two
   `F(| T)` / `F(T | U)` rows, the inner bar is therefore `Unknown` under
   Error, not `Pipe`. Assert both bar spellings, their owner-specific kinds,
   inner Error ancestry, outer non-Error ancestry, and both variants. Keep
   the other rows' native inner `Pipe` requirement.
2. `role_head_is_one_full_type_and_nested_body_punctuation_is_suspended` and
   `impl_head_and_description_use_full_nested_type_surface`: the inherited
   Type-ML correction §§1–2 retains the stop before every nonempty trailing
   trivia cluster, and reactivates it in P/E only for OuterTypeApply
   provenance. Consequently `F (A -> B) 't` is not a zero-recovery example:
   the space before the arrow ends the first Parenthesized item. Retain both
   original role/impl literals as explicit one-Error controls with the arrow
   at `10..12` inside the Parenthesized owner, no Missing and one head Type.
   Add `F (A->B) 't` and `F(A -> B) 't` as accepted controls. Do not broaden
   Type-ML or add a declaration-specific parser workaround.
3. `pattern_annotation_type_caller_close_matrix_preserves_pending_leading`:
   recovery-authority §4 explicitly gives committed P/E the eligible ordinary
   horizontal gap before a raw caller close. The pending payload is protected,
   not that gap. Rename this test to state the horizontal ownership contract,
   include the space in the P/E green text, and require empty pending leading.
   Keep exact caller kind, remainder, completion and recovery counts. Add
   comment-bearing controls requiring the complete nonhorizontal leading to
   remain pending; the horizontal exception must not erase that distinction.
4. `pattern_annotation_named_record_type_owns_its_first_same_kind_close`:
   the record-field current-Item rule gives boundary leading to the record
   sequence/caller, not the failed field slot. Keep both source literals,
   Missing counts, actual first close and second pending close. Remove the
   close-leading space only from the failed field's direct children, and
   explicitly require it as a record-sequence child before the local close.

Governing sources:

- `2026-09-07-successor-t3-typecall-recovery-amendment.md` §3.2;
- `2026-09-07-successor-t4-inherited-type-ml-correction-amendment.md` §§1–2;
- `2026-09-08-successor-recovery-authority-amendment.md` §4;
- `2026-09-08-successor-pe-current-item-recovery.md`, selected rule;
- `2026-09-08-successor-record-field-current-item-recovery.md`, selected rule.

## Bounded gate

M2 test-contract alignment, primary-only, one pass and at most two batched
repairs. No production code or public fixtures change. Run the affected
Pattern/role/impl/variant filters first, then the same known-small 429-test
caller/output filter set from the required-Type checkpoint (plus new tests).
Compilation is already required by the focused test build; the previous
package check remains applicable to unchanged production code. Run scoped
format/diff checks. Benchmark budget: zero samples/processes. No independent
certification, workspace-wide suite, or public cutover claim.

Tuple-field nonprogress, D4e's conflicting malformed role label, calling
owners' raw recovery, the complete Type/PV ledger and actual embedded/header/
full/Yumark/public gates remain separate follow-ups.

## Completion evidence

All five original failures are resolved by the predeclared test alignment;
all original literals remain covered. Three new named tests separate the two
inherited-ML malformed controls and the comment-bearing caller-close control.
No production file, recovery implementation or accepted grammar changed.

- `cargo test -p yu-syntax --lib rewrite::tests::pattern:: -- --test-threads=1`:
  25 passed; test build 39s, existing 38 warnings.
- `target/debug/deps/yu_syntax-b491637626fa8c73 rewrite::tests::role_decl:: rewrite::tests::impl_decl:: rewrite::tests::declaration_variant:: --test-threads=1`:
  43 passed.
- The same binary with all 16 filters listed in the required-Type checkpoint,
  `--test-threads=1`: 432 passed, zero failed/ignored, 1.19s execution.
- `rustfmt --check --edition 2024` on the four changed test files and
  `git diff --check`: passed.

One pass, zero repairs. Primary pre-write and closure inspection are not
independent review. Benchmark budget consumed: zero samples/processes. The
unchanged production package check is carried forward from `2918fa51`; no
workspace-wide suite was repeated. Required-Type's wider caller checkpoint
is now green; the separate tuple progress and aggregate obligations remain.
