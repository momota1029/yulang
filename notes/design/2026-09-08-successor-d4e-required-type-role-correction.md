# D4e required-Type malformed role correction

Status: Authoritative conformance clarification

Date: 2026-09-08

Approved-by: user through the current recovery-selection/documentation
delegation; this applies the existing SD-T/SD-R ownership contract.

Checked-by: primary under the no-subagent instruction, before any matrix
expectation update. No independent review or new parser behavior.

Supersedes: only the D4e primary role label in
`2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`. The original cell is
retained as historical text with navigation to this correction.

## Corrected cell

Keep the exact witness `R({struct S { f: @ }})`, equivalently
`\ref({struct S { f: @ }})`. Its malformed primary fact is:

```text
GrammarRole::Type(TypeRole::Primary)
span("@") = 20..21
RecoveryKind::Error
ExpectedSyntax::TypeExpression
```

The former `Declaration::Struct(FieldType)` Error label conflicts with SD-T
and the named-field SD-R rows: FieldType overrides only a completely absent
outer primary's Missing. Nonempty malformed bytes belong to canonical
Type::Primary. The required-Type role gate and subsequent Equals-ownership
fix preserve this distinction; a caller-role rewrite of Error would violate
it. No second FieldType Missing accompanies the same malformed run.

The witness, recovery extent, expected syntax, ordering and actual embedded
fact-equality obligation are unchanged. D4e remains open for real successor
Yumark evidence; ordinary field/helper tests are not embedded certification.
No snapshot, fixture or executable expectation is changed in this clarification.
