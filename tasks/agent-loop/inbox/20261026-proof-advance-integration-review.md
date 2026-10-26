# Independent integration review: proof advancement

Revision: r1. Reviewer: `/root/call_entry_review`, non-author of this integration
configuration and audit. Requested model/effort inherited; separately observed
model/effort metadata UNKNOWN. Bounded follow-up from the primary; no children,
Git commands, Lean reruns, source changes, or shared-state changes.

## Verdict

**CLEAN for the inspected integration surface.** No blocking, major, or minor
finding. Recommend accepting the added default-build aggregate and complete
originating-module axiom audit. This is an integration review, not independent
certification of all four modules' mathematical or source/native meanings.

## Default build coverage

`notes/theory/lean/lakefile.toml:3,6–8` retains default target `YulangClosure`
and explicitly includes both `YulangClosure` and `YulangClosure.ProofAdvancement`
as library globs. The original root therefore remains in default coverage.
`YulangClosure/ProofAdvancement.lean:1–4` imports exactly:

- `YulangClosure.PaperTermSubstitutionAlgebra`
- `YulangClosure.PaperCallEntryFormation`
- `YulangClosure.PaperAllocationExecution`
- `YulangClosure.NativeIntegerArithmetic`

The inspected default-build log reports successful compilation of the original
`YulangClosure` root at line 6966, the added aggregate at line 6991, and
`Build completed successfully (58 jobs).` at line 6992. It also prints Built
entries for call entry, allocation, and integer arithmetic. The algebra module
is required by the aggregate import and appears in the complete audit's
originating-module inventory; absence of a separate Built line for an
already-current dependency is not missing default-target coverage.

The foreign-reserved `YulangClosure.lean` was deliberately not read or changed
in this narrow review. Its byte preservation is the primary's stated fact;
this review verifies the configuration retains it and the build includes it.

## Complete-module audit and application roots

`AuditProofAdvancement.lean:25–30,53–71` enumerates constants by their actual
originating module index. It selects every `.thmInfo`, without namespace-name,
privacy, visibility, or generated-name filtering. Missing modules, empty
theorem inventories, duplicate theorem targets, and any originating project
`.axiomInfo` fail the audit. Consequently the audit covers generated/private
theorem constants as well as public declarations.

At `:31–52,72–74`, all 20 distinct named application roots must occur in that
theorem inventory. At `:75–85`, each target receives its printed type and
complete transitive axiom report. `collectAxioms` rejects every axiom outside
`propext`, `Classical.choice`, and `Quot.sound`; errors are not caught or
suppressed. The only option changes are printing options at `:18–20`.
No proof hole, native-evaluation shortcut, or kernel-check bypass appears in
the inspected integration/audit source.

Read-only parsing of the complete log independently confirmed:

| Originating module | Theorem constants |
| --- | ---: |
| `PaperTermSubstitutionAlgebra` | 306 |
| `PaperCallEntryFormation` | 23 |
| `PaperAllocationExecution` | 50 |
| `NativeIntegerArithmetic` | 159 |
| **Total** | **538** |

There are exactly 538 unique BEGIN markers, 538 matching END markers in the
same order, and 538 complete axiom reports covering exactly those names.
Every one of the 20 required roots appears exactly once in each inventory.
293 target names are private; generated equation/recursor/termination helpers
also visibly occur. No error or disallowed axiom was found.

| Complete actual axiom set | Count |
| --- | ---: |
| `[propext, Quot.sound]` | 420 |
| `[]` | 68 |
| `[Quot.sound]` | 3 |
| `[propext]` | 19 |
| `[propext, Classical.choice, Quot.sound]` | 28 |

The original audit log ends at `YULANG_AUDIT_COUNT 538`; it does not itself
contain an explicit process-exit marker. The primary then supplied the repeat's
receipt and confirmed log. I read that JSON receipt: the recorded native Lake
command runs `env lean -j1 -M1024 AuditProofAdvancement.lean`, returns exit 0,
takes 2.235 seconds, and reports the same counts. The confirmed log's computed
hash equals the original audited log's hash. Thus the repeat adds explicit
successful-exit evidence without changing the inspected audit content.

## Frozen evidence

All paths below are relative to `notes/theory/lean/` or, for logs/JSON,
`/workspace/scratch/f98087c7ac1a/`.

| Input/evidence | SHA-256 |
| --- | --- |
| `lakefile.toml` | `834b73ad29dd92c372a948c35d7c6c0f3744eade289a3afbab2ab7375a0d6c01` |
| `YulangClosure/ProofAdvancement.lean` | `db2f2f3a548b0b20b15b2435f08a362e903c3e52a035c7eca5580925f08dd598` |
| `AuditProofAdvancement.lean` | `95a10406b14ad9e073e17857b012c9a3c2940bac84c32e21a5fca268562a52dd` |
| `proof-advancement-default-build.log` | `11c37ca02e1f88b47eef5f5efe4da5165dc07c615417d47d06993ba1ea0f0056` |
| `proof-advancement-complete-audit.log` | `0d92bfba29b20072e627c1a71ad6ddc1e62f7fc2aca621a5f70f68de53f06c98` |
| `proof-advancement-confirmed-audit.log` | `0d92bfba29b20072e627c1a71ad6ddc1e62f7fc2aca621a5f70f68de53f06c98` |
| `proof-advancement-audit-receipt.json` | `f6e37ebc4604b6bf5c46b6c4667a25d9cd1bbb9ed58ec369e2d78fe1f08f4986` |

## Scope and cessation

Inspected the three integration files in full, the default build's coverage and
completion evidence, and the audit's complete name/axiom inventories. Did not
re-review all four source modules, every printed theorem's mathematical meaning,
their dependencies, native implementation, source correspondence, or parent
proof closure. Existing semantic reviews retain their separate scopes.

INFO at `AuditProofAdvancement.lean:12–15`: kernel acceptance and axiom-policy
compliance do not discharge hypotheses or replace source/meaning review.
Recommended action: retain those boundaries in the integration outcome. No
source repair or further reviewer rerun is requested.

Only this exact leased review receipt was written. **Receipt frozen; review
writes STOPPED.**
