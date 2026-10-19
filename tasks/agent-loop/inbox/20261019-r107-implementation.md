# R107 test-only implementation handoff

Sprint-ID: `method-role-entry-correction-20261019-r107`, revision 1, contract
SHA-256 `6d9cde2feb3b8f91c82cf11a872ea04e03d157ab73ccb53b7b044e9a88082f43`.
Assignment-ID: `R107-TEST-IMPLEMENTATION`; handoff revision 1.
Parent: `/root` (Luna primary). Author/writer: `/root/r107_test_impl`.
Current session: `current-conversation-2026-10-19-r107-method-role-entry-correction`.
Launch receipt: assigned exact test and handoff path leases after CLEAN pre-edit
spec review. Requested model/effort: `gpt-6-luna`/high. Observed model/effort:
UNKNOWN/UNKNOWN.

## Frozen artifact and source correspondence

Artifact: `crates/yu-hir/src/tests/shadow_method_role_source.rs`, SHA-256
`3519e4a5e3cf3fa2a855125f6ea739e6765fea0dd34b0c2c881088a129b259f4`.
The edit restores the original `declarations` binding in the existing test,
preserving its assertions, and completes
`exact_role_impl_member_source_reaches_original_occurrences`:

- The exact original `BindingStatement` is walked through its original syntax
  parents to the `ImplDeclaration`. Each ancestor must have a key owned by the
  same `ParsedFile`; the terminal node/key must equal the implementation node
  and key supplied by the associated declaration view.
- The complete raw `ImplDeclaration` subtree is traversed from original syntax.
  For every node, its same-parse source key resolves to a retained position.
  Original raw children, including tokens and trivia, are compared slot by slot
  with retained child positions for count/order, parent, ordinal, kind, range,
  and node/token status. The declaration's parent and raw slot are derived
  independently from its original syntax parent and raw child sequence.
- Existing exact spelling/range, ordered formals, body occurrence, same-parse
  key ownership, and distinct formal/body `selected` assertions remain.

The embedded fixture remains the exact 148-byte R100 source with no final LF,
SHA-256 `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`.
No semantic scope, production API, diagnostic or expected output changed.
Parent/source/native correspondence is finite parser-entry and retained-source
ownership evidence only for this fixture. It establishes no executable
HirParameterIds, lexical binder resolution, body checking, method lookup,
selection, dispatch, ordinary Apply, candidate/runtime admission or result `2`.
R100 P2/P3/P4, the original Simple-sub/evaluator claims and R85 adoption remain
OPEN. The conditional R106 proof is reused only as argument; no successful
observation is claimed before Luna's authorized command passes.

## Frozen inputs, prior evidence and checks

The R107 contract hash matched before work. Direct pinned hashes rechecked
after the edit and matched: R106 proof note
`b7591ef9aefbe6d8f7694afc2a2b967fd9c4489756d78b52eb7d474aad2523cd`, R106
closeout `5f475d4d09208593ecb929ccfad1faa6266d3d2767a60f96df96b527159eb4bb`,
R106 post-spec review `c13a408a1f7ca156ee03ec8db2a39b71dc1b1a8322201a0ea7f897c5fcb2e97c`,
R106 compiler/source review
`965f2024521e928727b54095faad73fee0b93fff3556b8ab116c222399dbc19`, and the
pinned `yu-hir`/`yu-syntax` sources `lib.rs` (`8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8`),
`shadow.rs` (`9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b`),
`source_identity.rs` (`7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`),
`full_parse.rs` (`24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`),
and `syntax_kind.rs` (`26d2a0ddbe1862c95c503420ded0b0d35217bee5ba9f350be9163c065c6b488d`).
The pre-edit R107 target hash matched the contract at
`1e0683edf8820e7599f196322f653ddb4698555e089e5f4f88b33ed9fae21df4`.

Reused: R106's exact fixture, ranges, same-parse key construction and
declaration/member source observations. Rejected as incomplete: R106's missing
member-to-implementation ancestry and missing raw-order/retained parent-child
comparison, along with its `pending_declarations` compile typo. The fresh R107
pre-edit spec review is CLEAN and confirms the pinned APIs suffice.

Checks performed: read-only review of frozen inputs/APIs and SHA-256 rechecks;
manual source inspection of the fixture and complete raw/retained traversal.
No test, build, compiler, runtime, CLI, formatter or Git command ran. No
command is claimed as green. Allocation charged at grant: 120 seconds; exact
active elapsed time is UNKNOWN.

## Boundary and stopped writer

Required post-output spec and independent compiler/source reviews are pending.
Only Luna may run the one authorized focused command, exactly once, and only
after both reviews are CLEAN. Any review mismatch or command failure ends R107.
No further implementation write is needed under this lease.

New paths: none; changed paths are exactly the leased test and this handoff.
Disposable scratch/generated paths: none. Descendants and unknown descendant
leases: none. **STOP / writes ceased at this frozen handoff.** The producer
does not certify its own artifact.
