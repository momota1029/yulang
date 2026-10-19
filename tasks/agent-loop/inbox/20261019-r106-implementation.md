# R106 test-only implementation handoff

Sprint-ID: `method-role-source-entry-20261019-r106`, revision 1,
contract SHA-256 `edd6c951b46b3f1993c57b5f5cdec4928652cfb313120bd60d9e64c6ebc922bf`.
Assignment-ID: `R106-TEST-IMPLEMENTATION`; handoff revision 1.
Parent: `/root` (Luna primary). Author/writer: `/root/r106_test_impl`.
Current session: `current-conversation-2026-10-19-r106-method-role-source-entry`.
Launch receipt: parent assigned the exact two-path R106 test-only lease.
Requested model/effort: `gpt-6-luna`/high. Observed model/effort: UNKNOWN/UNKNOWN.

## Frozen output and source evidence

Added exactly one test, `exact_role_impl_member_source_reaches_original_occurrences`,
to `crates/yu-hir/src/tests/shadow_method_role_source.rs`.
Artifact SHA-256: `1e0683edf8820e7599f196322f653ddb4698555e089e5f4f88b33ed9fae21df4`.
The existing test assertions remain present. The test embeds the exact 148-byte
fixture with no final LF, constructs one `ParsedFile`, and uses the retained
artifact's same parsed value for source-key lookup, retention, and association.

The source observation checks the direct `RoleDeclaration` and
`ImplDeclaration` roots (ranges `0..51` and `52..114`), and the implementation
member's nested `BindingStatement`/header/pattern/body ownership. It checks
ordered target children `second`, `self`, `selected`, their exact source ranges,
and a distinct body `selected` at `104..112`. For each inspected syntax node,
the key is minted by `source_keys(artifact.parsed())`, is owned by that same
parse, and round-trips through `artifact.source_position` to a retained position
with matching kind and range. The two `selected` nodes have distinct syntax
nodes, source keys, and retained position IDs.

Parent/source/native correspondence: this is finite exact-source parser-entry,
same-parse identity, and retained syntax evidence for this fixture. It supplies
the R100-ENTRY observation for the proof lane to apply to R100's conditional
constructor/consumer analysis. It does not establish executable HIR binders,
lexical resolution, body checking, member selection, dispatch, candidate/runtime
admission, or evaluation result `2`. R100 P2/P3/P4 and the original
Simple-sub/evaluator theorem remain OPEN. No production source or semantic
expectation changed; no withdrawn Simple-sub bypass was restored.

## Inputs, checks, and budget

Contract SHA-256 matched. All 18 direct input hashes listed in the frozen
contract matched before editing and were rechecked after editing; no dependency
drift or missing owner was encountered. This includes the original target-file
hash `6d5c3fec7b4ca0d4618f4ad378f0ad5e8e0689b4897d406ab90d175ba78e6135`,
R100 proof note `84a2aad8a63cad8673e2862e343eff27664c3daf003e97015a0289ba9569a971`,
R100 proof handoff `1a692cb7f3c31e83bf60ee90763216ef3253f2c357747c9258eff16e2f8cec19`,
R100 closeout `6fefb70bf9c211e7cdb5a37a9d09706b8530f5aa7a3fa80575af6ea74ef3516b`,
R95 closeout `dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1`,
and the pinned HIR/syntax sources in the contract. The exact fixture hash
specified there is `fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb`.

Checks performed: read-only inspection of the frozen contract/review receipt
and pinned APIs; source hash rechecks; manual source-range and ownership review.
No test, build, compiler, runtime, CLI, formatter, or Git command was run.
Implementation allocation: 360 seconds charged at grant; precise active elapsed
time was not independently instrumented and is UNKNOWN. No additional budget
was requested or spent on tests.

## Boundary and stop

The fresh pre-edit spec review is CLEAN. The exact output now awaits fresh
post-output spec and compiler/source reviews. The one authorized test command
remains Luna-owned and must only run once after both reviews are CLEAN.
Falsifier: a differing parse root, source range/order, parent relation, or
same-parse key/position round-trip fails this bounded observation; the test has
not been executed here.

Next in-envelope action: Luna obtains the assigned post-output reviews, then
may run the single authorized command under the contract. No worker-side next
write remains. New paths: none; only the two leased output paths were changed.
No generated or disposable scratch paths were created. No descendants or
unknown descendant leases. **STOP / writes ceased at this frozen handoff.**
This producer does not certify its own work.
