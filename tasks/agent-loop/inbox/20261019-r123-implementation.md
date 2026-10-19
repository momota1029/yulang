# R123 implementation handoff

Status: Luna reviewed and repaired the stopped partial output; frozen for independent review; implementation lane STOPPED.

Appended one isolated structural test, member_annotations_stay_on_their_original_formal,
to the leased shadow method-role source test file. It parses the contract's three
exact full sources independently and checks empty syntax diagnostics; member
ancestry under each parse's original ImplDeclaration; source-key ownership in
that parse; binder order second/self/selected; no annotations on the first two
formals; absent, int, or explicit empty-row annotation only below selected's
formal pattern; and distinct formal/body selected nodes, source keys, retained
positions, and ranges. For every source it resolves the member, all three binder
nodes, the BindingBody, and the formal/body selected identifiers through
ShadowArtifact::source_position, then checks retained kind and range. It also
checks retained annotation and BracketRow positions when present, and verifies
that retained parent chains preserve the relevant source ownership: binders
under the member, the selected annotation under its binder, the explicit row
under its annotation, the formal identifier under its binder, and the body
identifier under BindingBody (itself under the member).

The explicit empty-row case additionally requires one indexed `BracketRow`
with original source text `[]`; the ordinary `int` annotation requires none.
The test also checks that pending_role_impl_sources and
with_associated_method_role_sources retain the original RoleDeclaration and
ImplDeclaration nodes. Those declaration-level APIs do not return binder order
or a member formal's own annotation; the test obtains those facts from the
original member subtree. No HIR lowering, candidate solve, runtime, or method
execution is involved.

Producer began under R123 rev3 SHA-256
5d452b7521fd1027a64236dba70ad5e86588ac1908a523e3db15de8dcf1b1e71. Final
contract is R123 rev4 SHA-256
77b3aa1b50738366590faac3524ac86c38603155fa74c6ffe8fe82c648bded63; Luna
checked its added `full_parse.rs` pin. All 21 rev3 input pins matched before writing. The three source lengths and
hashes are the contract values: 148 bytes / fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb;
154 bytes / 9785e53f0ac8782dfa8369e844054f0e18234b92973ddde01c6b9b236cde63cd;
157 bytes / 335126c188f068f2682a94b5e0bf7b81687ec453b53ca62fedec4bdb9f760060.
No production code or existing expectation changed. No tests/builds/CLI/
formatter/Git actions, scratch paths, or child workers were used by the producer.
After all three final delta reviews returned CLEAN, Luna ran the sole contracted
targeted yu-hir command once. It passed: 1 passed, 0 failed, 134 filtered out.
The command output and exit status are recorded in the R123 closeout.

The initial append accidentally omitted the prior test’s final retained-position
assertion and contained an extra leading plus before the new test. Luna restored
the assertion and removed the plus, preserving all pre-existing test bytes. This
repair and handoff reconciliation use the existing closeout allowance only; no
implementation cap is renewed. No tests/builds were run.

Test SHA-256 after the first Luna retained-index repair: `ca2d37da14fccbb04cae64e1086008470043ea177b05416fa1ff406dffd20fa4` (superseded by the ancestry repair below). Final test SHA-256: `e7a332e65d7c4e7f252e8d04cc57b1d0d5fa3fd416c16a8522c6880b834840a1`. The final handoff hash is recorded in current state. Producer model requested Luna/high,
observed UNKNOWN/UNKNOWN. The producer did not measure elapsed time; Luna
conservatively charges the full 300-second implementation cap. The original
worker stopped with its partial output before the primary repair.

After the three final reviewers independently identified missing retained-index
assertions, Luna added the source-key to PositionId checks above, including
distinct formal/body retained IDs and member ancestry for binders. This primary
repair is within the existing closeout allowance; no tests/builds were run.

The compiler/source reviewer then noted that relevant descendant parent chains
needed explicit checks too. Luna added retained ancestry checks for selected's
annotation and explicit row, the selected formal identifier, and body
identifier, along with BindingBody under its member. This second repair also
uses only the existing closeout allowance; no tests/builds were run.
