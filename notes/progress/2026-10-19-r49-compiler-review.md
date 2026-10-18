# R49 independent compiler review

Receipt revision: 2; corrected freeze against R49 contract revision 2.
Contract: `tasks/agent-loop/sprints/active-root-admission-20261019-r49.md`,
SHA-256 `aa0823710a5dae66eac151bf3da92ca21448328f4f115f90031b6abedb4f3679`.
Status: terminal bounded source review; **no outstanding BLOCKING, major or minor findings** in
the frozen proof and owner-map claims. The bounded result
**NO_SAFE_CODE_SLICE under R49** is supported.
Reviewer: `/root/r46_compiler_review`; sole author; no descendants.
Requested role: compiler_referee; effective observed model/effort UNKNOWN/UNKNOWN.

## Root cause, authority and first missing contract

I independently inspected the source protocol and the pinned authoritative
local-self-recursive-binding decision and approved answer. Producer explanations
and prior review outcomes are not correctness premises for this review.

The authoritative decision's Selected source behavior and Proposed
source-to-solver seam require the same open monomorphic initializer root for
active recursive references, including a nested helper reference to an active
outer binder. It expressly prohibits LocalScheme/capture/FreshUse before
installation. Its Required invariants retain later use-time capture and preserve
private-session discard after intrinsic source-action failure. The approved
q1/a1 answer selects this source behavior; it does not specify an active-Link
alternative to the scoped authenticator. The pinned local-use-retention
contract is Draft/unapplied and supplies no such authority.

The current source and scoped admission contracts do not compose for the exact
active recursive fixture. The first absent operational premise is the exact
callee Name occurrence's committed LocalFreshRoute at
`candidate_call.rs:727`, followed by the required installed scheme at `:731`.
The first missing compatibility contract is how an authentic active monomorphic
Link/root is admitted by this scoped consumer without pretending to be that
FreshUse route. This is structurally upstream of q's output formation and does
not depend on Desc, D_q, complete Call or an inferred final type.

R49 is read-only and creates no alternative admission protocol. Its stop result
therefore correctly identifies the source/consumer seam requiring a new primary
contract and applicable design approval. This is bounded to the inspected
scoped path and authorities. It is not a global impossibility theorem, rejection
of approved recursion, or a finding that a future implementation must change
language meaning. A future implementation proposal must determine whether its
consumer meaning changes and apply the corresponding approval boundary.

## Independently checked complete owner path

- `candidate_source.rs:1032–1041,1090–1124`: source-order work and deferred
  Install keep loop's active initializer endpoint available throughout the
  direct recursive Apply and helper initializer. `:1239–1253` emits Link for
  those exact Local identities and Local only after active lifetime ends.
- `candidate_source.rs:1292–1310,1316–1359`: scoped Apply retains the exact
  unannotated callee Name's expression/occurrence/local/slot in LocalCalleeRoute,
  joins the exact recipe/endpoints and schedules Candidate. This record does
  not retain an active-root admission certificate or Link receipt.
- `candidate_source.rs:1669–1678,1688`: Link admits its ordinary value constraint
  at slot 30; Candidate calls admission; Local alone enters use-time routing.
  Ordinary link provenance does not itself establish the missing consumer rule.
- `candidate_scheme.rs:1968–1983,2011–2042,2165–2183`: installation exposes the
  original root/boundary; later Local reconstruction requires that installed
  scheme, captures it, prepares FreshUse, restores bounds and links the image.
- `lib.rs:9292–9312` and `candidate_scheme.rs:662–691`: successful completed
  Local publication moves the exact frame/maps into a route and indexes its
  own occurrence. `lib.rs:9467–9490` restores retained continuation ownership
  and removes new routes/index entries on failure. These are current owner
  operations, not a new general rollback requirement.
- `shadow_apply.rs:1763–1775`: scoped authentication occurs before admitting
  the Apply relation/native ports. `candidate_call.rs:712–735` authenticates
  the exact HIR Name and local witness, then insists on its occurrence-indexed
  route, installed scheme and authentic use instance. No active-Link branch is
  present. Equal endpoints, a shared local ID or a sibling route cannot satisfy
  the exact occurrence lookup and subsequent route checks.

The scoped fixture at `candidate_scheme.rs:2663–2677` explicitly enables scoped
collection and then executes the session before selecting q or helper maps.
The direct active-root Apply precedes helper-use inspection and cannot pass
that mandatory guard. The nested q has the same mismatch. This is a static
control-flow conclusion; no fixture was executed. The non-scoped source test
at `candidate_local_self_recursion.rs:110–137` and schedule test at
`candidate_source.rs:1717–1754` express the intended monomorphic Links and later
FreshUse mode, but their declarations/assertions are not scoped success evidence.

The proof's falsifiers are discriminating: an authentic owner must either
supply the exact occurrence route without active-root freshening under existing
authority, or supply an already-approved active-Link admission judgment and
actual consumer path. A sibling route, synthetic certificate, changed schedule,
endpoint equality or unrelated successful query is insufficient. No such path
was found in the frozen owner trace. No producer claim silently substitutes
monomorphic linkage for installed generalized-use evidence.

## Scope and parent boundary

No additional compiler defect is asserted by this clean review of the R49
obstruction report. The previously blocked positive fixture remains blocked;
no test gate is opened. The audit covers the pinned recursive source case,
producer/consumer ownership and transaction lifetime, not all language forms,
all alternative authorities or global semantic nonexistence. No new source
restriction, runtime behavior, annotation rule, fixture substitution, expected
output, production or theorem status is adopted.

The original full inference/evaluator theorem and original Simple-sub A/B
remain **OPEN, 0 -> 0**, with their original quantifiers, source domain and
accepted semantics. R48 temporal transport remains conditional and unexecuted.
This review does not certify source typing, Desc/D_q, complete Call/effects,
frame/alias completeness, soundness, principality, evaluator or cutover.

## Exact SHA-256 bytes inspected

Correction to receipt revision 1: its statement that all contract pins matched was false.
The revision-1 contract printed approved-answer hash
`1c0ea94c359f08496185594848ab9082b4eac174ab247d67d37f316462db145b`,
but the actual bytes hash to
`1c0ea94c359f08496185595448ab9082b4eac174ab247d67d37f316462db145b`.
I failed to compare those strings correctly. The actual approved answer was read;
its source behavior and the independent source-path finding are unchanged.
The remaining source, authority and frozen producer artifact hashes match.
The primary preserved revision 1 in Git history and supplied revision 2 at the
canonical `tasks/agent-loop/sprints/active-root-admission-20261019-r49.md` path. I read that complete revision
and verified its SHA-256 as
`aa0823710a5dae66eac151bf3da92ca21448328f4f115f90031b6abedb4f3679`.
The corrected approved-answer pin matches the actual bytes. The revision-1
pin discrepancy is corrected; its blanket match claim is superseded. This is
a closed minor receipt/dependency-transcription issue, not a source-path change.
All six source/fixture hashes and the authoritative local-recursion design
were revalidated unchanged. Therefore the exact source-path finding and bounded
NO_SAFE_CODE_SLICE disposition remain valid under contract revision 2.
The producer artifacts remain frozen revision-1 submissions; their old contract
references and erroneous pin claims are not adopted as fresh verification.
No new budget was granted or requested for this compact correction.
Handoffs were checked for frozen artifact identity, not used as independent
source/authority evidence. Prior review files were hashed as dependencies;
their conclusions did not replace the source trace above.

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/active-root-admission-20261019-r49.md` | `aa0823710a5dae66eac151bf3da92ca21448328f4f115f90031b6abedb4f3679` |
| Historical contract revision 1 (preserved in Git history) | `6a8fa0a9f1189e247b6462b45083f814e0420ee53000f60b19d6d6ffcb3a57ff` |
| `notes/theory/2026-10-19-r49-active-root-admission.md` | `9c8352ac1e4e53c2e0559ef2fcd6e3db1ffcc49517b4456bb7cfbe49d7b06058` |
| `notes/progress/2026-10-19-r49-active-root-owner-map.md` | `6cb3926f0fad89d6a220c8d7cff75353fd38d7faf5df6bc2c8632651ebd2652b` |
| `tasks/agent-loop/inbox/20261019-r49-proof.md` | `4cce925bb5dbb5d72b57ba0fb7ac4ad8a204ce6dff39df2cefaaeaec344ec67d` |
| `tasks/agent-loop/inbox/20261019-r49-implementation.md` | `a388e5e67db39ec9fbff9fe03577c72610aaabcfd54ce009a4bed063842a2359` |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` |
| `questions/2026-10-10-local-recursive-binding-scope/approved-answer.md` | `1c0ea94c359f08496185595448ab9082b4eac174ab247d67d37f316462db145b` |
| `notes/progress/2026-10-19-r48-closeout.md` | `35de4c623562f01c636b3c5e463f0dd105fe996136fefdf39a5149d5825c7e98` |
| `notes/progress/2026-10-19-r48-compiler-review.md` | `b91fa227bd1a686ab08b9a5fa492fc69a2530ba4671f158fd5f1c0563b513fea` |
| `notes/progress/2026-10-19-r48-spec-review.md` | `4ec09e82ae00e13f47332178b64dde325c4c1baf8bdbc84db92e06dc0943d53c` |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/candidate_scheme.rs` | `d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55` |
| `notes/design/2026-10-17-local-use-retention-code-contract.md` | `1dd2bab703624a51d50dca95e35ffbddd117b940bf95aca6b9b610f7d0425c2a` |

Checks: read-only source/authority text inspection and SHA-256 recomputation.
No tests, build, Cargo, runtime probes, source/fixture/current-state edits, Git,
external contact, scratch paths or delegation. Only this receipt was written.
Review grant: 300 seconds; no extension. Total elapsed/CPU/RSS not measured.
Observed clocks: 2026-10-18 16:39:09 UTC and 16:39:41 UTC, covering only part
of the review. Baseline is parent-supplied; no Git verification performed.

**WRITES_STOPPED; NO_DESCENDANTS**.
