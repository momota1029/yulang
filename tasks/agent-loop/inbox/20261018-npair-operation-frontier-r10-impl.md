# r10 implementation handoff — choose source to native frontier

Sprint / contract revision and SHA-256: `npair-original-input-and-operation-frontier-20261018-r10`, revision 2, `6e828681713295da2a6f46ca005ac10c4a4af928cbfb129dae5ad67fce892f53`.

Assignment / handoff revision: `NP-OPFRONTIER-R10-IMPL`, revision 1.

Parent gate: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original fixed-c quantifiers, source domain, R/W/Z, `rho_u`, consumer, F1/FK1 and accepted semantics unchanged; **OPEN / closure 0**.

Baseline and direct dependencies: HEAD `1a541b80990d6eb3012900d5b4edb4ee1a2d19f0`; input receipt `tasks/agent-loop/inbox/20261018-npair-original-term-input-r10.md`, SHA-256 `f4ea6658d4f097b74b04af0479dc61659fd361a6099777eb5044ebae37223175`. All 14 contract manifest pins were rechecked at intake; the only changed dependency is the leased `candidate_effect.rs` implementation target. The original source characterization and omitted-row fixture hashes are recorded in the input receipt.

Role / worker / runtime: `implementer`, `/root/npair_operation_frontier_r10_impl`, current session. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN. No model substitution was made.

Exact leased paths and authors: `/root/npair_operation_frontier_r10_impl` authored only `crates/yu-solver/src/candidate_effect.rs` and this handoff. No descendants, scratch files or other paths were written.

Outcome class: **implementation / source-native probe instrumentation**, unexecuted and research-only.

## Source to native frontier contribution

Added one isolated test, `original_choose_operation_rendering_reaches_native_frontier`, using the contract's full new research rendering:

```text
act ctrl:
    our choose: () -> (([ctrl] ()) -> [ctrl] int)

my f0 = ctrl::choose ()
```

The test parses and lowers those bytes, finds the actual `SourceOperationDeclaration` for `ctrl::choose`, finds the resolved source occurrence under `f0`, and checks that the candidate-source schedule carries the same declaration identity and occurrence. It invokes `execute_candidate_source_root(&f0)`, the real owner path, rather than calling the operation constructor directly.

Static owner-path inspection identifies the first expected refusal in `candidate_operation`'s recursive signature construction: descending into the inner function reaches `candidate_signature_effect`; the concrete `[ctrl]` argument row is in negative variance and the existing `variance == Negative && !row.concrete.is_empty()` guard returns `IdentityExhausted`. Construction reaches neither operation slot 42 admission nor publication. The test records the returned error, source-frame clearing, view/contribution/conflict counts, effect-bound count, scratch bytes, and whether slot 42 entered the fact store. It asserts no partial view/bound/contribution/conflict/slot-42 residue after the refusal. This is static expected behavior only until the authorized runtime invocation occurs.

Parent/source/native correspondence: this establishes no historical-source identity, original `F_c`, complete `Sigma_choose.Lambda`, output license, consumer witness, or original source acceptance. The text is a separate research rendering, not the missing historical source/CST/HIR. A refusal in the candidate path does not refute the source judgment or parent theorem.

## Evidence and checks

Reused: r10 input receipt classification `INPUT_UNAVAILABLE`; the pinned choose mathematical signature and owner-path note; current `source_annotation`/`local_source` declaration-resolution path; current candidate signature constructor and concrete negative-row refusal; the existing omitted-row fixture only as syntax/history context.

Rejected: the existing `receive-choose.yu` rendering is not substituted because it omits the inner `[ctrl]` argument-effect row. No Simple-sub bypass was restored. No semantic rule, diagnostic, source domain, test expectation or production path was changed.

Checks: source/diff inspection only. No test, build, Cargo command, formatter or runtime was run under this lease. The fresh independent compiler review and the separate runtime sequence remain Luna-owned.

Resources: 360-second implementation cap; one isolated test and one handoff produced. Exact elapsed active time was not available to this worker; cap not intentionally extended. No runtime/build resource consumed.

Unresolved premises / owner TODO: Luna must obtain a fresh independent compiler review of the frozen test delta before running the exact compile-only and one-shot executable command in the contract. The original source/CST/HIR and complete semantic Operation package remain unavailable; resolving those is outside this implementation lease and does not follow from a green probe.

Frozen artifact: `crates/yu-solver/src/candidate_effect.rs` (SHA-256 to be supplied with freeze receipt); this file (SHA-256 to be supplied with freeze receipt). No other artifacts changed by this assignment.

Next related in-envelope step: freeze and independently review this exact test delta; if CLEAN, Luna may execute only the contract's compile-only command followed by the single direct invocation with complete capture. Stop on the first failure. Do not promote production behavior or close any original parent condition from this test.

Worker state: **STOPPED — writes stopped; no descendants or outstanding writes.**

Integration: pending independent review and Luna runtime/integration. Not commit-ready as production code.

## Revision 2 — Luna repair under r10 contract revision 3

Prior handoff revision 1 SHA-256: `30cc3ad9b5bfa3b0919e33ad3dad774585cd1901314d08f74b1711af3805284e`.
Contract revision 3 SHA-256: `9847b49f9cba87230e3f6686c9bc5fcdb9794faa6fa67d656a44921b05121368`.

The fresh compiler review of revision 1 was BLOCKING: the HIR Arc was moved while borrowed, the scheduled declaration pointer comparison used mismatched reference types, and an undifferentiated root error did not identify the failing scheduled action. Revision 1 remains preserved above as the prior frozen submission and is not represented as approved.

Luna repaired only the existing named test under the same source lease. It now retains the HIR Arc while collecting, compares declaration pointees with matching types, advances the real root source schedule through successful prior steps, and observes the exact scheduled `Action::Operation` (declaration identity and source occurrence) returning `IdentityExhausted` without advancing the schedule. A separate fresh session invokes `execute_candidate_source_root` and observes the real synchronous root rollback. Both paths compare effect views, contributions, conflicts, effect bounds, scratch bytes, facts, term-arena capacity/owner snapshot and slot-42 publication before and after. The inner negative-concrete-row guard remains a static source attribution; runtime records the Operation action boundary and returned error, not a test hook inside that guard.

Updated source SHA-256: `1372302dd224205646f4d39668ffedde9d9e23565d90d527b9be8f11fa5fbf88`.
No test, build, Cargo command, formatter or runtime was run during this repair. `git diff --check` passed. All prior fixture assertions and production source remain unchanged. The original source/HIR/package remains unavailable; parent OPEN / closure 0. Luna writes stopped at freeze. Fresh independent compiler review is required before the sole compile/runtime sequence.

## Revision 3 — successful-prefix-aware rollback observation

Prior handoff revision 2 SHA-256: `4bb964a25510c5c4a6377b16599689fdb254cb059cb27d61b433ab4ee9d30c5c`.
Contract revision 4 SHA-256: `e9b7bf0bf33f604b8110d891c336ea9a29efce9259a67cee01c80ba0821c67f9`.

The independent rev3 review found the root assertion had incorrectly compared post-error facts to the fresh session's empty initial store. Two collected effect facts are successfully admitted by earlier schedule actions; root source-frame cleanup does not roll back those facts. No semantic rollback defect was found. The rev3 review receipt remains a frozen BLOCKING historical review.

This revision records a full expected-state tuple from the trace session immediately before its observed `Action::Operation`: views, contributions, conflicts, effect bounds, scratch bytes, facts, and term-arena capacity/owner snapshot. The fresh root session reports its initial state and compares its post-error state against that successful-prefix tuple. Thus prior facts remain expected while no failed Operation residue is admitted. The root frame must be cleared and slot 42 must remain unpublished. This changes only the test observation/assertion and this handoff; no production or fixture changes.

Updated source SHA-256: `22a9e7a25f59638a24df746be9954ec711ca99f7c89802fa75808d7e07fdcca3`.
`git diff --check` passed. No Cargo, test, build, formatter or runtime was run during this targeted repair. Parent/source theorem remains OPEN / closure 0. Luna writes stopped at freeze; fresh independent compiler review is required before runtime.
