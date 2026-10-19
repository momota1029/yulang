# Sprint R74 — observe and prove the fixed source's C1 state

Status: CANDIDATE; Luna activation receipt follows this contract.  
Branch / baseline: `research/simple-sub-intrusion` / `d21c8eb3a87e43dd441474c9f138e71b1d8372ff` (clean, pushed).  
User goal: implement Yulang type inference and evaluator with proofs; Luna is primary owner and sole Git integrator.  
Authority: this user's explicit implementation request; top-level inference principles §§1–5. No language-rule or production-semantic change is selected.

## Original outcome and fixed scope

Original parent: computation-forwarding preservation §§1, 6–7, unchanged quantifiers/source domain; full inference/evaluator and Simple-sub A/B remain OPEN 0→0; R50 NOT_ADOPTED. R74 does not close any of these parents.

Fixed ordinary source is the R72/R73 source, exactly:

```yu
act io:
    our tick: int -> int

my outer (q:[io] int) = {
    my loop (x:[io] int) = {
        my direct = loop x
        my helper (y:[io] int) = loop y
        helper x
    }
    loop q
}
```

Observe C1 immediately after `route_candidate_local_run` captures the helper graph, prepares `FreshUse`, and pushes `LocalUse`, before the first `step_candidate_local_use`. At that point require exactly the fixed occurrence/slot and cursor `(next_bound=0, restoration=None, complete=false)`. The observer resolves the helper through existing HIR occurrence/local identities; it must not inject a pause, add solver work, intern or canonicalize solver values, change ordering, mutate maps/queues, or alter production behavior. All observer code is test-only.

## Success evidence and falsifiers

Success: an ordinary-mode bounded execution reaches this C1 hook exactly once; one ledger includes exact physical multiplicities and raw/canonical identities, graph bounds/evidence, relevant typed memo entries and rewrites, activated groups and `by_output` keys, source sets, generations, pending parents, and replay ownership, each with constructor-owned provenance. A separate proof derives observation erasure/fidelity against the unobserved transition. Frozen code, ledger, execution receipt and fresh independent compiler/spec reviews must agree.

This is observed C1 evidence only. It does not establish complete suffix coverage, a later production `Work::Bound`, consumer/provider lineage, source/native evaluator correspondence, soundness, principality, termination, production cutover, or parent closure.

Falsifiers/stops: source rejects before C1; hook or helper identity is ambiguous; any requested field lacks an owner/provenance; observer changes solver control/ordering/identity; execution exceeds 180 seconds; allocation/resource limits prevent a complete ledger; or either independent review finds a blocking/major fidelity defect. Record the first actual obstruction and leave all parents OPEN. No fixture combination, forged rows, injected pause, changed expected output, semantic test-name changes, or solver repair is allowed in this packet.

## Lanes and exact leases

- Luna primary implementation / source-owner map / integration, 900 seconds total, including at most one 180-second focused test execution. Code leases: `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/candidate_intrusion.rs`, `crates/yu-solver/src/lib.rs`, new `crates/yu-solver/src/candidate_c1_observer_tests.rs`. Writes only under `#[cfg(test)]` and the new test module. Luna alone updates current state and Git.
- Sol/high constructive proof, 600 seconds: `notes/theory/2026-10-19-r74-c1-observer-fidelity.md` and `tasks/agent-loop/inbox/20261019-r74-proof.md`. Derive a read-only projection and erasure/fidelity argument from the exact constructor path; inspect the frozen implementation after Luna's handoff only as a producer claim, not self-certification.
- Luna evidence artifacts: `notes/progress/2026-10-19-r74-c1-observer.md`, `notes/progress/2026-10-19-r74-c1-ledger.txt`, `tasks/agent-loop/inbox/20261019-r74-implementation.md`.
- After every author stops and snapshots freeze, fresh compiler/source review (300 seconds) and separate spec/conformance review (300 seconds). Luna adjudication/integration (300 seconds). Total charged envelope 2,400 seconds; Astra 0; no carryover or extensions.
- No extra descendants, probes, builds, tests, commands or output paths. One verification owner; the single bounded execution is the ordinary fixed-source observer test. Runtime model/effort absent from receipts remains UNKNOWN.

## Dependencies and baseline

All paths below are direct pins; baseline Git blobs equal live bytes at activation on the clean commit above:

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5  notes/theory/2026-10-19-r72-third-owner-prefix.md
38b46fa0ea2183ab5ebedb727979a8c343e1bdd0820c4941f22df4e503fda03d  notes/theory/2026-10-19-r73-helper-suffix-history.md
a129236f5e1450ab5ec821f4e5e045594f466427f13998bc2101eac5be9b138a  notes/progress/2026-10-19-r73-suffix-consumer-owners.md
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
d4ff8a9e98eb667a5eb85aff9c0feec1f0227e86257bb56892493ac1d04a9278  crates/yu-solver/src/candidate_scheme.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca  crates/yu-solver/src/candidate_context.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c  crates/yu-solver/Cargo.toml
d61446115ce45d7010898090bce323fe1134b1cca53471ac9416e441d45865d9  Cargo.toml
7a5d49d2c5eb05f839020f89debedd440e9909658cdff676ef8be0b6e9f29883  tasks/agent-loop/sprints/third-owner-prefix-20261019-r72.md
25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f  tasks/agent-loop/sprints/helper-suffix-history-20261019-r73.md
```

R73 is explicitly incomplete with partial corrected-map review coverage; the owner-map compiler delta resolved its major finding, corrected-map spec delta remains unreviewed. R73 overrun and unknown Luna elapsed remain charged historical resource facts. R72/R73 artifacts are conditional evidence only. This sprint changes no open question bundle and does not claim R50 adoption.

## Review, stop, and integration boundary

Freeze the exact code and all five artifacts before review. Reviewers must check observer erasure/control flow, complete field/provenance coverage, exact C1 identity, conformance to top-level principles, unchanged expectations and no implied source/suffix theorem. Only Luna adjudicates; repairs within the exact leases invalidate reviews of changed bytes. If no blocking/major findings remain, Luna may commit/push the explicit reviewed artifact set. Only Luna stages, commits and pushes; no force-push or broad cleanup. Update compact state, record actual runtime/stop evidence, and consult the selector at this sprint's close or any material obstacle/authority/dependency/lease change.

```text
Sprint SHA-256: assigned by Luna after freeze.
Activation receipt: assigned by Luna only after direct pins and current runtime reconciliation.
```
