# Sprint R138 — helper cut ledger and qualifying transport suffix

Status: CANDIDATE until Luna validates live runtime, pins and exact grants.
Branch / baseline: `research/simple-sub-intrusion` / `66c7b52b197aa035d6feaf20ff4f84198a92f9cb`.
Contract revision: 1. Primary and sole Git integrator: Luna.

## Original outcome and success evidence

Parent remains the unchanged computation-forwarding preservation theorem in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7:
one shared satisfying assignment, original current-formal identities and Name
arguments, arbitrary finite prefixes, repeated calls, simultaneous receiving
entries, and independent foreign-continuation obligations. Full inference and
evaluator correspondence and Simple-sub A/B remain OPEN 0→0; R50 remains NOT
ADOPTED. No source domain, quantifier, accepted behavior, or semantic authority
changes.

Fixed source is the exact ordinary-mode R72/R73 specimen:

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

Continue the exact open `R73-CUT-LEDGER-1` toward the original R72 A/B/C
outcome. First construct an event-sourced, ordered ledger from source admission
through helper Local capture/restoration and then continue through both loop
Lambda demand replays, boundary-1 Local and any later production `Work::Bound`
with its independently licensed consumer/provider. Each ledger event names its
actual constructor, predecessor state, and resulting physical/canonical storage
changes. Preserve source-action order; FIFO queues, saved indices and vector
orders where applicable; distinguish sets where code defines no order. Include
physical multiplicity, raw/canonical keys, RelationIds, dependencies, witness
lineage, representatives/levels, fibers/evidence, memo/rewrite/group keys,
generations, source sets, pending parents, replay heads/cursors and completion.
FreshUse transport and physical FreshUse admission are distinct events.

Success is exactly one of:

- **A:** derive the authentic later occurrence with exact physical owner/slot,
  raw and canonical keys, producer/provider, all aliases and same-class slots,
  ordered event history, merge parents, fibers/dependencies/witnesses, and an
  independently justified source consumer/provider including residual or
  discharge correspondence;
- **B:** derive the fixed source's earliest authentic constructor rejection and
  its owning premise;
- **C:** prove complete relevant schedule/cut coverage through the suffix and
  show this fixed source does not produce the requested third-owner/merge/
  production-copy/consumer pattern. C is case-specific only.

Any missing ledger entry, unproved queue/memo coverage, absent independent
consumer, or budget exhaustion is **UNFINISHED/OPEN**, never B or C. Endpoint
equality, row levels, manual alias schedules, or the incomplete R73 cut do not
complete this target. Do not repeat the earlier level projection as a method.

## Reused evidence, provenance and authority

R73 is frozen but **UNREVIEWED/UNFINISHED**, not a theorem or activation of
source claims. Its reported Astra runtime overrun (302 seconds against 300)
remains disclosed; it grants no carryover. Revalidate every reused source claim
against current pinned owners and preserve authorship. In particular, recheck
the helper provider `Int−` argument, separate FreshUse transport/admission,
`by_output[(TypedPairKey, ExtrusionEndpoint)]`, and the identity-context
characterization. Matching hashes establish bytes only. Do not import the R73
partial cut as complete or close its review debt by Luna self-review.

The R73 contract at SHA-256
`25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f` contains
32 historical direct source pins. At the new baseline, 24 remain byte-identical
and eight core owners have changed since R73. The successor must not import
historical hashes as current evidence: rederive the affected claims against the
newly pinned bytes below, and stop if a changed owner invalidates a required
constructor premise. All 32 files matched these current bytes in both the
baseline Git tree and live worktree at candidate preparation.

Current baseline direct dependencies (SHA-256):

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb  tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e  notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
4b5f57b27d5bfbb0b3e4f7cfa86c03488f5d02f995c7f861dbe29e0d448edd3b  notes/progress/2026-10-19-r71-closeout.md
527b7ac19e446f964c234cf832db8daa0046d893d73d8078c007d7277d4c20d2  notes/theory/2026-10-19-r53-ordinary-mixed-capture.md
0ebbc5e0e0b1c85b3f89e9017d9759fc3c8cfec80aced22457ed2fdc5867b258  notes/theory/2026-10-19-r55-original-name-attack.md
d1aa7f1a1af5da50a78e012540e9c0f01878a3ec13bb43d2565f75ae279895a4  notes/progress/2026-10-19-r55-original-name-owners.md
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907  crates/yu-hir/src/module.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0  crates/yu-solver/src/candidate_value_graph.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
30cbf8b9a3ab11e9448d2ea5aa47ee40aa3d80d0ee2bceec1e1b1abb6b1393d3  crates/yu-solver/src/candidate_intrusion_tests.rs
d685b44e43a1bca796a0299b2b19117d562245788206ede229b879801f94f6b5  crates/yu-solver/tests/candidate_computation_source_plan.rs
d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442  crates/yu-hir/src/module/local_source.rs
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60  crates/yu-solver/src/term.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
7a5d49d2c5eb05f839020f89debedd440e9909658cdff676ef8be0b6e9f29883  tasks/agent-loop/sprints/third-owner-prefix-20261019-r72.md
504abc36cd877407b57b744484640c3fb2f8e12d09f08bfe90188dc700ee18a5  notes/theory/2026-10-19-r72-third-owner-prefix.md
8e30e80a5e382fe6e3a88a65933ac5eb787e5b7773bae72657f3eb2348668401  tasks/agent-loop/inbox/20261019-r72-proof.md
e6ab1ac3c2b02e668980bf5ccef94877505501a5b3465248e68866de58d4fb67  notes/progress/2026-10-19-r72-third-owner-prefix-owners.md
adff1dc79b175d6ccacf36b75abaf275eeb3a6fab7d4e9d51e747a267303813d  tasks/agent-loop/inbox/20261019-r72-implementation.md
```

The following R73 artifacts are direct frozen dependencies and must match both
baseline and live SHA-256 before work:

```text
25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f  tasks/agent-loop/sprints/helper-suffix-history-20261019-r73.md
38b46fa0ea2183ab5ebedb727979a8c343e1bdd0820c4941f22df4e503fda03d  notes/theory/2026-10-19-r73-helper-suffix-history.md
23903fa51053f8493017b1298037badd01793d57e235cfacde8334e795206bc6  tasks/agent-loop/inbox/20261019-r73-proof.md
a129236f5e1450ab5ec821f4e5e045594f466427f13998bc2101eac5be9b138a  notes/progress/2026-10-19-r73-suffix-consumer-owners.md
e66a229d4fef816b4e1e2ec4d091d4ed522af16ea276ea345aa1f96c302d07c9  notes/progress/2026-10-19-r73-suffix-counter-reading.md
a82e91d399694680a74d49861fa9b9602ce72e6d51f6b741e14bdc6a2570672c  tasks/agent-loop/inbox/20261019-r73-implementation.md
2df8ac0decc0a30f62b672f0aa93bb53aa290fefd8291affc4dca708f0119f6f  tasks/agent-loop/inbox/20261019-r73-research.md
```
R72/R70/R71 results remain conditional within their recorded premises. Keep
the original theorem, Simple-sub A/B, R70/R71 coverage, source/native and
production gates OPEN unless separately reviewed in their original scopes.

## Two lanes and exact leases

- Constructive proof owner: assigned Sol/high prover; ordered ledger, complete
  suffix attempt and parent application. Exact write leases:
  `notes/theory/2026-10-20-r138-helper-cut-ledger.md` and
  `tasks/agent-loop/inbox/20261020-r138-proof.md`.
- Luna source/native owner lane: independently map the actual source/native
  constructors and consumers, audit the ledger against at least two current
  owners (`candidate_scheme.rs` plus `candidate_extrusion.rs`, with
  `candidate_context.rs` / `candidate_intrusion.rs` where the event requires),
  and record whether a concrete approved-behavior violation supplies a safe
  implementation slice. Exact write leases:
  `notes/progress/2026-10-20-r138-cut-owner-map.md` and
  `tasks/agent-loop/inbox/20261020-r138-implementation.md`.
  No compiler, test, runtime, semantic, or expected-output edits are granted.
  If no specific violation is derived, record `NO_SAFE_CODE_SLICE`. A temporary
  observer or instrumentation is outside this contract and needs a new exact
  Luna decision/lease; do not add it implicitly.
- Independent review after both author lanes freeze: fresh compiler/source
  review of the complete event/source/native ledger and fresh spec/authority
  review of unchanged claims, quantifiers, provenance, outcome classification,
  and all R73 limitations. Neither author may certify their own contribution.

No worker starts a sprint team. No tests, builds, probes, parser/solver runs,
instrumentation, benchmarks, code/semantic changes, expected-output edits,
network, or nested CLI. Static source inspection and symbolic/event-sourced
derivation only.

## Resources, stop conditions and integration

Total cap 1,800 active seconds, reserved once: activation/preparation and pin
validation 240; proof 900; Luna source/native owner lane 240; paired fresh review
120 each; adjudication/closeout/integration 180. Zero Astra; at most one heavy
process (none planned). Do not inherit or refund any R73 grant or UNKNOWN time.
Preserve all existing UNKNOWN worker reservations and quarantined paths.

Stop on any dependency mismatch, unexpected source/authority requirement,
writer/lease conflict, newly necessary user decision, or cap boundary. Freeze
all four output artifacts before review. Only Luna adjudicates, updates
`tasks/agent-loop/current.json`, stages explicit paths, commits and pushes the
intended range non-forced. Preserve failures and open gates. Consult the
dispatcher again only at a genuine counterexample, material dependency or
authority change, integration seam, budget boundary, or sprint end.
