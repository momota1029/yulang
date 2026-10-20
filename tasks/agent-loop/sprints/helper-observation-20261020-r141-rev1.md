# Sprint R141 — fixed-source helper and replay observation

Status: CANDIDATE; no source writes authorized until fresh prospective spec and
compiler/source reviews are CLEAN and Luna validates the live session and pins.
Branch / baseline: `research/simple-sub-intrusion` / `94a34c4113cb4e5a0de3d0e4b88ffe3c785d9fd4`.
Revision: 1. Luna is primary, sole code author, review adjudicator and Git integrator.

## Original parent and bounded outcome

Continue the unchanged computation-forwarding preservation theorem in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7,
through its exact ordinary-mode R72/R73 source and the helper Local/action25
boundary followed by both action31 loop-Lambda replay families. Preserve one
shared satisfying assignment, original current-formal identities and whole
Name arguments, arbitrary finite prefixes, repeated calls, simultaneous
receiving entries and independent foreign-continuation obligations. Simple-sub
A/B, source/native correspondence, inference/evaluator correspondence and
production gates remain OPEN. No source domain or accepted semantics changes.

The sprint's measurable evidence is a test-only, bounded, read-only snapshot of
the actual fixed-source solver execution that identifies (1) the complete
native state at completed helper Local/action25, including the capture and
restoration boundaries needed to interpret it; (2) actual ordered pops and
replay ancestry for each of the direct and helper action31 families; and (3) a
constructive mapping from the fixed source occurrences to those native records.
Apply each observed fact to the original parent and name the exact remaining
premise. Any missing boundary, incomplete event history, overflow, ambiguous
lineage or uncovered state yields **UNFINISHED/OPEN**. Numeric equality, final
endpoint equality or a test-only observed fact is not theorem closure.

The exact source is R138's unchanged specimen:

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

Action labels 25 and 31 are the frozen source-action labels in the reviewed
R138/R140 ledger, not a new runtime counter or guessed vector index. The test
must identify their actual native boundaries by source occurrence and
constructor lineage. The two action31 families remain distinct even if a
numeric relation or endpoint is equal.

## Baseline and dependencies

The complete 39 path/hash pairs from R138's two dependency manifests are copied
verbatim into the final section below. Before activation and before output
freeze, verify every pair against both this baseline Git tree and the live file.
All 39 pairs were checked against current `HEAD` and live bytes during candidate
preparation; the review must independently validate that this agrees with the
embedded list. A mismatch requires a sequential contract revision before any
source write. The explicit R140 action31 constructor/consumer owners are among
these pins; the fixed R140 and R138 proof artifacts retain their own pinned
hashes as members of the same list.

## Exact leases and method

Luna owns all implementation and constructive source mapping, serially, under
these exact code write paths only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/term.rs`
- new `crates/yu-solver/src/r141_observer.rs`

Exact artifacts:

- `tasks/agent-loop/sprints/helper-observation-20261020-r141-rev1.md` (Luna; frozen contract)
- `notes/progress/2026-10-20-r141-helper-observation.txt` (Luna; closeout)
- `notes/theory/2026-10-20-r141-helper-observation.md` (Luna; source mapping and parent application)
- `tasks/agent-loop/inbox/20261020-r141-implementation.md` (Luna; implementation handoff)
- `tasks/agent-loop/inbox/20261020-r141-proof.md` (Luna; constructive mapping handoff)

No additional write path, worker, descendant, scratch file, compiler semantic
change, expected-output change or production API change is authorized. Reuse
existing test-only accessors where they expose the exact fact; do not repurpose
`incoming_sample_trace` as a semantic trace. The observer must be behind
`#[cfg(test)]`, store bounded records, expose read-only snapshots and preserve
ordered events, relation identity, raw/canonical key distinctions, fiber and
replay ancestry, source occurrence, queue pop, lifecycle/currentness,
acknowledgement, global sweep, and allocator/interner dependencies whenever
they affect the observed boundary. Any limit hit marks the entire trace
incomplete and fails closed; silent truncation is forbidden.

The observer may not create semantic terms, canonicalize or intern extra terms,
add constraints, alter provenance edges, affect queue order, change solver
scheduling, or suppress work. Observe at existing mutation/dispatch boundaries
using only already-produced identities and data. Paired observed/unobserved
outcomes are supporting evidence only; they do not alone prove noninterference.
If a read-only observation cannot establish its own lack of semantic effect,
stop and leave the obligation OPEN. Luna owns removal/rollback of all temporary
observer code on the exact leased code paths before closeout unless independent
review authorizes retaining a test-only regression observer within this same
contract.

## Review, verification and resources

Two fresh prospective reviews of this frozen contract are required before code
edits: one spec/authority review and one compiler/source review. Both must be
CLEAN for the exact bytes and pins. Fresh independent final reviewers inspect
the frozen observer, boundedness and fail-closed behavior, source-occurrence
mapping, actual records, noninterference argument and parent application.
Neither reviewer may be an author. Review accepts only this finite evidence
slice; it does not certify R72/R73, Simple-sub A/B or production.

One heavy command, run once after code and notes freeze:

```text
timeout 240s cargo test -q -p yu-solver --features shadow-apply-candidate --lib r141_observer::tests::fixed_source_action25_action31 -- --exact --nocapture --test-threads=1
```

The test's exact module/name, stable summary fields and output capture must be
frozen in the implementation handoff before running it. No retry after failure.
No other heavy test/build process. Lightweight source inspection and hash
validation are allowed. Cap: 1,800 active seconds total, allocated once:
preparation and pin validation 120; prospective reviews 120; implementation
540; constructive mapping and theory 360; final reviews 300; exact test 240;
adjudication and closeout 120. Zero Astra. Unknown legacy writers and the
quarantined board and held R104 lease remain reserved; this sprint starts no
producer child and uses two review slots only after the candidate contract is
frozen.

## Falsifiers, stops and preserved gates

Falsifiers: an observation changes semantic state or scheduling; action25 or
action31 is attributed to the wrong source occurrence; a saved-prefix product,
actual pop, replay parent, lifecycle/currentness event, acknowledgement or
global sweep is omitted; equal numeric identities replace lineage; an overflow
or incomplete capture is reported complete; the fixed-source test does not
reproduce both families.

Stop on source/dependency drift, unavailable lease, newly required semantic
decision, observer-induced semantic effect, incomplete trace, failed exact test,
review finding not repaired within this envelope, or budget exhaustion. A
failed/incomplete outcome is UNFINISHED/OPEN. R135's pending compatibility
decision remains pending; R141 cannot authorize more unchanged Y2 examples or a
language change. No inference, evaluator, theorem, source/native, adoption or
production gate closes from this instrumentation.

Only Luna updates current state, records closeout, stages explicit leased paths,
commits and pushes the intended range. Git requires no user permission. The
next dispatcher consultation is sprint end, a material counterexample, authority
or dependency change, integration seam or budget boundary.

## Frozen dependency manifest (baseline and live SHA-256)

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
25b360d23fee6ee41482486facaaa602db8008fafdb0b4e5d94f594e43bf772f  tasks/agent-loop/sprints/helper-suffix-history-20261019-r73.md
38b46fa0ea2183ab5ebedb727979a8c343e1bdd0820c4941f22df4e503fda03d  notes/theory/2026-10-19-r73-helper-suffix-history.md
23903fa51053f8493017b1298037badd01793d57e235cfacde8334e795206bc6  tasks/agent-loop/inbox/20261019-r73-proof.md
a129236f5e1450ab5ec821f4e5e045594f466427f13998bc2101eac5be9b138a  notes/progress/2026-10-19-r73-suffix-consumer-owners.md
e66a229d4fef816b4e1e2ec4d091d4ed522af16ea276ea345aa1f96c302d07c9  notes/progress/2026-10-19-r73-suffix-counter-reading.md
a82e91d399694680a74d49861fa9b9602ce72e6d51f6b741e14bdc6a2570672c  tasks/agent-loop/inbox/20261019-r73-implementation.md
2df8ac0decc0a30f62b672f0aa93bb53aa290fefd8291affc4dca708f0119f6f  tasks/agent-loop/inbox/20261019-r73-research.md
```
