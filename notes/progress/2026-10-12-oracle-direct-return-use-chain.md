# Oracle direct return: source-to-observation chain

Date: 2026-10-12
Status: frozen, unreviewed source correspondence; no counterexample or theorem closure
Claim class: source-derived construction facts and an exact missing artifact premise
Assigned Y3 baseline: `de3f00e3219c379bc47cb87fa59411a922744c1b`
Oracle HEAD: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Lease: this note only

## Authority and fixed discriminator

The [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–2 permits subtraction within the receiving function at a composed-negative
concrete annotation. The [contextual design](../design/2026-10-10-contextual-attachment-admission-design.md)
§§1,3–4 retains occurrence/scope and actual instance identity; equal families
do not grant unrelated cancellation. The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 govern inference and abnormal paths. No selected meaning changes.

The [recorded probe](2026-10-11-oracle-callback-reuse-projection-probe.md) includes:

```yulang
pub act tick:
    pub ping: () -> ()
my direct(cb: (() -> [tick] ())) = cb
my provider() = tick::ping()
my observed_direct() = (direct provider) ()
```

Its larger source prints `provider: () -> [tick] ()`,
`direct: (() -> [tick; 'a] ()) -> () -> ['a#0[tick]] ()`, and
`observed_direct: () -> ()`. The separate direct-call control retains `[tick]`.
This extracted smaller source has not been run alone. Display `#0` is not a
raw identifier. The [previous policy audit](2026-10-11-oracle-callback-reuse-policy-falsification.md)
remains frozen.

## Established source chain

Paths in this section are relative to `/tmp/yulang2-oracle-read`.

| Stage | Exact source evidence | What follows, and limit |
| --- | --- | --- |
| Local callback formation | `lowering/pattern.rs:242–280` creates `Def::Arg` and a `LocalBinding` with `scheme: None`. | The parameter is a shared local slot, not a generalized local scheme. |
| Return `cb` | `lowering/name_ref.rs:145–173` resolves the reference to `local.def` and obtains `instantiate_local_value`; `lowering/expr/tail.rs:855–858` returns `local.value` when there is no local scheme. | The returned expression retains this callback DefId and value coordinate. This is compiler identity evidence, not runtime execution. |
| Annotation evidence | `annotation/constraints.rs:363–389,424–470` constructs the callback Function ports, its effect PUSH/filtered view and output predicate; nested Function result Value is wrapped with `NonSubtract`. | An annotation-derived effect view is genuinely present. Its concrete raw row/ID records for the run are absent. |
| Direct's output | `lowering/expr/lambda.rs:1571–1578` gives a Function parameter an empty parameter-output predicate. `tail.rs:1058–1072,1084–1111` combines frame predicates and emits bare Value/Effect variables if the predicate is empty. | Merely returning this Function parameter does not add its call predicate to the enclosing output. The source has no callback call to extend the latent predicate. Nested annotation evidence still exists inside the returned callable. |
| Stored top-level scheme | `analysis/session/instantiate.rs:14–83` generalizes component roots, captures witnesses, finalizes with ancestors and calls `set_def_scheme`; `session/generalize.rs:958–964` stores it in `Def::Let`. `generalize/finalize.rs:3–25` preserves root stack quantifiers and allocates a scheme predicate from compact data. | Identifies the real stored-scheme owner. The actual compact root, quantified IDs, ancestors and stored predicate for `direct` cannot be recovered from its short printed string. |
| Use of stored scheme | `analysis/session/instantiate.rs:341–395,448–520` reads the target's stored scheme and imports its predicate/provenance into the use value. `instantiate.rs:620–648,770–786` freshens stack quantifiers consistently and adds a root POP with count `u32::MAX` for each quantified ID. | This is an actual possible effect-observation operation, not permission supplied by the local policy. Whether the relevant annotation ID occurs among `direct`'s actual quantifiers remains missing. |
| Later invocation | `tail.rs:844–850` recognizes only an `Expr::Var` as a local callee. `make_app_with_origins` builds `Expr::App` at 626. Thus the second callee, `(direct provider)`, is not a local-variable callee. At 690–705 and 740–749 it receives no local call predicate or special unannotated-callback wrapper. At 543–563,615–624 it gets a fresh ordinary call-effect demand and forwards both its callee evaluation Effect and returned call Effect into the application Effect. | A new local callback projection at this second call cannot explain purity. It does not prove that a concrete `tick` lower reaches that call-effect variable. |
| Observation | `poly/src/dump/surface.rs:139–172` reads the stored Let scheme and calls `format_scheme`; `type_format/formatter.rs:64–65,90–93` renders its predicate, and Function rendering around 488 uses its result-effect row. | The printer observes a stored scheme. Exact CLI dispatch and completeness of compaction/row rendering for this run remain unverified. |

Oracle's `web/docs/reference/effects.md:250–255` restricts argument capture to
handlers inside the receiving function; 273–278 requires caller propagation
unless a visible handler consumes the effect. Neither the source nor these
clauses introduces a handler at the later root. Thus, conditional on actual
returned-provider behavior and a complete final effect observation, the later
invocation must retain `tick`. The compiler's callback identity construction is
now source-backed; preservation of operation behavior across this stored scheme
and its use has not been established.

## First missing premise and successor boundary

The first decisive missing artifact is **the actual generalized `direct`
scheme and its correlated return-effect/stack records**. Needed fields are its
stored predicate, compact return-effect row, raw annotation SubtractId, stack
quantifiers and the concrete provider lower/instantiation records linking them
to the second call. The source specifies constructors and consumers; it does
not supply those run-specific objects. Without them, asserting that the root
POP removed `tick`, that compaction alone removed it, or that an independent
provider contribution reached the output would assume the central bridge.

Current Y3 does not supply a replacement witness: `candidate_source.rs:98–120`
starts formal preflight negative and requires negative explicit effect rows to
contain no concrete atoms and exactly one symbolic variable. The callback
result retains that negative polarity, so `[tick]` fails this guard.
`candidate_effect.rs:1054–1071` likewise accepts explicit concrete formal rows
only in positive variance; the formal constructor starts negative at 1090.
`yu-hir` retains parameter annotations, but this exact negative concrete source
cannot enter the candidate consumer. This is the current admission boundary,
not a selected language restriction or evidence that Oracle's output is valid.

H retains every original quantifier in the [original statement](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md#1-objective-authority-and-frozen-original-statement).
No actual counterexample is established. Soundness, intrusion, full effect
hygiene and F5 remain OPEN. The next owner is the primary's source/constructive
lane: obtain or account for the named stored-scheme and instantiation records,
then trace concrete output/compaction. More syntax variants do not discharge
this missing premise. This handoff does not authorize a new Oracle execution.

## Snapshot, checks and limits

Ten lightweight static-read commands used `cat`, `sed`, `rg`, `head`,
`sha256sum`, and read-only Git revision/diff inspection. Zero Oracle processes,
builds, tests, mutations, numeric searches, samples or child agents. Some
aggregate output was truncated; guessed `call.rs`, `var.rs`, `candidate_annotation.rs`
and dump-module paths were absent. Conclusions use the located owners above.
No independent executable oracle exists: documentation and compiler share
project assumptions, and the previous dump supplies observations only.

HEAD moved concurrently from the assigned baseline to
`8c63f03adfbbe94c10b7f538807c485caf119831`. Targeted diff against the assigned
baseline was empty for the three governing notes, both prior notes and the
three Y3 dependencies below. Targeted Oracle diffs against its HEAD were empty
for the hashed owner files. No dependency was edited by this worker. Commands
each returned in about 0.1 s; peak memory, total task wall time and effective
runtime model/effort were not measured or supplied. Artifact checks and fresh
independent review are deferred to the primary.

SHA-256 snapshot (Oracle paths relative to `/tmp/yulang2-oracle-read`):

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/progress/2026-10-11-oracle-callback-reuse-projection-probe.md` | `975c2f7460ca5a9663938485cc2ce8669160b864c19928151589c9904016ccd2` |
| `notes/progress/2026-10-11-oracle-callback-reuse-policy-falsification.md` | `04871010ce820d80f6295d79adb31691dcb6de31a2e45d99651171abc127abfe` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| Oracle `web/docs/reference/effects.md` | `18ccbebf2ae25cd977e4faab181c47a8c53719fa2f82a2cc30469dbbbe4a44a1` |
| Oracle `crates/infer/src/lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| Oracle `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| Oracle `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| Oracle `crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |
| Oracle `crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| Oracle `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| Oracle `crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| Oracle `crates/poly/src/dump/surface.rs` | `4d0d8f4b0c8c1cee3ab44cbb58486cccfe7fa4a88ff09a23b3401990e89f76e4` |
| Oracle `crates/poly/src/dump/type_format.rs` | `49800841ea8059b007076b8018076baa91ae275c76f3f07eb24a57341fe35bd7` |
| Oracle `crates/poly/src/dump/type_format/formatter.rs` | `10ef65e06243dff901d83e37bde22b99065c05dc92a31872fb8179397c3c2265` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-12-oracle-direct-return-use-chain.md`; frozen, writes stopped at submission.
- Baseline: `de3f00e3219c379bc47cb87fa59411a922744c1b`; relevant Y3 dependencies unchanged through observed HEAD `8c63f03adfbbe94c10b7f538807c485caf119831`.
- Dependency hash changes: none observed in the rechecked dependency scope; hashes recorded above. No prior hash was supplied for every newly read owner.
- Status: unreviewed static source bridge with missing run records; no theorem, counterexample, independent review or production promotion.
- Checks: ten static source commands, exact dependency hashes, targeted baseline diffs; no builds/tests/Oracle run or artifact checks.
- Proposed checkpoint message: `research: trace Oracle direct callback return and use owners`.
- Shared deltas left for primary/curator: record the ordinary second-call route, shared callback identity and exact stored-scheme premise; retain H, soundness, intrusion and F5 OPEN; record Y3's current negative-concrete formal admission boundary without promoting it to semantics.
