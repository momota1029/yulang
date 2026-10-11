# Negative formal effect row: current-source falsification audit

Date: 2026-10-11
Status: unreviewed research evidence; frozen at handoff
Claim class: bounded static source correspondence/falsification; no theorem or gate closure
Baseline: `cfab95a2cb64be8f8a58f8e69abee22390042135` on `research/simple-sub-intrusion`
Exclusive lease: this note only
Budget: 30 minutes; source reads and hashes only; no builds, tests, Oracle runs or delegation

## Objective and premises

Test whether the minimal Oracle-qualified negative formal row now has a live
candidate constructor and subtraction consumer. Authority is
[annotation effect hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. The selected language meaning remains composed-negative concrete
subtraction at the owning function-local position, and composed-positive
allowance. Concrete identity is resolved; symbolic variables stay connected.
The user-retracted callback output and expansive `my ans: [E] int` are excluded.

Hypotheses for the static conclusions: the dependencies below retain these
hashes; HIR formation receives the complete resolved annotation tree described
below; the private candidate entry is `CandidateInference::solve`. Parser
admission of an exact byte string, executable candidate output, public/default
inference and correctness of hypothetical enabled transitions are not assumed.

The prior [Oracle-qualified audit](2026-10-11-negative-formal-effect-source-audit.md),
now marked independently reviewed bounded Oracle/source observation by the
primary, supplies the already executed discriminator:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> [tick] ())) = cb ()
```

At supplied Oracle revision `a58eefc31e22141574b6f20c6a5748151c6d79f1`, its
recorded dump contains `my d2:f: (() -> [tick] ()) -> ()`, exit 0, empty stderr.
The exact source hash, full output, binary hash, command and run metrics remain
in that audit. They were not regenerated here. The dump records no `tick` row
after f's outer arrow; it does not establish absence from every internal solver
variable or runtime effect removal. Yulang3's structural spelling uses `act`,
`our` and `my f (cb:(() -> [tick] ())) = cb ()`; no Yulang3 parsing run occurred.

## Result and smallest falsifier

The source form is representable by the current resolved HIR carrier. It is
**not admitted by the private candidate inference entry**. The selected negative
result row still has no live candidate PUSH/POP subtraction consumer.

The one-Function, one-formal, one-concrete-row, one-call witness above falsifies
the premise “current candidate formal construction and ordinary Apply already
supply the negative annotation subtraction transition.” This is a static
source-qualified rejection witness, not a newly executed candidate mismatch or
a refutation of the selected policy. Removing the concrete row removes this
specific rejection predicate; removing the call removes the required call-local
consumer discriminator. No deletion mutation was executed and no globally
shortest textual program is claimed.

The old/current comparison is decisive: `source_annotation.rs`,
`local_source.rs`, `candidate_source.rs`, `candidate_effect.rs` and
`candidate_context.rs` all match the old audit's SHA-256 values exactly.
The scoped Git comparison from old baseline
`e899d1acd0f40b3b29b9f651f6cb658be316fbc1` to this baseline changes only
`shadow_apply.rs` among the named owners plus Function/replay dependencies.
That delta adds a graph-export conflict guard and two value-conflict tests;
it adds no annotation construction or subtraction transition.

## Exact source occurrence, identity and composed polarity

1. `crates/yu-hir/src/module/local_source.rs:289–305` retains cb's original
   annotation on `LocalSourceParameter`, its admitted source key and lexical
   scope, then binds its spelling to the exact `HirParameterId`.
2. `source_annotation.rs:367–375` retains f's `DefinitionRootId`, the annotation
   node's `SourceNodeKey` and parsed type. `399–500` represents the grouped Unit
   argument and Function result separately; the result has Unit value and the
   explicit row. This row's own key is retained at `509–516`.
3. `source_annotation.rs:183–202` creates the effect declaration identity as
   `(module, declaration SourceNodeKey)`. `538–551` looks up `tick` in the effect
   namespace, requires exactly one declaration and stores that resolved
   `SourceEffectId`. The singleton row is one resolved concrete member, zero
   symbolic variables. No numeric key ordinal or module identity was obtained
   by execution here; the exact structural owners are identified, not guessed.
4. `candidate_source.rs:98,117–120` starts the formal at `positive=false`, flips
   the Function argument, and preserves the result. Thus cb's result `[tick]`
   remains composed-negative. Its negative predicate is
   `row.concrete.is_empty() && row.variables.len() == 1`; both conjuncts fail
   for this singleton closed concrete row. `shadow_apply.rs:89–93` calls this
   preflight before collecting/solving it and returns `CandidateError::Unsupported`.

This is structural representability under resolved input, not executable
admission of the literal Oracle syntax in Yulang3.

## Actual pairing and real body-call provider

On admitted trees, `candidate_source.rs:276–283,663` schedules
`FormalAnnotation` before the lambda body and invokes the paired owner.
`candidate_effect.rs:1090` starts `candidate_formal_pair` at Negative;
`1035` independently rejects the same negative concrete row. Function recursion
at `1045–1052` reverses arguments and preserves results. Consequently removing
preflight alone would still fail before constructing the pair. The effect port
at `1054–1074` has omitted/shared rows, singleton symbolic rows and composed
positive Support/Allowance pairs; its remaining case rejects. The generic
signature effect owner also rejects negative concrete at `1507–1509`.

For admitted pairs, the positive Function uses `(an, qan, qrp, rp)` and negative
Function `(ap, qap, qrn, rn)` at `candidate_effect.rs:1052`. The owner adds
annotation-positive → parameter-negative and parameter-positive →
annotation-negative links at `1107–1115` and stores the negative formal domain.
`lib.rs:11242–11244` uses that domain in f's exposed Function argument. These
real paired links do not supply a successful pair for this rejected witness.

The real body is an application of the **formal cb provider**, with no callback
implementation body or `tick.ping` invocation. `candidate_source.rs:213–215`
maps cb's name to the exact parameter endpoint; `239–245` retains the formal
name registration. `394–411` retains the actual callee/argument keys, call
occurrence, result and evaluation-effect components. Parameter lookup itself
receives bottom/empty evaluation constraints at `369–380`.

`shadow_apply.rs:1339–1383` constructs ordinary Apply's negative Function demand
and fresh invocation-effect row. Function dispatch at `lib.rs:12493–12521`
reverses argument value/effect and forwards result value/effect. Invocation
effect and callee evaluation effect both flow to the application effect at
`shadow_apply.rs:1422–1439`. The outer lambda sends entry and body effects into
a fresh returned row at `lib.rs:11263–11342`; its inferred-entry record is inert
authorization evidence (`candidate_context.rs:157–169`). There is no cb-local
POP predicate lookup or annotation-owned subtraction wrapper on this path.
This traces the ordinary wiring under admission; the witness never reaches it
through the public private-entry preflight.

## Contribution lineage and allowance are not subtraction

Composed-positive formal effect ports call `candidate_signature_effect` twice
with the same per-pair view map. `candidate_effect.rs:1539–1576` keys their
shared view by the exact row `SourceNodeKey`, retains owner, resolved members,
symbolic tail, composed variance and lexical annotation scope, then inserts
Support versus Allowance bounds. Support expansion creates
`AnnotationMember(view, member)` obligations (`895–917`), distinct from actual
`Contribution(id)` operands. The latter retain `(effect, source origin,
instance)` at `864–886`. Equal `tick` identity alone does not make those
operands the same lineage. This witness invokes an abstract formal; there is
no executed operation-origin contribution to report.

`candidate_context.rs:2174–2195` retains source metadata/member ordinals, but
`LocalWeight.left_word` and `right_pops` are typed as `[(); 0]` at `115–122`.
`unit_push` is dormant preparation (`130–132`), set only for composed-positive
nonempty sets (`2187`). `materialize_unit_push` returns a **DetachedWeight**
(`2197–2215`); a solver-source search finds its definition only. The separate
`evaluate_context` algebra explicitly has no source consumer (`1486–1533`).
Thus the actual annotation pair has live Support/Allowance checking, no live
nonzero attachment word and no matching subtraction consumer. Detached exact
count arithmetic does not prove source-generated PUSH/POP discharge.

The checks are real: `candidate_zero_word_filters` requires empty words and a
matching closed weight (`2649–2654`); execution registers/replays
`Allowance(view)` (`2769–2798`) and records discharge (`2800–2809`). Exact upper
bounds are retained by `candidate_extrusion.rs:544–554`, and each insertion
replays against opposite bounds (`763–803,840–863`). Concrete membership accepts
a matching effect, forwards an unmatched operand to the symbolic tail or emits
mismatch (`candidate_effect.rs:919–954`). These current/future lower checks are
allowance checks. They do not remove a contribution from f's output.

Function context propagation preserves result context and swaps argument
context at `candidate_context.rs:2576–2606`; replay combines retained lower and
upper contexts at `2955–2969`. Those operations transport existing contexts,
without producing the missing nonzero words. Scheme capture preserves four
ports (`candidate_scheme.rs:458–513`); fresh use remaps annotation views/member
ordinals and freshens contributions with retained effect/origin
(`1046–1067`), then remaps source context payloads (`1089–1106`). No subtraction
can be recovered merely by these copying operations.

## Precise owner gap and recommended action

The missing premise is an actual construction and discharge chain for the
composed-negative **formal Function result-effect row occurrence**: a retained
annotation attachment tied to cb's exact source occurrence/resolved `tick`, a
consumer on the real body call provider and the outer function's result-effect
projection, plus the invariant preserving independent contribution lineage.
Current HIR supplies its source identity; current paired formal construction
rejects it; current Apply/Lambda forwards effects without its subtraction.
Configured allowances and future-lower checks cannot stand in for that chain.

Recommended next action: feed this exact owner gap to the existing prover lane's
negative-formal source-step premise, and keep its implementation/admission gate
OPEN until an authorized construction/consumer cut has source correspondence.
This audit grants no code changes, semantic reinterpretation or gate closure.

## Checks, independence and omitted scope

Checks performed: bounded `rg`, `sed`/`nl` source reads; SHA-256 snapshot;
read-only HEAD/status and scoped old/current Git diff; note path/whitespace and
dependency stability inspection. No compiler test, build, execution, Oracle
rerun, random seed/range, enumeration, mutation run, benchmark or child ran.
One diagnostic search named nonexistent `candidate_bounds.rs` and returned
exit 2; the search was corrected to the actual `candidate_extrusion.rs` owner.
Broad routing/search captures were truncated; all cited decisive owner excerpts
were separately read. CPU/RSS and total wall time were not instrumented; this
was a lightweight source-only lane within the 30-minute bound.

Oracle and candidate are independent implementations, but this audit depends
on the prior note's supplied revision/binary/run evidence and the same accepted
policy; it does not independently rebuild Oracle provenance. No model/checker
was treated as an independent source-semantics oracle. Unverified scope:
literal parsing/admission, binary-to-source correspondence, candidate execution,
concrete foreign/late-lower runs, handlers, returned callback use, recursion,
symbolic/parameterized effects, fresh-use/extrusion/intrusion universality,
soundness, principality, complete Call and public/default/F5 cutover.

## Dependency snapshot and commit packet

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/progress/2026-10-11-negative-formal-effect-source-audit.md` | `8b0c9c7bfa131b9119d82a5a3c7ef6f8eb9636093176a2bd5818b6fe9aa7a538` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/shadow_apply.rs` | `230ed70cc8575016967cdf16c6c814544b25e45b0fc687d6c89f0d38e8fb5cd6` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |

Commit packet:

- Exact leased/change path: `notes/progress/2026-10-11-negative-formal-effect-current-source-falsification.md` only; frozen, writes stopped before review.
- Baseline: `cfab95a2cb64be8f8a58f8e69abee22390042135`; Oracle revision supplied by prior audit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency delta against old audit: `shadow_apply.rs` changed from `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` to the hash above; five other recorded owner hashes unchanged. The primary changed the supplied Oracle audit during this lane from `152e74484064811622474384b2ee8362921e2e7989e30a383884625d48024c98` to `8b0c9c7bfa131b9119d82a5a3c7ef6f8eb9636093176a2bd5818b6fe9aa7a538`; its witness/output are unchanged, and its corrected consumer wording was reread before freeze. No dependency edited by this lane; scheme/lib/extrusion are additional baseline dependencies.
- Review/claim: unreviewed bounded static source falsification; independent production certification and theorem/admission/gate closure are not claimed.
- Checks already run: source owner reads/searches, scoped old/current diff, dependency SHA-256 stability, note-only integrity inspection; no build/test/Oracle run.
- Proposed research checkpoint message: `research: falsify current negative formal subtraction source premise`.
- Shared-record deltas intentionally left to primary/curator: link this audit to the negative-formal source-step premise; record unchanged rejection and absent live subtraction consumer; preserve OPEN theorem/admission/cutover gates. No shared task/index/design/theory or question-board file edited.
