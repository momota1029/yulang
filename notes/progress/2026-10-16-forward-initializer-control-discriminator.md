# Forward initializer: bounded admission/control discriminator

Date: 2026-10-16
Status: independently reviewed finite executable evidence and static owner trace.
Original typed-source initialization/control adequacy remains OPEN.
Baseline: `2d78525b85e6fe0e70161ffe2299d3e3ecffad28`;
successor production/runtime integration `35e87f844`.
Exclusive repository lease: this note. Scratch:
`/tmp/yulang-forward-initializer-control-20261016/`.

Independent review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256
`e7b4ad065fa2aa66b6b2e65f21d0b68cdf7820d57a1bfee66f5f87024eeb4887`.
Review checked retained source/provenance, GlobalRead attribution and the
limited Oracle result without another execution. The exact artifact-only
root/instance correspondence packet is now assigned; no source-validity or
publication-law gate is closed.

## Objective, authority and result

Distinguish the actual before-publication forward-Name control boundary with
one frozen Oracle process and one successor process. This is a **negative
admission/control discriminator**, not an asserted well-typed source witness.
The primary confirmed the exact replacement source before either execution.
No production change, semantic adoption, cache law or A/B selection is proposed.

Governing inputs are the consumed correction bundle `1e62dfdc3`, especially
approved-answer “解釈と回答”; Oracle mono contract “Program と roots”; ordinary
computation package §§3–5; runtime charter §§15–16 and §21; and top-level
inference principles §§1, 3–4. The module-expression source-owner design retains
source order and explicitly leaves whole typed-source materialization adequacy
OPEN. The user correction rejects using an initializer's unresolved operation
as though it were justified by a handler around the published value reference.
This experiment does not reinterpret that correction or require all roots pure.

Consumed, already reviewed results:

- [Oracle raw-continuation exclusion](../theory/2026-10-16-resumed-definition-source-reachability.md):
  this materialization invocation's pending publication is outside explicit raw
  continuations. Ambient handler availability alone is not a source theorem.
- [Initializer admission correspondence](../theory/2026-10-16-initializer-effect-admission-correspondence.md):
  stored-value comparisons do not certify a separate original root effect.
  The failed value-scheme certificate route stays withdrawn.

**Observed:** Oracle passed source-to-poly, runtime readiness and control-error
checks, then failed with escaped `signal::ping`. Successor passed its own
experimental preparation and reached `ContinuationMaterialization` at pending's
operation payload. Both exited 1, with no stdout. Neither run returned a value.
This establishes the successor guard's reachability through its permissive
experimental entrypoint, while supplying no valid-source witness or semantic
divergence. The Oracle observation does not identify its precise dynamic
root/instance/handler path (§3).

## Exact source and preflight

The initial proposed source was not executed:

```yu
act signal:
    our ping: () -> int
my main = catch pending { signal::ping(), k -> k 1, v -> v }
my pending = signal::ping()
```

At `runtime/primitive.rs:66–69`, a bound continuation prevents the whole-program
closed-primitive certificate. At `runtime/receiving.rs:221–224`, ModuleRun cannot
supply a positive local Grant. At `machine.rs:1257–1269`, this combination fails
with HandlerEvidence before raw capture. Using that known earlier failure
would not discriminate the intended seam.

The primary confirmed this exact replacement; both processes received the
same UTF-8 file, including final newline:

```yu
act signal:
    our ping: () -> int
my relay (thunk:[signal] int) = catch thunk { signal::ping(), k -> k 1, v -> v }
my main = relay pending
my pending = signal::ping()
```

Source SHA-256:
`17a44c97b4a0804ca41ce01cb971bff68555d3a6eb77bfe1644f85f54cf7065c`.
The additional receiver is an existing authenticated local permission route,
not an added source-admission premise: pending's own initializer still requests
signal, while its ordinary Name occurrence is pure. The concrete receiving
annotation does not discharge that independent initializer obligation.

## Boundary coverage: actual observations versus source owners

| Boundary | Oracle | Successor |
| --- | --- | --- |
| Parse/lowering | Actual compact source-to-poly succeeded with no reported lowering errors. | Actual `prepare` returned: no syntax diagnostic, candidate-lowering failure, unsupported result or candidate conflict. |
| Readiness/admission | Actual `poly.ensure_runtime_ready()` returned successfully. This is a particular compiler readiness check, not source-semantic validity. | Experimental candidate preparation succeeded; `execute` discards `_candidate` and passes `RuntimeEvidence::default()`. No production admission certificate is supplied. |
| Original initializer effect | Static producer: authentic operation declaration adds signal to pending's own body effect. Name lowering separately constructs a pure occurrence. No per-input graph/type dump was emitted. | Same source declaration and original pending body retained by HIR; no body-effect dump or independent source judgment was emitted. |
| Stored value/body task | Static audited route retains body, compares value at binding commit, then emits original InstanceBody tasks; the prior admission note's projection obstruction applies. No new per-input task dump was emitted. | `RuntimeProgram::from_hir` constructs original body code after experimental preparation; this is not an initialization-effect admission consumer. |
| Root order | Static `body/mod.rs:2071–2075` walks source children; `body/methods.rs:387–398` appends ComputedDef for computational bindings. Specialization `emit.rs:45–75` maps retained roots in order. User-binding demand order is main before pending when these computational roots are emitted; relay is an inert function value. Actual root list was not printed. | Actual source program starts fresh ModuleRun. Static `begin_root` visits its source schedule and skips already materialized globals; root completion remains below nested relay invocation/handler. The diagnostic proves the operation reaches a selecting handler before publication. |
| Name/InstanceRef | Static `emit.rs:372–418` emits nonlocal Let Names as InstanceRef. Evidence plan maps this to Instance; runtime `:15521–15522` calls synchronous `eval_instance`. Actual InstanceId/signature-key correspondence was not logged. | Static `machine.rs:462–479` sees empty pending cell, pushes GlobalRead and evaluates pending's original body under current owner. No owner reset occurs. |
| Handler boundary | VM execution was entered. It eventually returned EscapedEffect; output does not identify the tested Catch profile, its selection/forwarding, or whether the escape occurred on forward initialization versus a later root/specialization. | Comp entry authenticates annotated Int RootCompSchema and receiver receipt (`:706–726`). Direct thunk execution opens the view (`:1500–1518`); request observation remains available while pending's body runs. Positive local Grant permits the relay handler to reach capture. |
| Exact failure | `evidence VM failed: runtime-evidence-run escaped effect request: signal::ping (EscapedEffect { site: Some(ExprId(15)), path: ["signal", "ping"] })` | `runtime unavailable: ContinuationMaterialization(SourceSite { source_root: Definition(DefinitionRootId { .. }), occurrence: HirOccurrenceId { ordinal: 15, .. }, range: 166..168 })` |

The successor error is discriminating: `capture_template` at
`machine.rs:1011–1015` returns this variant only for saved GlobalRead/Root.
The selecting relay handler is inside main's Root, so main's Root is below its
capture delimiter. Pending's GlobalRead lies above that handler while its
initializer runs. Thus the target is the pending GlobalRead suffix. Bytes
166..168 are `()` in pending's original operation call, not a published-value
reference. Earlier HandlerEvidence did not prevent this observation.

The Oracle wrapper prints its VM result only after the whole run succeeds, so
empty stdout does not establish that no earlier root completed. Its error's
ExprId(15) is not an authenticated cross-version identity with successor
occurrence 15. The single allowed run omitted mono/control dumps and per-event
tracing. No precise Oracle handler-selection explanation is inferred from the
shared operation spelling, numeric coincidence, source order alone or the
reviewed absence of publication in Oracle raw continuations.

## Commands, provenance and resource accounting

Exactly these existing-binary invocations ran, sequentially under the scratch
`observe.py` guard:

```text
python3 /tmp/yulang-forward-initializer-control-20261016/observe.py oracle
python3 /tmp/yulang-forward-initializer-control-20261016/observe.py successor
```

Oracle child, cwd `/tmp/yulang-hygiene-audit-my68a_85/oracle`:

```text
/tmp/yulang-callback-exact-20261015/compact-driver /tmp/yulang-forward-initializer-control-20261016/forward-initializer.yu
```

Successor child, cwd `/home/momota1029/rust/yulang`:

```text
/home/momota1029/rust/yulang/target/debug/yu-playground --run main --steps 30000 /tmp/yulang-forward-initializer-control-20261016/forward-initializer.yu
```

Oracle used the already reviewed compact-web wrapper, with child-only
`YULANG_CACHE_DIR=/dev/null/yulang-callback-oracle-cache`; no installed yulang,
full-stdlib fallback or rebuild. Frozen Oracle commit is
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. Verified wrapper/source/library hashes:

```text
compact-driver 1ff46aa60505491cae24c0764fa3914cd7c2e5d27caef6a9f4f5cda738da2b2f
compact_driver.rs c0682ca30cf7c0cb5dd3a4556e5794699331ee7e0423d2aa2ad4b143c30aa619
libyulang-41b7b66fe2aeddb3.rlib c9901b70f1aeb40672079bc6ec12aa5183660ec2ea345b25ecb05d9c49d45eb3
libevidence_vm-a4defe861965a781.rlib 9a664f737a8039a75cd3dafa5c37851648645dbae395916d1de8bb2d81ec6c32
libpoly-878c74cab6a005c0.rlib ab2cb05251904978ab4bb06f1f0befea3cb3577b05f5a8ea6cab13b4214c515a
successor executable a75918c7f15cb25688458839820e5d9bf3a00b078771ea71a328f3e5012b40af
Cargo.lock 2055b82e7c2c68df727940d7053da0490368a99217bd3587866a7003177484e6
observe.py 68f9c0de489b062fa5246d963d9882bfa6184e2479b83f1bc2682b2c4188b523
```

Primary supplied successor build/source continuity: sole primary Cargo owner
ran `CARGO_BUILD_JOBS=2 timeout 90s cargo run -q -p yu-playground -- --run main -`
on frozen production source later committed as `35e87f844`;
`/tmp/yulang-expression-cli-1.log` contains `7`. Primary reports no production
source or Cargo.lock delta since that integration and no intervening writers.
The current lock and lib.rs hashes were verified here. Package verification
log `/tmp/yulang-expression-playground-all-1.log` records its preceding build.
This is build-command/source continuity evidence, not a reproducible-build
attestation or a new build performed by this worker.

Both children had 90 s wall, 60 s CPU, 4 GiB address space, 2 GiB sampled RSS,
256 KiB combined stdout/stderr, zero core size, isolated process group,
unexpected-child kill and 100 ms polling. No process-wide file-size limit.
No guard fired, child appeared, output was truncated, or source/binary hash
changed. The successor also had 30,000 transition budget and did not exhaust it.

| Process | Exit | Wall s | User/system CPU s | Sampled peak RSS B | stdout/stderr B |
| --- | --- | --- | --- | --- | --- |
| Oracle | 1 | 37.736 | 37.037552 / 0.623958 | 601165824 | 0 / 228 |
| Successor | 1 | 0.102 | 0.018067 / 0 | 655360 | 0 / 180 |

The short successor lifetime makes sampled peak RSS a weak lower observation;
4 GiB address-space and CPU limits still applied. This is one deterministic
source, no random seeds/ranges, mutations, repetitions, warmups or benchmarks.
No repair/retry, builds, Cargo, code/test edits, Git mutation or delegation.
Initial baseline inspection used read-only `git rev-parse HEAD`/`git status`;
all subsequent provenance checks used files/hashes. Machine resource snapshot
showed about 24.7 GiB available; primary confirmed no competing compiler process.

Retained exact stdout/stderr and resource manifests are under scratch
`oracle/` and `successor/`. SHA-256:

```text
oracle/manifest.json 54160c5622215e85fd449c8107121d4523f25f74ef7461af67a587a73439b3ca
oracle/stderr 7c6b109d4d931434f8263ab5db820c9fe6c84725c3f46150e6e4295466080f9f
successor/manifest.json f700363a78b8f4a51c46826f887217d2a18283b0ccad8f6d24707d4b74d2f98b
successor/stderr 4b6f1fa739830dde3831b970451f8f07abfa568abc48e1f9502dc07d5f6d40fb
both stdout e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
```

## Independence, limitations and next action

The Oracle is the actual frozen source-to-poly/control/evidence-VM route, not
a checker supplied successor transition rules. The successor uses a different
current parser/HIR/candidate/runtime implementation. They share source bytes,
operation declaration, retained language authority and this experiment's guard.
Oracle implementation success is not an independent source-semantics proof;
its readiness checks may omit the same initialization obligation identified by
the prior audited route. Both rejections are compatible with the consumed
correction, without establishing identical source admission or failure causes.

This finite result establishes no principality, whole-source validity,
unreachability, root purity, cache-bearing Resume behavior or runtime repair.
No new conditional theorem replaces the original parent. No omitted selection
trace is filled by assuming compiler soundness, or by equating source Names
with pending initializer computations.

Minimal additional artifact: the exact ordered poly/control roots plus the
pending InstanceId used both by main's executable reference and pending's own
root, with their InstanceKey/signature join. The existing specializer has a
`YULANG_DEBUG_MONO` dump hook (`emit.rs:89–90`); it was not enabled here and no
dump is retained by this run. These identities, together with a static proof
that main actually executes that reference, can distinguish a first forward
materialization failure from a later pending-root failure: successful execution
of the same synchronous instance publishes it before returning, so its later
root would read the cache. If the identities differ or the executable demand
cannot be authenticated, the additional discriminator is a root/instance
entry/return event trace locating the existing escaped ExprId, rather than
another untraced repetition of this source. No such trace was collected here.

Recommended next action: primary assigns that bounded source/artifact
correspondence packet and then explains the exact receiver-Catch profile.
Consume it at the original source-control gate; no publication-law question
or second identical run follows from this packet.

## Frozen dependencies and commit packet

Twenty direct dependency hashes and eight equal Oracle sibling/build-source
comparisons are retained in scratch `dependencies.json`; all were rechecked
unchanged before freezing. Key current dependencies:

```text
runtime/machine.rs e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a
runtime/program.rs b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748
runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
runtime/receiving.rs 5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd
src/lib.rs bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b
resumed-definition-source-reachability.md f8a04dd97c42810e33792e7029795ecb7f20721672986a911ef15890debdc57a
initializer-effect-admission-correspondence.md b01ac0edb76e5a2aa2ed5e32aa2750757ff510d57c9579021d0f9bce3b75653d
```

Runtime paths above are under `tools/inference-playground/src/`; theory notes
are under `notes/theory/`. Oracle owner hashes equal those already recorded in
the reviewed admission/exclusion notes, with build-source equality checked here.

Commit packet:

- Exact leased path: `notes/progress/2026-10-16-forward-initializer-control-discriminator.md`.
- Baseline: `2d78525b85e6fe0e70161ffe2299d3e3ecffad28`; runtime `35e87f844`;
  frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none during packet; prior integrated note hashes
  differ from their historical producer hashes because they include review
  metadata, as frozen above. No dependency was edited here.
- Claim/review: bounded negative-admission/control evidence, frozen and unreviewed;
  producer supplies no independent certification or gate closure.
- Checks already run: exact-source/library/binary/dependency hashes; actual 1+1
  guarded sequential executions; narrow static owner reads. No separate artifact
  checker was run after the primary's stop instruction.
- Proposed checkpoint: `research: discriminate forward initializer control failures`.
- Shared deltas left to primary/curator: record the intended successor guard
  reached and Oracle readiness-to-escaped-request result, retain original
  source/root/InstanceBody-to-Name/GlobalRead adequacy OPEN, and record the exact
  missing Oracle per-input profile/root/instance correspondence. No shared task,
  index, authority, theory map or question bundle was edited.
