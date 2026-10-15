# Forward initializer: exact Oracle instance and root correspondence

Date: 2026-10-16
Status: independently reviewed artifact characterization and bounded operational
derivation. Original valid-source/control adequacy remains OPEN.
Baseline: `cfded839e`; frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Sole repository lease: this note. Scratch lease:
`/tmp/yulang-forward-initializer-artifacts-20261016/`.

Independent review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256 `0fc04a0f084a9328fdff8d0a6e0f11cc22d381dd7700f14153564d0c3198ebfd`.
The complete graph, two instance keys, retained operation sites and frozen
build-source provenance support the bounded attribution below. Attribution to
the preceding run retains the stated unchanged-construction premise; it is not
a newly collected event trace or a valid-source judgment.

## Objective, authority and conclusion

Resolve the [previous discriminator](2026-10-16-forward-initializer-control-discriminator.md)'s
specific missing artifact: ordered Oracle roots, original pending DefId, actual
specialization keys, executable demand and escaped operation site. The primary
explicitly authorized one scratch wrapper compile, a compile-error-only repair
if necessary, and exactly one artifact-only source-to-control invocation.

**Result:** the same source pending definition has two actual Oracle instances.
Main receives its already materialized **effect-thunk instance m5**. The later
pending root independently executes **value instance m3**, which forces its
operation. The earlier VM error's control ExprId(15) belongs to m3's forced
operation; m5's operation site is 28. Thus the prior escaped request is explained
by the later pending root, rather than a failed before-publication request in
main's forward materialization. No new VM run was needed or performed.

This is a concrete artifact/control result, not a valid-source witness or a
source-semantic counterexample. The consumed user correction `1e62dfdc3`
continues to reject justification of an initializer effect by handling a later
value reference. Oracle compiler readiness and specialization do not independently
certify the corrected source judgment. No cache law, A/B choice, blanket root
purity, delimiter or implementation change is selected.

Governing sources are the correction's approved-answer “解釈と回答”; Oracle mono
contract “Program と roots”; ordinary computation package §§3–5; charter §§15–16,
21; top-level inference principles §§1,3–4; and the module-expression design's
retained source-order/OPEN whole-materialization boundary. Consume the reviewed
[Oracle publication exclusion](../theory/2026-10-16-resumed-definition-source-reachability.md)
and [failed stored-value admission route](../theory/2026-10-16-initializer-effect-admission-correspondence.md)
with their existing hypotheses. This packet does not repeat their proofs.

## Exact source and observed artifact

Both the previous execution and this artifact observation use these exact bytes,
including final newline (SHA-256
`17a44c97b4a0804ca41ce01cb971bff68555d3a6eb77bfe1644f85f54cf7065c`):

```yu
act signal:
    our ping: () -> int
my relay (thunk:[signal] int) = catch thunk { signal::ping(), k -> k 1, v -> v }
my main = relay pending
my pending = signal::ping()
```

The wrapper returned success after unchanged compact source construction,
lowering-error checks, `ensure_runtime_ready`, public control construction and
control-error checks. It never constructs an evidence plan or VM. Complete
output: 18,432 bytes stdout, 53 bytes stderr. No truncation or guard trigger.

Source labels and original body identities:

| Label | Poly DefId | Original poly body |
| --- | --- | --- |
| relay | 1007 | 2843 |
| main | 1008 | 2846 |
| pending | 1009 | 2849 |

Actual ordered poly roots are ComputedDef(117), ComputedDef(147),
ComputedDef(1008), ComputedDef(1009). Control roots are EvalInstance(0),
EvalInstance(1), EvalInstance(2), EvalInstance(3), in that same order. The first
two instances initialize compact-std flow labels. No relay root is emitted.

Let E be `EffectRow([signal])`. Actual relevant instances:

| Instance | Source DefId | Runtime signature/key type | Control entry |
| --- | --- | --- | --- |
| m2 | 1008 (main) | Int | e12 |
| m3 | 1009 (pending) | Int | e16 |
| m4 | 1007 (relay) | Fun(Thunk(E,Int), Pure, Pure, Int) | e25 |
| m5 | 1009 (pending) | Thunk(E,Int) | e28 |

This is an authentic key distinction, not a label/shape guess. In
`specialize2/emit.rs:119–129`, InstanceKey is `(original def, closed runtime
signature)`. The instance stores that same signature and converted original
DefId. `control-ir/src/lower.rs:96–110` preserves source/signature and instance
ID, checking its index. Thus m3 and m5 have keys `(1009,Int)` and
`(1009,Thunk(E,Int))`. They do not share a runtime publication cache cell.
The private instance_by_key map itself was not exposed or changed.

The exact control subgraph is:

```text
e10 = InstanceRef(m4)
e11 = InstanceRef(m5)
e12 = Apply(e10,e11)                         [main m2 entry]

e13 = EffectOp(signal::ping, def1006)
e14 = Unit
e15 = Apply(e13,e14)
e16 = ForceThunk(E,Int,e15)                  [pending m3 entry]

e17 = Local(def1010)                        [relay formal]
e18 = ForceThunk(E,Int,e17)
e19 = MarkerFrame(signal,e18)
e20 = Local(def1011)                        [raw continuation k]
e21 = Int(1)
e22 = Apply(e20,e21)
e23 = Local(def1012)                        [value arm v]
e24 = Catch(e19, signal::ping(_,k)->e22, v->e23)
e25 = Lambda(def1010,e24)                   [relay m4 entry]

e26 = EffectOp(signal::ping, def1006)
e27 = Unit
e28 = Apply(e26,e27)                        [pending m5 entry]
```

There is no ForceThunk in m5, and no reference to m3 from main or relay. There
are 29 control expressions total; the full expression table was captured.

Actual InstanceBody task owners authenticate both bodies against original
poly body 2849. m3's body actual type is Thunk(E,Int), consumer Int. m5's body
actual and consumer are both Thunk(E,Int). Main's pending Ref signature is
Thunk(E,Int); relay's formal and Catch body are Thunk(E,Int). These are artifact
facts about specialization, not a claim that the source Name inherits the
initializer's effect or that the stored source scheme is semantically valid.

The relay task records Catch site 2842 handling exactly signal::ping and one
value arm; Lambda site 2843 has `argument_contract:false`. All recorded
stack_weights are empty. Two actual static-route entries for original operation
2849 are `Dynamic(Unclassified)`; neither establishes a selected handler.
The control MarkerFrame(signal) and Catch are retained exactly as above.
No absence of a source contract or universal visibility theorem is inferred
from that artifact flag or the dynamic classification.

## Bounded consumer derivation and explanation of the earlier error

All paths below are actual frozen build-source paths under `crates/`.

1. **Main demands m5, not m3.** `e12` applies the closure from m4 to the value
   from m5. Evidence plan translation maps InstanceRef directly to Instance
   (`evidence-vm/src/runtime.rs:9539`). Application evaluates callee and argument
   (`:16151–16161,16467–16525`, including tail counterparts). An Instance is not
   an immediate literal/local shortcut (`:15980–16017`), and invokes synchronous
   eval_instance (`:15521–15522`).
2. **m5 publishes an inert operation thunk.** The effect operation callee at
   e26 is an EffectOp runtime value. Applying it at e28 returns
   `Value(Thunk::Effect{payload,route,evidence})`, without performing the effect
   (`:18408–18420`). m5's entry is exactly that Apply. eval_instance accepts its
   value and inserts it under m5 before returning (`:14699–14726`). No pending
   m5 publication is live when relay consumes the thunk.
3. **Relay runs latent code after publication.** Closure entry binds the
   already obtained argument and evaluates its body (`:18318–18339`). Catch
   installs its active frame before evaluating e19 (`:22558–22591`). e18 forces
   the formal; forcing an Effect thunk performs its request using its retained
   evidence (`:22242–22282`). Catch selection uses the actual operation/hygiene
   checks (`:22690–22996`), not the static route's `Unclassified` spelling.
   This packet does not independently certify the whole receiver visibility
   algorithm or a general source permission theorem.
4. **The later root is a different demand.** The root loop visits m3 after m2
   (`:10553–10578`). m5's cached value does not satisfy m3's different ID. m3
   enters e16, which forces the operation generated at e15. Its body is not
   reusing m5's completed publication. Root completion does not retain relay's
   Catch: eval_catch truncates the active frame list on return (`:22584`).
5. **Site 15 identifies this later force.** Plan translation recognizes
   ForceThunk(e15) as a fused ForceEffectCall (`:9581–9594`), and
   `forced_effect_call_parts` sets `site = thunk = e15` (`:9646–9656`). The
   unfused m5 operation instead records its actual Apply site e28:
   `effect_thunk_evidence` preserves its input `site` (`:11066–11080`), and
   EffectOp application passes that actual site (`:18408–18417`). Performing
   the effect uses `evidence.site`; escaped-request conversion preserves
   `request.site` (`:14853–14877`; direct/routed variants likewise at
   `:14789–14804`). This is not a comparison of unrelated numeric IDs.

The prior actual VM process reported EscapedEffect(signal::ping, site e15),
not e28. In this complete graph, the e15 operation is evaluated only through
m3's entry at root ordinal 3. Hence that diagnostic is explained by the later
pending root. Main's force of m5's latent operation has a different site and
occurs after m5 publication; it is not the requested before-publication capture.
The prior process did not print main's value, and this packet makes no new
numerical-result observation.

Applying the new artifact to the prior execution assumes the same unchanged
frozen-library construction of the same source gives the same control graph.
Both wrappers call the same public builders with filename `playground.yu`, same
bytes, compact profile and cold failed-cache override; the library hashes are
identical. The new wrapper's added code only reads returned artifacts, after
all checks, and omits VM execution. No original compiler transition rule was
supplied by this observer. This is source/artifact correspondence evidence with
an explicit reproducibility premise, not a newly recorded prior-run event trace.

## Process, caps and provenance

Commands actually run:

```text
python3 /tmp/yulang-forward-initializer-artifacts-20261016/observe.py compile
python3 /tmp/yulang-forward-initializer-artifacts-20261016/observe.py artifact
```

The first command invoked exactly one initial rustc compilation with no repair:

```text
rustc --edition=2024 /tmp/yulang-forward-initializer-artifacts-20261016/artifact_driver.rs -L dependency=/tmp/yulang-hygiene-audit-my68a_85/target/debug/deps --extern yulang=/tmp/yulang-hygiene-audit-my68a_85/target/debug/deps/libyulang-41b7b66fe2aeddb3.rlib --extern poly=/tmp/yulang-hygiene-audit-my68a_85/target/debug/deps/libpoly-878c74cab6a005c0.rlib -o /tmp/yulang-forward-initializer-artifacts-20261016/artifact-driver
```

The second invoked exactly one artifact-only compiler process:

```text
/tmp/yulang-forward-initializer-artifacts-20261016/artifact-driver /tmp/yulang-forward-initializer-artifacts-20261016/forward-initializer.yu
```

Both cwd: `/tmp/yulang-hygiene-audit-my68a_85/oracle`. Source/poly/control gates
match the old wrapper; the g-only rendering loop is replaced by observation of
returned public artifacts. No evidence plan/VM/successor execution, Cargo,
production edit, test, mutation, random search, delegation or Git operation.

The wrapper formats atomically into a 128 KiB bounded buffer. Explicit cap
failure withholds the artifact; it does not truncate. Caps: 256 total poly plus
control roots, 64 instances, 64 tasks, 2,048 control expressions, and 4,096
printed site/type/ref-signature/static-route entries. Actual counts: four poly
and four control roots, six instances, six tasks, 29 expressions, 39 evidence
entries. Full output ends with `artifact-complete`.

Guard: 4 GiB address space, 60 s CPU, zero core, isolated process group,
256 KiB combined output, 2 GiB sampled main RSS and 100 ms polling. Compile
wall cap 60 s; artifact wall cap 90 s. Artifact unexpected children cause group
kill. Compile permits linker/helper descendants in its one group; no direct
child was sampled, which is not a complete descendant census. No RLIMIT_FSIZE.
Artifact child-only cache override is
`YULANG_CACHE_DIR=/dev/null/yulang-callback-oracle-cache`; YULANG_DEBUG_MONO is
removed from child environment because explicit public diagnostics replace it.
No guard fired, output was truncated or source/wrapper/binary hash changed.

| Invocation | Exit | Wall s | User/system CPU s | Sampled main peak RSS B | stdout/stderr B |
| --- | --- | --- | --- | --- | --- |
| rustc | 0 | 3.116 | 1.932149 / 1.678340 | 225452032 | 0 / 0 |
| artifact-only | 0 | 38.941 | 38.268849 / 0.616013 | 600313856 | 18432 / 53 |

This is bounded correctness evidence, not a benchmark. Child/linker peak RSS,
aggregate transient RSS and complete descendant counts are unmeasured. Both
library hashes match the previous reviewed provenance; no compiler was rebuilt.

```text
libyulang-41b7b66fe2aeddb3.rlib c9901b70f1aeb40672079bc6ec12aa5183660ec2ea345b25ecb05d9c49d45eb3
libpoly-878c74cab6a005c0.rlib ab2cb05251904978ab4bb06f1f0befea3cb3577b05f5a8ea6cab13b4214c515a
artifact_driver.rs 26a8548305f993eb2fc0a53bb31942090761f8db92f8f84c2bb78b4e8e82fb9b
artifact-driver 1bbd3be919562faf5190983a5362ab9b061fa9100fbf224c370051a7613c2ca4
observe.py 205ad49dd6cd64eec75cf30d11c6d00a1e54f1043e0799b6ce53f4f387035633
compile/manifest.json c170334f250c7508cd4dca201e31b4390793b66b0f8420e180b3e09699501467
artifact/manifest.json 11da2a03518dbf6f1e4f75896a5cf0e04590eb65b461e904726e0052e4241db5
artifact/stdout 00201078f5f4d5d38694d59a8345423004cc5caa7573b431c4f1b250e8d686f5
artifact/stderr 81b148e648e5a5d710539de335aa415dec824f55fb18cb485219c7eb9453fa13
```

## Dependencies, limitations and commit packet

Scratch dependencies.json records nine exact Oracle build-source hashes, their
sibling comparison, five repository dependencies and the scratch manifests.
Eight Oracle files equal the sibling capture. One difference is explicit:
`crates/yulang/src/source/mod.rs` build hash
`0ac0d078323428abf42292e765d2987fb072cc89afb140cb3a86bb98129af3f9`
versus sibling hash
`de29d6bbcbe8a969f7bf77b852cae2c314de1d6158c6cdb7dec8b6022e06d059`.
The sibling adds `research_projection_source_labels(check)` and its bounded
research-only diagnostic helpers; the frozen build source has neither. The
inspected public builder and structures are identical; this packet uses the
actual frozen build source, not an unexplained sibling equality assumption.
The new wrapper uses existing frozen rlibs, not sibling recompiled libraries.

Key build-source SHA-256:

```text
specialize/src/specialize2/emit.rs 7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c
specialize/src/specialize2/mod.rs 8ccf7a3850384bfe6e0dab024732a830364cb920197b8f75392efc90c68a67a8
specialize/src/specialize2/runtime_evidence.rs 301c2c26cbe0c562b1d4a6d7d17bb8ce1a43e0ff2331fa782e4a9f7013822616
control-ir/src/ir.rs 69b2bfc106e4159a04cf7d66ebfa5cbe47578b534fd36f18a0f4842347ff95a3
control-ir/src/lower.rs 0c07166a515e89b27bd0b5f21fe5f5349b76955b2213e4bfde24c8150ce547fd
evidence-vm/src/runtime.rs eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7
```

The preceding reviewed discriminator note remains unchanged at SHA-256
`985bb9af15f964f25904e78b666626df367bcafe62e83a0226b49b300b146368`.
No broad source-domain characterization, general specialization equivalence,
normal source validity/rejection proof, whole hygiene theorem or production
cutover follows. Source admission still needs its original effect attribution;
this artifact explains one implementation rejection without certifying that
implementation as the language definition. The successor's different earlier
GlobalRead capture failure therefore remains unsuitable evidence of semantic
divergence or authority for removing its guard.

Recommended next action: primary consume this concrete two-signature distinction
at the original source/control bridge, using authentic Name consumption and
original root/InstanceBody effect ownership. Authenticate when a forward Name
materializes an inert value versus forces the original computation, including
its actual specialization key, before considering any delimiter or cache rule.
No repeated version of this probe is recommended.

Commit packet:

- Exact repository lease: `notes/progress/2026-10-16-forward-initializer-artifact-correspondence.md`.
- Baseline `cfded839e`; frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`;
  scratch lease `/tmp/yulang-forward-initializer-artifacts-20261016/`.
- Changed dependency hashes: none edited in this packet; sibling/build-source
  diagnostic-only difference explicitly recorded above.
- Claim/review: frozen, unreviewed bounded artifact characterization and
  operational derivation; no independent certification or original gate closure.
- Checks: one successful initial scratch rustc compile, one successful guarded
  artifact-only process, exact provenance/source/output hashes, narrow static
  source/site derivation, dependency recheck and note whitespace/link inspection.
- Proposed checkpoint: `research: locate forward initializer escape in distinct Oracle instances`.
- Shared deltas left for primary/curator: replace the prior Oracle trace gap for
  this exact input with m5 latent-value versus later m3 root distinction; retain
  valid-source and whole source/root/InstanceBody-to-Name/GlobalRead adequacy OPEN.
  No old note, shared record, authority, index, question bundle or code changed.
