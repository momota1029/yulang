# Oracle operation path: bounded static source correspondence

Date: 2026-10-11
Status: frozen, unreviewed research characterization; original H remains OPEN
Claim class: conditional static parser/resolver correspondence, no executable qualification
Y3 baseline: `7ebcc92a1d32bc3316e2803979c3872e5ab42046`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle checkout: `/tmp/yulang2-oracle-read`
Exclusive lease: this note only; leaf, no delegation or Git mutation

## Objective and governing premises

Identify the source operation invocation for the declared `pub act tick` with
`pub ping: () -> ()`, and the binding/lambda form for a returned callback.
This supplies the missing syntax owner after the failed qualification in
[postpublication call probe](2026-10-11-oracle-postpublication-call-probe.md)
§§3–4. It does not rerun that probe or adopt its rejected provider.

Authority: [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§1, Oracle correspondence §2, and withdrawn callback result §6;
[original H](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md) §1;
[top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. Concrete effect identity is resolved, symbolic tails remain connected,
and the withdrawn callback scheme is not an expected result. No language
meaning, source domain, annotation rule or production representation changes.

Static claim premises: the inspected source bytes are the pinned Oracle;
the displayed declaration is registered successfully in the root module;
`tick` has no competing module binding/import and `ping` has no competing
value binding; normal parser/lowering calls complete without resource failure.
These are candidate execution premises, not observations of this provider.

## Exact candidate and owning examples

The operation invocation candidate is **`tick::ping()`**. A single candidate
for the existing provider/call experiment is:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
my provider() = \() -> tick::ping()
my observed() = f provider
```

This candidate was not parsed, lowered or run in this packet. Its nested
lambda shape is intended to provide a unit-taking function returning a
unit-taking effectful function. Its actual inferred scheme and compatibility
with `f` remain unqualified.

Two pinned source examples independently locate the spelling:

- `examples/effect-hygiene/02_local_sub_handler.yu:10–22` declares
  `pub act note` / `pub tell: () -> ()` and invokes `note::tell()` inside
  `our use_residual()`. This matches the candidate's nullary operation shape.
- `examples/state_handler_escape_repro.yu:5–8` declares `pub act log` /
  `pub put: str -> ()` and invokes `log::put "a"`. Lines 20–26 also return
  a lambda from a named unit-argument binding. This is a scratch reproduction,
  not a verified acceptance fixture or hygiene theorem.

The visibility fixture
`tests/yulang/regressions/visibility/my_act_operation_ancestry_allowed.yu:2–13`
uses qualified operation names in catch arms; it corroborates path spelling
but is not the owning expression-invocation example.

## Conditional static derivation

Oracle paths below are relative to its checkout.

1. `crates/parser/src/expr/scan.rs:243` classifies `ColonColon` as
   `ExprLedTag::PathSep`. `expr/tail.rs:84–102` emits a PathSep node and
   consumes the following identifier. Lines 351–368 define the admitted path
   segment scanner. The parser consequently has a route for `tick::ping`.
   The adjacent `()` uses CallStart/ApplyC (`scan.rs:246–248`,
   `tail.rs:103–108`), also exercised by the `note::tell()` example.
2. `crates/infer/src/lowering/expr_syntax.rs:49–73` collects an identifier
   head and successive PathSep nodes into `[tick, ping]`.
   `lowering/expr/chain.rs:104–121` detects that complete path before
   lowering its head, calling `lower_path_name_at`. Thus this route does not
   first require `tick` to be a value expression.
3. `lowering/name_ref.rs:7–37` calls `ModuleTable::value_path_at` and uses
   its resolved target. Missing/private paths have explicit error branches.
   `module_table/mod.rs:850–874` splits the path into module prefix `tick`
   and final value `ping`. `module_table/query.rs:542–598` resolves the prefix
   through lexical module lookup and imports, with visibility checks.
4. `module_map/mod.rs:1277–1299` creates the act's child companion module
   under its declared name and records it as the type companion. Lines
   1316–1342 create the operation Let DefId, install `ping` as a visible
   companion value, and register its declaring owner. Under the premises
   above, the path lookup therefore targets this declared operation DefId.
5. `module_table/mod.rs:157–164` records that DefId's `effect: owner` and
   operation name. Lines 994–1015 recover its `ModuleTypeDecl` and signature
   by that identity. `lowering/expr/block_local.rs:990–1020` retains the
   resolved reference target and schedules ApplyRefResolution; lines
   1029–1064 use the operation declaration to constrain the reference and
   record its canonical operation path. Its signature builder at 1067–1091
   forms the effect annotation with `operation_decl.effect.id`.
   `lowering/body/act.rs:94–140,168–194` supplies the corresponding declaration
   registration/signature path. This establishes the owning identity route,
   not a proof that every signature/constraint operation succeeds.

The last step distinguishes a resolved action identity from matching the
letters `tick`: the registered DefId refers to a declaring TypeDeclId. No
fresh SubtractId map, provider binder or call/output incidence is established
by this path resolution.

## Binding and returned lambda constraints

`crates/parser/src/stmt/binding.rs:58–128` parses the binding header pattern
until Equal, then its body expression. Its body accepts inline expressions
or a more-indented block (`134–155`). Named unit-argument bindings appear in
both owning examples. `expr/control.rs:198–294` parses the lambda patterns
until Arrow and an inline/indented body. The candidate includes the explicit
unit pattern and Arrow, and uses no protocol `my` binder or result annotation.

`crates/infer/src/syntax.rs:520–565` extracts ordinary lambda patterns.
`lowering/pattern.rs:919–938` constrains an empty parenthesized pattern to
the exact primitive `unit` and emits `Pat::Lit(Lit::Unit)`.
`lowering/expr/lambda.rs:20–70,244–368` recursively lowers the body in a
function frame and emits a Function value carrying the body's result/effect
ports. The lambda expression itself receives a pure effect coordinate at
351–368. This is the static route for a returned callable; compatibility of
the outer named provider, its nested callable and `f` is still an inference
obligation. No full named-binding/SCC/generalization proof was attempted.

## Coverage, independence, checks and stopping boundary

Method: serial bounded static inspection of the named grammar, registration,
resolution, lambda/pattern owners and the two expression examples. Searches
used `rg -n` on those owners, the small effect-hygiene example directory and
the examples/tests-root locators to find `log::put`; reads used `sed`/`cat`.
Several guessed source paths were absent (`parser/src/pat/group.rs`,
`infer/src/syntax/`, `lowering/body/binding.rs`, `lowering/signature.rs` and
`infer/src/signature.rs`); actual path/pattern owners were subsequently located.
No exhaustive fixture scan or unbounded source search was completed.

Evidence shares the pinned Oracle implementation with any later Oracle run.
Examples were separately authored source artifacts, but their acceptance was
not observed here and they are not an independent semantic oracle. No checker
assumes transition rules; no executable probe, build, test, mutation, seed or
input range was used. Oracle call budget consumed: **0**. No heavy processes
or parallel compute were launched. CPU time, peak RSS and exact wall time were
not measured; only short file/hash/Git-read processes ran.

`git -C /tmp/yulang2-oracle-read rev-parse HEAD` confirmed the pinned revision;
its final `git status --short` was empty. Y3 HEAD initially matched its pinned
baseline and advanced concurrently to `161886f1b63b93a3f1d08130170c509bae2feb7d`
at the final recheck. All four direct Y3 dependency hashes were unchanged.
Direct Y3 dependencies were SHA-256 checked and are listed below.
The syntax mechanism and owning expression example satisfy this packet's stop
condition. Parser execution, whole-provider acceptance, inferred schemes,
postpublication freshening, retained checks, runtime operation identity and
call/output qualification remain unverified. Original H remains OPEN.

Recommended next action: the primary may authorize one bounded Oracle
qualification of this exact candidate, within the previously remaining call
budget, requiring a nonmissing provider and no diagnostics before analyzing
call/output identity. An exit status alone does not qualify the source.

## Dependency snapshot and commit packet

| Direct Y3 dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/progress/2026-10-11-oracle-postpublication-call-probe.md` | `09ea064b0598b59414be2debc2aea9c31a2bcc831f95e4fc36a22b0a1658da96` |

- Exact leased/change path: `notes/progress/2026-10-11-oracle-operation-path-source-audit.md`; writes stop at handoff.
- Baseline: Y3 `7ebcc92a1d32bc3316e2803979c3872e5ab42046`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` with clean working tree. No dependency bytes changed by this worker.
- Claim/review status: frozen unreviewed static characterization with explicit candidate premises; no independent review or H closure claimed.
- Checks already run: named source/fixture reads, Oracle revision/clean-tree checks, direct dependency SHA-256 checks, leased-note whitespace/fence inspection. No build/test/Oracle run.
- Proposed research-checkpoint commit: `research: resolve Oracle operation path for returned callback candidate`.
- Shared-record deltas left for primary/curator: record the `tick::ping()` candidate and companion-module/DefId owner chain; keep provider and call/output qualification unverified and original H OPEN. No task/index/authority/theory-status file edited.
