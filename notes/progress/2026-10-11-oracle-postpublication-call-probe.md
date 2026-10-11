# Oracle postpublication call probe: provider formation rejected

Date: 2026-10-11
Status: frozen, unreviewed research characterization; original H remains OPEN
Claim class: bounded failed source qualification, not a hygiene theorem or counterexample
Assigned solver baseline: `35e88c8113c9c6516e260170503bea753e4ede6`
Notes-only HEAD at start: `fbb3eec4d5744c7151da739e9cffc4a9c69eebe2`
HEAD observed before handoff: `7ebcc92a1d32bc3316e2803979c3872e5ab42046`
Oracle revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: `notes/progress/2026-10-11-oracle-postpublication-call-probe.md`
Method: one serial prebuilt Oracle dump after static binding/schedule inspection; leaf, no delegation or Git mutation

## Objective, authority and execution premises

Add one named callback provider and one later named binding calling f to the
already accepted source A. Attempt to give the nested annotation an actual
provider, postpublication use and output route. The accepted prior observation
is [generalized observation attack](2026-10-11-oracle-generalized-observation-attack.md);
the frozen [source bridge](2026-10-11-oracle-weight-source-bridge.md) establishes
that A alone has no later f use or direct same-ID right-POP producer.

Original H stays as quantified in
[global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. Governing meaning is
[annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5 and
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5. No withdrawn callback output, successor semantics or additional language
restriction is used. This packet supplies complementary source qualification;
constructive proof and independent review remain primary-owned.

Execution premises are the exact stdin bytes below and the primary-pinned
prebuilt Oracle identity. Before invocation, SHA-256 was verified against both
the prior observation note and the primary's explicit pin:
`0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58`.
The binary was rehashed after invocation and matched. Build-to-source
correspondence was supplied by the primary, not independently reconstructed.

## Binding grammar and definition schedule inspected first

Oracle paths here are relative to `/tmp/yulang2-oracle-read`.

- `crates/parser/src/stmt/binding.rs::parse_binding_from_nud_inner` parses
  the binding header pattern up to Equal, then parses its expression body.
  `crates/parser/src/expr/control.rs::parse_lambda_after_intro` (198–295)
  parses patterns up to Arrow, then an inline or indented body. Existing
  examples also use named unit-argument bindings and unit-pattern lambdas.
- `crates/infer/src/lowering/name_ref.rs::lower_name_at` (64–121) resolves
  a top-level name, allocates a fresh use coordinate, and enqueues
  ApplyRefResolution. `analysis/session/lifecycle.rs` (1092–1101) resolves
  the reference and submits UseResolved with that use's parent, target and
  coordinate.
- `scc.rs::add_use` (266–277) emits InstantiateUse for an already quantified
  target. `settle_components` (329–359) emits QuantifyComponent before
  InstantiateUse for incoming uses when a component becomes ready.
  `analysis/session/instantiate.rs::quantify_component` (14–83) generalizes,
  finalizes and installs schemes; `prepare_instantiated_use` (358–367)
  requires a Let with Some(scheme).

Thus textual order alone is not proof of postpublication instantiation.
The candidate contains an acyclic reference from observed to f, but the dump
does not expose SCC event order or the selected fresh SubtractId map. A
successful provider and normal route completion would still be needed for
the requested source-qualified complete call/output incidence.

## Exact candidate and complete bounded observation

The candidate preserves A and adds exactly these two named bindings:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
my provider() = \() -> tick.ping ()
my observed() = f provider
```

There is one named callback provider whose nested returned lambda attempts to
invoke tick.ping, and one later syntactic f application. This is a candidate
source, not an accepted tick-producing program.

Exact Bash command from `/home/momota1029/rust/yulang`:

```sh
ulimit -v 2097152
printf '%s\n' 'pub act tick:' '    pub ping: () -> ()' 'my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()' 'my provider() = \() -> tick.ping ()' 'my observed() = f provider' | timeout 20s /tmp/yulang2-oracle-read/target/debug/yulang --no-prelude --no-cache dump /dev/stdin --poly 2> >(while IFS= read -r line; do printf 'STDERR: %s\n' "$line"; done)
oracle_status=${PIPESTATUS[1]}
printf 'ORACLE_STATUS: %s\n' "$oracle_status"
```

Complete captured output (STDERR and ORACLE_STATUS are wrapper labels):

```text
roots d0:tick d2:f d3:provider d4:observed
pub d0:tick mod {
}
my d2:f: (() -> ['a] () -> ['a & [tick; 'b]] ()) -> ['b#0[tick], 'a] () = e5:(fn p0:d5:cb -> e4:(e2:(e0:r0:cb->d5:cb e1:()) e3:()))
my d3:provider: never = <missing>
my d4:observed: () -> () = e9:(fn p3:() -> e8:(e6:r1:f->d2:f e7:r2:provider->d3:provider))
detached {
  pub d1:"tick.ping": () -> [tick] () = <missing>
  d5:cb arg
}
STDERR: error: unresolved value name: tick
ORACLE_STATUS: 0
```

Oracle status was 0 and wrapper status was 0. The nonempty unresolved-name
diagnostic and missing provider make source qualification fail despite that
status. There was no timeout or signal. The tool capture was not truncated.

The explicit first-candidate rejection/unsupported stop condition applied.
No control was invoked. The planned single-change control would replace only
the provider's inner body `tick.ping ()` with `()`; it remains unexecuted.
No repaired syntax or alternative source was tried. An initial JavaScript
command-construction attempt failed before exec_command with a PIPESTATUS
interpolation ReferenceError; it launched no shell or Oracle process.

## Discriminating result and exact missing premise

| Evidence item | Bounded result |
| --- | --- |
| Produced source | Exact five lines above were submitted once. |
| f scheme observation | f retains the prior displayed nested scheme and weighted result residual `'b#0[tick]`. |
| Later syntactic f use | observed contains `e6:r1:f->d2:f` and application e8. |
| Actual generalized f instantiation | The inspected SCC/Let route supplies its operational owner; runtime instantiation event/fresh-ID map was not captured. This failed source does not qualify a complete call witness. |
| Provider identity | observed's argument reference resolves to d3:provider, but d3 has `never = <missing>`; no tick-producing provider body was formed. |
| Output residual | observed displays `() -> ()`. That observation follows a provider-lowering error and cannot establish authorized subtraction or successful provider discharge. |
| Discharge/rejection | Authentic unresolved-name diagnostic observed; annotation lower-check activation, discharge and safe nonpublication were not established. Oracle still emitted a partial dump. |
| Same authentic annotation ID | Rendered `#0` is not an observed raw SubtractId or a same-use provider/call identity certificate. No concrete provider/call/output incidence for it was established. |

The route fails before the desired effect operation can be supplied. The first
missing source premise is a successfully resolved/lowered operation reference
inside the nested provider, followed by a normally completed generalized f
instantiation and its actual fresh-ID/call/output bridge. The dump's declaration
label `"tick.ping"` does not itself license that spelling as an expression
path. Existing Oracle source examples use operation paths such as `log::put`;
this is static syntax evidence only, not a tested replacement candidate.

This is not a hygiene counterexample. It does not show removal of an
independent same-family contribution, loss of a retained check, or a accepted
incorrect lower. In particular, the apparent pure observed scheme is not an
accepted-output witness once the provider has failed. Original H and successor
production gates remain OPEN.

## Independence, coverage, resources and omissions

The executable is independent of a worker-authored transition checker, but is
the implementation whose behavior is being examined. Its dump cannot certify
its own universal hygiene. Interpretation shares the primary-supplied
executable/source correspondence and accepted prior A qualification. No
transition rules were assumed to manufacture a provider.

Coverage: exactly one candidate, once. Zero control executions, mutations,
seeds, numeric ranges, enumeration, new builds, Cargo/tests, instrumentation,
temporary source/log files, solver edits or test edits. The unused control is
not differential evidence. Searches were limited to named binding/lambda,
name-reference and SCC/instantiation owners. Some initial combined reads/search
captures were truncated and some guessed paths were absent; narrow reads of
the named owners ground the claims, and the search is not exhaustive.

Budget consumed: 1/2 Oracle invocations, strictly serial, bounded by
`timeout 20s` and `ulimit -v 2097152` (2 GiB virtual address space).
The tool returned the complete immediate result within its 0.1-second display
window; its `wall_time_seconds` is not a reliable child runtime measurement.
Precise CPU time, maximum RSS, child wall time and total reasoning wall time
were not measured. No heavy or overlapping Oracle processes were launched.

Unverified: accepted nested provider syntax, actual tick operation lowering,
runtime f freshening, raw annotation-ID correlation, projection inclusion,
retained checks or their discharge, independent contribution preservation,
generalized output hygiene, error publication safety, successor semantics,
soundness and principality. This artifact is frozen at handoff; producer
inspection is not independent review.

Recommended next action: primary assigns a new explicitly bounded source
qualification packet for the resolved operation-path owner before any further
Oracle invocation or fresh-ID incidence analysis.

## Frozen dependency snapshot

SHA-256; no dependency was edited by this worker.

| Dependency | SHA-256 |
| --- | --- |
| Oracle executable | `0afe6aa1d0d4019dd5778fec012a2ee2aad57ea6a58ac42e347c0f6199cf1e58` |
| Prior observation note | `faba92bc95ca1a46f0b45c4278a5a21a5836f3fbc62045b05227e6d3481176e9` |
| Frozen source bridge | `009cf138309389c445e2ffb8f2acb2bc143b38798e032641388d21a600342bb0` |
| Original H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Annotation policy | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Oracle parser binding.rs | `3e17d035b5009b61fe34f193ab5aac3304cc81b42c590ba7ebd4b15b0e151817` |
| Oracle parser control.rs | `0102f9e8c6ded9c03c51a71356a1532a9db8742de181d649f642ad9d325f4e5b` |
| Oracle lowering/name_ref.rs | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| Oracle scc.rs | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| Oracle session/instantiate.rs | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| Oracle session/lifecycle.rs | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |

The primary reported notes integration while this worker ran. Start and handoff
HEAD differ; integration equality and unrelated branch movement are primary
responsibilities. No meaning was changed or inferred from that movement.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-oracle-postpublication-call-probe.md`; writes stop at handoff.
- Baseline SHA: `35e88c8113c9c6516e260170503bea753e4ede6`; start notes HEAD `fbb3eec4d5744c7151da739e9cffc4a9c69eebe2`; observed handoff HEAD `7ebcc92a1d32bc3316e2803979c3872e5ab42046`.
- Changed dependency hashes: none authored; binary recheck matched the exact primary pin. Direct dependency snapshot above; no comprehensive repository/source-change audit.
- Review status: frozen, unreviewed, research-only failed source qualification; no self-certification or theorem closure.
- Checks already run: named static grammar/schedule reads, exact dependency hashes, one bounded Oracle dump (status 0 with unresolved-name diagnostic), leased-note whitespace/fence inspection. No build/test or control run.
- Proposed one-line research-checkpoint commit: `research: record failed Oracle postpublication provider qualification`.
- Shared-record deltas left for primary/curator: record candidate operation-reference rejection and first-run stop, 1/2 calls used and zero controls, retain original H and actual provider/fresh-ID/call bridge OPEN. Shared task/index/theory/authority/question records were not changed.
