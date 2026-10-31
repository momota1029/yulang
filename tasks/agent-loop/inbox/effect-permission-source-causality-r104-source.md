# R104 Rust source-causality handoff — Stage-1 observation candidate

Sprint / contract: `EFFECT-PERMISSION-SOURCE-CAUSALITY/20261101-R104`,
`tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`,
SHA-256 `0f70cfbcbe18c74c2b1b6aa0130fc425261c916d2418b4e6e10251568a9357dd`.
Amendment: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v2.md`,
SHA-256 `b2fcf0ba32a2c657d59d3e468da9f7308e4edf517f4eb256b86d3be581711752`.
Amendment: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v3.md`,
SHA-256 `981a27735113601873cd3335709ac42534d0a7e7bb25f63f08b0f6eb99bb4be1`.
Assignment: R104 Rust source-causality lane; handoff revision 4, successor to
frozen revision 3 SHA-256
`4d4504ab88a462d634e6151b60a189f248e960ab7979df7e26b5fc85d05f7629`.
Parent: original effect-hygiene/source-preservation obligations and protected
R102 failures; their source domain, quantifiers and accepted effect semantics
remain unchanged.

## Runtime, role, leases and result

Requested role/model/effort: `implementer`, Luna/high. Observed model/effort:
UNKNOWN (runtime model metadata unavailable). Worker identity: `/root/r104_source_causality`;
session/launch receipt: UNKNOWN to this worker. No descendants.

Outcome class: provisional source-native evidence instrumentation. Cargo call
1/2 failed during pre-test compilation; no test ran. This handoff records the
authorized formatter repair and awaits fresh independent review before the
final call 2/2. No theorem, source/native correspondence, semantic gate, or
production gate is claimed. Two earlier candidate reviews rejected source
observation targets before execution; a later review passed the observation
invocation against the prior four source hashes, followed by the Cargo
pre-test failure below.

## Exact artifact and dependency hashes

Leased files:

- `crates/yu-solver/src/candidate_effect.rs` —
  `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`
- `crates/yu-solver/src/candidate_scheme.rs` —
  `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`
- `crates/yu-solver/src/candidate_source.rs` —
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/lib.rs` —
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- This handoff — hash reported with the frozen submission.

Direct read-only dependencies rechecked unchanged:

- `candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `candidate_receiver.rs` `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `shadow_apply.rs` `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`
- HIR `module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- root `Cargo.toml` `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- solver manifest `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

## Diff and Stage-1 evidence planned

All source/driver, live-effect constraint/propagation, diagnostic and route
instrumentation is under `cfg(test)`. No solver decisions, source domains,
expected outputs, original fixtures or existing assertions are changed.

1. Source actions log schedule/index/action plus before/after diagnostic
   occurrence, cause and kind. The shared-tail test records identities after
   root execution and after the late `E` constraint, with its late constraint
   occurrence/cause/contribution/tail. Effect-constraint entry/return,
   candidate effect-propagation result and diagnostic insertion are also
   observed at their owning boundaries.
2. Capture logs the raw effect endpoint before `intern_shape` canonicalization,
   its canonical endpoint, representative and witness list. The identical
   unequal-transport source is executed in one visible session that records
   source origin/allocated row, interned node, full effect `ParentWrite` events
   and final representative pairs in the same run. The protected `r != q`
   assertion remains unchanged.
3. The original recursive `f pair` fixture and consumer assertion remain
   unchanged. A distinct source fixture defines `f(pair) = pair`, then uses
   the existing case projection and application consumer; its returned graph,
   conflicts, Support nodes and source trace are printed. This fixture makes
   no handler/subtraction claim.
4. Each fresh route reports its own source/use/provider identity, Support
   template nodes and bounds. The trace reports Support view creation and
   source-port binding; the live session lists exact Support lower/upper rows.
   For each route Support node it joins the captured node index/original view
   and tail to `FreshRoute.retained.observe_map_entries`' exact
   `effect_operands` entry, mapped endpoint/view tail and live bounds. Missing
   retained entries or views print as absent rather than being inferred from
   row mappings. The captured tail-node index is resolved through its actual
   `Node::Row` before consulting the route row map. Captured original tail and
   fresh mapped expected tail are labeled separately, with their current
   representatives. The mapped Support view tail is compared with the mapped
   expected tail. The live mapped-tail observation includes direct lower/upper
   row lanes, exact non-variable atom lanes, reverse direct-row references and
   representative identity. A present row with empty vectors reports
   `Available(..., [])`; a missing node, route row, view or bounds slot reports
   `Unavailable(...)`.

R104 v1 review had rejected (a) the invalid `row.position` read in the
no-source-row branch, (b) missing retained `effect_operands`/fresh-use remap
evidence, and (c) the contract command hiding successful test output. R104 v2
repairs (a) using `context.position()` and explicit `row=None`, (b) adds the
exact retained map/tail/live-bound join above, and (c) authorizes `--show-output`
for the exact Cargo command. The second review accepted those three findings
but rejected the remaining mapped-tail bound evidence: it omitted direct-row
lanes/reverse references and conflated original with mapped tail labels. The
dispatcher authorized this exact in-envelope repair under R104 v2; at that
point no v3 or semantic change had been admitted. R104 v3 later admitted only
the explicit test-output formatter after Cargo call 1/2 failed to compile.

## Reused and rejected evidence; parent application

Reused the R102 independently reviewed Cargo receipt (45 passed, 5 failed, 2
ignored) and R103 reviewed Rust handoff. These establish the protected failure
locations and assertions only. Reused R103's owner map and its correction that
a failed `.all` proves at least one route lacks Support, not every route. The
R102 finite identity joins do not prove unequal transport. No source/native
result from this instrumentation has been executed.

The first missing edges remain unadjudicated pending the one Stage-1
observation call:

- Shared-tail error: R103 saw the assertion only after late `E`; it did not
  distinguish a prior root diagnostic from rejection of that contribution.
  Required evidence is exact before/after occurrence/cause/kind and action.
- Unequal transport: no source-attributed strict-level demand, qualified
  pending Parent activation and copy-side representative write has been shown.
  Required evidence is the same-run raw origin/witness → ParentWrite/merge
  chain → canonical captured node/returned port, or explicit absence.
- Provider consumer: recursive `f pair` does not return/projection-connect its
  input pair to `left`. Only the separately admitted pair-returning fixture can
  observe the existing projection/application path; handler/subtraction and
  provider completeness remain open.
- Fresh-use Support: the R102 assertion and R103 source audit establish that
  the existing assertion fails, not where a route loses Support. Required
  evidence is per-route creation → live bound storage → captured node → retained
  endpoint/tail remap, including any missing/inconsistent link.

No owner-local Stage-2 repair is evidenced yet. The Stage-1 logs will determine
whether the first lost edge belongs to an already leased effect/scheme owner.
If it is outside those owners, a new source fixture/owner is required, or an
expected semantic edge is absent, stop and return the exact owner TODO to Luna.

## Checks, budgets, provisional boundary and cleanup

The v3 formatter repair changes only test output: Support operands are rendered
from existing fields as node index, source owner/position, permitted effects,
origin identity and tail identity. Tail lookup uses `graph.nodes().position`
with `same_identity`; absent tails and unresolved tail identities have separate
labels. No `Debug` implementation or solver behavior is added.

Cargo call 1/2 used this exact command, CPU 0, 180-second timeout and unique
authorized `/dev/shm/yulang-effect-permission-source-causality-20261101-r104-target`:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1 --show-output
```

It failed before tests with exit 101: `candidate_effect.rs:3618` required
`CandidateGraphEffectOperand: Debug`, which is not implemented. Complete stdout
was 0 bytes, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`;
complete stderr was 27,612 bytes, SHA-256
`70cdafc05b6f98774466d8b5bee8d8d1afa0564de83df3d12bf9bc6648034481`, including
the compiler error, warnings and GNU time receipt. Elapsed 73.13 seconds,
maximum RSS 1,211,796 KiB, zero swaps, measured CPU 82%; the target directory
was absent after completion. No retry occurred. The full invocation is
recorded in `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`.

Before this edit, the fresh complete-component review passed for the
observation invocation against the four hashes in revision 3; its sole finding
was the stale effect hash in that handoff, corrected sequentially while source
hashes remained unchanged. The current formatter delta is not yet reviewed.
Cargo call 1/2 is spent; call 2/2 is the final permitted corrected invocation,
only after a fresh independent review and Luna's execution gate. It uses the
same locked/offline command, one CPU, 180-second timeout, 2-GiB RSS bound and
unique target capped at 8 GiB. No retry, download, fallback or later Rust
command is allowed. Aggregate budget remains 4,200 seconds. No Rust execution
log or scratch path was created by this worker.

These test-only traces are reversible source evidence, not a source/native
bridge, cutover or theorem. Falsifiers include wrong source/action identity,
raw endpoint not joined to the allocated origin/witness, missing or unrelated
ParentWrite, route remap to a different Support view/tail, and no actual
provider projection/application path. Luna owns cleanup after reviewed source
evidence replaces or retires the instrumentation.

## Mutual TODOs, next step and stop receipt

- `R104-SHARED-TAIL-OWNER`: original parent is the protected shared-tail
  source/effect failure. Stage-1 output must identify whether the first
  diagnostic is already present after root execution or added by the late `E`
  contribution. Source owner supplies exact action/constraint IDs and
  falsifier is a different first occurrence/cause/action.
- `R104-UNEQUAL-TRANSPORT-OWNER`: original parent preserves `r != q`. Stage-1
  output must join the raw endpoint/witness and strict-level demand to an actual
  qualified Parent activation and merge ParentWrite, or report the first
  absent edge. Falsifier is a different raw row, witness, source, side or
  merge chain.
- `R104-PAIR-PROVIDER-OWNER`: source owner supplies the separately admitted
  `f(pair)=pair` provider and actual projection/application route. Required
  output is the returned Support/state path or its first absent consumer edge.
  No handler/subtraction inference. Falsifier is no source return/projection
  link or a different provider occurrence.
- `R104-SUPPORT-ROUTE-OWNER`: source/effect/scheme owners supply each route's
  Support creation, live bound, capture node, retained endpoint, mapped tail
  and bound relation. Falsifier is a route/provider mismatch or missing exact
  remap entry.

Next related step: fresh independent review of this revision-4 formatter delta;
then wait for Luna's execution gate before the final Stage-1 invocation. No
expanded owner, source domain, semantics, dependency or budget is requested.

Changed repository paths: `candidate_effect.rs` and this sole handoff in this
revision; the other three leased Rust files remain frozen at their revision-3
hashes.
Generated/scratch paths: none. Worker writes stop after this frozen handoff;
no descendants remain. The handoff is provisional and pending independent
review; no commit-ready milestone, source integration or parent closure is
claimed.
