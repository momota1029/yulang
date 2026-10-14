# Shallow Catch: premises of the existing hygiene proof at native owners

Date: 2026-10-15
Status: frozen research-only bounded conditional source-to-proof bridge; independent review pending
Baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`, `research/simple-sub-intrusion`
Lease: this file only; constructive leaf, no delegation or Git mutations
Parent status: H1/H2/U remain OPEN; no H3/P activation or production authority

## 1. Frozen objective, original scopes and exclusions

Reuse the existing hygiene result with its actual hypotheses, and identify
the first premise not supplied by the native source construction. This note
does not reprove that result. Governing sources are
[effects-handler-next](../../tasks/effects-handler-next.md) §§1–5;
[annotation hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5;
[contextual admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§2–4;
[typed-boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md)
§§2,6; and
[charter](../design/2026-09-29-scc-intrusion-redesign-charter.md) §§13–17,24.
Top-level inference principles §1.1 requires actual constraint generation and
reuse of established hygiene, without prior solving of an unknown formal.

The original parent U quantifies over the admitted shallow Catch source domain,
its original scopes, scrutinee and arm binders, actual provider/call paths,
raw continuations, future constraints and distinct residual constructions,
under one original scoped assignment `sigma`. Only eligible contributions
actually consumed at this Catch may disappear. Protected or unmatched
contributions, independent same-family contributions, outside-arm effects and
raw-resumption effects survive with their original dependencies and lineage.
The source domain is not restricted to direct calls or the illustrative route
below. No independently chosen provider, attachment, path or residual witness
is substituted for the original joint assignment.

The existing result is `lem:one-color-hygiene` in frozen Oracle
`a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex`,
lines 1665–1680. Its operational domain is the normalized-marker colored core,
with the guard/paint definitions at 1515–1561 and well-bracketed color invariant
at 1638–1645. The assignment imports this result exactly as established within
that domain. A bridge into native Yulang is a separate claim.

For each original static id `u`, its instance color `c_u = chi(u)`, dynamic
flow `Phi`, active guard copy with current family `H_u` and its entry snapshot
`Xi_u`, the lemma says: an operation of family `h` crossing this guard is
invisible to handlers in the same flow if `h` is outside `H_u` and its old
colors `kappa` do not intersect `Xi_u`, because the guard adds active `c_u`.
If they do intersect, it was already excepted at entry; well-bracketing keeps
that outside color active during the guard lifetime. If `h` belongs to `H_u`,
this guard leaves its colors unchanged. This last case does not guarantee
visibility through other guards, eligibility, selection or consumption.

Retain the original premises: fresh injective instance colors (same id shared
within an instance), normalized guard/push and matching pop/paint construction,
nonnegative bracketed flow, common current family of active copies, exact
entry snapshot before push, and the specified guard transformer on outcomes,
values, payloads and continuations. A snapshot of current visibility later in
execution is not the entry snapshot. The result does not identify typed paths,
construct a source boundary, select operation arms or prove full Call.

Accepted source policy: an omitted callback contract supplies protection on
its applicable typed paths and no concrete grant; transport follows matching
typed value paths and activation lifetime. The exact omitted-formal inventory
when an unknown formal is demanded as `A [Ein] -> [Eout] B` remains unselected.
This note neither chooses that inventory nor identifies `Ein`, `Eout`, nested
latent paths or Lambda entry by row equality. Generic rigid opening, complete
Call, source-global soundness/principality, general lifecycle and F5 cutover
are excluded from the claimed result, with their parent obligations retained.

## 2. Authentic source anchors and the real Argument consumer

Use the original discriminator as a source locator, not an executed program:

```yulang
act tick:
    our next: () -> int
my relay cb = catch cb() { v -> v }
my answer = relay tick::next
```

Let `L` be relay's Lambda, `C_in` its receiving call, `C_cb` the callback call,
and `H` the Catch. Preserve the original formal `cb` and value-arm binder `v`.
Relay is an ordinary Pure literal under charter §24; its Value parameter
entry is distinct from receiver role and callback protection. The value-only
Catch forwards the callback effect, so this locator is not a wrong-subtraction
counterexample or a claim of a particular inferred scheme.

Authentic HIR formation retains the parameter's source, id, scope and optional
annotation in `yu-hir/src/module/local_source.rs:385–413`, and forms actual
Catch arms/binders at `:855–887`. Native preflight
`candidate_source.rs:99–146` does not reject an omitted annotation; it retains
its current independent restrictions on operation signatures/patterns. No new
restriction is imposed here.

At the pinned baseline the following facts are supplied by real constructors:

1. `candidate_source.rs:273–284` registers the original Lambda/formal and
   recipe. `:387–394` retains `OmittedFormal` with owner, Lambda, formal,
   source position and lexical scope. The `FormalAnnotation` action at
   `:396–403` is emitted only for an actual annotation.
2. `lib.rs::admit_lambda_fact`, `:11254–11408`, creates
   `Function4(A_cb-, E_L-, R_L+, V_body+)`, admits `E_L <= R_L` and
   `E_body <= R_L`, and seeds the authentic Function/domain construction.
   `FormalConstruction` authenticates the original raw domain child and
   unknown Value row. `InferredEntryOrigin` separately records entry flow;
   it is explicitly inert and is not an `EntryCertificateId` or permission.
3. Actual Apply formation (`candidate_source.rs:602–621`) and
   `shadow_apply.rs::admit_candidate_fact`, `:1426–1522`, retain the distinct
   callee/argument, checking occurrence and four-port demand. `C_cb` passes
   Unit as argument; it does not authenticate the view received by `C_in`.
4. When a native Function comparison is dispatched, `lib.rs:12552–12584`
   constructs its actual Argument and ArgumentEffect pairs in the reversed
   direction, and Result/ResultEffect pairs in the preserved direction.
   `candidate_step_function_dispatch`, `:12699–12725`, calls
   `candidate_function_port_admit` before enqueueing each child.
   `candidate_context.rs:2777–2835` applies Swap to argument fields and
   preserves result fields, using the parent's retained post-check context.
   This is a real consumer of inherited context, not a source-profile creator.
5. The new `candidate_formal_argument_incidence`,
   `candidate_context.rs:298–377`, authenticates a bounded captured FreshUse
   route, optionally through one actual local Name handoff. It requires the
   Argument/Swap dependency, both comparison Replay bounds, exact FreshUse
   transport, original Function/domain child, and the named handoff's actual
   slot-0 Local source action. Equality only reconciles endpoints after this
   incidence has selected them. The reader has no production semantic consumer.

This advances the source anchoring available beyond the older
[reconstruction/receipt note](2026-10-15-callback-profile-reconstruction-receipt.md).
The bounded structural association is present at this baseline. It still
introduces no profile position, grant, receiver activation, Receive/Observe
witness, guard or residual eligibility. Earlier extrusion and arbitrary
alias/return paths remain outside that reader's authentication scope, not
outside the original parent domain. Dispatch and successful fallible admission
are premises of these transition characterizations; this pass did not execute
the assembled source.

## 3. Hypothesis-by-hypothesis bridge

The following rows are bridge obligations, not new hypotheses added to the
existing theorem. “Absent” means absent from these reached native constructors
and consumers; it is not a claim that no future representation can provide it.

| Original proof premise or necessary application input | Native owner/evidence | H1/H2/U disposition |
| --- | --- | --- |
| Original source boundary at an applicable typed path | OmittedFormal and FormalConstruction retain authentic source/domain identity. No omitted action constructs `b, Gamma_b` or profile incidence on any selected effect path. | H1 source anchor supplied; profile introduction absent. This is the first missing premise. |
| Actual typed route crosses that same boundary | Authentic FunctionPort/Argument and bounded FreshUse/Name incidence exist. Typed-boundary §6 requires image transport of the original profile on the same tagged paths. | H1 structural route supplied conditionally on dispatched comparison; transport of protection absent because no such profile exists. |
| Fresh injective color-instance map; same instance shares the same id | FreshUse has one per-use row/context/view map (`candidate_scheme.rs:1009–1188`). Source ids/row maps are not the original color-instance map. | H2 native maps supplied; semantic instance/bracketing correspondence conditional and unestablished. Row equality cannot create or identify boundary instances. |
| Active `c_u` in the same handler flow; matching guard/push/pop/paint | Live LocalWeight uses `[(); 0]` words (`candidate_context.rs:116–123`); SourceUnitPush is detached preparation (`:2345–2391`). | H1 executable protection absent. H2 bracketed active-copy preservation is not proved by copying these records. |
| Each active copy has the same current family `H_u = seedcap(u) intersect F_u` | Resolved nominal members and annotation-owned filters exist. No omitted profile/family projection or live guard-copy meet is constructed. | H1 family bridge absent; H2 common-family preservation conditional. No concrete grant follows from omission or equal members. |
| Snapshot `Xi_u` taken just before each guard push, excluding later inner colors | No inspected source/Function/context consumer records this dynamic snapshot or an equivalent proved native observation. Neither InferredEntryOrigin nor FormalConstruction denotes it. | Additional H1 operational-owner premise absent. Existing entry forcing is not snapshot coloring. |
| Guard adds `c_u` exactly on `h` outside `H_u` with old `kappa` disjoint from `Xi_u`; otherwise preserves colors | `candidate_context_execute_relation` (`:2964–3043`) executes identity/zero-word filter duties. `candidate_check_effect_operand` (`candidate_effect.rs:976–1015`) checks resolved member inclusion and forwards unmatched endpoints to a tail. Neither operation implements this guard judgment. | H1 consumer bridge absent. Zero stored words do not certify semantic unguardedness. |
| Guard/paint structure preserves value, payload and continuation paths | Capture retains Function children, source Bound/snapshot and reachable contexts (`candidate_scheme.rs:486–590,749–828`); reconstruction uses four child Terms (`:1173–1188`). | H2 retention of existing inputs supplied; path/profile/guard-frame preservation conditional, not established by stored constraints. |
| Same-flow visibility tests actual request colors against active flow | CandidateSourceCall authenticates native/source Apply fields but leaves receiver dispatch/complete future interfaces pending (`candidate_call.rs:81–145,224–245`). | Receive/Observe/current activity and same-flow visibility absent as native semantic suppliers. Full Call remains a separate parent; its closure is not made a prerequisite for every bounded static bridge. |
| Only visible, matched and actually consumed body contributions enter subtraction | Catch currently forwards the whole scrutinee effect and joins arm effects (`candidate_source.rs:516–530`). Plain P's membership test has no protected bypass/selection evidence. | U source-to-cut eligibility/coverage input absent; H3 remains disabled. The hygiene lemma alone does not prove consumption. |

Typed-boundary §6's existing transport theorem can already be consumed as
follows: **given** an independently supplied profile, valid correspondences,
matching receipt/observation and exact active owners under the same assignment,
composition/identity/source-union laws preserve its incidence without inventing
authority; current-scope filtering disables the expired handler/receiver's
incidence. That conditional application creates none of those inputs.

The one-color result can likewise be consumed at a genuinely realized guard:
its original family/snapshot/bracketing premises imply invisibility for the
protected operation. There is no authenticated native omitted-callback guard
instance to which this pass can apply that conclusion. The conditional
[concrete capture derivation](../progress/2026-10-05-concrete-capture-profile-derivation.md)
establishes eligibility only after an explicit profile contract and typed
incidence exist. Omission supplies no such concrete contract. The separate
[`'e?` notation](../design/2026-10-05-handler-hygiene-public-provenance-notation.md)
changes protection only after attribution and slot emission have been proved;
it supplies neither the missing profile nor a bypass/consumption premise here.

## 4. Shallow residual, future constraints and exact first missing fact

Actual Catch formation makes `S <= E_H` and `E_arm <= E_H` independently.
`candidate_catch_operation`, `candidate_effect.rs:806–865`, uses one declaration
environment for payload A and response B, original scrutinee Value V, and
fresh raw-continuation entry/return rows E/R with `E <= R` and `S <= R`.
The paired raw k Function uses response B, not payload A or Catch's result
join. Its full-S bound is conservative; it is not equality with the actual
suffix. This construction adds no handler reinstallation or residual cut.
These real type constraints retain outside arm/entry/suffix support. They do
not themselves prove runtime shallow control or full Call correspondence.

Plain P remains the separately reviewed conditional primitive. When authentically
admitted and eventually drained, its headed Allowance removes a delivered
member of J and forwards any other exact lower to gamma. Future lower/upper
coverage has actual insertion and Replay owners
(`candidate_extrusion.rs:766–809,843–876`). Replay construction transfers
children to the worklist (`candidate_context.rs:3281–3345`), whose completion
can remain Queued. Capture, freshening and qualifying parent/copy intrusion
retain/replay existing relations; they do not prove protection that was never
introduced. In particular, `candidate_intrusion.rs:511–606` merges actual
qualifying rows and replays bounds; it must not merge independent authority
or residual lineage by equal support. No all-history completion claim follows.

The first source-owned fact missing on the omitted-callback route is:

```text
At original (L, cb, position, scope), source boundary formation introduces
the required omitted-contract profile b on its applicable typed paths,
with protection and no concrete grant; that same b/path incidence is
bound to the authentic receiving-call Argument correspondence.
```

The existing D-only source/domain certificate supplies the locator for this
fact, not its meaning. The original profile's exact positional inventory is
still a decision prerequisite at that owner; this bridge does not select it.
The first native transport consumer is the real Argument/Swap relation in
`candidate_function_port_admit`, with capture/fresh-use on the same incidence.
The later operational owner must supply actual parameter-view receipt at
`C_in`, observation at `C_cb`'s complete executing view, and current activity;
matching this receipt from C_cb's callee id is invalid.

The remaining U owner is source Catch eligibility/coverage and its coupled
native context/residual consumer: establish, under the original joint
assignment, which original-body contributions are eligible and guaranteed
consumed, and route protected/independent same-family survivors to a live
bypass before the plain Allowance membership operation. Arm/default/guard and
raw-k computations remain outer contributions. Native family inclusion alone
cannot establish that disposition, even though P itself is reusable.

The proof-obligation-economy audit already applies after H1-A and the distinct
reconstruction/receipt route left this profile premise untouched. It is A/B
for required hygiene and natural inference; recovering discarded source/path
incidence from canonical ids would incur D debt. Source formation knows the
original omission/owner, and actual binding knows the received typed view.
Retain their authentic evidence at those owners once the applicable positions
are selected; do not add another profile-assuming proof, family-equivalence
checker, reconstruction calculus or source restriction. Classification and
this new crosswalk do not close the original gate.

One next action: after the omitted-formal position decision is available,
assign the original source-boundary producer and its incidence on the existing
Argument consumer a bounded coupled construction packet. Keep receipt,
observation, snapshot/bracketing correspondence and U selection/bypass as
explicit subsequent owner premises; obtain fresh independent review before
using any resulting bridge as established.

## 5. Evidence, resources and frozen commit packet

Static `git show`, narrow `rg`/`git grep`, `sed`/`nl` and read-only branch/status/
dependency comparisons were used. The Oracle theorem was read by `git show`
from `/home/momota1029/rust/yulang2-oracle-capture` at its exact pinned revision;
the historical `/tmp/yulang2-oracle-read` locator no longer exists. No network
lookup, executable semantic probe, build, test, measurement, child or Git
mutation occurred. Allocated budget: twenty-minute static pass; no heavy
processes. Independent reads briefly used up to three lightweight shell calls;
derivation/source follow-ups were sequential. CPU/peak RAM were not measured.

Requested model/effort: `gpt-6.1-sol` / `high`; actual runtime metadata is
unavailable, so observed model/effort is **unknown**. The callable role is
prover; repository prover model/effort pins are absent and agent defaults are
Sol/high. Configuration is not evidence of a live effective setting. No Astra
escalation or configuration change was made.

Unverified scope: actual execution of the illustrative source, omitted-profile
positions/introduction, all-path alias/return and earlier-extrusion incidence,
complete receipt/Call/Observe, guard/snapshot/bracketing realization, H2
preservation of those semantic inputs, U coverage/bypass and residual lifecycle,
generic rigid opening, global soundness/principality and production cutover.
Independent review remains pending. Shared task/design/theory status files
were not edited.

Dependency hashes below are SHA-256 of exact pinned bytes. All corresponding
live Yulang dependency bytes were rechecked for equality before handoff; changed
dependency hashes relative to baseline: none. Rules and current task/lab records
were read as policy/scheduling context, not replacement semantic premises.

```text
c5dfd30a4ae28a82ad50e2d23df79f6aa924af9d337b14903180839b62a53ab9  tasks/effects-handler-next.md
4389d6e67df9e1039821a70dd55f8d40e14467b437a02f52fb584ee39e85d6fc  notes/theory/2026-10-15-callback-profile-reconstruction-receipt.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a  notes/design/2026-10-10-annotation-effect-hygiene-integration.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
87c2c39bf41a8b652fb96cb3409cf9e2c5735c96e4ccfc8b7c5b7f8380ba6050  notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md
a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79  notes/progress/2026-10-05-concrete-capture-profile-derivation.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b  notes/theory/2026-10-14-native-handler-residual-cut.md
28d1d8f30a7bf4a6a80f120ed287db2b8a35ba75972eeb7c76121dd0238c0875  notes/progress/2026-10-15-omitted-formal-structural-incidence.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
664999082a17e59457f0de7cca21a0cf6be6a968285f95c5e074f320ac576015  crates/yu-solver/src/candidate_call.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  crates/yu-solver/src/lib.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  crates/yu-solver/src/candidate_extrusion.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  crates/yu-solver/src/candidate_intrusion.rs
993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1  .codex/config.toml
485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98  .codex/agents/prover.toml
efed007a3848c94f9d8925985f66e76ab86082dcb094c7ec3851b2bdd7082843  Oracle@a58eefc31e22141574b6f20c6a5748151c6d79f1:research/effect-mini-language/directed_stack_weight_letrec_complete_ja.tex
80491d935c59b0098bd0c80d9d81ba5c53771b1786a3290bd48f055a93d155aa  Oracle@a58eefc31e22141574b6f20c6a5748151c6d79f1:spec/2026-06-13-runtime-guard-markers.md
```

Commit packet: exact leased path
`notes/theory/2026-10-15-shallow-catch-hygiene-constructor-bridge.md`;
baseline `427d1ff5daab866fa7d89cb513a077063cc6454d`; changed dependency
hashes: none. Claim: bounded conditional source-to-proof bridge and exact
constructor obstruction; unreviewed research-only, no parent promotion.
Checks already run: pinned/live byte and SHA-256 equality for the 23 Yulang
dependencies above, two pinned Oracle dependency hashes, and final leased-note
whitespace/fence/newline inspection; zero tests/builds/probes/measurements.
Proposed message: `research: map shallow Catch hygiene premises to native owners`.
Shared-record deltas for primary/curator: record the bounded authentic source/
Argument incidence as supplied, but source profile introduction as first missing;
retain distinct receipt/observation/activity and guard/snapshot/bracketing
bridges, H2 preservation and U selection/bypass as OPEN. Do not mark H3/P
active or any theorem closed. No shared records were edited. Writes stop at
handoff; fresh independent review belongs to the primary.
