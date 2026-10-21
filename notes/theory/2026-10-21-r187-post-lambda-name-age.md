# R187 — post-Lambda age, historical groups, and an older local bridge

Revision 1. Author: `/root/r187_post_lambda_age_proof`.
Class: **candidate local proof and source-derived candidate falsifier**.
All original parent/A/B, source/native, `R183-FRONTIER-COVERAGE-1`,
`R186-POST-LAMBDA-NAME-AGE-1` and production gates remain **OPEN**.
No theorem or counterexample is independently certified here.

## Parent, authority, and actual progress

The unchanged original parent is
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1,6–7,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
For EACH authentic provider use i the required native inclusion remains

```text
e_A <= mu_i(e_t) <= mu_i(e_n) <= mu_i(e_R) <= e_C <= e_out.
```

Keep the original shared satisfying assignment xi, original declarations and
formals, open incoming E, all finite chains/prefixes, repetitions/simultaneous
entries, alternatives, independent protections, pending ordinary matching,
guards/value-arm computation and typed raw resumptions. F1, FK1 and foreign
continuations retain their separate quantifiers. No static inequality supplies
a runtime entry, receipt, observation or handler grant. Group remains in the
accepted language but is outside §1's exact whole-actual-argument-as-resolved-
Name fragment; `R186-GROUP-SAME-USE-1` stays separate and OPEN.

R187 contract rev2, SHA-256
`b34c47bb9714f34eb274179dc77bdeeb265585c68091e40a9fbe3ebc732db7ff`,
and Luna's activated assignment govern this leaf. Baseline:
`d314168e12e2e5138c7d45f84767f5e6eb39edbc`. The prospective header alone
does not activate a lane. Luna's current assignment and this leaf's launch
acknowledgement establish actual work; requested Sol/high, observed UNKNOWN.
During work Luna sequentially repaired the implementation contract. The later
observed sprint rev5 hash is
`bff3b6236818754d17ee5f3ae11f668a98b259400d13ee027208a991af613b01`.
Its baseline, proof paragraph, output paths and 1200-second proof grant are
unchanged; current state explicitly retains the proof lane's original grant.
All 50 current manifest byte hashes match the same committed baseline. This
does not claim implementation-review acceptance or code activation.

Before: R186 established only first-construction joint Value/Name compensation.
After: a fresh post-Lambda negative demand traversal also compensates when
its actual upper-owner suffix is present; historical-group reuse need not
traverse that suffix. More decisively, inserting a completed older local
bridge gives a new whole-Name candidate loss without Group. This changes the
discriminating source input rather than repeating a connected-row argument.
Its full emitted-fiber/source qualification remains a concrete evidence TODO.

## 1. Source order and the fresh post-Lambda case

Within one successful original source schedule, each formal Name in a Lambda
body is planned before that Lambda's action. `candidate_source.rs:981` puts
Finish below all child Visits; `:1003–1005` visits both Apply children before
its Finish; `:1048` visits the Lambda body; `:1293–1304` emits its formal Name
action; `:1482–1498` emits Lambda after the body. The executor advances its
action cursor only after successful execution (`:1727–1729`). A Local use
instead invokes Capture/FreshUse (`:1761`, scheme `:2025–2057`); it does not
rerun the original Name action. Thus a later exposure of THIS already emitted
Name is propagation, copying or reuse, not a new late original Name action.
This is a source-schedule fact, not a theorem about every later row frontier.

Here is an exact useful local case. Let D be one authentic forwarding demand
with AE=n and invocation RE=c. Suppose its provider Lambda r already exists,
and the current canonical graph has the finite source suffix

```text
c=q_0 <= q_1 <= ... <= q_j=r
```

with each corresponding physical upper key at q_i, and all these rows above
the extrusion target k. A NEW negative extrusion of D reverses Function AE
and preserves Function RE polarity: it visits n positively and c negatively
(`candidate_extrusion.rs:229–258`). At each negative row visit it snapshots
and visits all upper keys (`:99–106,129–167`). Induction on this finite path,
with row memoization terminating cycles (`:80–96,124–125`), visits every q_i
and records its actual parent/copy pair in this SAME occurrence. If this
occurrence qualifies and finishes settling, `candidate_intrusion.rs:324–355,
568–594,666–691` merges those pairs and lowers canonical r to at most k.
At Capture boundary b>=k, r is shared, and its future source suffix reaches
the same r used by this provider instance. R186's common-map restoration
argument then applies, retaining its successful admission/two-input premises.
Here Capture must occur after the completed settling just described. A use
that already copied r before the event needs its own correspondence; lowering
the original later does not silently update a preexisting FreshUse image.

Apply this to an unchanged equal-age completed direct Apply body: Apply slot
2 emits c<=q (`shadow_apply.rs:2456–2461`); Lambda slot 4 emits q<=r
(`lib.rs:11373–11422`). At their fresh equal levels those are upper-owner
keys (`candidate_extrusion.rs:946–969`). A fresh later traversal sees r, unlike
the pre-Lambda traversal in R186. Ordinary Catch scrutinee/arm and Block-final
effect emissions supply longer suffixes at their actual owners
(`candidate_source.rs:1184–1199,1501–1513`). For those longer paths the stated
physical-key premise must still be checked; mere logical connectivity is
insufficient. This lemma is candidate local evidence, not the universal age
induction: an older stop or a different physical owner can invalidate its
premise, without invalidating the original parent obligation.

## 2. Why historical-group reuse needs different evidence

`recapture_candidate_extrusion` does not perform the traversal just proved.
It finds groups by the reused dispatch output and original comparison,
retains a new source association, and activates the OLD `[start,end)` pair
range (`candidate_intrusion.rs:388–418`). `lib.rs:12525–12537` then enqueues
the retained rewritten comparison. A return or suffix allocated/admitted
after that original range was frozen is not added by this function.

Therefore a pre-Lambda unqualified group later activated after Lambda cannot
be assumed to contain the new r merely because c<=q<=r now exists. Joint
Value lowering AFTER allocation also does not retroactively rerun
`admit_lambda_fact:11357–11370`. This identifies an exact failure in the
proposed induction method, not an authentic emitted counterexample: a real
source must still supply that old group, later qualifying source association,
actual retained output, and BOTH ordered Replay inputs. Source SCC membership
is fixed by `candidate_value_graph.rs:217–243`; it cannot be toggled later to
manufacture qualification. No such source-qualified historical reuse loss is
claimed here.

## 3. A different whole-Name source discriminator

Use R186's finite Catch/finish source plan with one added earlier local:

```yu
act signal:
    our ping: () -> int
my finish (x:[signal] int) = x
my outer (t:[signal] int) = {
    my bridge (x:[signal] int) = outer x;
    my relay (u:[signal] int) = bridge u;
    catch t { signal::ping(), _ -> relay t, v -> finish t }
}
```

This is a manually derived retained source construction, not a compiler run.
Every displayed forwarding actual is a bare resolved formal Name. It introduces
no Group or higher-order/field interface. The Catch value arm retains the
finite terminal `finish t` branch; the cycle alone is not terminal evidence.

HIR retains original local parameter/annotation identities and ordered binding
initializers (`yu-hir/src/module/local_source.rs:638–669,1385–1479`), resolves
the Names (`:1056–1089`), constructs actual Apply children (`:941–985`) and
Catch arms (`:1170–1240`). Native source scheduling installs bridge after its
initializer and before relay's initializer (`candidate_source.rs:1050–1057,
1126–1160`); a later Name bridge takes Action::Local, not an active-initializer
Link (`:1318–1325`).
The scoped local-callee authenticator checks the same source local, scheme
slot and authentic retained route (`candidate_call.rs:689–739`). Its rejection
of a binding-level annotation is distinct from these formal annotations;
this construction has no binding-level annotation or wrapped callee.

The selected Value graph has outer→relay→bridge→outer. The local initializer
owners and Name edges are actual constructions
(`candidate_value_graph.rs:93–155`); bridge's `outer x` event has origin
bridge and receiver outer (`:192–207`). Consequently that event qualifies in
the sealed source Value SCC. This uses no type-row SCC or unrelated event.

### 3.1 Earlier bridge: apply R186 only within its premises

Both local initializers start at level 2 with publication boundary 1; outer's
active module root is level 1. For bridge's body `outer x`, the R186 bare-Name
argument applies verbatim: a negative demand extrusion to the older root
visits BOTH original Value V_x and Name effect n_x positively. Its qualifying
completed group lowers those two to 1. Bridge Lambda then allocates r_b at
current V_x level 1, while its registered entry t_b remains at 2. This is the
already scoped R186 compensation, not a fresh universal assumption.

Bridge's first authentic local FreshUse in relay's body occurs at level 2.
Capture at boundary 1 retains t_b<=shared n_x and shares V_x and r_b.
`prepare_candidate_fresh_use:1611–1623` reconstructs one image per canonical
row, so that use has the Function ports

```text
argument = shared V_x (level 1)
AE       = fresh t_b^v (level 2), with t_b^v <= shared n_x
RE       = shared r_b (level 1)
```

Its local root and Name occurrence remain at use level 2. This is a completed
local route, rather than R186's original older module root comparison.

### 3.2 Relay: an older port does not imply an older callee root

Write t_u,n_u,V_u for relay's registration, Name effect and Value parameter,
c_u for its invocation row, q_u for its body Apply effect, and r_u for its
Lambda return. These start at 2. The source Apply constructs its actual
NegativeFunction using V_u,n_u,c_u and body result
(`shadow_apply.rs:2333–2405`), admits slot 0 and then c_u<=q_u
(`:2408–2422,2456–2461`).

The proposed local route compares bridge's reconstructed positive Function
to this negative Function at level 2. `lib.rs:12573–12606` negatively extrudes
a demand only when its lower endpoint is a receiving ValueRow; it does not
take that branch for Function<=Function. Direct Function dispatch emits its
four actual field comparisons (`:12667–12695`), including

```text
V_u <= shared V_x
n_u <= t_b^v
shared r_b <= c_u.
```

Candidate row<=row admission stores/replays bounds; it does not age V_u
(`candidate_extrusion.rs:914–969`). Structural Int comparisons introduce no
row copies. Even though relay→bridge qualifies, qualification creates no
parent/copy pair by itself. Thus the candidate history leaves V_u at 2, and
relay Lambda allocates r_u at 2. Its original source suffix is
shared r_b<=c_u<=q_u<=r_u.

At relay Capture, the predicted physical effect keys are:

| Owner | Side and item |
| --- | --- |
| t_u, local 2 | upper n_u |
| n_u, local 2 | upper t_u and t_b^v |
| t_b^v, local 2 | upper shared n_x |
| c_u, local 2 | lower shared r_b; upper q_u |
| q_u, local 2 | upper r_u |
| r_u, local 2 | no key reaching c_u or q_u |

Capture follows the first three local owners and stops at n_x. It also reaches
r_u as the Function's RE child, but r_u has no key to q_u. Neither c_u nor q_u
is a Function child. This is the proposed missing suffix at the SAME relay use,
despite all forwarding actuals being bare Names.

The inspected extra channels do not automatically supply it. Both formals
are explicitly annotated, so the omitted-formal ScopedDemand supplier is
absent (`shadow_apply.rs:2378–2393`, context `:3324–3329`). Capture enumerates
physical local bounds, actual context payload weights and actual scoped
demands (`scheme:1067–1145,1272–1305`). It does not traverse the entire
dependency DAG as a type graph. These row/row contexts have identity weights
(`context:3291–3297`); Function port dependencies preserve provenance, not
unlisted Function children (`:3428–3491`). Evidence import only interns the
captured snapshot (`:1799–1800`). Owned regions remap retained scope/input
inventory, not every hidden effect row. A full emitted-fiber audit is still
required before treating this absence as certified source qualification.

### 3.3 Same-use interpretation and parent application

Outer's later `relay t` creates a NEW relay FreshUse at level 1. The predicted
Capture copies t_u,n_u,t_b^v,r_u consistently, keeps n_x shared, and restores
the captured prefix. Its local return image r_u^w has no restored suffix.
All original later outer/body constraints continue to reach original r_u.
They do not equate r_u^w with r_u. The actual relay comparison supplies
e_A<=t_u^w and r_u^w<=e_C<=e_out, with its own two Replay parents.

A finite candidate interpretation sets the named original nonpure dependency
effect rows, shared n_x/r_b and copied prefix t_u^w,n_u^w,(t_b^v)^w to {m},
and sets r_u^w plus THIS relay invocation/output to empty. Pure evaluation
rows remain empty. The original suffix and bridge's own same-use compensation
hold. All listed relay copied constraints hold, but

```text
mu_relay(n_u) = {m}  is not <=  mu_relay(r_u) = empty.
```

This is a countermodel to closure from the enumerated candidate graph, not a
reported native result or a certified complete model of every emitted fiber.
It places the loss at a particular whole-Name use and avoids R186 Group's
domain exclusion. The source theorem in parent §3 is not refuted; its native
realization premise remains OPEN. The universal age claim likewise remains
OPEN: the new construction shows that proving only direct negative-exposure
compensation would leave an older-local routing seam unaudited.

## 4. Exact next evidence, provenance and STOP

**R187-OLDER-LOCAL-SAME-USE-1 / Luna source/evidence owner.** Authenticate the
source above at bridge's qualifying first extrusion, bridge's local use in
relay, relay Lambda/Capture and the actual later relay use. Required readback:
original source/formal/Value identities; both callee root levels; all four
reconstructed bridge ports; exact pending parent groups and settled levels;
relay's V_u and r_u allocation levels; every reached Capture row/bound/context
payload/scoped demand; same-use reconstruction map; and BOTH ordered Replay
inputs/completed comparison for relay. Falsifier of the candidate: an actual
pair lowers relay V_u/r_u, or Capture/restoration reaches c_u/q_u or another
finite authentic mapped suffix to r_u^w. Falsifier of the proposed coverage
claim: the full emitted history has the table above and the displayed model
survives all actual mapped constraints. Never use a synthetic transition or
one Replay ancestor as source authentication.

If execution evidence is necessary, the minimal **provisional TODO only** is
passive readback at the existing `admit_candidate_fact`,
`retain_extrusion_parent/recapture_candidate_extrusion/merge_candidate_rows`,
`admit_lambda_fact`, `route_candidate_local_run`, `Capture::row/expand_row`,
`prepare_candidate_fresh_use` and `candidate_context_begin_replay` owners.
Preserve inference and record real operands/completions; Luna owns exact code
leases, authorization, execution and cleanup. This packet authorizes no code.

**R186-POST-LAMBDA-NAME-AGE-1 / Luna proof owner.** The fresh traversal case
in §1 is available under its exact owner-key premise. Remaining coverage is
old-group activation, preexisting older cuts, aliases/current/reuse and actual
per-use suffix restoration. The older-local input is a concrete next
discriminator, not a renamed conditional theorem. Group remains separate.

Direct documentary dependencies, verified over bytes:

- R186 note, author `/root/r186_positive_name_emission`:
  `84a235ad62c8ee980c3d71f96bf24496d4e9941ea13d4bca2c33eee44bc0a4ae`;
  handoff `8776b1a2cf3bb7777479c2eb165b00221d526ba4b6fd6409c9909b93c0748a2d`.
- R186 closeout, Luna:
  `2f82f1c08deb5ce3bcc3c6ebe5671d966527039eefa8a47e6f99ef83fc5d92c2`.
- R185 local note, author `/root/r185_source_history_proof`:
  `8e102bfa1badaba2578eaef3cf6e76100d52bdb9b312b22e2368dbc570c47161`.
- R185 admission note, author `/root/r185_admission_frontier_bridge`:
  `929390664ca527725661fbc434c4a24d5d64d37db6f718a436a92e17dc8ce780`.
- Inference principles:
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.

Only eleven committed source blobs were semantically inspected/searched; every
hash matched R187's manifest. They are candidate_source, candidate_scheme,
candidate_extrusion, candidate_intrusion, candidate_value_graph, lib,
shadow_apply, candidate_context, candidate_effect, candidate_call, and HIR local_source.
Source modes are the frozen contract's `100644` evidence, not remeasured here.
The remaining 39 manifest blobs received byte/hash checks only, not semantic
coverage. No additional source domain or dependency was introduced.
No dirty compiler or external Yulang2 worktree bytes were read. Source authors
UNKNOWN. R183 is reused only through the stated R186 common-map premises;
its differing candidate source bytes are not current evidence.

Checks: committed-byte/document hashes, static source/action/polarity/physical-
owner reasoning and manual row algebra. Zero tests, builds, compiler/sample
runs, probes, network, Git mutations, production edits or descendants.
Read-only `git show` extracted only exact authorized baseline source blobs.
No scratch paths. Every Simple-sub generation, accumulation, propagation,
level, extrusion, qualifying intrusion and generalization rule is preserved.

Requested `gpt-6.1-sol`/high; observed model/effort UNKNOWN/UNKNOWN. Actual
worker `/root/r187_post_lambda_age_proof`; host session identifier UNKNOWN.
Launch receipt: Luna's activated NEW_TASK and this worker's acknowledgement.
First observed clock 2026-10-20 21:04:09 UTC. Grant 1200 seconds, no renewal;
full launch elapsed UNKNOWN, so charge full 1200 and return 0 conservatively.
Final observed freeze clock/elapsed and actual byte hashes are returned in the
handoff/message. This worker alone authors both outputs and cannot review them.

Only new paths are this note and
`tasks/agent-loop/inbox/20261021-r187-proof-result.md`.
**FROZEN revision 1 after final hashing; writes STOPPED.** No descendant or
background writer. Fresh review, adjudication, state/Git and any lease transfer
belong to Luna. No further work runs while awaiting intake.
