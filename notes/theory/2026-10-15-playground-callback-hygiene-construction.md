# Exact playground Callback Hygiene: source derivation and native gate

Date: 2026-10-15. Status: independently reviewed conditional source derivation and necessary native consumer invariant; no native/source-supplier closure, native execution or global theorem claim.
Review: independent proof/source review accepted the finite derivation; its minor exact-excerpt transcription finding is repaired below. No semantic change.
Baseline: `58b0d3760e1dde103474179ed52b1792770c9585`.
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1` at
`/tmp/yulang-hygiene-audit-my68a_85/oracle` (read-only source, not executable evidence).
Exclusive lease: this note. Existing hygiene proofs remain unchanged.

## 1. Frozen exact claim, binders and premises

Target: Oracle `web/playground/src/main.ts:508`, preserving its original `g`, `h`, loop `i`, callback `i`, `b`, `outer`, imports and standard definitions:

```yu
// Callback effects are hygienic:
// a callback's return is not captured by g's local sub.

use std::*
use std::control::flow::*

our g h = sub:
    for i in 0..3:
        h i
    return 1

my outer = sub:
    my b = g \i -> if i == 0: return i
    println b.show
    2
outer.say
```

The two `i` binders are distinct original source binders: write their values as `i_loop` and `i_cb` only in this proof. Fix one shared `xi=(nu,K,D)` with
resolved standard `sub::return : int -> never` at both relevant requests.
Let `r_g` be this invocation of g, `H_g` its local sub activation, and `H_o`
the enclosing sub activation. The callback is the actual lambda argument of
this invocation; it is not a provider chosen independently of the h binding.

Finite required conclusion: its request at `i_cb=0` passes H_g, is consumed
by H_o, discards the pending `println b.show` and tail `2`, and leaves the
single console output `0\n`. In the control where the callback returns
normally for all four iterations (0,1,2,3), g's own `return 1` remains catchable by H_g.
This control is a separately quantified source substitution, not a request
claimed reachable after the original callback has already aborted.

Premises: ordinary resolved primitive range/equality/Display/console behavior;
selected source computation entry, sequencing and shallow handling; the exact
omitted h boundary and typed paths described below. Source inference must still
construct and preserve these premises. Neither Oracle acceptance nor native
source-to-machine correspondence is assumed proved by this note. Exclusions:
all-source soundness/principality, recursion/multishot generalization, arbitrary
stores/aliases, VM implementation, and adoption of legacy runtime carriers.

Authority: inference top-level principles §§1–3; SCC charter §§13–17;
directional inferred protection §§2–4. Reused results: typed-boundary realization
§6 composition, no-authority-creation, receiving-side consequence and current-
scope filtering; ordinary-computation package §§2–5; source-owner realization
§6 outside shallow selection; protection-only release and scoped kernel/ownership
derivations. Their full source/operational hypotheses remain explicit.

## 2. Actual standard-source expansion

Oracle `lib/std/control/flow.yu:1–5` defines:

```yu
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a
```

The operation arm discards its raw continuation. The spelling `sub`, its
wildcard annotation and family equality create no callback capture grant.
Ordinary direct input requests are handled subject to actual boundary eligibility.
Oracle `crates/infer/src/lowering/expr/block_local.rs:424–484` lowers a for
body to a lambda over the item and applies `std::control::flow::loop::for_in`.
Thus the actual body lambda captures the original h, rather than replacing h
with a new unprotected callable. `flow.yu:30–39` folds the range and invokes
that lambda under last/next/redo helpers; their arms cover loop operations,
not sub::return. Their callback annotation admits loop, not sub.

`lib/std/core/ops.yu:21` maps `..` to `range::inclusive`; `range.yu:10–11,43–67` supplies included endpoints 0 and 3.
Its fold begins by invoking the body at 0. Later work is
sequenced after that body computation. `lib/std/io/console.yu:9–13` defines
say as writing `value.show + "\n"` and println as writing its string plus newline.
These source reads ground the intended transitions; they do not prove the
successor currently resolves or executes those modules.

## 3. Constructive finite semantic derivation

At receipt of h by r_g, introduce its original omitted-contract boundary
`b_g=(r_g,h,profile,endpoints)`. The h-use `h i_loop` exposes the original
upper Function demand's output-effect position. That is the protected position;
the known callback provider's lower effect is not reverse-painted globally.
There is no explicit concrete sub grant at this h boundary.

Transport the same b_g witness along h's captured-environment path into the
for-body lambda, then through its actual invocation/observation at `h i_loop`.
Composition preserves the same receiver and witness. No-authority-creation
prevents the loop helpers or wildcard sub input from manufacturing a sub grant.
Receiving-side transport preserves this protection at H_g while r_g is live;
merely invoking the original callback does not install its callee view on the
callback body's private bindings or create an origin-based veto elsewhere.

At the first item, `i_loop=0`, ordinary h application binds `i_cb=0` and the condition is true. The callback yields one fresh request q0 for sub::return
with payload 0. Its pending continuation contains the rest of the loop,
g's `return 1`, completion of b's initializer, println and tail 2. Every
sequencing step retains that same suffix by request-bind; none executes it.

| Search point for this same q0/xi | Required evidence | Derived action |
| --- | --- | --- |
| Loop helper handlers inside H_g | No exact sub::return arm. | Forward unchanged request/suffix. |
| H_g while r_g is active | Transported b_g protection; no receiver-local sub grant. | H_g is ineligible although its return arm has the same exact operation/type. Forward. |
| H_o after search has crossed g's activation | r_g is no longer active at this candidate. Current-scope filtering disables b_g incidence. The request is an ordinary request from H_o's body; no other applicable protection is introduced in this fixed derivation. | H_o is visible and its unconditional return arm matches payload 0. |

Outside selection exits H_o and evaluates its arm to 0. Because that arm does not invoke k, every pending suffix/forwarding wrapper stays unexecuted;
in particular neither println nor tail 2 runs. The binding outer receives 0;
outer.say performs the one write `0\n` by the console definition.

In the normal-callback control all h calls return, and the fold reaches g's
own q1=`return 1`. q1 is a distinct direct-body contribution: no h CallView
observes it and b_g has no incidence on it. H_g's exact return arm is therefore
visible and discards q1's continuation, yielding 1 locally. A protection bit on
the whole g effect row would incorrectly conflate q0 and q1.

This derives the exact trace within the selected source semantics with its
explicit typed-boundary premise. It consumes existing transport/lifetime and
shallow-control results; it is not a fresh universal hygiene proof or a proof
that native constructors emit that premise for this program.

## 4. Decisive native obstruction and required owner change

The current kernel can represent the local difference between a protected h
contribution and an independent direct-body contribution. At an authentic h
demand, `candidate_context.rs:2989–3002` projects StampInput(u_h) on AE and
ProtectBody(s_h,u_h) on RE. For a genuine callback-body q0 with u_h absent,
that operation adds s_h. Ordered replay and injective FreshUse preserve it.
This is useful algebra once the actual captured-h source route is supplied.

It does **not** yet supply the decisive consumer/expiry invariant. In
`candidate_context_seed:2864–2883`, the protection scope is the computation
scope of the original h-use, while an Apply slot-2 release names the scope
of that Apply's **argument expression**. At the outer `g (lambda)` call,
the argument is the callback lambda, not the original `h i_loop` computation.
Those are distinct source occurrences and original scope allocations in
`candidate_source.rs::Plan::computation_scope:62`. Injective FreshUse does
not equate them. Thus the existing rule gives Release(s_lambda), not an
established Release(s_h) when search crosses r_g. This is a constructor
identity mismatch to a proposed automatic-expiry argument, not an executed
native-source counterexample: the exact program is not admitted by this carrier.

Minimal consumer obstruction: with unchanged request state containing s_h,
the same operation/payload must forward at H_g and be consumed at H_o. A
consumer using only family/type row and global `protections nonempty` cannot
make both decisions. It needs the actual candidate receiver/activity relation,
or a separately proved source-owned boundary-release construction equivalent
for these crossings. Releasing every scope on exit would destroy independent
protections. Source names, static Lambda IDs and row equality cannot replace
original receiver instances; repeated invocations must preserve their distinction.

Required executable handoff, before enabling a residual cut:

| Owning implementation seam | Exact required output/consumer invariant |
| --- | --- |
| Source for lowering and module resolution | Preserve this real for expansion, captured h identity, standard operation identity and primitive dependencies. At the pinned baseline LocalSource has no For form (`local_source.rs:123`), rejects unhandled syntax (`:793`), and requires an explicit else (`:931`). A transformed substitute is insufficient to claim the exact sample runs. |
| Original h binding/use and capture/FreshUse | Bind protection to this received h view and its receiver instance; retain it along the loop lambda's environment and actual complete h CallView. Keep direct q1 separate. |
| Catch formation and candidate-specific request consumer | For q0 establish protected/no-grant at H_g and inactive-b_g at H_o using the same request, xi and source witness. Match exact return operation; consume only the accepted original contribution, preserve independent survivors and outer effects. Existing `candidate_effect.rs::candidate_check_effect_operand` only tests family membership and has no such consumer. |
| Shallow evaluator/core/backend | Forward q0 with its suffix; H_o's discarding arm must prevent all suffix effects. `crates/yu-backend-vm/src/lib.rs` is presently a boundary comment, not an evaluator. |

No new runtime representation is selected here. The exact missing controlling premise is **source receiver-instance lifetime realized at the reached handler consumer**, joined to the captured h witness. The scoped kernel alone cannot
derive it. This is A/B correctness/required behavior; reconstructing it from
merged rows would incur D debt. Do not repeat family-only P proofs or the
failed raw-template probe; work at binding, lifetime and Catch consumer owners.

## 5. Freeze and commit packet

Checks: bounded source reads and SHA-256 snapshots; no tests, builds, probes, semantic executions, network, Git mutations or delegation. One leaf, <=12-minute budget; CPU/RAM not measured. Requested inherited Sol/high; observed runtime metadata unknown. Independent finite derivation review accepted; original global gates stay OPEN.

Dependency SHA-256 (Oracle paths relative to frozen root O; native to repository):
```text
baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90  O/web/playground/src/main.ts
8800b16df70d6df4cf45f652bebc57cd9a0428dcd3849a1d852e0a2546a331d8  O/lib/std/control/flow.yu
a7c341ebac7cf7f43a0e548da92fb06caf731f6691f1053abf9498cb1f066f7a  O/lib/std/data/range.yu
e822e1ba32abd4147179ef580bfcecaeb28027e514d368bda057a6953f88cbd3  O/lib/std/data/fold.yu
cb2c15eca2803a6b5a65e33541dd1213bd5f985c470a7767c17a4d59f77ca8c0  O/lib/std/core/ops.yu
661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898  O/crates/infer/src/lowering/expr/block_local.rs
37e95b1e3b744e5824268f46022b8544f9aeaad8f7532733ad074aef61598a93  O/lib/std/io/console.yu
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917  notes/design/2026-10-02-ordinary-computation-semantics-package.md
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa  notes/design/2026-10-02-typed-source-owner-realization.md
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
f4120e2c828695bb5ca5adcc86e05cc7eb1199b6ba9e926daf4aa69e9e0804da  crates/yu-solver/src/candidate_source.rs
72bdca0b4e81d587966e695bfaacef31fcc9c91e5fe67e94c9538b066fb79a86  crates/yu-solver/src/candidate_context.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
7a52b6e5f77b6f1c8ba9f590c4327a151381cfe254fc52c843a6421189666ad5  crates/yu-backend-vm/src/lib.rs
```

Exact lease: `notes/theory/2026-10-15-playground-callback-hygiene-construction.md`.
Baseline SHA: `58b0d3760e1dde103474179ed52b1792770c9585`. Pinned bytes/hash checks pass; live dependencies changed during freeze and are not audited here:
`crates/yu-hir/src/module/local_source.rs` now `bfd2d79347d80481c5b15cc93be62006fabbcd21762a8635a1897efac3e7b51c`; `crates/yu-solver/src/candidate_source.rs` now `6b2fb6acedfa670d323a65fc7819d72bfab7cb8d6a5207496bf61909926fbef9`.
Proposed message: `research: derive exact playground callback return crossing`.
Shared-record delta for primary/curator: retain exact-sample inference/runtime
OPEN; add source receiver-instance expiry at the Catch consumer as the decisive
kernel-to-behavior bridge. One next action: assign that coupled construction
with this exact program and normal-callback control; review before subtraction.
