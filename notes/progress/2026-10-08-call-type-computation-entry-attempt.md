# CALL_TYPE: computed callee and retained receiver derivation attempt

Date: 2026-10-08
Baseline: `2569c0182e2c562d176c837b4d60e0ee693d8c02`
Status: research-only; compiler-referee reviewed with minor notation repair
Claim class: conditional operational derivation and bounded premise localization
Method: expand the computed-callee Bind and actual retained-entry/body-consumer branches
Exclusive lease: this note only
Semantic and implementation authority: none
Review: compiler_referee substantive PASS with one phase-boundary notation finding on pre-repair SHA-256 `6b71501a4b5a08c0b9f161bf4fce2be2aa5931f9bd7fdb1f362eee663d6cd0cc`; primary repaired the notation locally without changing claims.

## Objective and dependencies

Attempt `CALL_TYPE` for a computational callee and a receiver with retained
computation entry. Preserve every complete output and the original pending
suffix. This is a different proof slice from the prior Value-entry identity
receiver: execution of the argument here belongs to the body consumer, after
retained entry, and callee execution may suspend before receipt.

The governing sources are the pinned DAG's `CALL_REL`, `CALL_TYPE`,
`DESC_CLAUSES`, `ADMISSION_CLAUSES` and `SEM_JOINT`; typed computation core
§§3, 6, 7, 9; source contracts §§2.1–2.2, 3.5, 5; and Authoritative inferred
call views §§2–5. Source-contracts §3.2 supplies the displayed Return/Request
Bind equations; §3.3 supplies the separate admission inventory. The core is
Draft; source contracts are a reviewed conditional package whose concrete
clauses remain Draft. The call-view decision is Authoritative within its
declared formation/protection scope and supplies no completed local typing
rules.

The prior [constructive attempt](2026-10-07-call-type-local-law-constructive-attempt.md)
localizes Value-entry carrier elimination. The [rejected separation](2026-10-07-call-type-local-law-falsification.md)
does not satisfy the complete independent interpretation premise. Neither
closes this computation-entry slice. No output-membership erasure, value-entry
identity probe, or larger variant of that reduced countermodel is attempted.

Retained decisions: actual callable role and entry remain provider-owned;
source tags determine normalization; argument construction is inert; receiver
receipt precedes entry; consumers execute the designated one-layer interface;
raw resumption uses the current state. The directional source protection
decision is retained: a source upper-output seed does not back-propagate to
lower/provider effects. Provisional formal inference states, written
annotations and actual roles remain distinct. Pending comparison success
creates no source path, receiver, slot, protection or authority.

## Hypotheses and pointwise target

Fix one original `X`, its binder tree and `xi=(nu,K,D)`. Every tuple below
retains original source/provider/consumer/path witnesses at their original
scopes. State letters denote actual threaded configurations, not additional
independently selected assignments.

- `H_rel`: the stipulated ordinary Call, Return, Request, Bind, lookup,
  designated consumer and actual receiver relations, including their original
  delimiters. This is the conditionally closed `CALL_REL` premise.
- `H_joint`: one fixed independently justified interpretation satisfying the
  complete `SEM_JOINT` clauses. This note neither constructs that interpretation
  nor treats the names of its predicates as an available exhaustive clause
  list.
- `H_operand`: the original independently admitted callee computation,
  argument computation, environment and initial world. Its actual descriptor,
  carrier and provider-entry predicates are those of `H_joint`; admission is
  independent of `Q`.
- `H_slice`: the callee has the original source interface
  `Computation(E_f,F)`, and a returning branch supplies the actual closure
  whose declared parameter is `Computation(E_a,A)` and whose body is `x`.
  Closure identity and its source derivation are stipulated to select this
  branch; ordinary semantic membership is not thereby established. A known
  actual role is retained without selecting Pure/Handler from entry mode.

`H_slice` is a bounded source-derivation specialization, not a new language
rule or a claim that an admitted world with this branch exists. The universal
local target remains, for every admitted assignment at that original scope,

```text
O in (J_f >>= S_f)  =>  DescMem(R_call,O,w;xi).
```

The premises are `H_rel`, `H_joint` and `H_operand`; the slice restricts the
derivation considered. `O` is the complete observation/current-state tuple,
including the raw pending continuation when exposed. Its membership is not
defined by the source image. No hypothesis supplies a `TypedCallCert`,
complete-image `CIncl`, original attachment, licensing, an inhabited initial
world, or whole-source coverage.

## Finite structural construction

Core §6 supplies the following existing derivations at the original typed
ports, before executing any code:

```text
n_f = Normalize(Computation(E_f,F),d_f) = eliminate_p_f(d_f)
n_x = Normalize(I_x,d_x)
J_f = X[n_f] = Execute_p_f(V[d_f])
J_x = X[n_x]

S_f(f,C) = let t = Delay(J_x,original lexical references) in
             ExecuteCallable(f,t,C;original complete view)

J = J_f >>= S_f.
```

Delay construction occurs on the callee Return branch. It captures the
original lexical references and does not snapshot a store for later resume.
The argument code is neither run nor partially evaluated by construction.
This is a finite graph using references to `J_f` and `J_x`; recursion is not
unfolded.

For the selected actual receiver, core §6 gives
`Gamma_body(x)=Computation(E_a,A)`. Forwarding body `x` constructs the
designated consumer `eliminate_p_a(name x)`. Thus the relevant receiver spine
is

```text
establish actual receiver, original source boundaries and receipt;
retained entry: bind x to the same t at its declared computation view;
body: Execute_p_a(lookup x) >>= R_r.
```

`R_r` abbreviates only this closure's original remaining invocation-return
shell and delimiters. The designated consumer in this specialization is the
body's `Execute_p_a`; no second result force is inserted. An operation's
post-native-return declaration consumer is a different actual producer
expansion and is not silently identified with this closure spine.

The retained binding is operationally the same carrier `t`. Substitution of
an empty row or latent endpoint does not change entry or add another force.
Returning a latent `A` completes this consumer without eliminating `A`.
Typing the bound carrier at its declared view is a separate premise below.

## Conditional operational derivation

For each fixed original witness and current state, ordinary Bind gives:

```text
J_f(C0) = Return(f,Cf)
--------------------------------------------- Return-Bind
J(C0) = S_f(f,Cf).

J_f(C0) = Request(qf,Cq,kf)
--------------------------------------------- Request-Bind
J(C0) = Request(qf,Cq,
    (response,C') -> kf(response,C') >>= S_f).
```

These are branch reductions under `H_rel`, not equations asserting that each
computation has exactly one output. The full original witness tuple is
retained, even where notation displays only `q`, state and continuation.

On the selected returning branch, receipt and retained binding reach the
actual body state `Cb`. Lookup obtains `t` without executing it. Apply the
same two Bind clauses to its designated body consumer:

```text
Execute_p_a(t,Cb) = Return(a,Ca)
--------------------------------------------- Return-Bind
remaining receiver execution = R_r(a,Ca).

Execute_p_a(t,Cb) = Request(qa,Cq_a,ka)
--------------------------------------------- Request-Bind
remaining receiver execution = Request(qa,Cq_a,
    (response,C') -> ka(response,C') >>= R_r).
```

The first branch yields the original complete invocation-return tuple only
when its original `R_r` relation supplies that return. The second retains the
actual outstanding return shell. No unused entry Force or repeated receipt
is prepended. Repeated suspension follows by applying the same equation to
the continuation's next Request, always with the current resumed state.
Induction on the finite number of such exposed Request/Return reductions
preserves the ordered suffix. This is conditional suffix preservation, not
admission preservation or a descriptor typing induction.

| Exposed observation | Original incidence | Pending suffix |
| --- | --- | --- |
| Callee Request before returning a callable | Callee computation at `p_f` | `kf >>= S_f`; includes argument Delay construction, actual receiver receipt, retained entry, body consumer and return when reached |
| Body-consumer Request after retained binding | Actual receiver invocation at the body consumer `p_a` | `ka >>= R_r`; receipt/binding have already occurred |
| Complete invocation Return | Actual receiver completion | Original remaining shell completes; latent returned data is retained |

The first Request is part of the whole Call contribution while preceding
this receiver's activation. Its continuation mentioning `S_f` cannot give
that prefix the receiver's upper-output protection. Conversely the body
consumer runs within the actual complete receiver view. On raw resumption
of either branch, existing owner/expiry rules and current state continue to
apply; syntactic retention alone proves no active protection or authority.

## First unavailable semantic consequence

The typing proof stops before it can type the receiver branch. Independently
admitting a callee computation and evaluating it to `Return(f,Cf)` must yield
the ordinary callable/provider membership and valid current world needed by
the actual receiver rule. The first missing consequence can be stated without
inventing its predicate definition:

```text
fixed H_joint; original independently admitted J_f and C0;
J_f(C0) = Return(actual_f,Cf) with original witness w_f
---------------------------------------------------------------- missing
actual_f and Cf satisfy the fixed ordinary F/provider/world
premises for S_f at their original scope and shared assignment.
```

The conclusion refers to the existing independent predicates, not a new
`TypedCallee` atom. The source endpoint `F`, the actual closure label, and the
Return equation do not provide their semantic clauses. If `H_operand` is
read as already supplying this output consequence for every callee branch,
the displayed leaf is conditionally discharged by that stronger reading;
the source derivation of that stronger premise remains required. This note
does not claim that a complete future `SEM_JOINT` interpretation cannot
entail it.

For the callee Request branch, the companion missing consequence must type
the **composed** pending observation `Request(qf,Cq,kf >>= S_f)` and all its
independently admitted response/raw-resumption developments. Merely typing
`kf` at the callee result port does not derive typed Bind closure with its
pending invocation suffix. This is the pending version of the first proof
seam, not evidence that callee-prefix effects receive invocation protection.

Even granting those callee consequences leaves concrete later leaves:

1. The inert Delay and retained binding must satisfy the fixed whole-carrier
   predicate at the actual receiver's declared computation view and `Cb`.
2. The explicit body consumer must yield the fixed ordinary result predicate
   and world after Return, or its complete pending predicate after Request,
   with `ka >>= R_r` and every independently admitted future development.
3. The original return shell must preserve those facts at the actual outward
   state and complete tuple. Latent returned handles keep their future-use
   obligations.

These are consequence obligations, not proposed new semantic clauses.
Source contracts §2.2 explicitly requires constructor typing to keep the
descriptor filter from discarding generated observations. §3.5 assumes the
local typing lemmas. §5.3 compares fixed positive constructors with unchanged
operands; it cannot introduce these independent membership facts. Core §7's
checking erasure uses supplied inclusion, and its Function-contract statement
requires actual complete invocation satisfaction. Neither derives these
leaves from the raw transitions.

The existing premises therefore supply a finite operational proof tree, but
no instantiated ordinary descriptor/provider/world last rule at its first
computed-callee Return/pending seam. This is a bounded localization in the
inspected sources, not a complete-semantics counterexample, impossibility
theorem, globally minimal premise set, or repository-wide absence claim.
`CALL_TYPE` stays open. The prior two unsuccessful methods leave the same
independent-semantics premise open; another transition-only checker or larger
branch enumeration would not test it.

## Independence, coverage and failure conditions

No executable checker, reference implementation or Oracle is used. The
operational derivation shares the stipulated source transition equations;
it proves their stated branch consequences only. It does not independently
validate the rules, their source association, or complete semantics. The
ordinary typing predicates were not assigned arbitrary truth values.

Analytical coverage: one computed-callee derivation, one actual retained
closure body forwarding its parameter, callee Return/Request and body-consumer
Return/Request branches, plus finite repetition of the displayed pending Bind
equation. There is no finite search domain, random seed, measured sample set
or executed mutation. The table is not an exhaustive classification of every
ordinary finite-prefix constructor.

Named failure conditions for applying the reduction: an unspecified adapter,
changed actual role/entry, changed designated source port, snapshotting the
pre-resume store, replaying receipt, dropping/reordering the original suffix,
or moving the body consumer before retained entry. Inferring typing from
filtered `P_E`, comparison success, an asserted complete `CIncl`, or a
certificate containing attachment would invalidate the claimed premise
separation rather than repair it.

Unverified: independently inhabited operands/worlds; exhaustive descriptor,
carrier and history clauses and their joint realization; typed Bind
preservation; other prefix/divergence constructors; operation-native return
and post-return consumer typing; arbitrary source callee/receiver bodies;
recursive or latent returned-handle discharge; production-only Option 2
observations; original association/licensing; all-world coverage; principality;
production conformance. No approved language meaning is reopened.

Recommended next action: supply and independently justify the original
callee-computation elimination and pending Bind clauses in the
`DESC_CLAUSES`/`ADMISSION_CLAUSES`/`SEM_JOINT` dependency component, then
instantiate the two displayed callee leaves before retrying this `CALL_TYPE`
slice. This is a missing research premise, not a new user decision.

## Checks and resource use

Only source reads, read-only baseline/hash comparison, path inspection and
leased-note whitespace verification were authorized. Initial broad batched
reads were truncated; the governing sections and both prior attempts were
reread in bounded extracts. Searches were limited to the assigned design,
theory, task and progress locators; no complete repository search is claimed.

Commands/results: `git rev-parse HEAD` matched the pinned baseline at startup;
bounded `cat`/`sed`/`rg` inspected sources; Python read-only `git show BASE:path`
compared the following six dependencies with working bytes, all equal. Final
hash/whitespace and lease checks are returned in the handoff. No semantic
experiment, tests, builds, production edit, formatter, child delegation or
Git mutation ran. Only the leased note was written.

No numeric CPU/RAM/wall-time limit was supplied in the packet. Work used
lightweight source-reading processes and one sequential hash/whitespace
process; zero heavy processes or probes. Total wall time and peak memory were
not instrumented. Tool calls reported subsecond source/hash durations; no
performance claim follows.

| Frozen direct dependency | SHA-256 |
| --- | --- |
| `notes/theory/successor-proof-obligations.json` | `73696ff1a930854f1764cc1efd3b83ff26e020933cb13801883e8014adf07c27` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md` | `564deef056a8609fb570d7a4a17c33f0ee14d3d49c6eb7f87c1b1d91c3f0fa43` |
| `notes/progress/2026-10-07-call-type-local-law-falsification.md` | `9e521a9543d0f523572b8f7e2f838b1ff63063385a239d651e85287e9f89f33f` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-call-type-computation-entry-attempt.md`.
- Baseline SHA: `2569c0182e2c562d176c837b4d60e0ee693d8c02`.
- Dependency hash deltas: none at prewrite comparison; final recheck in handoff.
- Review status: compiler_referee substantive PASS. The sole minor
  phase-boundary notation issue was repaired by the primary above, with no
  claim changes; no theorem or gate closure is claimed.
- Checks already run: exact source/prior-attempt reads, six baseline byte/hash
  comparisons, leased-path absence, and targeted Normalize/executable-translation
  notation check against typed-core §§3/6.
- Proposed commit message: `research: localize computed-callee Call typing seam`.
- Shared-record deltas left for primary/curator: optionally reference the
  computed-callee elimination/pending Bind seam and the distinct retained
  body-consumer suffix; preserve open `DESC_CLAUSES`, `ADMISSION_CLAUSES`,
  `SEM_JOINT` and `CALL_TYPE`. No task, index, authority, theory, manifest,
  lockfile, another worker's path or question-board bundle was edited.

The producer froze the artifact before review. The primary closed the one
minor notation finding without changing the derivation or gate status.
