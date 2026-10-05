# Exact nested-block candidate: conditional typed-core derivation

Date: 2026-10-06
Status: frozen conditional derivation; unreviewed research checkpoint; no implementation authority
Baseline: `81ceae2804d66142245384db298b8dfb3d0813a8`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: static constructive derivation using existing core constructors

## Objective and authority

Derive the structural core for exactly:

```text
my apply f = { my step x = f x; step }
```

The Authoritative nested-block addendum §§1–4, approved
`nested-block-function-source-realization/q1 a1` and its receipt fix sequential
local binding, final-expression function value, lexical resolution, and retained
outer `f` capture across later calls. These are selected source decisions,
not hypotheses this note attempts to infer from a model. The receipt records
integration at `a6bdcf99fba35497cf1323c70101e34669a3ba71`.

The approved `function-call-view-formation/q1 a2`, its receipt (integration
`61a3651376166346a5baa03ec6679c310b0edbdb`), and the Authoritative call-view
document §§1–5 retain the provisional protected Handler view, ordinary-value
resolution, comparison-independent admission, and correlated evidence. Those
directions do not yet supply their generating judgments.

F5 §§19–21,41 supplies the one-identifier-formal header contract. Syntax
architecture clauses at 4573–4588, 5327–5341, 6415–6432, 6600–6620 and
11090–11229 supply expression application, canonical Statement composition,
brace ownership and the semantic deferral narrowed by the addendum. F5's
restricted HIR/constraint recipe does not elaborate this composite candidate.
The two prior source-registration audits are retained characterization inputs;
their earlier missing block-meaning premise is now resolved only in the
addendum's exact scope. Their production limitations and open typed bridge
are not rerun or silently promoted.

Typed computation-core §§2–3,6,9 is **Draft**, with scoped reviewed
derivation-indexed results. It supplies the candidate proof constructors and
translation used conditionally here, not additional source authority. The
Authoritative result-synthesis choice §§1–2 and charter §21 fix forwarding and
ordinary unannotated parameter entry. No registration rule, generalization
algorithm, allocation strategy or production acceptance is selected below.

## Claim classes and premises

**Established decisions:** the exact source meaning and ordinary parameter
roles just cited. **Bounded characterization:** the prior audits' grammatical
composition and implementation observations, at their recorded revisions.
**Conditional result of this note:** given a finite admissible typed decoration
of this candidate, its existing-core term and local return calculation below
follow. **Unestablished:** generation of that decoration, general source
adequacy, principality, production conformance and inference replacement.

Let `d_f`, `d_x`, `d_step` be distinct lexical binders; let `u_f`, `u_x`,
`u_step` and `c` be the two inner names, final name and application occurrence.
The approved lexical map is
`u_f -> d_f`, `u_x -> d_x`, `u_step -> d_step`.
These are source labels, not a proposed allocation of production HIR IDs.
Each formal is ordinal zero in its own header; common spelling or ordinal
does not identify the two declarations.

The exact conditional premise is the existence of one finite typed decoration
`Delta` satisfying **T1–T4**, independently of the pending comparison `Q`:

1. **T1 — admitted ordinary-core instance.** `Delta` respects the fixed
   lexical map and source interfaces. Its two ordinary parameters generate
   `P_f=Value(A_f)` and `P_x=Value(A_x)`; body environments contain their
   rebound values. Local closure introduction and result binding admit the
   existing core rules. Required checking/conversion evidence, if any, is
   already supplied with its original source boundaries. No unsupported
   conversion is added to make this derivation work.
2. **T2 — complete typed call.** At `c`, the callee result has an admitted
   Function interface and the **whole** argument `Comp(empty,A_x)` satisfies
   its parameter/receipt contract. Typed paths, `Flow`, source origins,
   owner/receiver incidences, static `beta`/`Slots(beta)`, profiles and
   constraints are generated from this source component. Admission and
   protection evidence exist before and independently of `Q`; neither the
   Function shape nor the lexical map generates them. The provisional fully
   protected Handler seed and its ordinary-value determination use the same
   inferred formal/use interface, preserve annotation absence, and retain
   actual supplied callable roles/entries. The required two-stage judgment
   remains an assumption, not a rule proposed by this note.
3. **T3 — capture and evidence transport.** Constructing and returning the
   local closure retains the value of `d_f` from the enclosing `apply`
   activation and its admissible typed correspondence/evidence. Its later
   lookup and call use that captured instance. Transport preserves original
   slot identity, annotation absence, scope, receipts, profiles and correlated
   `nu,K,D`; it creates no new grant, receiver or protection fact. A static
   binder can have several dynamic activations: the correspondence must retain
   `(d_f, alpha_apply)`, not accidentally look up another activation's `f`.
   Static lexical identity and later-call capture are approved; this typed
   transport/lifetime realization is still conditional.
4. **T4 — coherent candidate translation.** The existing `V/X`, ordinary
   bind/return and same-context delay/force laws apply to this typed instance.
   Closure construction and data lookup are inert; environment extension
   preserves the captured descriptor and evidence. Any administrative
   contraction preserves typed paths and the current view and crosses no
   receipt, handler or return delimiter. This assumes the Draft core's scoped
   construction, not a proof that production lowering implements it.

For later principality/source-adequacy claims, further premises are needed:
the generating judgments produce the required most general completed
contracts/profiles and residual constraints; local generalization and use
instantiation retain the captured dependencies and source positions; complete
call images, admissible future challenges and production membership satisfy
the approved joint containment law. **None of these additional premises is
needed to write the conditional term; none is discharged by writing it.**

## Constructive derivation

Work under `Gamma_f = Gamma_0[d_f:Value(A_f)]` and
`Gamma_fx = Gamma_f[d_x:Value(A_x)]`. The outer environment is unrelated to
recursive references to `apply`; this candidate uses none. Parameter entry
owns the rebound value before its body; it is not executed by constructing
the closure.

The existing name, call, closure and bind rules yield:

```text
Gamma_fx |- result(name d_f) : Comp(empty,A_f)
Gamma_fx |- result(name d_x) : Comp(empty,A_x)

C = call(result(name d_f), result(name d_x))
Gamma_fx |- C : Comp(E_c,A_c)                         [T2]

S = lambda(P_x,C)
A_s = Fun(P_x,Comp(E_c,A_c))
Gamma_f |- S : Value(A_s)                            [T1,T3]
Gamma_f |- result(S) : Comp(empty,A_s)

Gamma_fs = Gamma_f[d_step:Value(A_s)]
Gamma_fs |- result(name d_step) : Comp(empty,A_s)

B = bind(d_step,result(S),result(name d_step))
Gamma_f |- B : Comp(E_b,A_s)                         [T1,T4]

L = lambda(P_f,B)
Gamma_0 |- L : Value(Fun(P_f,Comp(E_b,A_s)))
```

Here `E_c,A_c,E_b` remain symbolic endpoints constrained by the existing
complete call/bind relations. No row-union recipe or principal solution is
inferred. `Fun(P,Result(I_body))` is §6's closure body/result skeleton;
it must not be read as a solved complete-invocation scheme.

After restoring source labels, the term is exactly the addendum's intended
structure, with `f` and `x` standing for their parameter interfaces/binders:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

There is one call node, inside the local closure body. Final `step` is a
data result, not a call or elimination of that closure.

The literal §6 synthesis table also retains administrative wrappers. Its
application row gives `I_c=Computation(E_c,A_c)`, `d_c=reify(C)`, hence
`n_c=eliminate_p_c(reify(C))`. The local closure then has body `n_c`; the
binding row similarly gives `n_B=eliminate_p_B(reify(B_n))`, where `B_n`
uses that closure. Under T4, §6's same-context law contracts these two pairs
to the displayed core term. Retaining both pairs is equally valid. The
contraction acts inside each original view; it does not hoist the inner call
outside the closure or move entry demand to closure construction. This
distinction avoids treating the synthesis table's inert `d` as executable
`n` without its declared normalization.

For a fixed enclosing activation, let `rho` contain its rebound `f`, and
let `v_s=V[S](rho)` retain that instance's lexical/evidence correspondence.
Existing translation gives the local calculation:

```text
X[B](rho)
  = Return(v_s) >>= (v => Return(lookup(d_step,rho[d_step:=v])))
  = Return(v_s).                                      [T3,T4]
```

Thus the block returns the same local function descriptor without executing
`C`. Within this candidate core's observation law it can be presented as
`lambda(P_f,result(lambda(P_x,C)))`. This local bind/return calculation is
not an unrestricted raw-source contextual-equivalence or an optimization
authorization. It fixes no observable closure allocation mechanism.

In particular, the complete call of `apply` can execute an effectful or
divergent incoming carrier while establishing `f`; a later call of returned
`step` likewise owns entry/rebind for its incoming `x`. At inner `c`, the
actual captured callable owns its own entry. Core §9 distinguishes these
whole carriers `J_arg` and complete invocations `J_call` from each closure's
`J_body`. Returning a closure does not make all these invocations pure, and
this calculation does not execute effects or select handlers.

## Residual blocker, independence and omissions

The source-choice blocker from the prior audits is resolved for this exact
candidate. The precise remaining bridge is **constructing Delta satisfying
T2/T3 from this source**, including the shared provisional/discharged
formal-use relation, captured activation correspondence and original joint
evidence. A second toy core that assumes those premises would leave this
bridge untouched. No extra language decision was needed for the derivation.

No executable oracle or checker was used. The calculation shares its bind,
closure and call laws with the Draft core; it proves their conditional
composition, not their independent raw-source validity. Prior legacy
documentation/lowering/ledger evidence has a common legacy lineage and is
not independently reproduced here. Selected user source meaning is authority,
not an experimental oracle. Seeds/ranges, mutants, numerical enumeration and
performance samples do not apply to this static method.

Failure conditions include changed governing bytes; inability to generate an
admitted complete typed call independently of `Q`; transport losing the outer
activation, slot or joint constraints; or a required conversion outside this
core's scope. Any such condition blocks the typed theorem, rather than being
repaired by a fresh role, force, carrier or source reinterpretation. The
additional principality premises can fail while the structural conditional
term remains valid.

Omitted: parser execution and exact-byte production acceptance, current HIR
construction, production constraint collection, arbitrary braces/records,
recursive local groups, broader local polymorphism, general closure storage
and lifetime, mutation/alias models, annotation-dependent removal beyond
preserving this unannotated position, effect execution, general Function
admission/containment, solver algorithms and implementation.

Recommended next action: construct and independently review the single
source-generated typed decoration obligation T2/T3 for this candidate, retaining
the exact lexical map and all original `nu,K,D`; use this frozen term as the
target rather than another model assuming the missing decoration.

## Checks, coverage and resources

Lightweight static reads only; zero builds, tests, executable probes, child
agents, network calls or Git mutations. Read-only Git resolved the pinned
baseline and compared each direct dependency below byte-for-byte with it.
All matched. Existing approved question/draft/answer and receipt bytes also
matched the baseline; approval is consumed through their integrated receipts.
No other leased artifact or production path was written.

Early task/index and batched output captures were truncated; decisive
governing passages and both prior audits were subsequently read narrowly.
The absent `spec/` locator returned an error; no current spec authority was
inferred from it. This is an assigned-source derivation, not an exhaustive
repository/history/Oracle search. Artifact readback and dependency hashes
are bookkeeping checks, not mathematical independent review.

Resource budget: one Markdown output, lightweight static reading, no compute
experiment. Command wall times were approximately 0.0–0.1 seconds per read,
with at most three independent lightweight reads submitted in one batch;
hash subprocesses ran sequentially. Complete agent wall time, aggregate CPU
and peak RSS were not instrumented and remain unknown. The artifact is frozen
for handoff; its producer reread does not count as independent review.

## Frozen direct dependencies

SHA-256 of pinned bytes; all were unchanged at final dependency recheck.

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-nested-block-function-source-realization/question.md` | `154bcaeefa3212aecc5f2fcb72df32f579f8621ac059dad644f44ef8fd3d27f1` |
| `questions/2026-10-05-nested-block-function-source-realization/answer-draft.md` | `a96d187d9e6991e4b3d974e2128ca6af830ba5a8004142351d8439976e08d1bb` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `questions/2026-10-05-function-call-view-formation/question.md` | `f3915c64daeccf466115b74a895c2c937f2ec10c1872fc91ff220ed2b0cf7c5f` |
| `questions/2026-10-05-function-call-view-formation/answer-draft.md` | `585211d345ead07c8401576c84d216be858d3c7c81e8b412e8ba36a28460d35c` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | `08beb9711c2373e161a408b19a6ccd6c08e24e0b41791e7fac2ea0a332dec1ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` | `bef24bf81b5d561538974db75c950a2df9cc2ed0b49248f2440fb0781941e436` |

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-nested-block-function-conditional-core-derivation.md` only.
- Baseline SHA: `81ceae2804d66142245384db298b8dfb3d0813a8`.
- Changed dependency hashes: none; frozen inventory above.
- Claim/review status: frozen conditional derivation, unreviewed research checkpoint; no principal scheme, source/production gate closure or implementation authority.
- Checks already run: assigned-source reads, direct dependency baseline equality and SHA-256 inventory, lease existence guard, artifact readback and lease diff scope. No tests/builds/probes.
- Proposed one-line research-checkpoint commit message: `research: derive conditional core for exact nested-block function`.
- Shared-record deltas intentionally left for primary/curator: link the conditional term; distinguish the resolved exact source-choice premise from open T2/T3 generation and additional principality/production obligations; preserve J_body/J_call and static-binder/dynamic-activation distinctions. No shared task/index/theory/authority/question-board edit is proposed as gate closure.
