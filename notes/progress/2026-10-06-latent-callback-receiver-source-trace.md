# Captured provider and later invocation: first unsupported typed edge

Date: 2026-10-06
Status: frozen, unreviewed research checkpoint; no implementation authority
Baseline: `d8e25902a946edfd907f1c385fa2b18b5cf12370`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: source proof-tree inversion and chronological operational trace

## Objective, authority, and claim class

For exactly `my apply f = { my step x = f x; step }`, locate the first
supported edge, and then the first unsupported typed judgment, connecting the
original formal to a captured provider and its later invocation. This note
does not propose another registration algorithm or a `PROPOSE/REGISTER` rule.

The governing sources are callback-context-delivery §§2–4, typed-computation-
core-elaboration §§6,9, nested-block-function-source-realization-addendum
§§2–4, and inferred-function-call-views §§1.1–5. Core §§2–3 are read only to
expand the translation referenced by §6. Both approved q1 answers and their
receipts were read directly: call-view q1/a2, integrated at
`61a3651376166346a5baa03ec6679c310b0edbdb`, and nested-block q1/a1, integrated
at `a6bdcf99fba35497cf1323c70101e34669a3ba71`. The design index is a locator.

**Established source decisions:** sequential binding, final `step` as a
function value, lexical resolution of inner `f` and `x`, and retention of the
same captured outer `f` across later calls. The fixed parameter-entry rules
give ordinary `f` and `x` Value entry. These do not determine the actual role
or entry of the callable supplied as `f`.

**Bounded characterization:** the inspected documents supply structural
consumer rules and require pre-existing typed evidence; their named formation
and capture gates remain open. **Conditional derivation:** the executable
prefix below follows within the Draft core from the stated admitted-call
premises. **Unestablished:** a producer for the typed capture judgment, a
profile-to-later-receiver rule, source adequacy, principality, or production
acceptance. No source-semantic counterexample is claimed.

The prior conditional-core and registration notes are stable context. Their
conditional transport premises and the primary's reported U1–U5 remain
unproved. Current HIR's rejection of Apply/composite block bodies is preserved
as the supplied audit result; it was not rechecked here. Conditional schedule
equivalence still supplies no formation rule.

## Labels and explicit hypotheses

Use `d_f,d_x,d_step` for source binders, `c` for the sole application `f x`,
and `u_f` for its callee-name occurrence. The approved map resolves `u_f` to
`d_f`. Let `g` be the callable value obtained on one invocation of `apply`,
and `s` the returned local closure from that invocation. These are proof
labels, not new source syntax or a proposed compiler representation.

Keep three activation labels separate:

- `r_A`: the invocation of `apply` receiving `g`;
- `r_S`: a later invocation of this returned `s` receiving an argument;
- `r_G`: invocation of the captured `g` at `c`, if execution reaches `c`.

Let `C_f=(F_cb,beta,Slots(beta),annotation-absence,scope)` name a **supplied**
original formal contract/profile, not the result of a producer established
here. Let `xi=(nu,K,D)` denote its one jointly scoped source assignment.
Profile inventories, activation identities, and `xi` are not interchangeable.

For the conditional execution only, assume:

1. A conditional kernel expansion of the displayed structural term: the
   executable definitions of `apply`, `step`, and `g` have their original
   entry/result data and the actual invocation premises needed below.
   Bind/name/closure operations use core §§3,6; same-context administrative
   delay/force contraction is admitted, without crossing a source delimiter.
   A complete source derivation graph with typed capture evidence is **not**
   supplied, and the whole-core simulation theorem is therefore not invoked.
2. Admitted outer and later calls, with their whole argument carriers and
   ordinary parameter receipt/entry premises. For the shortest reaching trace,
   choose carriers whose consumption returns `g` and then a value `a`, without
   suspension or divergence. This is a conditional invocation environment,
   not an accepted raw source program or a claim that all carriers are pure.
3. To analyze the seam after registration, additionally supply a valid
   original formal contract `C_f` and its certified receipt relationship to
   `g` at `r_A`, all under `xi`, independently of `Q`. This assumption is
   stronger than supplying a symbolic name for `C_f` and is not derived below.

Hypothesis 3 does **not** include typed capture transport or any association
of the original profile with a later receiver. Supplying those conclusions
would make the intended proof circular. No independently selected assignments
for `apply`, `step`, and `g` may be combined to satisfy the missing premises.

## Grounded prefix and conditional execution trace

The first source premise is the approved lexical/capture fact, not Function
shape. The first syntax-directed core premise is
`P_apply,f=Value(A_f)`; after its entry rebind, `Gamma(d_f)=Value(A_f)`.
Likewise `P_step,x=Value(A_x)` and its own entry supplies the rebound `x`.
With these environments, §6's name/result rules yield

```text
Gamma_fx |- result(name d_f) : Comp(empty,A_f)
Gamma_fx |- result(name d_x) : Comp(empty,A_x).
```

This establishes normalization of those names. It supplies neither a
completed Function contract nor typed capture/Flow/profile incidence.
Core §6's call rule leaves complete callable, argument, and typed-path
obligations; it cannot discharge them from these two Value tags.

Under hypotheses 1–2, expand the approved structure in chronological order:

```text
t0: construct the apply closure; execute none of its body.
t1: invoke apply at r_A with its whole delayed argument carrier.
    establish apply's admitted boundaries and receipt;
    Force_argument >>= rebind d_f := Value(g).
t2: construct s from lambda(d_x, call(result(name d_f),
                                      result(name d_x))).
    s retains this activation's captured g; its body is not executed.
t3: bind d_step := s; evaluate final result(name d_step); return s.
    No invocation of s or g occurs in this binding/return prefix.
t4: later invoke the returned s at r_S with another whole carrier.
    establish step's admitted boundaries and receipt;
    Force_argument >>= rebind d_x := Value(a).
t5: reach c; evaluate result(name d_f) using s's capture, obtaining g.
    Build the inert whole argument Delay(Return(a)) for c.
t6: ExecuteCallable(g, Delay(Return(a))) at r_G.
    Establish g's independently admitted actual boundaries and receipt.
    Use g's original entry and completed result consumer.
```

The local calculation at t2–t3 is only
`Return(s) >>= (v => Return(lookup(d_step,[d_step:=v]))) = Return(s)`.
It uses the fixed final-expression meaning and the existing conditional
bind/return law. It introduces no callback event or runtime protection.

At t6, Value entry forces the designated argument once and rebinds before
the body. Computation entry retains it until an explicit consumer acts.
Neither the internal provisional Handler view for `f` nor `x`'s ordinary
Value tag changes `g`'s actual Pure/Handler role or this entry choice.
For this shortest reaching trace the argument consumption returns `a`;
the two entry modes remain different even if this example's observations
coincide. With an effectful, divergent, or suspended incoming carrier, that
coincidence need not hold. `J_body` is not the complete `J_call`.

Thus the supported source-level chain is
`outer received g -> s's stored g -> later lookup g -> actual invocation g`.
The source decision fixes the identity chain; the Draft kernel conditionally
expands its execution laws. This partial calculation is not a complete typing
derivation for the candidate. It does not contain a justified typed edge
carrying `C_f` and `xi` through the capture to a later boundary.

## First unsupported judgment

Without hypothesis 3, the earliest missing judgment is source formation:

```text
exact resolved source component
  |- original formal d_f has admitted C_f and joint xi,
     independently of the pending comparison Q.
```

Call-view §2 states this direction and explicitly leaves its constructing
judgments open; callback-delivery §2 starts with an already instantiated
contract/profile. A symbolic placeholder for the original slot is not that
formation judgment.

Supplying hypothesis 3 to isolate capture versus later invocation moves the
first missing edge to t2. The required judgment is, in descriptive proof
notation only:

```text
certified original receipt of g through C_f at (d_f,r_A), under xi
  + approved lexical capture of that same g into s
  -/-> a typed captured-provider correspondence in s preserving
       original C_f, slot/profile scope, and the whole joint xi.
```

The arrow is deliberately marked **underived**. The missing premise is a
typed source capture/return elaboration rule with a preservation proof for
this relationship. Its inputs must arise independently of `Q`; its output
must specify how the original profile and jointly scoped evidence accompany
the same captured provider instance. Merely asserting that a kernel
descriptor captures “typed evidence” is insufficient: core §2 takes a finite
source derivation graph with Flow/receipt and `K,D` as input, and §3 translates
that input. Its translation does not construct the missing source capture
certificate. Core §6 expressly adds no independent capture rule.

Even a future proof of that t2 judgment would leave the later activation
premise open: which actual receiver at t6 realizes invocations through the
original slot, and why its profile/owner/activity relation is valid at that
time under the same `xi`. `r_G` exists as an actual invocation in the
conditional core trace, but no inspected rule identifies its boundary with
the original slot's receiving owner. No equality between `r_A,r_S,r_G`, or
their boundaries is licensed.

The returned provider value can outlast `r_A` by the selected source meaning.
That selects retention of `g`; it specifies no extension, expiry rule, or
revival of `r_A`'s receiver authority. General closure lifetime remains outside
the addendum. If `r_A` has ended before t4, its earlier receipt is still a
historical receipt and cannot by itself prove a boundary active at t6. This
is an omitted premise, not a rejected source execution or a counterexample
to the approved capture meaning.

The expected falsifier is met as a failed proof edge: the only available
justification at t2 is lexical value capture plus a kernel translation whose
typed input is assumed. Function shape, `Q` success, prior receipt at t1, or
the unrelated later `step` receipt at t4 cannot replace that premise. A
later invocation is not a proof of the earlier typed capture certificate.

## Evidence independence, checks, and remaining scope

There was no checker, executable oracle, seed, enumeration range, mutation
suite, performance sample, test, or build. The trace shares its entry/bind/
call laws with the Draft core and therefore establishes conditional
composition of those laws, not independent validation of source generation.
The approved source meaning is authority; it is not an experimental oracle.
No legacy inference output was used to fill the missing typed judgment.

Checks already run: read-only `git rev-parse HEAD` matched the assigned
baseline; pinned `git show` reads inspected the exact governing sections,
both approved answers/receipts and prior conditional notes; a Python
SHA-256 comparison of ten direct dependencies against pinned `git show`
bytes found all live files unchanged. The leased path did not exist before
creation. Rules research-lab, design-authority, git-concurrency and
question-board were read. The task/index/lab records were read as locators,
not proof premises. Initial broad task output was truncated; only the
relevant registration/capture locator paragraphs were inspected afterward.
No claim relies on a complete search of that long task file.

All work was static bounded reading and one note write. Heavyweight process
count: zero. No process used a build cache or shared generated output.
Peak RAM, aggregate CPU, and elapsed wall time were not instrumented;
reported tool calls completed without timeout. No test/build authorization
was consumed. No Git mutation, child dispatch, or shared-record edit occurred.

Open gates: original formation, typed capture/return transport, later
profile-to-active-receiver realization, ordinary-value seed resolution,
annotation/protection generation, independent complete admission,
principality, production acceptance/conformance, and inference soundness.
Annotated variants, local polymorphism, recursive local groups, alias/store
mutation, requests/handler selection, multishot resumption, and arbitrary
future clients were not analyzed. Governing dependency changes invalidate the
affected trace; a required unadmitted conversion, missing capture certificate,
lost joint scope, or unsupported owner mapping blocks the stronger claim.

Recommended next action: assign a source/kernel correspondence method to
produce or precisely invert the typed capture/return rule at t2 from an
independently formed original receipt certificate; keep later receiver
realization as a separate dependent gate. Another model assuming that rule
would leave this blocker unchanged.

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-latent-callback-receiver-source-trace.md`.
- Baseline SHA: `d8e25902a946edfd907f1c385fa2b18b5cf12370`.
- Changed dependency hashes: none. All ten direct dependencies matched the
  pinned baseline at the final pre-write check. Governing SHA-256 values:
  callback delivery `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5`;
  typed core `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`;
  nested addendum `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0`;
  call views `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`.
- Claim/review status: frozen unreviewed research-only checkpoint; bounded
  rule characterization and conditional trace; precise missing premise;
  no source counterexample, theorem closure, or production authority.
- Checks already run: pinned section reads, baseline/branch identification,
  ten dependency byte/hash equality checks, pre-write path absence check;
  no tests/builds/checker runs. Primary owns final lease/diff inspection.
- Proposed one-line commit message: `research: isolate missing typed capture edge in latent callback trace`.
- Shared-record deltas intentionally left for primary/curator: link this
  note from the source-registration gate in `tasks/current.md` and the relevant
  theory dependency record; record the t2 typed capture certificate and later
  receiver realization as distinct open premises. No status promotion or
  authoritative design/index change is proposed.

Writing stops at submission of this frozen artifact; independent review is
pending and must be assigned by the primary.
