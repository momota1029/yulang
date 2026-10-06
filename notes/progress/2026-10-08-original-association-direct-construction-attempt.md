# ORIGINAL_ASSOC: direct construction at the nested ordinary Call

Status: research-only constructive prefix and localized derivation stop; unreviewed
Gate: ORIGINAL_ASSOC, with CALL_TYPE and SIG_RULES dependencies retained
Baseline: `162aac715e04bc54985737887bcfc9bf98e20a3f`
Implementation authority: none
Write lease: this file only

## Objective and method

Attempt to construct an inhabited fiber of the **existing** original
signature/owner/view kernel `I_orig(X)` at the approved source

```text
my apply f = { my step x = f x; step }
```

The method is forward construction from the source clauses: generate the
parameter bindings, synthesize both names, normalize their interfaces, and
apply the ordinary Call construction. It does not invert a licensing grammar,
enumerate absent rules, or consult Frozen Oracle. The fixed cut is
`call(result(name f), result(name x))`, with five derivation nodes.

Result: the clauses construct a source/consumer skeleton and a conditional
executable expansion. They do not supply the original owner/view introduction.
This is a stop in this bounded derivation, not a nonderivability theorem,
counterexample, completed semantic specification, or new user-decision blocker.

## Baseline and exact premises

Governing inputs:

- Inferred Function call views §§1.1–5 and integrated
  `function-call-view-formation/q1 a2`: formation direction and protection;
  detailed construction judgments remain open.
- Source contracts §§2.1–3.6, 6.1, 10: conditional emission/realization
  contract, with independently typed primitive and owner/view kernels as input.
  Section 6.1's allocation rules are a candidate abstraction, not selected
  source semantics.
- Typed computation core §§2–3, 6, 9: source interfaces, normalization,
  generated ordinary parameter entries, and complete invocation expansion.
- Nested-block addendum §§1–3: exact lexical binding, captured outer `f`,
  sequential local binding, and return of the inert `step` value.

The dependency map's CALL_TYPE / SIG_RULES / ORIGINAL_ASSOC entries are read as
gate locators. The existing fiber query is taken from successor-source-
association falsification §4; its displayed introduction is expressly a proof
target, not a rule used here. No earlier attack's result is a proof premise.

Keep original `X`, its binder tree and one assignment `xi=(nu,K,D)`. Do not
solve ports independently or add a new telescope. `beta`, `p0`, all legitimate
original slots and witnesses, original provider/result arms, and actual
receiver activation remain original objects. The executable translation
`X[c]` in typed-core §3 is separate notation from the original kernel `X`.

## 1. Construct the source prefix

The addendum fixes the following structural source correspondence:

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

Generate the unannotated ordinary parameter bindings by typed-core §6:
outer `f` has `Value(A_f)` after its own entry rebind; inner `x` has
`Value(A_x)` after the `step` entry rebind. `A_f,A_x` are fresh symbolic
value endpoints, not chosen solved types. The inner lexical environment
retains the same outer `f`, rather than a fresh provider per invocation.
The approved capture identifies that binding; it does not certify every
typed path, profile or owner incidence.

The name row and disjoint normalization clauses give this constructive tree:

```text
ordinary outer formal f                   ordinary inner formal x
----------------------- §6 parameter     ----------------------- §6 parameter
Gamma(f) = Value(A_f)                     Gamma(x) = Value(A_x)
----------------------- §6 name          ----------------------- §6 name
(I_f,d_name_f)=(Value(A_f),name f)         (I_x,d_name_x)=(Value(A_x),name x)
----------------------- Normalize        ----------------------- Normalize
n_f = result(name f)                     n_x = result(name x)
---------------------------------------------------------------- §6 application
I_app = Computation(E_call,A_call)
d_app = reify(call(n_f,n_x))
```

The last row generates endpoint constraints, including identification of the
callee Function interface and the whole-argument relation to its parameter
interface. It does **not** establish their satisfaction. The computation
normalization additionally supplies the designated outer consumer for the
reified application; it does not recursively force a latent result. The
fixed Call cut is the computation inside that inert reification.

`Value(A_f)` is the outer source-interface tag for the formal binding. It does
not decide the actual callable's Pure/Handler role or entry. The provisional
fully protected Handler inference view in call-views §3 is a distinct internal
seed. Neither this tree nor receiving `x` silently resolves that seed; the
exact shared-interface resolution rule remains open in call-views §5(2).

The local binding and final name rows likewise preserve the generated `step`
provider and return its value. They do not execute this inner Call while
constructing or returning the closure. Wrapping the cut in those constructors
adds lexical correspondence; it adds no original slot/contribution constructor.

## 2. Construct the complete executable shape, conditionally

Given the original decorated source derivation and its admitted typed
interfaces, typed-core §3 gives

```text
X[call(result(name f),result(name x))]
  = Return(lookup(f)) >>= (lambda v_f.
      let t = Delay(Return(lookup(x)), lexical references) in
      ExecuteCallable(v_f,t)).
```

The explicit state form of source-contracts §3.2 reduces the callee Return
with `Return(v,C) >>= S = S(v,C)`. This removes that Return/Bind layer only;
the original callee/result arm and its scope remain recorded. It creates no
slot identity, permission or contributor.

`ExecuteCallable` retains the **actual** producer's complete invocation.
For a value-entry closure it contains receiver activation and receipt,
one argument Force, typed result-path rebind, body, and invocation return.
For retained entry it retains the same carrier without that entry Force.
For an operation it retains the declaration's result consumer after native
return. These are conditional expansions for the actual producer; this
attempt does not select one producer or entry for unknown `f`.

Any exposed entry request keeps the pending suffix through

```text
Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S).
```

The suffix includes the original rebind, body, return, and any designated
post-return consumer. It uses resumed current state and the original operation
witness and `xi`; it does not replay receipt. A pure body port is insufficient
to replace this complete image. No source step equates a whole Call contribution
to the receiver's upper port or discards callee-prefix incidences.

## 3. First unavailable premises

There are two distinct stopping points, rather than an assumption that the
skeleton is already a typed original contribution.

**Typing stop.** Section 6 generates the Function/whole-argument constraints
at the application row. From the approved source identity and the generated
symbolic endpoints alone, it does not prove the independently interpreted
complete descriptor/carrier contract, its typed paths, provider conditions,
and pending suffix. Thus the existing judgment sought at the cut is

```text
Gamma |- call(result(name f),result(name x)) : Comp(E_call,A_call)
```

with the complete independent contract, not merely fresh endpoint names.
The first missing premise is satisfaction of that complete callable and
whole-argument contract at the original `xi`. This retains CALL_TYPE and the
upstream independent semantic dependencies; it does not re-open CALL_REL.

**Association stop even with that typing supplied.** Conditionally grant
CALL_TYPE, the original typed exposure `beta,p0`, and the original complete
receiver family `F_C(X)` to isolate the assigned gate. The remaining goal is
the existing query

```text
exists (t,w) in Fiber_C(X,e0),

Fiber_C(X,e0) = { (t,w) in I_orig(X) |
  t.beta = original beta,
  t.p is original typed p0,
  w owns t through original (d_f,R,u,sigma_x),
  w types t.c at the same complete receiver family F_C(X),
  w retains original provider/result arms, scope, xi and dependencies }.
```

These conditions query original witnesses. They are not a new definition of
`I_orig`, an endpoint equality test, or a licensing rule. For a conservative
original contribution, complete-family coverage and its independent typing
must both hold; exact trace equality is not required.

Trying to fill this goal directly from the next applicable clauses stops:

| Clause used forward | What it supplies | Still required for the fiber |
| --- | --- | --- |
| Call-views §2 | Original source position and contract must form stable `beta`/`Slots(beta)` | The document expressly leaves their construction judgments open |
| Typed-core §§3, 6, 9 | Call skeleton and complete actual invocation meaning under the typed input | Original static slot owner and jointly typed contribution witness |
| Source-contracts §3.2 Call row | Required callee/argument/receiver/body/consumer incidences | Its independently typed owner/view kernel input from §2.1 |
| Source-contracts §3.5 | Correspondence using supplied source-base and local typing certificates | Construction of the owner/view primitive contract consumed by that theorem |

The precise association blocker is the independently typed original
owner/view-kernel introduction at this source cut. No displayed clause here
constructs its witness from the generated Call constraints. Call-views §2 and
§5(1) explicitly retain that construction as future work. This is sufficient
to stop this constructive method under the assignment's stop condition; no
repository-wide absence search is needed.

Supplying an independently valid kernel witness would permit later composition,
but would assume the assigned existence goal. We therefore supply no conditional
fiber theorem with existence hidden in its hypotheses. Nor do we choose
`c=j_call`, `s=p0`, singleton `Slots(beta)`, Q-success, or an identity-only
attachment rule. Exhaustive licensing and both coverage directions remain
unproved, because no original fiber introduction was obtained.

## Evidence, limits and next action

Claim classes: the source/normalization prefix is a direct consequence of the
selected source interpretation and typed-core skeleton rules; the executable
shape is conditional on that core's decorated typed input; the owner/view
result is a localized research stop. Candidate allocation clauses supply no
selected semantics. No unconditional fiber inhabitance or gate closure is
claimed.

Oracle independence: Frozen Oracle was neither read nor used. Source clauses
and accepted decisions are the only semantic inputs. There is no differential
oracle, checker, shared transition implementation, enumeration, seed/range or
mutation run. A checker populated with an assumed owner rule would merely test
that assumption, so none was built. The source prefix shares the typed-core
rules it instantiates and is not independent validation of those source rules.

Coverage is the exact approved nested source, the fixed five-node cut and the
specified governing sections. Arbitrary source forms, unsolved annotations,
recursive/generalized constraints, all-world admission, exhaustive licensing,
Option 2 extra observations, descriptor adequacy and production acceptance
were not searched or verified. In particular, no competing complete semantics
or same-X counterexample was constructed.

Read/hash checks used `sed`, `rg`, `sha256sum`, and a short Python comparison
of each dependency's live bytes against `git show` at the pinned baseline.
All seven semantic/locator dependencies below matched the pin. Final checks
also check the leased file's whitespace and recheck dependency equality.
No tests, builds, formatters, heavyweight processes or Git mutations ran.
Only lightweight sequential read/hash processes were used; peak CPU/RAM and
total wall time were not instrumented. There was no finite search to truncate.

Failure conditions: any changed accepted source interpretation, governing
typing clause or existing kernel/fiber query invalidates the affected prefix
or stop. A newly selected, independently justified owner/view introduction
would supersede the association stop. Branch movement alone is not such a
change; direct dependency bytes must be rechecked before integration.

Recommended next action: primary should obtain or construct the independently
typed original owner/view-kernel introduction from the selected source direction,
with exhaustive original witness accounting; a further Call/Return/Bind toy
probe cannot supply that premise.

## Frozen dependency SHA-256 values

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `notes/theory/inference-theorem-dependencies.md` | `21031cfd0ee3ca62a077af4674869bf3c5668400fc62b624435659988bdb4464` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-08-original-association-direct-construction-attempt.md`.
- Baseline SHA: `162aac715e04bc54985737887bcfc9bf98e20a3f`.
- Changed dependency hashes: none; frozen values above match baseline.
- Review status: unreviewed research artifact; producer writes frozen before
  handoff. No independent-review claim, authority promotion or gate closure.
- Checks: direct clause instantiation; pinned/live dependency equality;
  leased-file whitespace check. No executable semantic test or build.
- Proposed commit message:
  `research: record direct original association construction stop`.
- Shared deltas left for primary/curator: link this bounded constructive
  prefix/stop if useful; retain CALL_TYPE, SIG_RULES and ORIGINAL_ASSOC as open.
  No new DAG edge or user-decision blocker is proposed. `tasks/current.md`,
  theory map, design index and question-board bundles were not changed.
