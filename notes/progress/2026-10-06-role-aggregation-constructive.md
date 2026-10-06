# Constructive boundary for two uses of one inferred formal

Date: 2026-10-06
Baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`
Status: frozen research-only authority derivation and conditional consequence; independent review pending
Scope: aggregation in the unresolved source producer for one higher-order formal
Semantic/implementation authority: none

## Objective, method and result

Derive what the approved source rules require when two ordinary applications
refer to one unannotated higher-order formal. The method is a constructive
rule crosswalk, not an executable checker or an interpretation of Oracle
output.

The established design direction requires one shared role-indexed contract
from the relevant component, including both uses, and one original joint
`(nu,K,D)` relation. The ordinary conditional core rules produce a shared
symbolic callee endpoint and two distinct whole-argument call obligations.
They do **not** supply the rule that turns an eligible ordinary-value use
into a refinement of that shared role-indexed contract. The missing rule is
not supplied by interpreting conjunction, joining port directions, or
computing the conditional complete call image.

No new language choice is proved necessary by this result. The user already
selected shared inference from relevant declarations/definitions/uses.
Detailed eligibility, lifting and aggregation judgments remain a design and
proof obligation. If the primary's proposed completion exposes incompatible
observable meanings or principality results, that concrete unresolved choice
requires a user decision; this note selects none.

## Governing premises

- Inferred-function-call-views §§1–5 and approved formation answer `a2`:
  infer one shared role-indexed contract; annotations are optional; an
  unannotated higher-order formal starts internally as a fully protected
  effect-returning Handler view; ordinary-value evidence in the approved
  `apply f x = f x` pattern determines non-Handler in the inferred formal/use
  relationship. Exact generation, ordering, principality and protection
  judgments remain open. The actual supplied callable's role/entry is retained.
- Nested-block addendum §§1–4 and approved answer `a1`: only the exact
  `my apply f = { my step x = f x; step }` candidate has the approved
  sequential block/result/capture meaning. That permission does not extend
  to a new two-use brace example.
- Typed-computation-core-elaboration §6: ordinary formal bindings have
  `Value(A)` interfaces; names copy them; application synthesizes a
  computation interface and a constraint against the whole argument.
  These are conditional source skeleton rules, not completed Function
  inference. Section 9 distinguishes whole carrier, body and complete call;
  actual entry owns receipt/force/rebind behavior. Direction-bit joining
  classifies supplied typed occurrences and does not resolve Function roles.
- Source-contracts-and-common-allowance §§2.1–2.2, 3.1–3.5, 8–10:
  conjunction is on one whole tuple, but the source envelope already supplies
  roles/entry/typed incidences and the original tuple. Repeated provider uses
  retain occurrences and order; flat support removes no such obligations.
  The package is conditional and does not select the missing producer rules.
- The Q-independent judgment candidate and source-call-image producer
  boundary records: shared endpoint registration is a prefix; the formal
  relation, slots, typed incidences, joint source relation/admissible fibers
  and Q-independent admission are still missing constructors. A supplied
  decorated call image cannot prove its source premises.

## Minimal two-call fragment

Use the ordinary expression fragment

```text
apply f x = f (f x)
```

under two resolved ordinary formal binders `d_f,d_x`. This uses the same
ordinary application/name forms as the approved example and needs no block,
branch, record, capture, recursion or annotation rule. It is a source-rule
candidate, not a claim of exact-byte parser or production acceptance.
The header is notation for the ordinary nested parameter skeleton; the
derivation below is explicitly relative to its resolved lexical environment.

Label the inner application `c1` and outer application `c2`:

```text
c1 = Apply(u_f1,u_x)      u_f1 -> d_f, u_x -> d_x
c2 = Apply(u_f2,c1)       u_f2 -> d_f
Gamma(d_f) = Value(A_f)   Gamma(d_x) = Value(A_x)
```

Both are ordinary application constructors. Only `c1` has an ordinary
**value-interface argument**; `c2`'s argument has the inner application's
computation interface. Ordinary application and Value-interface argument
are different predicates. With two uses the minimum is two application
nodes; nesting them avoids introducing a second composition constructor.
This is a minimized structural probe of the missing rule, not a minimized
counterexample to Yulang semantics.

## Derivable ordinary prefix

Relative to the lexical/interface premises above, §6 gives:

```text
I(u_f1) = I(u_f2) = Value(A_f)
I(u_x) = Value(A_x)
Result(I(u_fi)) = Comp(empty,A_f)
Result(I(u_x))  = Comp(empty,A_x)

I(c1) = Computation(E_1,A_1)
Result(I(c1)) = Comp(E_1,A_1)
I(c2) = Computation(E_2,A_2)
```

The inner whole-argument constraint relates `Comp(empty,A_x)` to the
unknown callable interface at `A_f`. The outer constraint relates
`Comp(E_1,A_1)` to that same unknown endpoint. No equality between `A_x`
and `A_1`, no empty-effect conclusion for `E_1`, and no support-row equation
for `E_2` follows from these skeleton rules.

The corresponding core has inner `call(result(name f),result(name x))`
and an outer `call(result(name f),n_c1)`, where `n_c1` is the §6
normalization of the inner computation. This constructs inert argument
delays through the existing call translation. It does not decide whether
an unknown received callable uses Value or retained entry. Complete entry,
receiver/receipt and invocation relations require their supplied typed
premises; this prefix does not generate them.

The approved non-Handler example supplies a direction for ordinary-value
evidence. Applying it to this larger component requires proving which use
is eligible and how its evidence lifts to the shared contract. Inclusion
of the same local syntactic subexpression is not itself that theorem.

## Exact stop and conditional consequence

Let `C2` denote this resolved component. A future producer must first supply
a complete joint relation `Phi_C2` at the original binder scopes, and a
shared inferred-formal role coordinate `r_f` referenced by both uses.
Neither symbol is defined here by pretending the ordinary endpoint prefix
already determines it.

The first absent proof step for aggregation is:

```text
resolved C2 + shared d_f + local argument interface Value(A_x)
  -> EligibleOrdinaryUse(C2,d_f,c1)
     and a sound lift into the shared inferred-formal relation
```

`EligibleOrdinaryUse` is a name for a missing judgment, not an admitted
predicate. The lift must connect the provisional protected Handler seed to
the non-Handler conclusion while retaining the outer use and the whole
joint relation. Authority does not give its quantifiers, eligibility
conditions, transition, order independence or principality proof.

A precise **conditional consequence**, requiring no new transition rules,
is the following. Assume:

1. A sound producer generates `Phi_C2`, its Q-independent admission and one
   shared `r_f` at the original scopes, with both call obligations retained.
2. It proves `EligibleOrdinaryUse(C2,d_f,c1)` and the selected source-specific
   lifting lemma: every admitted whole assignment of `Phi_C2` satisfies
   `NonHandlerFormal(r_f)` because of that eligible evidence.
3. Use/reference transport preserves the same inferred contract and its
   original joint dependencies.

Then every admitted assignment has `NonHandlerFormal(r_f)` at the shared
interface referenced by **both** callee uses. Proof: take one admitted whole
assignment; apply hypothesis 2 to its shared `r_f`; hypothesis 3 identifies
both use references with that contract. No second port witness is chosen.
This proves no existence, uniqueness or principal solution and chooses no
operational implementation of hypothesis 2. In particular, writing
`Phi_C2 and NonHandlerFormal(r_f)` does not construct or prove that lift.

The outer `Computation(E_1,A_1)` argument remains an obligation under this
conditional conclusion. It does not prove Handler, refute non-Handler,
change to a Value source tag, or disappear because the inner use qualifies.
Actual argument carriers remain delayed; an actual callable's independently
established entry determines their consumption. A shared inferred-formal
conclusion rewrites neither a supplied callable's actual role/entry nor a
source annotation/public printed type. Full protection from annotation
absence is not an empty row or a permission to subtract effects.

This reduces the aggregation question to a source-specific eligibility and
lifting lemma. Independent per-use choices followed by witness combination
are already forbidden. An existential-use trigger, an all-use trigger, or
retention of role alternatives is not independently adopted here. Their
precise predicates must be specified before checking whether they agree
with the approved single-use result and the shared-contract requirement.

## Static identities, independence and failure conditions

Binder sharing is established in the prefix. It does not complete a static
`beta`/`Slots(beta)` inventory or establish how call occurrences reference
that inventory. Two applications do not imply two distinct static slots or
two runtime activations. No run or termination premise has been supplied.
Active receiver boundaries/receipts are event objects with separate typed
premises; no such event is manufactured from the formal's static identity.

There is no oracle/reference implementation: authority is the approved text,
and the conditional core rules share their explicitly supplied typing and
incidence premises. No checker transition is evidence for the source rule.
`Q` appears in none of the prefix constructions; complete admission
independence still depends on the unconstructed producer. No seeds, ranges,
enumeration or mutations were used. A proposed completion fails this gate
if it resolves actual callable roles from Value arguments, invents receipts
or slots from comparison success, chooses separate port witnesses, drops
the outer carrier dependency, or assumes eligibility/lifting as if proved.

Omitted: exact-byte acceptance, mixed retained-formal examples, recursive
components, generalization/lifecycle solving, protection-contribution maps,
completed slots/typed Flow, runtime capture, production Option 2 coverage,
source adequacy, principality and finite complete invocation presentation.
No incompatibility between approved decisions is established.

## Checks, resources and handoff

Checks: narrow `cat`/`sed`/`rg` authority reads, eight dependency SHA-256
captures and a final equality recheck; no build/test/runtime/Oracle command.
One read-only `git rev-parse HEAD` confirmed the pinned baseline at startup;
no Git mutation occurred. At most four lightweight read processes were
concurrent; heavyweight process count zero. Tool-reported command time is
subsecond per read; aggregate agent wall time and peak RSS were not measured.

Recommended next action: primary adjudicates this stop against the parallel
methods, then requires an explicit `EligibleOrdinaryUse`/shared-lifting lemma
for `C2` before any aggregation implementation or larger toy probe.

Commit packet:

- Exact lease: `notes/progress/2026-10-06-role-aggregation-constructive.md`.
- Baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`.
- Dependency hashes: eight inspected dependencies unchanged on final recheck;
  SHA-256 snapshot is listed below. No dependency writes.
- Claim/review status: authority-constrained prefix and conditional consequence;
  missing source judgment explicit; frozen, independent review pending.
- Checks already run: scoped reads and dependency hash equality only.
- Proposed message: `research: isolate shared role lifting premise for two formal uses`.
- Shared-record deltas intentionally left for primary/curator: cite the missing
  eligibility/lifting lemma in the successor producer gate; preserve existing
  shared-contract authority and open principality/admission obligations. No
  task, theory, index, authority or question-board files were edited.

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536  questions/2026-10-05-function-call-view-formation/approved-answer.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0  notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e  questions/2026-10-05-nested-block-function-source-realization/approved-answer.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
27aa739681078a4ec574d1075869469a281af468ab9a32f3166be3c79df07d78  notes/progress/2026-10-06-qind-source-generation-judgment-candidate.md
fa72654af21f4fa7c597a4d20167e5cb0171149d840059916cd2a48f1eb16d20  notes/progress/2026-10-06-source-call-image-producer-boundary.md
```
