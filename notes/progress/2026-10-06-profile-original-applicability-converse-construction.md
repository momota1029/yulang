# Original applicability at the captured formal: failed source-introduction induction

Date: 2026-10-06
Baseline: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`
Status: frozen research-only producer note; independent review pending
Claim classes: bounded source-rule inventory; conditional singleton lemma;
unproved original-applicability converse
Scope: P for `my apply f = { my step x = f x; step }` only
Semantic and implementation authority: none

## 1. Objective, method and result

The objective was to derive, from original source introduction rules,

```text
Applicable_original(C,d_f,R_f,p;xi)
  => p = p_0 and ElimOrigin(c,u_f,d_f,R_f,p_0,p_out(c)).
```

Here applicability is the original source contract's relation, not a new
definition equating it with a generated footprint. All coordinates use the
same original `xi=(nu,K,D)` and scope tree. Actual provider/result packets
retain their distinct introduction provenance, even if static labels coincide.

The method was forward structural induction over the selected source tree,
asking whether each *source introduction* rule establishes an exhaustive
original-position inventory. This does not repeat transport inversion or
compute the least footprint again. The induction cannot start at the outer
formal's original interface: the inspected rules supply its signature profile
as an input, without an exhaustive applicability-formation judgment. The
initial Call constructor establishes one position, but no inspected premise
bounds the other original positions of that supplied signature profile.

Consequently the requested converse is unproved. This is a precise missing
premise in the inspected proof route, not a proof of semantic ambiguity, a
source counterexample, or a reason to reopen the selected source meaning.
The assigned stop condition is met: the source introduction inventory does
not bound arbitrary original signature-profile inputs.

## 2. Baseline and exact governing clauses

The following were read from the pinned revision; their working copies matched
the pinned bytes at the dependency check:

| Source | Governing sections / role | SHA-256 |
| --- | --- | --- |
| [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md) | §§2–5: source-derived shared contract, stable slots, unannotated protection, open generation gates | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) | §§2–3, 10: supplied decorated source, exhaustive relation emission conditional on inputs, remaining coverage | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md) | §§1–4: exact core correspondence, shared lexical capture, implementation gates | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) | §6: signature-profile introduction and typed transport | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| [Source-call construction](2026-10-06-source-call-generation-construction.md) | §§3–7: shared roots, Gen-Call-0, initial policy, remaining P | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| [Prior normal-form construction](2026-10-06-profile-source-normal-form-construction.md) | §§3–6: generated/inherited distinction and original converse left open | `74604c54f23efc406d5359cd4e2dfcc946065d8b01071874ea8c0945116fce05` |

Accepted decisions are used unchanged: contracts come from declarations,
definitions and uses; neither inferred type shape nor pending Q creates a
source relation; the block returns `step` without calling it; captured `f`
is the same outer formal; annotation absence causes full protection at
applicable positions without a concrete removal grant. Written contracts,
inferred public types and internal views remain distinct. No Oracle rule is
an authority or premise of this argument.

## 3. Forward induction and the failed formal case

The selected finite source tree is

```text
lambda(f,
  bind(step,
    result(lambda(x,
      call(result(name f), result(name x)))),
    result(name step)))
```

Its one source Function elimination is `c = f x`; the resolved callee is
`d_f`. Returning or capturing a closure introduces no additional invocation.
These are fixed source facts, independent of solving `F_c`.

A successful forward proof would need the following distinction at each
node: execution-clause emission; introduction of an original applicable
position; and transport of an already introduced position. The relevant
inventory is:

| Case | What the inspected clause supplies | Missing implication, if any |
| --- | --- | --- |
| Outer formal interface | Shared `A_f,R_f,F_c,beta` at the original scope | An exhaustive rule deriving the applicable positions of its original signature |
| Local ordinary formal `x` | The same Value interface at the resolved name | No original `beta` introduction is specified here; its inherited evidence is not discarded |
| Name / capture / result / bind | Same provider roots, inert returns and typed transport of supplied evidence | These rules cannot repair an unproved original introduction inventory |
| Local and outer lambda | Closure/body/captured-root relation clauses | Execution-clause accounting does not say their formal-profile formation has no other cases |
| The single Call `c` | `Gen-Call-0`, `p_0`, `ElimOrigin`, initial protected/no-grant policy | Produces a position; it supplies no inversion for arbitrary original applicability |
| Generalization / use | Whole-scope certified transformation of the existing relation | Preserves an inventory once supplied; it does not determine that inventory |

Source-contracts §3.1 takes actual roles, typed paths, owners, receipts and
the shared original tuple as inputs to a decorated graph. Its §3.2 says every
*emitted relation clause and alternative* is accounted for by the execution
inventory or a certified transformation. Thus its C-realization induction
matches relation clauses to source constructors after those inputs are fixed.
It is not an inversion theorem for introduction of each profile position.

The positive introduction in typed-boundary §6 has the input

```text
b = (receiver r, callback slot a, signature profile Gamma, type endpoints).
```

It specifies the meaning of positions marked by `Gamma`, but says profiles
are supplied by source elaboration and leaves their derivation from arbitrary
syntax open. An introduction can have several positions while having one
boundary identity. A constructor count for the execution tree cannot turn
that parameterized introduction into an exhaustive singleton rule.

The failed induction case is therefore the formal-interface case, before
body composition. It needs a derivation of `Gamma_original` from this
unannotated formal and its relevant component. Neither `NoAnnotation(d_f)`
nor the ordinary-value role refinement has a conclusion that excludes a
second applicable signature position. They constrain protection and the
shared inferred role, respectively. Grant absence is not inventory absence.

## 4. Exact conditional lemma and minimum remaining leaf

Let `E_C(d_f)` be the source Function elimination occurrences in the fixed
component whose resolved callee is this formal's shared original root.
The selected tree proves `E_C(d_f)={c}` by inspection of its constructors.
The established initial construction supplies `p_0` and the displayed
`ElimOrigin` for `c`.

The additional **candidate premise**, not proved or adopted here, is:

```text
EliminationCompleteness_at_f:
  every Applicable_original(C,d_f,R_f,p;xi) has an original
  source-introduction derivation identifying an e in E_C(d_f),
  with p the immediate complete-invocation position introduced for e.
```

This premise refers to original introductions; a packet transport route,
actual provider's profile, or equal endpoint shape is not its witness.
The introduction's source/address identification must commute with the
one joint original-scope substitution; it cannot select a new witness per
port. It is only required at this exact formal root, not for all Yulang
callbacks or all profiles in the surrounding program.

**Conditional singleton lemma.** Under EliminationCompleteness_at_f and the
accepted initial source constructor, every original applicable position at
this formal is `p_0` with the existing `ElimOrigin`. Proof: take an arbitrary
original applicability derivation. The candidate premise supplies `e`;
the fixed source inventory makes `e=c`. The same original Call/address
construction identifies its immediate position as `p_0`. No semantic port
witness, receiver or binder is changed. Conversely the accepted initial
constructor supplies the original initial position. Thus equality of the
applicability inventory with `{p_0}` follows *if* the candidate premise is
available. This conditional reduction establishes no new part of that premise.

The minimum unresolved leaf on this route is an exhaustive original
formal-profile formation/inversion clause establishing that premise for the
exact component. Adding it as an axiom, calling it a definition of
`Applicable_original`, or assuming profile completeness in a checker would
assume the requested converse. No such addition is made.

The absence of written annotations in this exact candidate removes written
annotation occurrences inside this tree. It does not bound every possible
inferred dependent signature at `F_c`, and no rule was found connecting
arbitrary original signature-profile positions to that absence. Actual
provider/result annotations may remain inherited inputs; counting or erasing
them is not a proof about this component's original introduction provenance.

## 5. Independence, omitted cases and stopping conditions

There is no executable experiment, random seed, enumeration range or mutation
run. The finite envelope is the one selected core tree and the six pinned
documents above; this is not a search over all source programs. No minimized
Yulang counterexample or incompatible complete semantics is claimed.

Oracle independence is literal: no Oracle source, trace or result was used.
The conditional lemma and the earlier least-footprint result share the
initial Call constructor and root/address convention. The lemma does not
independently validate those conventions or its candidate completeness
premise. A checker implementing only that constructor would leave the same
premise untouched, so no further footprint probe was run.

One diagnostic proof obligation is an arbitrary original applicable `p`
distinct from `p_0`: the rule inventory must exclude it by source formation,
or produce its actual source-introduction witness. Merely supplying such a
position in a decorated profile is neither a source-valid counterexample
nor a legitimate mutation of selected language meaning. Its potential
presence here identifies the unconstrained proof input only.

The conditional lemma fails if an original applicability derivation can
introduce a position without the stated elimination witness, or if the
source/address identification does not preserve the same root and scope.
Unknown latent Function/Thunk/recursive result positions remain unbounded;
no all-latent-descendant rule or prohibition was selected. Independent
initial admission A, operational realization/receipt/lifetime, complete
profile normalization, B-equivalent scheduling, all-view principality,
production Option A/2 conformance and compiler source acceptance are omitted.

Recommended next action: have the primary locate or construct the exact
original formal-profile formation rule and adjudicate its inversion before
dispatching another singleton or transport probe. If construction requires
a new durable semantic choice, return that concrete rule and alternatives
through the existing authority process.

## 6. Verification and commit packet

Verification is limited to pinned dependency-byte comparisons, local link
existence, final newline and whitespace checks on this leased note. No build,
test, Oracle execution, performance measurement or whole-workspace formatting
was run. Reads and checks used sequential lightweight local processes; no
parallel heavy process or generated scratch output was used. Tool-reported
individual command wall times were below one second; aggregate CPU time,
peak RSS and reasoning wall time were not instrumented.

This note is frozen after the final narrow metadata check. A producer's
inventory inspection is not independent review. The primary owns subsequent
review, integration and shared-record synchronization.

- Exact leased changed path: `notes/progress/2026-10-06-profile-original-applicability-converse-construction.md`.
- Baseline SHA: `0076fedf2e1ee5d012e68a8e316f1aedb3ecce9e`.
- Dependency changes: none in the six pinned dependencies; hashes are in §2.
- Review status: research-only, unreviewed producer construction; P unproved.
- Checks already run: baseline/live dependency equality; local relative links;
  no trailing whitespace; final newline; lease path was absent before writing.
- Proposed one-line research-checkpoint commit message:
  `Record original formal applicability induction blocker`.
- Shared-record deltas intentionally left for the primary/curator:
  record P as open at original formal-profile formation, retain the initial
  Call and generated-footprint results, and avoid treating this conditional
  reduction as source completeness in `tasks/current.md`,
  `tasks/research-lab.md` and any applicable theory/index records.

No compiler, checker, authority, manifest, lockfile, question bundle or
shared coordination path is changed; no Git mutation was performed.
