# Original signature licensing: callee-prefix contribution discriminator

Date: 2026-10-06
Baseline supplied by primary: `f551bac00adaa4fe7e8676f0bbeaee616674078c`
Branch supplied by primary: `research/simple-sub-intrusion`
Status: frozen, independently compiler-referee-reviewed research submission; non-authoritative
Method: ordinary-core reduction and typed-path inversion
Scope: necessary separation of whole source Call output from the protected
formal's original upper invocation contribution
Exclusive lease: this note only
Implementation authority: none
Review: compiler_referee PASS on content SHA-256 `96aaaac06e0cfe4a3a3d4d650278b10c9c266f2aea015eb1e1a855c43db63939`; scope limited to core reduction/order, typed-path inversion and bounded attribution claim

## Objective, inputs and result

Attack a plausible shortcut for the open original inferred-signature
applicability/contribution law: identify the contribution governed by the
formal's upper output with every contribution to its source Call expression's
complete output. One requesting callee-evaluation prefix distinguishes those
objects. The request occurs before the called receiver starts; its typed
computation-effect path is distinct from the prospective callee-result path
carrying the formal's upper profile.

This is a **conditional decorated-core discriminator**, not a Yulang
accepted-source counterexample, an alternate language meaning, or a complete
licensing relation. It refutes a proposed total-output attribution premise
within the supplied core/typed-view contracts. No current producer is asserted
to adopt that premise. The exact approved 11-node `apply/step` component has a
returning Name as its callee computation; this witness extends that restricted
case solely to test whether its port identification generalizes.

Direct governing inputs:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1.1–5:
  source formation, stable original slot, shared contract, Q independence,
  and separation of formal inference state from actual callable role/entry.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2, §3's opening grammar/inventory, §6.1, §§8–9: independent whole-tuple
  primitive meanings; Call includes callee evaluation and complete receiver
  output; coverage allowances do not identify original profile contributions.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: one justified upper output introduction, no provider backflow,
  and no blanket concrete-event conclusion from that introduction alone.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §3 and §9: evaluate the callee before `ExecuteCallable`; receiver/receipt
  belong to `Invoke`; complete receiver entry includes its actual carrier.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6, especially typed transport and observation: effect and result paths
  are distinct; a profile uses matching typed paths and the executing view.

The [original profile derivation](2026-10-06-original-profile-applicability-derivation.md)
§§3–6 and [completeness falsification](2026-10-06-profile-completeness-inference-falsification.md)
§§3–5 remain intact. The [Oracle signature archaeology](2026-10-06-frozen-oracle-signature-applicability-archaeology.md)
was read as bounded historical characterization only. Its marker grouping
and duplicate-shape witness are not used here. This attack also does not use
the earlier inherited-result-packet discriminator, conditional-uniqueness
argument, or a change to the independent admission relation.

## Explicit hypotheses and candidate premise

Fix one original binder tree and one whole row `X` with the same original
`xi=(nu,K,D)`, environment, providers, current configuration and continuation
on every line below. No local witness chooses a different row per port.

H1. The ordinary core and typed-view equations cited above apply. Source
typing supplies a formal binding `d_f` and a stored computation binding
`t_q`. A one-layer elimination of `t_q` exposes a single declaration-resolved
request `q`, then returns Unit if its original typed response is supplied:

```text
X[eliminate_p(name t_q)] = Request(q,C0,k_q)
k_q(response,C1)          = Return(Unit,C1)
```

This is an explicit provider premise. Its independent descriptor validity,
declaration compatibility and source admission are not inferred from this
equation. The `t_q` packet contains no incidence of the tested beta, and no
independent correspondence takes f's upper profile to `t_q`'s effect port.
Other unrelated profiles may be retained.

H2. The selected protected-variable witness and an original source upper
demand are supplied at the same shared f endpoint and original scope:

```text
ProtectedVarAt(k,A_f,sigma,u)
SourceUpperUse(u,A_f,U,sigma)
p0 = outEff(U)
```

Dir-Protect therefore gives the known original upper introduction at `p0`.
This assumes the established seed/exposure premises; it does not derive their
source-wide producer or complete `Slots(beta)`. The eventual actual f keeps
its own role and entry. For a completed suffix, it may be an independently
typed Value-entry closure with pure constant-Unit body; no q is introduced by
its own invocation in this witness.

H3. Bind and Return retain the same formal/provider packet at matching result
paths. There is no extra adapter, annotation grant, new boundary, backwards
path edge, or independent beta mark at the callee computation's effect port.
The view graph has exactly its supplied introduction/typed-flow/receipt/
observation edges. These exclusions identify the bounded witness, not a
source-envelope restriction.

The **candidate shortcut** being falsified is:

```text
q contributes to the full source Call output E_c
and that Call has original protected upper occurrence (beta,u,p0)
=> q is a contribution governed through that upper occurrence.
```

Here the conclusion is event/path attribution to that original upper view,
not just conservative allowance coverage. Static protection at p0 remains
present even when no event traverses it. The shortcut has no receiver-image
or matching typed-path premise. It is deliberately proposed as a research
assumption, not attributed to approved authority.

## Minimized explicit-prefix witness and derivation

Use this ordinary source/core term:

```text
c = call(cf, ca)
cf = bind(y, eliminate_p(name t_q), result(name d_f))
ca = result(literal Unit)
```

It has eight constructor occurrences: one Call, one Bind, one Eliminate,
two Name, two Result, and one Literal. The ignored local y keeps the callee
prefix and the original formal read explicit. There is one request and no
branch, recursion, handler, annotation, latent-result elimination, or second
invocation in the witness. This is minimal within this explicit-prefix
construction: removing the elimination removes q; removing the sequencing
removes its order before the formal return; removing Call removes the tested
upper invocation. No global minimality claim over all supplied provider
encodings is made.

The ordinary Call equation gives

```text
X[c] = X[cf] >>= (lambda f.
         ExecuteCallable(f, Delay(X[ca], original lexical references)))
```

Substitute H1 and ordinary state-threaded Bind:

```text
X[c] = Request(q,C0,
         lambda response,C1.
           k_q(response,C1) >>= (lambda y.
             Return(f,C1) >>= (lambda f.
               ExecuteCallable(f,Delay(Return Unit)))))
```

Consequently the finite prefix already exposes q as a request of `c`.
The `ExecuteCallable(f,...)` suffix has not run. In particular its `Invoke`
has established neither the target receiver activation nor that receiver's
receipt or executing CallView. On a typed response, the same pending suffix
first returns f and only then starts the invocation. No receipt is replayed
by this derivation.

The formal's prospective effect position in cf is
`cf.result.(u,p0)`. Return/result correspondence recovers `(u,p0)` on the
actual returned f. The request q is instead observed at cf's computation
effect position. Typed-boundary §6 supplies no correspondence

```text
cf.result.(u,p0) -> cf.effect
```

Returning the formal and subsequently invoking it does not supply this edge
retroactively. Inversion of the bounded view graph at the request prefix
therefore finds no observation of q in the target f invocation view at p0,
and no matching beta path through that view. An enclosing caller's executing
view may observe q at its own port; that different view does not change this
failure.

Thus, on this same original row and finite prefix:

```text
SourceCallOutputRequest(c,q;X)                  holds
ObservedThroughTargetUpper(q,beta,u,p0;X)       does not hold.
```

The source expression's output certificate must account for the first fact.
It cannot make the second fact true. The full source Call image includes
callee evaluation; the protected upper's complete receiver image includes
entry, body and result consumer after the callee is obtained. Keeping the
receiver image complete is consistent with separating the earlier callee
prefix. Restricting to the receiver body alone would also be wrong because
its actual argument Force and designated consumers remain within that image.

This is the first exact discriminator; no second toy probe is attempted.

## Consequence, independence and failure conditions

An original applicability/contribution constructor covering general Call
expressions needs separate incidence operands for the callee computation
and the obtained callee's complete upper invocation. If it uses the whole
source output E_c as an operand, it must still prove which source contribution
belongs to each tagged typed position. An output coverage inequality from
source-contracts §6.1 supplies no such attribution by itself.

This is a necessary interface condition, not an exhaustive licensing law.
It does not decide the number of static slots, add a latent slot, compare two
authority-consistent complete profiles, or establish which additional static
formation cases exist. The distinction is already explicit in the ordinary
core and typed-path contracts and requires no E/R decision.

There is no reference executable or independent Oracle. The reduction uses
the existing core equations, and path inversion uses the supplied typed-view
contracts. Both are shared assumptions with the source constructions. This
derivation does not prove those contracts from raw Yulang syntax. It does
independently test the proposed total-output attribution consequence against
those contracts, rather than declaring an unexplained licensing atom true
or false.

Conceptual mutations: move `ExecuteCallable` before callee evaluation; add
the forbidden result-to-immediate-effect edge; or treat the full source Call
output as a single target-receiver observation. Each changes a named ordinary
core/path premise. These are analytical mutations, with no executed counts.

The discriminator ceases to apply when the candidate explicitly preserves
the callee-prefix/receiver-image distinction, when the callee is the exact
pure returning Name of the restricted apply/step source, or when an additional
independently licensed beta edge is supplied at the prefix effect port. It
does not refute a candidate already requiring the matching receiver image
and typed contribution witness. No claim is made that all conceivable rules
using E_c must fail.

Complete original-profile existence remains an independent open premise.
If a completed original row independently admits this provider/context and
prefix, the same calculation refutes the shortcut on that admitted row.
This note does not produce that row or prove the premise nonempty. Independent
initial admission, all response/history coverage, production Option A/2
membership, all-view source adequacy and principality remain unverified.
Q is neither queried nor used to create any identity, path or receiver.

## Commands, dependencies, resources and handoff

Checks performed: narrow `cat`/`sed`/`rg` reads of the named inputs;
output-path absence check; dependency `sha256sum`; manual constructor count,
ordinary-core substitution and typed-path inversion. Note integrity checks
are recorded in the submission report. No executable search, test, build,
Oracle execution, formatter, code edit, shared-record edit or child delegation.
Seeds/ranges: not applicable. Heavyweight processes: zero. Commands were
short read-only processes; CPU/RAM peaks and total elapsed time were not
instrumented. No numeric resource budget was supplied beyond the explicit
prohibitions; no completeness of a repository-wide search is claimed.

Scope deviation: read-only `git show` and `git rev-parse` were used for pinned
reads before recognizing the packet's literal no-Git constraint. No Git
mutation occurred; no further Git command was used. Integration and final
dependency comparison remain with the primary.

| Dependency | SHA-256 at artifact creation |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-original-profile-applicability-derivation.md` | `d66a7ec9a57c676668d0ad4531a1607594e681a59c17d0cf239e29cd7cd02905` |
| `notes/progress/2026-10-06-profile-completeness-inference-falsification.md` | `bd2292e8348b36d8af0a4324a923f6302ee5774d52f24d010097fc34494aebb9` |
| `notes/progress/2026-10-06-frozen-oracle-signature-applicability-archaeology.md` | `1621abe333739b475222953ec52adfd5a67d54727c2b612bdee160186ede8b30` |

Recommended next action: require the proposed original signature contribution
rule to expose separate callee-prefix and complete receiver-image operands,
then prove its attribution/inversion clauses before attempting full inventory
coverage. Keep complete-row existence and independent admission as separate
obligations.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-06-original-signature-licensing-adversarial.md`.
- Baseline SHA: `f551bac00adaa4fe7e8676f0bbeaee616674078c`.
- Changed dependency hashes: none observed during this assignment; the table
  records the supplied/current read inputs. Full baseline comparison belongs
  to the primary and is not claimed complete here.
- Review status: frozen unreviewed conditional research discriminator;
  no independent certification, source admission, theorem closure or authority.
- Checks already run: source/core/path reads, output absence, dependency hashes,
  manual reduction/count/inversion, and note integrity checks in the report.
- Proposed one-line research-checkpoint commit message:
  `research: distinguish callee-prefix and upper invocation contributions`.
- Shared-record deltas intentionally left for primary/curator: add the
  callee-prefix/receiver-image attribution condition to the open licensing
  gate; record the conditional eight-node witness and its admission/profile
  premises; preserve exhaustive licensing, complete-row existence and
  independent admission as open. No task/index/theory/authority file changed.
