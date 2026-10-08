# Exact apply/step: falsifying the Alias-Principal premise

Date: 2026-10-08
Status: Draft research artifact; unreviewed; frozen at producer handoff
Baseline: `1bd34a0bf42f364c29e1deb04e17bf7d340fc46d`
Exclusive write lease: this file only
Method: necessary-condition derivation and minimized projected-solution separation
Claim class: conditional mathematical result and bounded contract audit; no source counterexample or gate closure

## 1. Objective and result

Attack only Alias-Principal in [the shared formal interface candidate](2026-10-08-apply-shared-formal-interface-construction.md) §4, for exactly:

```text
my apply f = { my step x = f x; step }
```

No actually source-admitted counterexample was established. The decisive missing premise is **source-derived coverage of the original principal observable fibers by common-reference completions**, with the original designated export and its principality order specified. A proper formal/check inclusion alone does not falsify this premise: another completion might represent the same exported observable contract. Conversely, one successful common-reference completion proves neither coverage nor reflection.

The candidate's existing one-result-tuple descriptor separation is retained as schematic evidence. This lane does not repeat that membership countermodel or the arbitrary-background RT.2 attack. It instead derives the exact projection condition they do not settle, then gives a minimal algebraic witness showing why the observable projection matters. No new interpretation of the approved source is selected.

## 2. Governing sections and fixed dependencies

| Source | Exact force used |
|---|---|
| [Shared interface candidate](2026-10-08-apply-shared-formal-interface-construction.md) §§3–4 | Retain preserves an existing completion; Alias-Principal proposes one complete Function referent with distinct actual maps. Both remain research claims. |
| [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1–5 | Shared source relation; optional annotations; provisional fully protected Handler view and scoped refinement from ordinary-value evidence; actual supplied roles/entries preserved; exact generation and principality judgments remain open. |
| [Nested source](../design/2026-10-06-nested-block-function-source-realization-addendum.md) §§1–4 | Sequential local binding, final step value, and retention of the same outer f; no generalization or complete inference rule. |
| [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md) §§1–4 | Protect the original upper output-effect occurrence from its protected inferred variable; retain independently sourced lower/provider provenance without backward seeding. |
| [Native signature formation](../design/2026-10-08-native-signature-formation-definition.md) §§2–4 and [SIG construction](2026-10-08-source-signature-incidence-construction.md) §§2–8 | Complete contextual placement, origin partitions and actual whole maps. Slot sharing never identifies occurrences, providers or witnesses; formation alone supplies no semantic endpoint equality. |
| [Contextual membership](../design/2026-10-08-contextual-function-membership-definition.md) §§2–3 | Same actual provider, every independent complete challenge and future demand, immutable hereditary binding/capture restrictions. |
| [Pure-read result](../design/2026-10-08-pure-read-call-result-constructor.md) §§2–5 | Complete `ReadInvoke(F_c,D_c,IF_e)` at original indices; original `VIncl(A_f,F_c)` is a premise, not a generated identity. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.1–2.2, 3.3–3.7 | Whole correlated solutions, original scopes, certified transport, independent histories, and Option 2 extras. The conditional grammar is not an exhaustive selected inference rule. |
| [Core skeleton](2026-10-08-apply-step-core-skeleton-ledger.md), fixed-source and supplier sections; [typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §6 | Conditional outer formal `Value(A_f)`, returned step and Call skeleton; no completed export/generalization or principal solution judgment. |

Read the required research-lab, design-authority and git-concurrency rules in full, together with compiler-engineering and orchestration-budget. Shared dirty task/index/theory records were context only. No pending question bundle was consumed; pending successor Generalize q1 supplies no premise.

Every semantic statement below fixes the original binder tree, full row `X`, `xi=(nu,K,D)`, actual occurrence/reference maps and one jointly scoped witness family. Independent provider decompositions, complete contexts/carriers, divergence, pending observations, Response/raw Resume/FutureUse, hard guards, and source/W/Z alternatives remain in the solution object. The proof uses no finite replacement for those domains. Scopes retain exited activations as exited; actual later events govern live authority.

## 3. Conditional criterion at the designated export

The following hypotheses are explicit, presently unsupplied source inputs:

1. **HGen:** an independent complete generating judgment for this exact source yields its original solution object `S`. It includes the provisional/refined formal relationship and all dependent source contracts, rather than defining `S` as common-reference completions or successful comparisons.
2. **HCommon:** the candidate generating judgment yields `T`, whose solutions contain a complete Function schema `F_star` and its actual whole maps `m_formal,m_check`. Contextual records remain distinct. This schema is a Function descriptor, not the §3 relation package renamed as a descriptor.
3. **HErase:** a total lawful erasure `e:T -> S` reintroduces the original relation/checking obligations, with unchanged jointly correlated witness fields and original scopes. This requires semantic reference/transport laws; the existence of frame injections alone does not prove it.
4. **HObs:** the original designated export supplies a projection `p:S -> O`, an observable equivalence `~`, and the ordering used to define principality. The candidate uses exactly `p o e`. Any observable residual, evidence, method/adapter choice or dependent profile needed by that order belongs in `O`; a printed type alone is insufficient. Principality is determined by this observable solution structure.

Write `L=e(T) subseteq S`. Membership in `L` means common-representability under the actual maps and semantic laws. It is not the unqualified equation `A_f=F_c`: differing contextual placements can be transported instances of one referent. Define the original observable fiber of `s` by:

```text
Fiber(s) = { s' in S | p(s') ~ p(s) }.
```

**Necessary condition for original-principal preservation.** For every original principal observable class represented by `s`,

```text
Fiber(s) intersect L is nonempty.
```

**Derivation.** Preservation gives a candidate principal solution `t` with the same observable class. HErase gives `e(t) in L`; HObs gives `p(e(t)) ~ p(s)`. Thus `e(t)` lies in the displayed intersection. No rule that merely retains the relation, proves final membership inclusion, or constructs one actual invocation supplies this existential witness for each original principal class.

**Sufficient condition for full observable solution and principality preservation/reflection.** Under HGen–HObs, if

```text
forall s in S. exists t in T. p(e(t)) ~ p(s),
```

then the two observable solution structures coincide, including their principal classes.

**Proof.** HErase gives `p(e(T))/~ subseteq p(S)/~`. The displayed lifting supplies the reverse inclusion. Both structures use the same observable order by HObs, so any principal-property definition intrinsic to that structure has the same truth value. The lift quantifies over whole source solutions, with existential fields at their original binders; it does not choose a new F_star or witness separately for each runtime challenge. QED.

This sufficient condition is stronger than the candidate's stated principal-only target and is not imposed as a new production prerequisite. For the principal-only target one must prove both directions for the independently specified principal sets. Covering old principal classes alone does not establish that restriction to `L` creates no new candidate principal class. Likewise, full-image equality is not yet a theorem about this source because HGen, HErase and HObs have not been supplied.

The minimal missing source obligation can therefore be stated without requiring identity in every original completion:

```text
OriginalGen(Delta, source, X, xi; R_src, export, order)
OriginalPrincipal(s, export, order)
----------------------------------------------------------------
exists original-scope complete F_star, actual m_formal,m_check, t.
  CommonGen(Delta, source, X, xi; F_star,m_formal,m_check,t)
  and Erase(t) in Fiber(s)
  and CandidatePrincipal(t, export, order)
```

Its converse retains the same original export/order. This is an obligation schema describing the required evidence, not an adopted language rule or a definition that makes CommonGen true. FVIEW §5.1 must supply OriginalGen; §§3 and 5.2 supply its scoped two-stage refinement; §5.4 supplies the relevant principal/export structure and preservation argument. Neither native registration nor the selected pure-read result definition supplies these judgments.

## 4. Minimized schematic separation and its exact limit

Assume only for this algebraic illustration that two endpoint coordinates range over the two-element order `0 < 1`, that an original completion permits `a <= c`, and that common representation at one identical event requires `a=c`. There are exactly:

```text
S_2 = {(0,0), (0,1), (1,1)}
L_2 = {(0,0),        (1,1)}.
```

For `p_pair(a,c)=(a,c)` with literal observable equality, the original fiber of `(0,1)` is disjoint from `L_2`. If principality means a constrained presentation covering the complete original observable solution image, a presentation restricted to `L_2` fails that contract. This claim is conditional on that meaning of principality; `(0,1)` is not declared a principal Yulang assignment.

For `p_first(a,c)=a`, both images are `{0,1}`. The same proper pair then causes no observable-image loss. Therefore the existence of a proper formal/check pair cannot decide Alias-Principal without the genuine export projection and its principal order. One element cannot distinguish proper inclusion from equality; two elements and the single off-diagonal tuple minimize this illustration.

This is a schematic projected-solution separation, not a Function interpretation, a source-generated pair, an actual-program witness, or an executable semantics oracle. It neither limits the complete context domain nor instantiates two unrelated port witnesses. Lifting it to the exact source would require, at a minimum: an OriginalGen derivation admitting a proper pair at one fixed original xi, an original principal-class proof, a distinguishing permitted export observation, and proof that every common-reference completion misses that entire fiber. None was found in the bounded governing-section audit. This lane therefore reports no source-admitted falsifier.

## 5. Contract-specific failure conditions

An attempted common-reference lift must fail or remain conditional if it:

- treats lexical identity of f, shared beta/Slots, equal printed endpoints or SIG injections as identity of complete semantic readouts;
- refines an actual supplied callable's role/entry from the provisional Handler seed, or replaces ordinary-value refinement by a generic Value-entry-implies-Pure rule;
- loses upper-versus-provider origin identity while propagating protection, or back-seeds a pre-existing lower/provider output effect;
- renames into a changed background/event and claims an action at the unchanged background without its semantic correspondence;
- retains only a structural provider branch and omits Option 2 W/Z arms, independent guards, future certificates, or full challenge/history admission;
- moves existential witnesses across their original dependent binders, chooses independent port witnesses, restores an exited activation, or chooses F_star after Q success or from one selected runtime provider;
- erases an observable residual or profile and then claims a weaker printed projection proves preservation of the original principal relation.

The local retained-package theorem and the conditional shared-clause RT.2 identity lemma already leave source generation/principality untouched. Another identity checker or larger endpoint algebra would share that premise and cannot independently prove it. Under compiler-engineering's economy classification, actual source identity is retained construction evidence (D), while this exact required inference preservation is B; the all-solution image condition above is a stronger optional characterization unless its consumer requires it. No canonical classification/status is changed here.

## 6. Evidence, resources and unverified scope

No executable semantic experiment ran. The reference and candidate share the selected source meaning, complete Function vocabulary, original xi/scopes and reference laws; the algebraic illustration assumes its own relation and equality condition. It proves no source transition rule. Random seeds, search ranges, mutations, runtime samples and exhaustive source coverage are not applicable. The two projection choices are a hand-derived discriminator, not a second implementation validating the first.

Commands/checks: read-only `git rev-parse HEAD` and `git status --short`; scoped `cat`, `sed` and `rg` for the listed governing sections; Python SHA-256 plus `git show 1bd34a0bf42f364c29e1deb04e17bf7d340fc46d:<path>` byte comparison of eleven direct semantic inputs; output-creation guard; final dependency recheck and leased Markdown integrity/readback. Initial combined output truncated parts of context/source-contracts; decisive relevant sections were reread narrowly. No exhaustive repository absence search was attempted.

Budget consumed: one documentary pass; zero builds/tests/semantic probes; at most three concurrent lightweight read commands in a batch. No numeric wall-time/CPU/RAM budget was specified by the packet. Aggregate CPU, peak RSS and complete agent wall time were not instrumented; individual read/hash calls returned within about 0.2 seconds. No compiler/configuration/shared-record/question-board writes, Git mutations, formatting or delegation occurred. Producer checks are not independent review.

Unverified: actual source acceptance, complete original/candidate generation, original principal/export judgment, source adequacy, provider/model inhabitance, full Option 2 conformance, reference semantic action, inference implementation and cutover. No source restriction or gate closure is justified.

Recommended next action: have the owning source-generation lane supply the exact unannotated formal/capture/Call generating judgment together with its designated observable export/order, then test the principal-fiber lifting obligation above before adopting a common complete Function referent.

## 7. Frozen input hashes

All eleven direct inputs byte-matched the assigned baseline when inspected; final recheck must use these hashes.

| Path | SHA-256 |
|---|---|
| `notes/theory/2026-10-08-apply-shared-formal-interface-construction.md` | `768ea876dc8373f4d119e0dcea59ea4b5a4a4d179b3eed1e97fb50042060d4c8` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-08-apply-step-core-skeleton-ledger.md` | `796e0f4993997769fa8610a1c377731d999f5629368aaa1fdba597a3663ae4f1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |

## Commit packet

- Exact leased path: `notes/theory/2026-10-08-apply-alias-principal-falsification.md` only.
- Baseline SHA: `1bd34a0bf42f364c29e1deb04e17bf7d340fc46d`; branch supplied by the primary: `research/simple-sub-intrusion`.
- Changed direct dependency hashes: none at producer checks; shared dirty records were excluded as semantic premises.
- Review status: frozen Draft research artifact; conditional criterion and schematic witness; no independent review or source-admitted counterexample claimed.
- Checks already run: governing-section audit, eleven baseline/current SHA-256 and byte comparisons, read-only HEAD/status, creation guard, final dependency and Markdown integrity/readback checks. No builds/tests/probes.
- Proposed one-line research-checkpoint commit message: `research: isolate apply alias principal fiber obligation`.
- Shared-record deltas intentionally left for primary/curator: link this result; retain Alias-Principal open; distinguish proper endpoint inclusion from principal observable separation; request the source generation/export/order supplier. No task/index/authority/DAG/question-board changes were made or authorized.
