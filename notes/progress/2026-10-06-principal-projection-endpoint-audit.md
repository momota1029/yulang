# Principal projection at the retained identity scheme

Date: 2026-10-06 (assignment/output date)
Status: frozen unreviewed research; bounded source/artifact audit and conditional projection lemma
Baseline: `45b81a28d614f9f0a4d15c7a861347cb14506566`
Exclusive lease: this note only
Implementation authority: none

## 1. Objective and endpoint

Audit one actual retained production endpoint against the effective-principal-projection premise, without repeating the general F5 pipeline inventory. The endpoint is the identity root's `ClosedValueScheme` in `SolvedModule`, consumed by `instantiate_and_route_closed_inner`; the competing coarse endpoint is `SolvedModule::root_value_for`.

The retained identity scheme and its one-per-use substitution preserve exactly the shared value coordinate needed for the elementary principal value query. A conditional pure structural elimination of that coordinate is effective. This discharges an algebraic subproblem and verifies that the corresponding identity-sharing object exists; it does not prove that current artifacts interpret the complete source Function relation or that all valid Function/effect views factor through them.

The scalar result alone is insufficient even for this value subproblem: both identity and constant Functions project to `Unknown`, while a closed pure structural query distinguishes them. This is a counterexample to using the scalar result as a sufficient principal synopsis, not a bug in the intentionally coarse API or an accepted Yulang source counterexample.

## 2. Governing scope and prior results

Accepted principal criteria are `notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md`, “Existing production value-skeleton evidence” and “Common-allowance factorization gate”. The user accepts identity's shared argument/result coordinate and the constant Function's `Top -> Int` value presentation. The earlier request for a negative-only quantifier on the constant has been withdrawn. This audit does not reopen it.

`notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.2, 6.3, 7 and 10 provides reviewed **conditional** active-root interpretation and allocation-view factorization. The complete `V_alloc,H` grammar and concrete query clauses remain unselected; the document is not unconditional production authority. Its exact quantified result is `forall V in V_alloc,H(S). exists finite m_V`, with the original scope tree and old constraints retained.

`notes/design/2026-10-04-common-allowance-context-preimage.md` §§3.2, 4 and 6 supplies the safe-preimage obligation, including independent admission. A finite written universal condition is not an effective representation theorem. `notes/theory/inference-theorem-dependencies.md`, EFF and PRIN entries, records effective joint projection and unrestricted principality as open; it is routing, not proof authority.

Current implementation facts use F5's Authoritative foundation §§8–9, 23, 30 and 32: elimination of negative-only variables to Top, retention of bipolar variables, the normative identity/constant schemes, and one fresh substitution per incoming use. Concrete compatibility §1 prohibits composing successful concrete comparisons. The structural lemma below uses an explicitly different, restricted mathematical preorder; it authorizes no such composition in the Yulang solver.

The committed q1/d1 answers for production Function membership, denotation and inlet context remain the primary's accepted user decisions: Option 2 extras are allowed without universal source-constructor inversion; complete membership uses the selected existing relation and retained constraints; admission ranges over all independently typed compatible punctured contexts at fixed original `(nu,K,D)` and cannot assume pending query success. None supplies complete production rules or implementation permission.

The already established identity value-skeleton and local empty-body-effect correspondence are respected. This note does not re-prove their source-generation theorem. Its new question is what a principal query projection can recover from the retained shared quantifier, and what the scalar endpoint loses.

## 3. Concrete retained objects

All locations are at the pinned baseline.

| Object | Source locator | Principal projection relevance |
| --- | --- | --- |
| Root scheme | `yu-solver/src/lib.rs:15708` `root_value_for`; `yu-types/src/lib.rs:630` `ClosedValueScheme` | Root index selects an exact arena-bound scheme. Scheme contains quantifier count, recursive-bound range and positive predicate. The scalar accessor subsequently maps every Function head to Unknown. |
| Identity predicate | F5 foundation §23; solver `f5d_identity_lambda_admits_exact_effect_and_function_facts` at `lib.rs:20282` | Normative predicate is `PureFun(q0-,q0+)`, one Q and no R. Existing test source checks shared live parameter ordinal and one quantifier. Test was inspected, not executed here. |
| Constant predicate | F5 foundation §23; solver test at `lib.rs:20375` | `my k x = 42` closes to `PureFun(Top,Int)`, zero Q and zero R. It is distinct from identity despite the same scalar result. |
| Per-use substitution | `lib.rs:14527` `instantiate_and_route_closed_inner` | Allocates one fresh row for each quantifier ordinal and puts it in `scratch.substitution`. This supplies one value coordinate for the identity use. |
| Two polarized references | `lib.rs:14255` positive Quantified arm; `:14382` negative Quantified arm in `closed_parts` | Both look up the same `q.ordinal()` in that one substitution map, then create opposite-polarity live terms. They do not independently freshen the argument and result. |
| Effect and scope boundary | `yu-types/src/lib.rs:614–626` polarized effect views; F5 foundation §8 | Closed effect views have only Bottom/Empty; no coupled complete-observation or context interpretation follows. Q/R and arena ownership are structural objects, not by themselves `(nu,K,D)` semantics. |

The concrete incoming source witness can be `my id x = x; my alias = id`: the resolved name use consumes the structured identity scheme. It transports that type without invoking the Function. No annotation, callback call or arbitrary external query is claimed to be generated from this source. The hypothetical direct query in §4 is an interpretation obligation on the retained endpoint, not an existing source annotation path.

## 4. Conditional exact value projection

Fix the following hypotheses explicitly:

1. Work only in a pure **value shadow**: finite closed proper type trees over `Int` and binary Function with contravariant argument and covariant result. No effects, Records, optional fields, concrete adapters, rigid names, scope guards, roles or admission predicates are interpreted in this shadow.
2. Let `sqsubseteq` be ordinary structural comparison for that signature. It is reflexive and transitive. This is a mathematical hypothesis of the shadow relation, not a claim that arbitrary successful concrete Yulang inequalities compose.
3. `U,V` are closed trees in that signature. The fresh identity coordinate `a` may legally take `U`; it has no additional scope/permission/residual restriction.
4. The shadow translation of the direct identity query `PureFun(a,a) <: PureFun(U,V)` is exactly `U sqsubseteq a` and `a sqsubseteq V`. The production shared ordinal establishes the syntactic correspondence of the two occurrences; semantic adequacy of this translation to complete Function membership is not assumed proven.

Then the public value projection has the exact finite form

```text
exists a. U sqsubseteq a and a sqsubseteq V
iff U sqsubseteq V.
```

Forward direction follows by transitivity of the stipulated shadow relation. Reverse direction chooses `a=U`; reflexivity proves its first conjunct and the assumed public comparison proves the second. Thus the existential does not require arbitrary-tree enumeration for this one coordinate. On finite closed DAGs, checking the remaining structural comparison terminates by descending through the finite product of their nodes. This gives an effective projected predicate in this restricted language.

This lemma is conditional and producer-authored, with no independent review claimed. It is not the general pure FMP effective-search corollary: that reviewed result decides finite pure structural satisfiability and explicitly disclaims principal public projection. Nor does this lemma remove a universal challenge quantifier, an alternating binder, a source kernel or an arbitrary residual. A hidden predicate `Phi(a,xi)` would change the formula to `exists a. U sqsubseteq a and a sqsubseteq V and Phi(a,xi)`; choosing `a=U` is then unsupported until `Phi(U,xi)` is proved.

The retained Q is enough to express the shared value variable in this lemma. The scalar Unknown is not. This shows a useful existing object rather than a need for another carrier.

## 5. Smallest discriminators

Let `T = PureFun(Int,Int)` and use these admitted source bindings:

```yulang
my id x = x
my k x = 42
```

Under F5's normative schemes the value query `PureFun(T,T)` has different results. Identity chooses its one Q coordinate as `T`, so both value children compare reflexively. Constant has result `Int`, requiring `Int <: T`; the pure Function comparison's concrete head table rejects Int against Function. Its argument obligation `T <: Top` is the ordinary F5 top case. Pure effect children contribute no distinction. Yet `root_value_for` returns Unknown for both, and the local Function projections are Unknown/Empty for both. Therefore no function of only that scalar result (or that scalar/effect pair) can decide this query correctly for both retained schemes.

This source pair is minimal within the admitted Function-body fragment for this failure: one plain binder and one body leaf per Function suffice; the query needs one Function constructor to distinguish Int from a Function, since only one primitive atom is present. This is a representation countermodel with an explicitly stipulated pure query, not a newly run executable experiment.

A second discriminator attacks correlation loss directly. Mutate one-per-use substitution into independent freshening of the two Q occurrences. The query against `PureFun(Int,T)` then changes from

```text
exists a. Int sqsubseteq a and a sqsubseteq T
```

to

```text
exists a,b. Int sqsubseteq a and b sqsubseteq T.
```

The original is false because Int and Function heads are incompatible in the shadow relation. The mutation is true with `a=Int,b=T`. It demonstrates why the retained ordinal/substitution equality is relevant to principal projection. Current production code uses one map and does not contain this mutation. No mutation run is claimed. No general concrete comparison transitivity is inferred from either discriminator.

## 6. Exact unresolved quantified obligation

At an original complete fiber `xi=(nu,K,D)`, write `S_xi` for original solutions and `Q_xi(s,a)` for a legal common allowance with all required direct complete queries and original evidence. The source-contract gate requires at least

```text
forall s in S_xi. exists a. Q_xi(s,a),
forall V in V_alloc,H(S). exists one finite scope-respecting m_V,
```

where the chosen map preserves **all** public solutions of its view:

```text
forall v satisfying C_V.
  exists original-scope s,a,evidence.
    C_G(s) and Link(s,v) and Q(s,a)
    and Direct(B_common(s,a),R_V(v)).
```

The wider accepted principality target still needs coverage of all independently valid supported views beyond that conditional allocation class. Effective public projection also needs a finite effective retained predicate whose solutions are exactly the appropriate scoped projection of those original complete solutions, with witnesses and evidence at their original binders.

For the containment-based route, complete valid input interfaces must satisfy both parts of the safe preimage:

```text
forall h in D_V. Adm_T(i,h)
and forall h in D_V. forall o. T(i,h,o) implies o in P_V(h).
```

The identity Q coordinate supplies neither `Adm_T` nor `T` nor a proof that the direct query atom represents their universal condition. The scalar discriminator falsifies a scalar-only shortcut; it does not falsify these quantified goals. The retained scheme supplies one necessary correlation and can support §4's restricted elimination, but full effective principal projection remains unverified. The post-solve store and HIR remain available as additional evidence; this note makes no impossibility claim about interpreting them.

## 7. Checks, independence, omissions and next action

The implementation oracle was actual pinned source; the independent obligation was the committed user decisions and reviewed conditional theorem statements. No executable checker imported a hand-supplied transition system. The projection proof shares its explicit pure structural assumptions with its query examples, so those examples do not independently validate source semantics. Existing test assertions were inspected only. No tests, Cargo builds, compiler edits, formatter, enumeration or probes were run; there are no seeds/ranges or hidden incomplete searches.

Commands were narrow `git show BASE:path | sed -n 'START,ENDp'`, `git show BASE:path | rg -n PATTERN`, and read-only Python SHA-256 comparisons. The early dependency comparison stopped at a live theory-routing-file mismatch; follow-up finished the six committed answer/receipt checks. Source and authority hashes matched their worktree copies. The theory routing input was read only from the baseline and does not enter the derivation. Its live hash at inspection was `865b81208ff1529620b1f8621c4878e9041d8de98401684a8dc91cc9fffe0d93`, versus baseline `7b4051773292e74ac46095b0620240e08f93be2e009c42d9d84bfefe30dedb11`.

One producer; lightweight single-process source/hash checks only; no child or heavy process. Individual captured commands completed below one second. CPU, peak RSS and total reasoning wall time were not measured. No independent certification is claimed. General query solver completeness, recursive/guarded/rigid projection, full value principality, complete effects/admission, Option 2 extra-observation grammar, production Apply and arbitrary views are omitted.

Recommended next action: derive the complete interpretation of **this retained identity Q/store endpoint** at one fixed original fiber, for an independently admitted computation carrier, and state the direct-query/evidence clause that represents its safe preimage. That bridge can determine whether §4 is a valid projection of the full relation or merely a value shadow. A new scalar probe, a second independent-Q toy model or a larger pure enumeration would leave this premise untouched.

Shared deltas proposed to the primary/curator: record the scalar-synopsis obstruction and the existing shared-Q projection subcase under EFF/PRIN, without changing their open status or repeating the general F5 inventory. `tasks/current.md`, theory files, design/index records, questions and the prior inventory remain untouched.

## 8. Baseline SHA-256 dependencies

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `a2103c6735d7a4efad00231f973544dda59d42219dbf83439fffc17889168e59` |
| `crates/yu-types/src/lib.rs` | `a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-04-common-allowance-context-preimage.md` | `e3aa657d281f8e528d41544d862ee5e938bb6d3c4d36fa60fd04306c1f1dfb7e` |
| `notes/design/2026-10-03-concrete-compatibility-boundary.md` | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| `notes/progress/2026-10-04-principal-scheme-acceptance-criteria.md` | `13c6feb02727d8cc735dcb19843b337dee9126cd7afc519f3d18c6e1cdf95337` |
| `notes/progress/2026-10-05-pure-structural-effective-decision-corollary.md` | `37bc762c22d32258355e835a29f598a8b50aa7307a88c01454ef63849c11e133` |
| `notes/theory/inference-theorem-dependencies.md` (routing only) | `7b4051773292e74ac46095b0620240e08f93be2e009c42d9d84bfefe30dedb11` |
| `questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md` | `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3` |
| `questions/2026-10-05-production-function-inlet-context-domain/receipt.md` | `a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `questions/2026-10-05-production-function-bound-membership/receipt.md` | `f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-principal-projection-endpoint-audit.md` only.
- Baseline: `45b81a28d614f9f0a4d15c7a861347cb14506566`.
- Changed dependency hashes: no source/authority change; routing-only live theory hash differs as recorded in §7. Reads and claims stay pinned to baseline.
- Review status: frozen unreviewed characterization, conditional projection lemma and scalar/correlation countermodels; no theorem/gate completion.
- Checks already run: narrow source/authority reads, baseline hashes and source/authority worktree comparisons; final note/hash/scope check at handoff. No tests/builds/probes.
- Proposed commit message: `research: audit identity endpoint principal value projection`.
- Shared-record deltas left for primary/curator: scalar synopsis is insufficient; shared-Q value elimination is a conditional subcase; complete EFF/PRIN and admission interpretation remain open. No shared file or prior inventory changed.
