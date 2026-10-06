# Source entry coverage of compatible relation instances

Date: 2026-10-06
Baseline: `d07fa561c15e66875aefb4092827a7030e736a81`
Status: research-only formal coverage countermodel; independently compiler-referee-reviewed with no findings in bounded claim
Lease: this note only
Scope: `my apply f = { my step x = f x; step }`
Method: logical countermodel to inferring source coverage from pointwise preservation
Semantic/implementation authority: none

## Authority and claim

Authoritative inferred-call-views §§2–5 and the nested-block addendum §§2–4
fix the shared source relation, joint `xi=(nu,K,D)`, Q-independent formation,
sequential binding, returned closure and retained outer `f`. They preserve
actual callable role/entry and distinguish static slots from receiver
activation. No selected source meaning is reopened here.

Typed-core §§3/6/9 and source-contracts §§2–3 supply conditional constructors
with decorated-input hypotheses. The exact-candidate relation construction
§3 additionally supplies `Dyn(rho)`, compatibility of dynamic instances with
a static row and its typing/capture certificates. The Q-independent generation
candidate and source-call-image boundary note leave the source producer open.
Source-contracts §3.5 already proves bidirectional coverage for its source base
when the independent admission, finite-conformance, and local descriptor-typing
hypotheses hold. This note does not attack that conditional theorem. It isolates
the absent evidence that the exact candidate's source producer supplies those
hypotheses and covers its independently admitted histories.

The finding is a missing **event-to-instance coverage premise**. The current
conditional construction is not refuted. Retaining all static fibers and
preserving each compatible instance do not establish that independently
admitted source entry histories have such instances.

## Smallest formal witness

Consider only the abstract preservation/coverage implication, with opaque
supplied predicates and one fixed whole `xi`:

```text
R_c = {rho}
Omega_S(rho) = true
T_c(rho) = true
Dyn(rho) = empty
H = {h}
```

Here `H` is a stipulated nonempty history domain, not a history derived from
the exact Yulang source. Every equation quantified over `delta in Dyn(rho)`
holds vacuously, including the conditional Return/Bind preservation equation.
The coverage conclusion

```text
forall h in H. exists rho in R_c, delta in Dyn(rho). Corresponds(h,rho,delta)
```

fails. One row and one history suffice; the failure needs no independent port
choice, Q input, altered role, eager argument, or receiver substitution.
Deleting `h` makes coverage vacuous too.

This is a **formal coverage countermodel**, not a source-valid program
counterexample, a model of completed typed-call semantics, or a refutation of
the conditional theorem. No source typing, primitive interpretation or receipt
certificate for `h` has been exhibited. The opaque leaves are shared supplied
assumptions; this calculation does not validate their source rules.

## Exact missing lemma

Let `H_S` denote the relevant independently admitted source entry histories.
Its construction remains a proof obligation; it cannot be defined by the
existence of the relation instances whose coverage is being proved. The needed
lemma is:

```text
forall h in H_S.
  exists rho in R_c, delta in Dyn(rho).
    Corresponds_S(h,rho,delta)
```

`Corresponds_S` names a proof obligation, not a new semantic object. It must
preserve the original joint `xi` and source references, actual provider
role/entry, static `beta`/profile separately from receiver activation, and
the whole inert argument with receipt/rebind and complete invocation. History
admission and this correspondence must be independent of Q; removing Q from
the generator signature alone is insufficient. These requirements identify
the existing bridge's premises rather than choose new formation rules.

Only independently admitted histories require representatives. Requiring
every abstract row to be realized is stronger than necessary and is not
proposed here. In particular, this note establishes neither nonemptiness of
`H_S` for undecorated source nor source derivability of `Dyn` compatibility.

## Evidence, limits and next action

No executable checker, tests, builds, random search, Oracle use or Git mutation
was performed. Seeds/ranges do not apply. The witness is a manual singleton
calculation. A checker assuming these predicates would reproduce the logical
gap without proving a source rule. The previously reported sixteen lightweight
read/search/hash commands were followed by two commands checking dependency
hashes and absence of this output path. Dependency hashes still match the
reported baseline snapshot. Initial combined captures included truncation;
no complete repository search is claimed. Wall time and peak RSS were not
instrumented; no compiler process or heavyweight calculation ran.

Unverified: the source producer, independent admission, capture attachment,
generalization/fresh use, mixed uses, recursion, principality, adequacy and
production conformance. Existing conditional clauses already reject the
listed role, argument and correlation shortcuts; another equivalent toy probe
would leave the producer premise untouched.

Recommended next action: construct an event-to-instance correspondence for
the exact candidate with independently declared provider/argument premises,
then state precisely which source formation and admission facts it still needs.

## Frozen dependencies and commit packet

The dependency snapshot was rechecked during integration:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/progress/2026-10-06-source-formal-relation-constructive-attempt.md` | `6b2f42ea99ffcb231e9fb73a048afba75dca050ad93706217806f904f1d93628` |
| `notes/progress/2026-10-06-qind-source-generation-judgment-candidate.md` | `27aa739681078a4ec574d1075869469a281af468ab9a32f3166be3c79df07d78` |
| `notes/progress/2026-10-06-source-call-image-producer-boundary.md` | `fa72654af21f4fa7c597a4d20167e5cb0171149d840059916cd2a48f1eb16d20` |

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-06-source-entry-instance-coverage.md` only.
- Baseline SHA: `d07fa561c15e66875aefb4092827a7030e736a81`.
- Six dependencies match the producer's original snapshot. The source-call
  boundary note was subsequently clarified by the primary to make its finite
  symbolic-presentation limitation explicit; the current hash is recorded
  above. Independent review confirmed this delta is compatible with the
  countermodel and does not change its premises.
- Claim/review status: frozen and independently compiler-referee-reviewed with no findings in its bounded claim; formal coverage countermodel only; no theorem refutation or gate promotion.
- Checks already run: governing-source reads, manual singleton derivation, prior dependency diff and current SHA-256 recheck; no tests/builds/Oracle.
- Proposed commit message: `research: isolate source-entry coverage premise for compatible instances`.
- Shared-record deltas intentionally left for primary/curator: optional locator and distinction between static relation retention and admitted-entry-history coverage; no task/index/authority changes or new semantics.
