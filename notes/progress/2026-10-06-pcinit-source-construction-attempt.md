# PCInit: source construction stops after the open call skeleton

Date: 2026-10-06
Status: compiler-referee-reviewed research; bounded source-rule derivation and premise localization
Implementation authority: none
Baseline: `aa7c796bb80acee436d19e790d2f7084b7d1be57`, `research/simple-sub-intrusion`
Exclusive lease: this file only

## 1. Objective and exact source boundary

Attempt to construct the initial independently typed punctured-context premise
`PCInit` of the [production admission attempt](2026-10-06-production-function-admission-constructor-attempt.md)
§§1–6. Use source-rule derivation only. In particular, do not fill a proposed
admission rule with transitions and then treat their consistency as a proof
that source semantics supplies that rule.

The inspected governing sections are:

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, 3.1–3.7, 9–10: independently interpreted constructor relations,
  conditional active roots, four admission cases, and Option 2 abstraction.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5: source component formation, original slot/profile and joint
  constraints, Q-independence, and still-open detailed judgments.
- [Callback context delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–2.1, 3–5, 7: B, supplied callback interface, actual entry, static/dynamic
  boundary distinction, and complete-domain obligations.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–4, 6–9, especially §6's source-name/application rows and §4's initial
  relatedness: structural construction relative to supplied typed premises,
  whole carriers, and the remaining complete-call relation.
- `tasks/current.md`, Objective and authority, Closed decisions, and the
  active admission/registration results at baseline lines 1235–1319.

Retained decisions: production Option 2; admission independent of the pending
query; integrated call-view answer a2 and annotation-boundary answer d1;
independently generated B endpoints; actual callable role and entry;
no weakening of soundness, principality or source adequacy; method/role
selection remains later. Source annotations, public inferred schemes and
internal views stay distinct. The source-contract package and typed-core
Draft constructions do not acquire implementation authority here.

## 2. Hypotheses and what can actually be constructed

Work at one original binder tree and `xi=(nu,K,D)`. Let `H` be a fresh lexical
name designated as the tested callable position. Let `F` be its supplied
complete declared interface, and `beta` its supplied original slot/profile.
The finite argument source has synthesized triple `(I_a,d_a,n_a)` under
typed lexical/declaration premises. Other free names retain their original
provider roots. No tested filling is supplied.

These are **candidate/supplied inputs**, not formation results of this note.
In particular, this attempt does not reconstruct `F`, `beta`, their shared
registration or their compatible ambient context from undecorated source.
Call-view §§2 and 5 explicitly leave those exact judgments open.

There is a useful distinction from simply saying that no hole-name rule
exists. Typed-core §6 does have an ordinary name rule relative to known
lexical interfaces. Extend the syntactic interface environment by

```text
Gamma_H = Gamma, H:Value(F).
```

Within that structural synthesis rule, lookup gives

```text
I_H = Value(F)
d_H = name H
n_H = Normalize(Value(F),name H) = result(name H).
```

This copies a supplied interface. No execution, filling membership or pending
Function comparison is used to construct this **syntactic skeleton**. It
does not prove semantic satisfaction of the extended environment. In
particular, introducing an ordinary free name is not yet an independently
interpreted semantic callable hole.

For the single application position `H a`, the same table constructs

```text
I_app = Computation(E_call,A_call)
d_app = reify(call(n_H,n_a))
n_app = Normalize(I_app,d_app).

J_arg = Result(I_a)
Result(Value(A)) = Comp(empty,A)
Result(Computation(E,A)) = Comp(E,A).
```

`E_call,A_call` are symbolic constrained endpoints, not already solved
interfaces. This structural step emits the callee constraint and the
obligation relating the **whole** `J_arg` to `F`'s parameter interface with
the existing typed path/contract obligations. It does not discharge them.

The translation displays which carrier would be retained:

```text
X[call(n_H,n_a)] = X[n_H] >>= lambda f.
    let t = Delay(X[n_a], original lexical references) in
    ExecuteCallable(f,t).
```

This equation identifies the whole delayed argument and its original
environment references. It has no eager argument prefix and no replacement
of `J_arg` by its eventual return value or outward request support. It still
requires a callee lookup/initial relatedness if executed; it is a code graph
construction, not execution with an absent callable filling.

## 3. First unresolved premise and the exact stop

For this construction to become `PCInit`, the emitted Call obligation must
have an independently interpreted source judgment at its original incidence.
It must relate this whole `J_arg`, its result/rebind path, the original
compatible **current** endpoint/context, and the hole's declared `F` under
the same `xi`. It must be derivable while the semantic environment certifies
only the other free variables, excluding the tested filling. Neither
`Q_pending` success nor satisfaction of a proposed filling at `F` may supply
that judgment.

**Stop:** typed-core §6 states that application emits the whole-argument
constraint “with the existing typed path/contract obligations”; it does not
give their complete source rule or a theorem discharging them for this open
context. Thus the first unresolved local premise is interpretation and
discharge of that Call link at the original current endpoint. Synthesis of a
symbolic endpoint does not prove its local contract. This attempt stops
before selecting such a rule or claiming `PCInit`.

Even granting that local premise separately would leave the precise
open-environment interpretation needed by `PCInit`: an initialization rule
for the context with a **formal declared callable hole**, whose semantic
environment excludes that callable's tested filling. No inspected rule maps
the available syntactic `Gamma_H` derivation to this initialization judgment.
That observation is a dependency statement, not a second completed proof
attempt past the stop.

The two possible overclaims can therefore be rejected directly:

1. `Gamma_H |- name H : Value(F)` does not establish that an independently
   typed semantic environment provides a tested value satisfying `F`.
2. Conversely, supplying a concrete environment value certified at `F`
   changes the hypothesis: it is the ordinary filled-environment realization
   route, and does not construct a challenge independently of that filling.

The [earlier attempt](2026-10-06-production-function-admission-constructor-attempt.md)
correctly leaves independent semantic hole/context/environment construction
open. This note sharpens its name-rule description: ordinary hypothetical
name **synthesis** is available; independent semantic hole interpretation is
the unprovided step. No correction to the selected language meaning follows.

## 4. Why the other inspected rules do not finish the derivation

| Rule/package | Available fact | Unprovided initial premise |
| --- | --- | --- |
| Typed-core §4 | Code realization preserves supplied initial relatedness, corresponding environments and typed evidence | Establishing that relation with a declared callable hole and no filling is not its conclusion |
| Typed-core §6 | Name/argument/application skeleton and symbolic endpoint constraints | Exact Call link and independent contextual initialization |
| Typed-core §§7–8 | Checking retains evidence; fixed-domain weakening retains an original certificate | Neither creates that certificate/domain from the open skeleton |
| Typed-core §9 | Whole-carrier entry and complete invocation depend on current configuration/environment; joint domain law | The complete challenge relation is still a source gate, not a consequence of port signs |
| Callback B §§2–2.1 | Known expected slot selects boundary/Handler; endpoints are synthesized independently before one inequality | A supplied known callback contract is a premise; a literal construction/check is not independent semantic hole initialization |
| Call-view §§2, 5 | Source-derived slot/path/ownership and Q-independent admission are required | Exact generation and preservation judgments remain listed obligations |
| Source-contracts §§2.2, 3.3–3.5 | Conditional active root, inventory of independent initial contexts, and correspondence given conformance | Inventory and active interpretation assume source-typed initial context evidence rather than derive it from raw or open syntax |
| Source-contracts §3.7 | Conditional production abstraction with conservative extras | Its unchanged admission domain and abstract-provider history certificates are supplied separately; positivity cannot create initialization |

Static `beta` need not be an already executed receiver receipt. Nothing in
the available skeleton changes the current source endpoint to an earlier
anchor, erases prior local evidence, or composes successful concrete
comparisons. An annotation's target view must keep the accepted local
boundary evidence; copying its written surface form into `F` would not prove
the needed interpretation either. The approved d1 rule is retained as a
constraint; it is not rederived or used to select a missing Call rule.

## 5. Claim class, independence and coverage

Result class: **bounded source-rule characterization**, with the structural
derivation conditional on supplied lexical/declaration interfaces and argument
typing. It is not an established production theorem, a proof that `PCInit` is
impossible, a source counterexample, a completed conditional `PCInit` theorem,
or an adoption of candidate admission clauses. The constructive result is the
open syntactic skeleton and exact residual premise. No finite-history extension
is repeated; it remains conditional on initialization and its later rules.

No checker, execution oracle, mutation or random/exhaustive search was used.
Seeds and numeric ranges do not apply. This method checks entailment in the
inspected source rules; it shares their supplied typed-interface, primitive
relation and owner/path assumptions. It has no independent interpretation of
unselected production admission. A future checker supplied with the missing
initialization rule would test consequences of that rule, not prove its
source origin. Compiler behavior and tests were not used to infer semantics.

The symbolic case is one generic application of a supplied declared callable
name to one source-typed whole argument, including both existing source
interface tags by the displayed `Result` table. It is not a new quiet-Unit,
captured-provider, receipt or role-resolution probe. No grammar-wide
minimization or exhaustive source-rule absence proof is claimed. Initial bulk
source capture was truncated; targeted retrieval supplied every section used
above. The assigned direct sources were checked against the pinned baseline.

Failure conditions for extending this derivation include: hidden tested
filling in the environment; pending-query-created slot/path/authority;
independent per-port witnesses; replacing the whole carrier by return support;
discarded provider contracts; changing the original current endpoint; altered
scope or joint `xi`; an initial rule requiring termination or a return; and
using the provisional formal view to rewrite actual callable role/entry.
No remedy for those cases is selected here.

Unverified scope: construction of shared `F/beta` from raw source, semantic
hole/context/environment formation, local direct Call/path evidence, complete
production admission/descriptor typing, non-source-witnessed provider history
closure, all clients, mutable State/imports/adapters, solving/principality and
generalization/lifecycle. The whole-carrier skeleton does not close any of
these gates.

Recommended next action: give one independently interpreted source rule that
discharges the emitted whole-carrier Call link and initializes the open
context at the original current endpoint with the tested filling excluded.
Review its premises before attempting the separate production-root embedding
or history closure. Do not increase toy-model cases while that premise stays
unspecified.

## 6. Checks, dependency snapshot and resource accounting

All ten inspected dependency files were byte-equal to the pinned baseline
before writing. The SHA-256 snapshot is:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/INDEX.md` | `d56f970490ec9e4699f55c47d1e037bbcfab00592b054c9b138d517b208ab9f0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-production-function-admission-constructor-attempt.md` | `5e4029097e684e5fc1dc7482af39b48ebec86ca608abb215b92567ebc6d7a8cd` |
| `tasks/current.md` | `e3f3e68a5a41df03a8f9eb76830477f066a8f05cbd346799963d26a6e9e1502e` |

Checks performed: read-only `git rev-parse`/status; bounded `rg`/`sed`/`cat`
source inspection; `git diff aa7c796bb --` for six assigned source paths;
serialized Python SHA-256/`git show` byte equality for the dependency manifest;
final dependency/lease/whitespace check and artifact hash reported at handoff.
These administrative checks do not independently review the derivation.
No tests, builds, code changes, probes, Git mutations, child delegation or
shared-record/question writes ran. Only the exact leased note was written.

Budget deviation: initial reading used a short wave of four read-only shell
sessions, followed by a six-session read wave, contrary to the assigned
single-process limit. This was disclosed to the primary; subsequent reads and
hashing were serialized. No heavyweight or compute process ran. Reported
individual shell durations were below a second. CPU and peak RSS were not
instrumented; exact aggregate process count and wall time are unknown. The
work stopped within the 30-minute assignment limit. No numerical correctness
or performance envelope is inferred from the resource observations.

The artifact was frozen at handoff; shared record changes were returned to the
primary.

## Independent review

`compiler_referee` reviewed this note together with the bounded falsification
note and found no blocking, major, or minor issue. The review confirms that
`Gamma_H` supplies only a syntactic Name skeleton from an already supplied
interface; the whole-carrier Call/path/context discharge and filling-independent
semantic hole initialization remain open. This is reviewed characterization,
not a PCInit theorem or production-conformance result. The reviewer did not
inspect compiler behavior, tests, exhaustive rule absence, or a production
counterexample.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-pcinit-source-construction-attempt.md`.
- Baseline SHA: `aa7c796bb80acee436d19e790d2f7084b7d1be57`.
- Changed dependency hashes: none at prewrite/final checks; snapshot above.
- Claim/review: compiler-referee-reviewed bounded source-rule derivation and
  premise localization; no production closure or implementation authority.
- Checks already run: pinned source comparison, targeted source-rule inspection,
  dependency byte/hash equality, exact lease and whitespace inspection, and
  independent review. No tests/builds/executable experiments.
- Proposed one-line research-checkpoint commit message:
  `Record PCInit open-name skeleton and unresolved Call initialization premise`.
- At producer handoff, shared-record deltas were returned for primary/curator:
  distinguish
  available hypothetical name synthesis from missing semantic hole/environment
  interpretation; keep whole-carrier/current-endpoint Call discharge before
  production initialization/embedding and history closure. The accepted map
  synchronization now records that distinction; no selected new semantics
  follows.
