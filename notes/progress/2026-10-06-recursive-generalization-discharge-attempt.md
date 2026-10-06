# Recursive discharge before an actual generalized use

Date: 2026-10-06
Baseline: `843f78ccaae0eac1a49838b54cf2a3863aa0b8a9`
Branch: `research/simple-sub-intrusion`
Status: frozen, unreviewed research-only premise reduction
Method: constructive source-rule tracing and inversion of the first missing rule
Exclusive write lease: this note only
Semantic/implementation authority: none

## 1. Objective and result

Attempt simultaneous body/member discharge and then semantic binder placement
for the exact constructor-guarded source:

```yu
my f x = g
my g y = f
```

The attempted subsequent use is `f ()`, with `(f ()) ()` as a second
observation of the returned member. Neither is claimed to have an accepted
generalized source derivation. The trace stops **before Generalize**: open
Name/Result/lambda synthesis does not validate its original simultaneous
member assumptions. The precise missing input is a constructor typing rule
that proves complete membership of the two actual mutually captured
providers, including independent admission, at those same registered
member contracts. No rule in the inspected clauses supplies that input.

This is a bounded rule-trace result, not a counterexample to the selected
language, a proof of language underspecification, or a new recursion policy.
The useful delta is the displayed failed proof tree through the proposed
actual use: it locates discharge before any eligible-binder question and
shows which original identity would survive the result of that use. The
reviewed actual-provider construction K/KP/KV and lexical map LX are used
with their existing scopes; they are not reproved or independently reviewed
here. No second equivalent toy probe is introduced.

## 2. Governing premises and claim classes

The authority order is `rules/design-authority.md`. The design index was
used only to locate the source documents. Direct governing clauses are:

| Source | Clause and scope retained |
| --- | --- |
| Inferred Function call views §§1.1–2,5 | Source annotation, public scheme and internal view are distinct; declarations/definitions/uses/component preserve one jointly scoped original relationship; exact formation rules remain open. |
| Result-synthesis choice §4; typed core §6 | Ordinary parameter registration precedes body synthesis; Name preserves its registered source interface; Value result uses one pure Result; forward references reuse registered endpoints. This constructs skeletons relative to the interfaces, not recursive inference. |
| Typed core §9; charter §§21,24 | Ordinary `x,y` use Value entry and actual Pure introduction; entry belongs to complete invocation even for an unused formal and pure body. |
| Callback-context delivery §§2–4 | B applies to a literal in a supplied known callback slot; endpoints are independently generated and one completed comparison is required. General scheme instantiation and member lookup are expressly outside its bounded judgment. |
| Source contracts §§2–3 | Independent `DescMem`/complete admission remain active on the same whole tuple; positive execution references are not a descriptor-typing rule; constructor typing and complete emission conformance are premises. |
| Source contracts §§6–9 | Allocation-view results require independently checked complete views, aligned kernels and retained simultaneous obligations; they do not construct recursive discharge or all generalizable views. |
| Certified constrained use §§2.2,5 | Given an actual generalizable presentation, copy only its eligible owned identities, fix imports, retain the whole residual/scopes and append the designated-export Direct query; availability of this syntax does not select eligibility or prove the query. |
| Charter §§22–23 | Guard each actual derived comparison with variable-only levels. These clauses do not create a body/member comparison or classify a template binder as an existential introduction. |
| RS/LX supplier §§3.4,7.1 | Lexical ownership and imports are constructively known; simultaneous discharge and actual semantic view/binder selection remain separate source clauses. |
| Recursive source validation §§3–5 | K constructs the actual knot; KP pairs finite execution prefixes; KV emits an exact same-provider validator relative to independent membership. Satisfaction, source-typing correspondence and effective presentation remain open. |
| Generalization eligibility attack §§3–4.1 | PG-1 covers nonrecursive projection lambdas relative to complete aligned constructor premises; it excludes this recursive-validation step. |

Explicit hypotheses for the supported trace:

1. The finite source is correctly resolved; its original lexical component
   is closed and its two member references resolve to each other.
2. Register original source interfaces `I_f=Value(R_f)` and
   `I_g=Value(R_g)`, without solving `R_f,R_g`. Preserve the ordinary
   fresh parameter endpoints `A_x,A_y` at their own original source scopes.
3. Use K's finite actual provider graph and the selected Name/Result/entry
   constructor laws. Typed core mathematical realization remains conditional
   on its independently typed premises.
4. Keep one symbolic original `xi=(nu,K,D)`, its binder tree and one whole
   witness `w`. Neither a satisfying completion nor successful `Q` is assumed.

Established dependencies: the reviewed K/KP/KV and LX bounded statements.
New bounded characterization: the exact open synthesis/tree below and the
first unsupported source-rule input. Conditional statement: the operational
constructor reductions in §4. Candidate only: any proposed `Omega` or
Generalize presentation. No full membership, admissibility, semantic
eligibility, principality or source acceptance result is established here.

## 3. Exact proof tree and residual leaves

Let `Gamma_K={f:Value(R_f),g:Value(R_g)}` use the *same* two registered
roots in both branches. These are open assumptions, not validated bindings.
Original source scopes are denoted by their lexical positions, without
assigning §22 levels. The constructor tree is:

```text
Gamma_K(g)=Value(R_g)                     Gamma_K(f)=Value(R_f)
-------------------- Name                -------------------- Name
Gamma_K,x:Value(A_x) |- g : Value(R_g)     Gamma_K,y:Value(A_y) |- f : Value(R_f)
-------------------- Result              -------------------- Result
n_bf = result(name g)                    n_bg = result(name f)
J_bf = Comp(empty,R_g)                   J_bg = Comp(empty,R_f)

x unannotated                            y unannotated
-------------------- Parameter           -------------------- Parameter
P_x=Value(A_x); ValueEntry(x)             P_y=Value(A_y); ValueEntry(y)

P_x, n_bf; actual Pure introduction       P_y, n_bg; actual Pure introduction
----------------------------------       ----------------------------------
S_f=Value(Fun(P_x,J_bf))                  S_g=Value(Fun(P_y,J_bg))
```

This table's `Fun(P,J_body)` is the source body/result skeleton. It must not
be read as a solved bound on complete invocation with arbitrary admitted
carriers. Lambda formation retains the original captured roots and the
complete entry/provider kernel.

The actual lexical operands furnished by K are:

```text
v_f = Closure(f, Pure, ValueEntry(x), result(name g), eta_f)
v_g = Closure(g, Pure, ValueEntry(y), result(name f), eta_g)
eta_f(g)=v_g; eta_g(f)=v_f; eta_K(f)=v_f; eta_K(g)=v_g.
```

No provider may be reselected in either branch. The next proposed source
conclusion would need the following application; `???` denotes a missing
proof rule, not an introduced rule of Yulang:

```text
open synthesis S_f,S_g on Gamma_K; the fixed graph K_S
independent descriptor/admission interpretation; original local obligations
??? complete constructor typing/discharge at these registered roots
-------------------------------------------------------------------------
OriginalLocalObligations_S(xi,w)
and CompleteMem(R_f,v_f,K_S;xi,w)
and CompleteMem(R_g,v_g,K_S;xi,w)
with a validated same simultaneous source environment
```

KV constructs the displayed semantic predicate with these exact operands;
KV does not prove it. The earliest unsupported rule input is **complete
constructor typing/discharge**, rather than root allocation, provider identity,
typed Name's syntactic endpoint copying, or a missing freshening map.

For these bodies, a closure check must retain the argument history,
receipt/rebind and actual result provider. When `f` finishes it returns
`v_g`, so its latent result check reaches the original `R_g,v_g` obligation;
the opposite branch reaches the original `R_f,v_f`. Open environment
soundness cannot close those leaves because it assumes the memberships it
would need to conclude. Constructor guarding makes the runtime knot finite;
it has not, by itself, supplied a decreasing complete-membership rule.
Independently admitted argument worlds and all subsequent provider uses
remain part of that complete obligation.

The blocked use tree can now be located exactly:

```text
validated simultaneous source environment               [missing above]
actual admissible generalized view P_f and binder tree    [not reached]
eligible owned Omega_f / rigid semantic anchors           [not reached]
whole-copy Use(P_f,V), designated-export Direct evidence  [conditional on P_f]
Name f at that instance; literal (); ordinary Call       [not source-derived]
```

No body/member equality, directed lower inclusion, exact SCC solution,
successful Q, closure coinduction, or guessed eligibility predicate is
inserted to complete this tree. No new query needs a §22 classification in
the completed fragment; if such a query is later generated it still needs
its independent introduction classification and guard.

## 4. Constructive operational subset and placement information

There is a constructor-equation reduction on the fixed graph that does not
solve the blocked typed tree. Conditional on an argument carrier actually
returning a value `a` in current state `C`, the selected Value entry gives

```text
Invoke(v_f,t,C0)
  = Receipt_f(t); Force(t) >>= (a,C).
      Rebind(x,a,C); Return(v_g,C)

Invoke(v_g,t',C1)
  = Receipt_g(t'); Force(t') >>= (b,C').
      Rebind(y,b,C'); Return(v_f,C').
```

For a pure returning literal argument these equations give the proposed
`f ()` result `v_g` and the proposed `(f ()) ()` result `v_f`. These are
reductions of the existing constructor schema, not parser/compiler runs or
claims of complete source typing/admission. For suspended or divergent
arguments, keep Pending and the original suffix; neither reduction asserts
that a result is reached. No generalized member is created by Return.

This determines concrete placement **constraints**, not eligible binders:

| Original identity | Information actually determined |
| --- | --- |
| `f,g` provider roots | Both use results retain their original lexical graph identities. A scheme copy cannot allocate a replacement runtime provider merely because it freshens semantic coordinates. |
| Cross-member references | `g` is an import of the individual `f` lambda and `f` an import of the individual `g` lambda. The closed lexical component has no captured outer value roots. These two facts concern different boundaries. |
| `A_x,A_y` | Two distinct fresh inferred parameter endpoints are registered at their own original source scopes. Each body's terminal Name resolves to the other member, rather than to its formal; no independent result endpoint is registered there. Transitive dependencies through unresolved member contracts remain unknown. Registration and runtime rebind do not establish template eligibility or source instantiation independence. |
| `R_f,R_g` and their latent dependencies | Original Name/Result references retain them jointly. The source supplies no independently fresh result endpoint at either return. Whether a legal generalized view binds particular semantic coordinates is still unproved. |
| `xi`, scopes, residuals, admission/profile incidence | All hypothetical later view transport must preserve the original joined relationship. No per-port or per-member independent witness selection is justified. |

Thus the trace establishes **no actual semantic binder entering a generalized
view**. It also does not establish that the eventual binder set is empty.
There is no actual admissible view to which PG-1 or certified-use freshening
could yet apply. Lexical closure of `{f,g}` does not authorize a single
component-wide binder block; individual capture imports do not establish
that every locally originated endpoint is permanently rigid. The placement
question has been localized, not answered by choosing either shortcut.

## 5. Evidence independence, omissions and freeze

No executable oracle or checker was used. Frozen Oracle supplied no premise.
The proof tree uses the selected source rules and existing reviewed
constructor results; these are shared assumptions, not independent empirical
validation of the source rules. A checker replaying these equations would
test their consistency only and would leave the discharge premise intact.

There were no search seeds/ranges, randomized cases, mutations, semantic
acceptance probes, tests, builds, child agents, questions or Git mutations.
Coverage is exactly the two lambda/Name branches and the two conditional
completed-call reductions above. Unguarded aliases, recursive initialization
effects, mutable captures, arbitrary clients, handler worlds, changed
contracts, all-view completeness and effective solver presentation remain
unverified. The assigned packet supplied no numeric CPU/RAM/wall-time limit;
this lane used bounded file inspection and one note construction/repair.
At most four lightweight shell read commands were dispatched concurrently;
hash comparison used one Python process and sequential read-only Git children.
CPU time, peak RSS and elapsed session wall time were not measured. No heavy
process or executable semantic model was launched.

Failure conditions: invalid resolution or constructor guarding invalidates
the graph dependency; altered parameter/role/result rules invalidate the
tree; a newly supplied independent closure descriptor/admission discharge
rule can remove the blocker and must be checked on these same original
operands. None of these conditions licenses filling the missing premise
with Q success or inferred shape.

Producer checks: initial branch/HEAD/status inspection; direct dependency
SHA-256 and byte equality against the pinned commit; narrow leased-file
whitespace/scope inspection after writing. Several oversized initial read
captures were truncated; the operative sections used in this note were
subsequently read in bounded captures. There is no exhaustive repository
search claim or independent review claim. The exact artifact hash is supplied
in the final handoff packet. Writes stop before submission for frozen review.

Recommended next action: derive the independent complete closure
descriptor/admission rule on K_S, including the returned provider's guarded
latent obligations and arbitrary admitted entry histories, before assigning
an actual Generalize view or binder set. This is the missing source proof
input; another alpha-copy or finite execution toy probe cannot discharge it.

## 6. Frozen direct dependencies and commit packet

All direct dependencies below matched baseline bytes before the note write.
Recheck them at integration; unrelated branch movement alone is not a
semantic invalidation.

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-04-certified-callback-and-constrained-use.md` | `887bc7c0743d2f34608b46ccb8e5ee9b58ea4a39995b93a5aaced764295bae80` |
| `notes/progress/2026-10-06-directional-recursive-generalization-supplier.md` | `2f169e0f894fff8695cf8e1ef40f5a9734abfe87484d9db6aab23eae941b8898` |
| `notes/progress/2026-10-06-recursive-source-validation-construction.md` | `630c73123239be97e2fb4466d84b5e2dccaeb535450ddce2ec063f1d67226407` |
| `notes/progress/2026-10-06-source-generalization-eligibility-attack.md` | `2445a67ab8ce3372e7acd62fd90d598ca1ea3bc92872ff9b8588f176fc077d3e` |

- Exact lease: `notes/progress/2026-10-06-recursive-generalization-discharge-attempt.md`.
- Baseline: `843f78ccaae0eac1a49838b54cf2a3863aa0b8a9`.
- Changed direct dependency hashes: none at producer freeze.
- Review status: unreviewed, research-only; frozen for independent review.
- Checks: branch/HEAD/status; pinned dependency byte/hash comparison; narrow
  leased-path whitespace/scope inspection. No tests/builds/semantic runs.
- Proposed checkpoint commit: `research: trace recursive discharge before generalized member use`.
- Shared-record deltas intentionally left for primary/curator: link this
  failed exact-source use tree if useful; preserve the discharge frontier
  before actual Generalize and retain semantic eligibility/placement as
  unresolved. No gate closure, authority promotion, task/index edit or new
  language decision is proposed.
