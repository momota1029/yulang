# Provider constructor derivation and the first production premise

Date: 2026-10-06
Status: independently reviewed conditional source/reference derivation; production interpretation remains open
Baseline: `4b8896bdad558431f09f1221661a10a1c8271469`
Branch: `research/simple-sub-intrusion`
Lease: this file only
Implementation authority: none

## 1. Objective, authority and hypotheses

This note extends the already reviewed [quiet-provider derivation](2026-10-05-quiet-provider-constrained-descriptor-derivation.md), rather than treating its constant-body argument as new evidence. Its new proof seam is the returned closure that captures a declared operation: what finite source derivation survives return and future invocation, and what production rule would have to certify it?

The approved denotation answer `production-function-denotation-answer/d1`, decisions 1–5, selects complete typed observations in the original `Rel_C` fiber, restricted jointly by independently interpreted endpoint, role/entry, typed-path, origin, continuation, scope, authority and dependency constraints. Admission is separate and comparison-independent. The approved membership answer `production-function-bound-membership-answer/d1`, decisions 1–4, retains Option 2: production observations need not have source-constructor witnesses. Neither answer selects concrete descriptor/admission rules, `W/Z`, a carrier, or implementation.

Governing sections read:

- [Denotation follow-up](2026-10-05-production-function-denotation-followup.md): accepted scope, direct derivation, paired provider probe, constant certificate refinement and its reviewed limits. This source has named headings rather than numbered §§1–4/7; those headings identify the assigned content.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md): §§2.2, 3.1–3.7, 6.1–6.3, 7, 8, 10.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md): §§2–3, 6, 8, 9.
- [Theorem C](../design/2026-10-04-source-generated-callback-structural-theorems.md): §§2.1–2.4 and 3.
- [Source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md): §§2–4.
- [Ordinary computation package](../design/2026-10-02-ordinary-computation-semantics-package.md): §§2–3, only for the existing inert introduction/current-context clauses. It remains Draft.

Fix one original `xi=(nu,K,D)` and binder tree. All derivations below are conditional on the following supplied premises, not inferred from four endpoints:

1. Theorem C's finite decorated immutable source envelope: preallocated labels and monomorphic recursive references; source-labelled exposed providers/consumers; independently certified whole-tuple primitive relations; compatible owner/view kernel, receipts and typed paths. No mutable cells, opaque imports, implicit adapters or offered handler-image nodes.
2. Theorem C §3's independent punctured-context certificate for the initial whole carrier, and its separate local response/resumption/future-use certificates. Each finite client graph is separately certified; no bound is imposed on finite history length.
3. An original declaration instance `op : Fun(Value(Unit),Comp(E,Unit))`, with its declared native producer, result consumer, request witness, response endpoint and existing authority/`K,D` premises. `E` is its supplied legal guarantee, not an invented singleton effect row.
4. For offering the quiet leaf at that displayed interface, the existing complete source/reference certificate and typed-core §8's fixed-domain, genuine-guarantee-only weakening premises. In particular `empty` is covered by `E`; the changed field is classified guarantee-only and not a shared/imported/routing invariant. Admission, entry, endpoints, receipts, paths, scopes and dependencies stay fixed.

These hypotheses retain the decorations that the source packages take as input. They do not assert their elaboration from arbitrary raw syntax.

## 2. Finite source derivation for the two leaves and their providers

Use the exact provider pair from the denotation follow-up, with the quiet input specialized to its existing constant leaf:

```text
G  = Fun(Value(Unit),Comp(E,Unit))
Q  = lambda(Value(Unit), result(literal Unit))
R  = lambda(Value(Unit),
       call(result(operation op), result(literal Unit)))

Fq = lambda(Value(G), result(name f))
Fe = lambda(Value(G), result(R))
```

`f` is the outer parameter binder, not a fresh provider chosen on future use. An admitted carrier that returns Q is rebound to this same binder. Q's source body skeleton is `Comp(empty,Unit)`; presenting its weakened certificate at G is conditional on hypothesis 4. R's body has the operation call's symbolic complete-invocation endpoints and constraints; identifying its declared completed result with `Comp(E,Unit)` requires the supplied operation contract and its typed composition premises. No arbitrary Function conversion is derived.

The finite construction has the following proof DAG. Each row refers to an existing constructor, and references shared operands instead of duplicating their witnesses.

| Node | Source derivation and retained evidence |
| --- | --- |
| `Unit` / `result(Unit)` | Literal relation; `Value(Unit)`; return in the current configuration. |
| `Q` | Lambda rule over `result(Unit)`; inert closure with Value entry and empty body/result guarantee. Its complete call certificate includes argument Force. |
| `op` / `result(op)` | Same declaration-instance producer and consumer; return the operation descriptor inertly. |
| `call(op,Unit)` | Return the callee; reify the whole Unit argument; actual operation receipt/entry; native request-carrier construction and native return; declaration-derived result consumer. |
| `R` / `result(R)` | Inert closure over that call; retain the same lexical operation root, source label, body/consumer and typed dependencies; return that closure without invoking it. |
| `Fq` | Value entry; typed rebind of the outer carrier result to `f`; name lookup returns that same provider. |
| `Fe` | Same outer Value-entry skeleton; typed rebind; inert construction and return of R. The captured operation is the original lexical declaration instance. |
| Future leaf call | Reference the actually returned provider's retained label/root and original typed port; establish a new invocation in the current compatible context. |

Thus both outer body/result **skeletons** can display `Comp(empty,G)` under the supplied endpoint/certificate premises. This says neither that their complete outer call is effect-free nor that production membership at the displayed descriptor follows.

For arbitrary admitted outer carrier `t_G`, the common entry is

```text
receiver / receipt;
Force_argument(t_G) >>= (v,C1).
  typed rebind f := v;
  Return(v,C1)   [Fq]
  Return(R,C1)   [Fe]
  >>= ReturnFromInvocation
```

Before Force returns there is no constructed returned provider on which a future-call rule can act. If Force requests, the original request witness is retained and the selected outer suffix is appended to its raw continuation. A resumed suffix runs in the current resumed configuration. It does not replay receipt, pick a different operation instance, or independently hide the continuation's shared witness.

For a later admitted carrier `t_Unit`, Q has the previously certified image

```text
receiver / receipt;
Force_argument(t_Unit) >>= (u,C2).
  typed rebind;
  Return(Unit,C2) >>= ReturnFromInvocation
```

R has the same entry followed by `ExecuteCallable(op,Delay(result(Unit)))` within its body. The operation executes its own source entry, returns its inert request carrier at its native delimiter, and its declaration-derived consumer executes that carrier. Only this last step exposes the declared request. The raw request suffix contains the existing consumer completion and all enclosing invocation-return obligations. Native producer return alone is not the completed operation call.

In each image, the ordinary equations are sufficient:

```text
Return(v,C) >>= S = S(v,C)
Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S)
```

Induct on each finite §3-admitted history using those equations and the retained provider labels. Initial carrier execution uses its supplied certificate; response extension uses the exposed request's original witness; repeated resume uses that same raw handle; future invocation unfolds only the returned provider. This yields the whole joined source/reference relation, including divergent Force prefixes and repeated finite future developments. It does not prove termination.

The three incidences remain distinct at every Value-entry call: `d-` is the received carrier/Force view; `d+` is its argument-origin contribution at the complete `CallView`; `b+` is the body/result-consumer contribution. Incoming requests can occur at `d+` even for Q. At R's later call the operation-consumer request is a body contribution of that call; it is not an event executed by Fe when returning R. Their dependency links remain joint in `xi`.

## 3. Small discriminator, with its exact limits

Choose independently certified pure `t_G=result(Q)` and future `t_Unit=result(Unit)`, and a compatible current context with no eligible handler for the declared request. The operation contract must permit the request on the supplied Unit payload. Then:

```text
call Fq t_G  -> returned Q; future call Q t_Unit -> Return(Unit)
call Fe t_G  -> returned R; future call R t_Unit -> Request(q,C,k)
```

With a separately admitted Unit response, the latter continues through the original k and the enclosing return suffix to Unit. This is a conditional source/reference witness, with one outer call and one future call per lane. For this pair, zero future invocations cannot expose the latent request difference: both outer calls return typed inert providers. Concrete value identity is erased by `Pi_xi`, so the typed request and retained origin/continuation/authority/dependencies are the discriminator. This is not a proof of identical production bounds or equality of the complete latent interfaces at the initial return.

No executable oracle was used. The argument is grounded in the cited source constructors and supplied primitive/kernel certificates. Those contracts are shared assumptions of both lanes. The witness discriminates inert return from subsequent operation execution; it does not validate the supplied source rules against legacy execution or production. No random seeds, enumeration ranges or implemented mutations exist. The named invalid shortcuts are: executing R when returning it; omitting the operation result consumer; restarting receipt on resume; erasing `d+` from Q's call; or picking a new operation witness after outer return. The documentary derivation rules out each shortcut conditionally, without reporting mutation-test results.

## 4. Smallest complete proof interface and the first absent premise

For this restricted constructor family, a source certificate is a finite rule graph plus its original-scope joint witnesses. Write `Src_i(h,O,w;xi)` for the generated relation of a leaf or outer provider i, and `Adm_ref,i` for the independently generated punctured histories. Existing rules justify

```text
Adm_ref,i(h;xi), Src_i(h,O,w;xi)
  => (nu,O) in the original complete Rel_C fiber
  => Pi_xi(O) in P_ref,i(h;xi).
```

The second implication is the reference root rule. It is not a constructor typing lemma for production.

A complete production bridge for these two cases would need exactly two separate interfaces, over the existing observations and retained evidence:

1. **Admission bridge:** an independently interpreted `A_A(R_i,h;xi)` with initial, typed-response, same-handle-resume and returned-provider-future clauses, and a proof `Adm_ref,i(h;xi) => A_A(R_i,h;xi)`. Future clauses must mention the actual joint history, original typed port, retained provider/continuation and current context. They cannot assume the filling satisfies the pending Function comparison.
2. **Constructor membership bridge:** independently interpreted endpoint and complete-descriptor clauses, proving

   ```text
   Src_i(h,O,w;xi) and Adm_ref,i(h;xi)
     => M_A(R_i,h,O,w';xi) and DescMem_A(R_i,h,O,w';xi)
   ```

   where w' preserves all original coordinates, binder positions, sharing, authority and complete evidence. Local witness packaging may change; independent per-segment choices are forbidden. For `result(R)`, the clause must retain a latent provider obligation whose later call is certified by R's same entry/body/consumer evidence. For R's operation call it must consume the declared result port after native return. Endpoint constraints must be incident to their proper `d-`, `d+`, `b+` and latent-result occurrences, rather than applied to separately projected marginals.

These are necessary proof interfaces for the source-to-production inclusion in this envelope, not selected definitions or an assertion that they suffice for all production extras. No new coordinate/carrier is introduced. The notation isolates the missing judgments; no recursive `DescMem_A` equation or exhaustive production admission grammar has been supplied by the cited clauses.

There is no required ordering between the two bridges: full inclusion first needs admission. **Even granting the admission bridge**, the first production-only step in the finite constructor DAG is source-contracts §2.2's constructor typing lemma. For Q it must certify the retained whole Force/bind image at G, rather than just `empty <= E` at the body port. For Fe it must certify that returning R installs the recursively valid original latent provider obligation, so future R calls can satisfy the complete descriptor without adding arbitrary request authority or losing shared operation dependencies. Source typing builds those retained source certificates; it does not define the production `DescMem_A` predicate to which they must map.

This is a missing **source-to-production rule clause**, not a missing operational clause for these constructors. Its precise absent content is the comparison-independent interpretation/typing rule for a returned Function value at its complete typed incidence, coupled to later admissible uses of that same latent provider and the original complete-call endpoint constraints. The lambda/result/source-label rules specify the witness's behavior; the production descriptor rule must specify whether that behavior satisfies its independently interpreted constraints. Four endpoint children, a local success `A <: B`, or source/reference realization does not supply that rule.

No proof here says the existing `Rel_C`, paths, `K,D` or subtraction evidence cannot express the rule. No source counterexample to selected A or Option 2 is established. Unsupported production clauses remain candidates only.

## 5. Why the sufficient abstractions do not discharge this step

Source-contracts §3.7 defines its hard envelope G to include ordinary descriptor membership and requires **source-base typing `R subset G`**. For the providers above, that inclusion already requires the missing constructor-membership bridge. Extensivity of `H_G(R)` proves source inclusion only after `R subset G`; the positive grammar cannot derive the guard's meaning or make a source tuple satisfy an unknown `DescMem_A`. Its unchanged-admission theorem likewise explicitly requires independently certified future-use rules for abstract providers. Paired `W/Z`, exhaustive alternatives and transport certificates remain unselected additional hypotheses. Approved A makes no such grammar mandatory.

Section 6.3 quantifies over finite independently source-checked, kernel-aligned allocation views with their original local endpoint witnesses, coverage certificates and unchanged value/typed paths. Section 7 assumes §§2–6, including §2.2's interpretation and descriptor lemmas. Their finite allocation proofs can supply coverage obligations and reconstruct old source constraints; they do not define complete production descriptor satisfaction or establish the necessary latent-provider admission certificate for an arbitrary view. The `higher` row in §8 identifies relevant outward regions, without certifying an entire source/value/capture interface. A latent stage outside one outward region needs its own certificate.

Consequently neither sufficient abstraction changes the exact first gap. If independently supplied membership/admission clauses eventually justify the bridge, these packages can transport its certificates under their stated premises. They currently cannot provide those clauses by applying their conclusions backwards.

## 6. Verification, resource use and frozen handoff

Read-only commands: `git rev-parse HEAD`; `git cat-file -t` for the initially mistyped packet SHA; narrow `rg`/`sed`/`cat` source reads; targeted `git status --short -- <dependency paths>`; Python SHA-256 byte comparison using `git show <baseline>:<path>`. The malformed packet SHA was not an object; the primary explicitly corrected it to the baseline above before the write. An attempted read of `2026-10-02-ordinary-computation-core.md` failed because that path does not exist; the index resolved the actual ordinary-computation package, whose relevant sections were then read.

All substantive dependency bytes matched the corrected baseline. No tests, builds, executable derivation checks, exhaustive searches, performance samples or compiler edits ran. Local calls were sequential, with at most one lightweight command process active at a time. Commands completed in less than 0.2 seconds each as reported by the command tool; aggregate CPU time, peak RSS and total wall time were not instrumented. One documentary pass and one leased note were produced. Source-history induction is conditional mathematical reasoning; it is not measured finite execution coverage.

Independent review found no BLOCKING, major or minor issue within the conditional source/reference scope. It confirmed that returned `R` retains its operation instance and dependencies, future invocation uses the current compatible context, and `A_A` remains separate from constructor membership. Unverified scope: production `DescMem_A`/`M_A` and `A_A`; conservative root extras; production callback containment; F5/legacy conformance; arbitrary source elaboration, imports, mutable state, adapters and handler images; full generalization/use certification and principality. The artifact is frozen after writing, review and byte/dependency checks; further repairs belong to an explicit follow-up lease.

Recommended next action: derive the comparison-independent returned-Function constructor clause and its linked admission clause against existing authority. Further toy executions of the same source transitions would leave this exact premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-descmem-provider-derivation.md`.
- Baseline SHA: `4b8896bdad558431f09f1221661a10a1c8271469`; supersedes the primary-confirmed malformed dispatch SHA. No Git mutation performed.
- Claim/review status: independently reviewed conditional source/reference derivation and production-rule blocker; no established production theorem or implementation authority.
- Checks already run: the source-section reads, reference bind/consumer/future-use derivation comparison, targeted clean dependency status, baseline-byte equality, and SHA-256 inventory stated here. No tests/builds or executable mutation results.
- Proposed one-line commit: `research: isolate returned-provider DescMem and admission premises`.
- Dependency hashes changed: none. SHA-256 direct proof dependencies:

  | Path | SHA-256 |
  | --- | --- |
  | `notes/progress/2026-10-05-production-function-denotation-followup.md` | `c625dd2b9bf73afc250d3d51cc7a04937aaad9881cf9c5def20e74082cd8509a` |
  | `notes/progress/2026-10-05-quiet-provider-constrained-descriptor-derivation.md` | `6fc4d90085b2762b3d91bf82c41b31557a69168314b77c9dc2b1ebc675371db9` |
  | `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
  | `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
  | `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` | `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe` |
  | `notes/design/2026-10-04-source-indexed-callback-realization.md` | `76874a219ac86068027b1f08a5bc27a12d93a0169a52cebd896a6ff6f2c6b671` |
  | `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
  | `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
  | `questions/2026-10-05-production-function-denotation/receipt.md` | `8654359c41d2bf4871904d017d0282155d8763496986a3254405a1220318708b` |
  | `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |

- Shared-record deltas intentionally deferred to the primary/curator: add a research-only locator in `tasks/current.md` and, if accepted, the theory dependency map; record that the returned-provider source DAG closes conditionally but source-contracts §2.2's production constructor lemma and independent domain bridge remain open. No gate/status promotion or design/index/authority change is proposed.
