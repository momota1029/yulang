# Attach-Call contribution: complete source prefix and the remaining interpretation

Date: 2026-10-06
Baseline: `1d29aafb1a89568ac61bc6bf007398db2b31cc23`
Status: frozen, compiler-referee-reviewed research-only constructive derivation; no findings in scope
Lease: this new note only
Scope: `my apply f = { my step x = f x; step }`, its one direct Call exposure
Authority and implementation permission: none

## 1. Objective and result

Attempt the smallest source-owned `Attach_C(X,e0,t0)` clause, retaining the
complete invocation and its original coordinates. The supported result is a
**source construction of a complete invocation expression with its origin**,
followed by a bounded determination of the exact unresolved field. It does
not establish original signature licensing.

The address/protection predecessors already construct `p0` and `e0`. This
attempt additionally spells out what must occupy the proposed attachment's
invocation operand: one source-rooted complete Call expression, including
callee evaluation, the inert whole argument, actual entry, body, designated
consumer, return and pending suffix, on the same original row. That expression
is constructible before solving the Call constraints. It is neither a bare
body row nor a witness chosen separately for each effect endpoint.

The expression does not determine the original contribution coordinate `c0`
in `t0=(beta,s0,p0,c0)`. The inspected original signature/owner/view input of
`TypedCallCert_Dec` still supplies the association of that complete invocation
with a licensed contribution and static slot. No inspected rule converts the
whole invocation expression into that input. The note therefore freezes a
maximum justified prefix and an explicitly candidate attachment; it does not
choose an interpretation of the missing field.

## 2. Governing sections and hypotheses

Use the primary's pinned baseline and these exact sections:

- [Inferred Function views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–5: source/public/internal distinction; one shared contract and original
  scope; source formation before Q; complete formation remains open.
- [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: original protected variable to upper output; no lower backflow;
  protection is not contribution membership, receipt or authority.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §2, §3 opening, §6.1, §§8–9: independently interpreted whole-tuple
  primitives and owner/view kernels; supplied decorated source; complete
  Call coverage is a candidate allowance interpretation; Option 2 extras
  and resolver completeness remain separate.
- [Approved nested meaning](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: sequential local binding; return `step` inertly; same outer `f`
  capture; no source-meaning expansion.
- [Call construction](2026-10-06-source-call-generation-construction.md)
  §§4.2–4.3, §5, §7: generated initial address; supplied decorated certificate
  inputs; complete invocation expression; original profile and admission cuts.
- [Licensing factorization](2026-10-06-original-signature-licensing-construction.md):
  the incidence sorts, conditional `A_sound`/`A_invert`, and separation of
  `Attach_C` from independently interpreted `Lic_C`.
- [Constructor derivation](2026-10-06-original-signature-constructor-derivation.md):
  the original signature/owner/view input of the complete Call certificate
  is retained by the ordinary constructors.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3, §6 structural rules, §9 entry: symbolic source interfaces, structural
  execution, actual provider-owned entry and complete invocation.
- [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6 introduction/transport: original profiles are supplied by elaboration;
  matching paths preserve their source indices and do not create grants.

Fix the resolved approved component C, original binder tree and one candidate
whole row X containing `xi=(nu,K,D)`, U, actual providers, environment,
world/current configuration, continuation, original source paths and the
retained semantic obligations. X need not be admitted, satisfiable or a
completed original solution. Each local existential remains under its original
rigid dependencies. All constructions below use this X once.

Hypotheses H: the approved core correspondence and lexical resolution;
ordinary symbolic parameter/Name/Result/Lambda/Bind/Call constructors; the
selected unannotated seed at `d_f`; and its same-root seed-at-exposure witness.
The established predecessor conclusions are the singleton **direct exposure**
domain `{e0}`, the original `ElimOrigin` address incidence and `NewProtection(e0)`.
Their proofs are not repeated. H supplies neither complete `Slots(beta)` nor
an original licensed contribution, profile certificate, admission or Q success.

Interpreting a complete image additionally uses the existing independent
actual-provider/entry/world and decorated kernel contracts. Retaining those
contracts as operands does not derive their validity. Actual callable roles
and entries remain actual; the formal's refinement changes none of them.

## 3. Construct the complete operand instead of inventing its contribution

Let `c_fx` be the source Call, `u` its upper-use identity, and
`sigma_x` its original body scope. Use the shared `R`, `A_f`, `A_x` and:

```text
beta=(d_f,R)
p0=(beta,call.effect)=outEff(U)       [corresponding notation, not all Slots]
e0=(k,beta,u,sigma_x,p0)
ElimOrigin(c_fx,u,d_f,R,p0,p_out(c_fx))

J_f = ReturnImage(Name(d_f), original typed environment)
J_x = ReturnImage(Name(d_x), original typed environment)
T_x = Delay(J_x, original lexical references)
```

`J_x` returns the rebound `x` value. It is not the external carrier received
by `step`; that carrier has already undergone `step`'s actual entry before
the body can read `x`. Replacing `J_x` by an arbitrary computation with its
printed `Comp(empty,A_x)` interface loses this source identity.

The structural translation constructs the expression:

```text
C_c[X] = J_f >>= (lambda actual_f.
    ExecuteCallable_X(actual_f,T_x; U,e))
```

Here U and e denote the original symbolic view/checking coordinates; e is
not the protection witness e0. This is the complete Call expression/root,
not a selected execution or an effect-family set. `ExecuteCallable_X` refers
to the actual callable's existing executable definition under the original
complete view. Its interpretation retains the decorated kernel operands
required by the existing Call rule. Generating this expression does not
manufacture those operands' source certificates.

For an actual Value-entry closure its structural branch is:

```text
actual receipt and boundary establishment;
Force_argument(T_x) >>= (a,current_state).
RebindResultPath(T_x,a,current_state);
Run(actual body in its original environment[x_formal:=Value(a)]);
designated result/return transition
```

For retained-computation entry, bind the same carrier without entry Force;
the actual body can execute its own designated consumers. For an operation,
retain its native return delimiter followed by its declaration-derived result
consumer within the complete consumer view. These are branches of the
existing actual-provider rule; the source formal's `NonHandlerFormal` record
does not choose a branch or rewrite a provider role.

Every request retains the original continuation and suffix:

```text
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S)
```

The suffix includes remaining entry/rebind/body/consumer/return stages. It is
not executed at suspension, dropped on divergence, or recreated by replaying
receipt at resumption. The current resumed state and original operation,
response, provider and K,D coordinates remain attached. This equation
therefore covers finite prefixes and suspended entry as well as returns,
conditional on the independent primitive interpretation.

The generated constraints retain this operand intact:

```text
WF_Dec(U;xi)
VIncl(A_f,U;xi)
WholeArgCompatible(J_x,CarrierContract(U);xi)
CIncl(C_c[X],Comp(E_c,A_c);xi)
TypedCallCert_Dec(c_fx,U,e;xi)
```

These are obligations. No solution, complete original profile or admitted
challenge is inferred by emitting them.

## 4. Maximum supported introduction and forward validity

Define a proof record `a_call(X)` containing only constructed coordinates:

```text
(OwnUpper source tag, e0, c_fx, beta, R, U, sigma_x,
 p0, p_out(c_fx), ElimOrigin, J_f, J_x, T_x, C_c[X],
 references to original environment/world/continuation/xi and checking operands)
```

This is note-local proof notation, not a new runtime carrier or original
contribution sort. Referencing an unresolved decorated input records where
it is needed; it does not supply its proof.

**Bounded source-prefix theorem.** Under H, the selected source constructors
introduce `a_call(X)` with one complete invocation expression rooted at the
actual `c_fx`. Its forward interpretation is the complete Call clause of the
existing structural translation, at `p_out(c_fx)` corresponding to p0. This
holds before successful checking; it is not the implication to `Lic_C`.

Derivation:

1. Name/Result give J_f and J_x over the resolved original roots. Lambda
   creation/capture and the outer Bind preserve these references without
   running `step`'s body. The approved final `step` returns that closure.
2. The ordinary Call constructor delays J_x and sequences J_f into the actual
   producer's `ExecuteCallable`; this is exactly C_c[X], not a projection onto
   a body or outward allowance.
3. Gen-Call-0 connects this source elimination to p0 and p_out(c_fx). The
   protection predecessor supplies e0 separately. Pairing them uses their
   same `c_fx,u,R,beta,sigma_x`; it uses no effect endpoint equality.
4. The independent constructor image interpretation gives the execution
   branches and Request/Bind equation in §3. Every stage keeps the original
   whole tuple and suffix. Thus the record's complete operand is the source
   Call expression, including finite-prefix behavior.

The first three steps establish deterministic source provenance of an emitted
expression. Step 4 is conditional on the independent decorated primitive
interpretation and cannot prove that interpretation or its raw-source inputs.
On canonical source labels, forgetting `a_call` and reconstructing it gives
the same record, up to one coherent fresh-name renaming of all dependent
coordinates. This conservativity concerns redundant source-expression records;
it does not assert that the retained semantic obligations have a solution.

The upper source tag stays separate from actual provider/result packet tags,
even when endpoints coincide. Constructing the entire actual invocation as an
operand does not stamp its provider-lower effects with e0. No actual event
membership, `Observe`, `Receive`, live receiver or removal grant follows.

## 5. Smallest candidate attachment and its exact unsupplied fields

The incidence sort remains `t=(beta,s,p,c)` from the licensing predecessor.
Let `j_call` denote the rooted expression record from §§3–4. A natural minimal
candidate is:

```text
a_call(X) generated from c_fx
original signature/owner/view input associates
    (beta,s0,p0,c0) with j_call on this same X
------------------------------------------------ Attach-Call [candidate]
Attach_C(X,e0,(beta,s0,p0,c0))
```

The second premise is the existing Call certificate's original table input,
not a newly proved source rule. The table entry must retain the complete
invocation, original scope, dependencies and own-upper versus inherited tags.
It must specify what c0 means: an original complete contribution
witness/contract associated with the invocation, rather than merely its
computation root, code descriptor, effect endpoint or outward support.

Taking `c0 := j_call` would be a **candidate interpretation** of the contribution
sort. The inspected sources define the Call image and demand original
contribution preservation; they do not equate those sorts. A whole image can
be generated even when its checking constraints are unsatisfiable or when no
returned observation exists. Consequently it cannot be cast to a licensed
contribution merely because the image expression exists.

Similarly Gen-Call-0 names the mandatory static `p0` and initial seed position.
It does not by itself identify the separate slot coordinate s used by the
original licensing table. Setting `s0 := p0` may be a representation convention
for this candidate, but is not proved as an interpretation of that table.
This local slot association is distinct from exhaustive `Slots(beta)` coverage.
If the independent original table already identifies s0 with this address,
that premise can be instantiated; the note does not require or select a new
slot policy.

Thus the exact residual is **not** an unspecified implementation of Call.
It is the original table's interpretation of its `(s,c)` fields for the known
`(beta,p0,j_call)` occurrence, plus a source rule establishing that table
entry. The complete invocation operand has been supplied structurally; the
conversion from that operand to those original fields has not.

Relation to the previous obligations:

```text
A_sound:  Attach_C(X,e0,t) => Lic_C(X,t)
A_invert: Lic_C(X,t) => Attach_C(X,e0,t)    [exact direct exposure domain]
```

The prefix theorem proves neither. Once the original table input is derived
and independently interpreted, forward validity must show that its entry
satisfies Lic_C on the same X. Reverse validity must enumerate original
licensing last rules, including the original contribution/slot interpretation;
the one source Call does not prove that enumeration. Lic_C is not defined as
Attach_C, and no complete singleton profile is inferred.

## 6. Failure conditions, independence and stopping boundary

This is a constructive derivation, not an executable experiment, counterexample
search or established theorem about complete raw-source solutions. It shares
the explicit source/core and decorated semantic premises with the predecessors.
No Frozen Oracle source, output or mechanism was used. A checker implementing
the Call/Bind equations would check consistency under those equations; it
would not independently prove the source contribution/slot interpretation.
Seeds, ranges and executed mutation counts are inapplicable.

Logical mutations expose the exact limits:

- Substitute the actual body for C_c: loses entry and designated consumer.
- Substitute an outward row union for C_c: loses suspension, current state,
  original provider/response and continuation constraints.
- Substitute step's external carrier for J_x: changes the body Call's source
  argument root and may repeat entry effects that occurred before the read.
- Map p0 to `result.latent.effect`: contradicts the designated complete Call
  correspondence; returning step does not supply that path.
- Replace c0 by the expression root without a sort/interpretation lemma:
  discharges the missing table field by assumption.
- Paint lower/provider packets with the OwnUpper tag: violates the selected
  direction and loses independent inherited evidence.
- Treat emission as admission or use a different xi/world for c0: the result
  ceases to describe the one original shared Call relation.

These are proof failure conditions, not executed language counterexamples.
No valid X,t refuting A_sound/A_invert was found or sought. No different source
meaning, semantic impossibility or need for a user decision is established.

This lane stops at the original `(s,c)` interpretation rather than producing
another equivalent profile-image probe. Additional counts or more Call/Bind
models would leave that premise unchanged. The next useful method is direct
construction of the original signature table entry with a contribution typing
lemma, or a source-to-existing-kernel derivation establishing those fields.

## 7. Checks, resources and shared-record proposal

Commands: read-only `git rev-parse HEAD`, `git status --short`, bounded
`cat`, `sed -n`, `rg`, `rg --files`; Python SHA-256 and byte comparisons using
`git show <baseline>:<path>` for the nine direct dependencies; lease-path
absence check and note-local integrity/dependency recheck. All dependencies
matched the pinned bytes. Aggregate captures initially truncated; all decisive
Call, contribution-input and governing sections were reread in bounded output.
No absence conclusion relies on an incomplete repository search.

No tests/builds, Oracle, checker, Git mutation, formatting, scratch files or
delegation. Resource budget: one new note, consumed; zero heavyweight processes.
No numeric CPU/RAM/wall-time ceiling was supplied. CPU time, peak RSS and
elapsed wall time were not instrumented. Only short shell/read/hash processes
were used. The independent compiler-referee review found no issue within the
bounded construction and its authority boundary.

Unverified scope: original contribution/slot interpretation and its source
introduction; complete licensing inverse; complete Slots/profile and row
nonemptiness; raw-source typing/admission over all contexts/histories; general
annotations, recursive/multiple-use formation; operational event protection;
principality, Option A/2 production inclusions and production acceptance.

Recommended next action: derive the original table's `(s0,c0)` association for
the already constructed `(beta,p0,j_call)` operand, proving its contribution
typing and A_sound before attempting exhaustive A_invert.

Proposed task-map delta for primary/curator: record the complete source-rooted
Call operand as constructed at the static expression level, conditional on
the independent semantic kernels for interpretation; retain the original
table's contribution/slot association and licensing inverse as open. Do not
close FVIEW/SRC, profile formation, admission or the main gate. Shared records
and authority files were intentionally not changed.

## 8. Frozen direct dependencies

Hashes are SHA-256 of bytes at the pinned baseline; each matched the live
input at inspection. Historical predecessor dependency inventories remain
their own snapshots.

| Direct path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |
| `notes/progress/2026-10-06-original-signature-constructor-derivation.md` | `5dc90af8e6c789487ed3f0cb82ba254ce7a99648350f7dbce0e0f000184f8f19` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-06-attach-call-contribution-construction.md`.
- Baseline SHA: `1d29aafb1a89568ac61bc6bf007398db2b31cc23`.
- Changed dependency hashes: none; all nine direct inputs matched the pinned
  bytes. Primary must recheck at integration if the branch moves.
- Review status: compiler-referee-reviewed bounded source-prefix derivation
  and candidate attachment, with no findings in scope; no source-gate closure.
- Checks already run: governing-rule/source reads; complete Call/suffix and
  same-row/source-sort audit; nine hashes and pinned-byte comparisons;
  lease-path absence and note-local integrity/dependency recheck. No runtime
  verification.
- Proposed one-line research-checkpoint commit message:
  `research: construct complete Call operand for source attachment`.
- Shared-record deltas intentionally left for primary/curator: link the
  complete invocation prefix and exact original `(s,c)` association leaf;
  retain A_sound/A_invert, full profile/admission/principality/production gates.
  No task, theory-map, index, authority or question-board bundle was edited.

Research writing stopped before submission for independent review. Primary
owns adjudication and integration.
