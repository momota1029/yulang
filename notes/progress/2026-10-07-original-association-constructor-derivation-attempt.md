# Original association: constructive source-rule elimination

Date: 2026-10-07
Baseline: `1777ccec8369915ad2829f324e3e6d6dd08f697c`
Status: frozen, independently compiler-referee-reviewed research-only derivation attempt; no findings
Method: direct source/core derivation, then elimination of available last rules
Exclusive lease: this note only
Claim class: conditional skeleton derivation and bounded premise localization
Semantic/implementation authority: none
Review: compiler_referee PASS on SHA-256 `1860dc05859a20864f231258149804ade16fe18918b805d9634a3b7047d5fb65`; scope is bounded derivation, premise separation, five-node proof cut, and no global absence claim

## 1. Objective and result

Attempt to construct the first missing producer

```text
OriginalAssocType_X(beta,p0,j_call; s0,c0)
```

from the assigned source rules for the exact selected source

```text
my apply f = { my step x = f x; step }
```

The strongest supported derivation constructs its source-interface/core
skeleton, the complete invocation operand at `f x`, and, under the stronger
typed/history premises of the composition input, the exact transported upper
packet at that operand's callee read. The first unavailable conclusion remains
the original owner/view kernel's association of that operand with an original
static signature slot and a contribution-typed contract.

The delta from the previous backward attempt is a direct application of the
typed-core synthesis rules to this whole source, followed by constructor
elimination at its smallest Call subtree. It does not repeat a packet checker,
production correspondence audit, or reinterpret the selected block meaning.
There is no source counterexample, closed attachment theorem, or proof of
impossibility for other source rules.

## 2. Authority and explicit hypotheses

Read directly at the pinned revision:

- Inferred call views §§1.1–5: Authoritative shared formation direction,
  source/public/internal distinction, stable source identity, Q independence;
  exact generating judgments remain open.
- Source contracts §§2.2, 3, 6.1, 8–10: reviewed conditional construction;
  independently interpreted descriptor/owner/view and decorated source inputs;
  complete images and allocation coverage retain the non-coverage kernel.
- Typed core §§2–3, 6, 9: reviewed Draft construction; finite source/core
  skeletons, ordinary parameter entry, normalization and complete invocation.
- Nested-block addendum §§1–3: Authoritative interpretation of this exact
  source; sequential binding, inert final return and the same outer capture.
- Directional addendum §§2–4: current explicit user decision protects the
  original upper output; its rule notation remains a proposed formalization.

Accepted decisions remain one original `X` and `xi=(nu,K,D)`, formation and
admission independent of pending `Q`, upper-output protection without provider
backflow, Oracle as historical evidence only, and no production cutover before
soundness/principality/source adequacy. No new language meaning is selected.

Separate these premise sets:

`H_gen`: the selected resolved source/core correspondence; lexical bindings
`d_f,d_x,d_step`; registered shared inferred endpoints/root `R_f`; ordinary
symbolic constructor and checking relations; original binder scopes; the
source-justified unannotated seed and seed-at-this-upper-exposure witness.
`X` is one candidate whole row with its original providers, world/current
configuration, environment, continuations, constraints and `xi`. It need not
be satisfiable, admitted, or a completed original solution. All local witnesses
remain below their original rigid dependencies.

`H_typed`: `H_gen` plus the independently typed original row, compatible
complete profile, original admission and source-slot/transport semantics used
by the assigned source-view composition. Actual result/rebind, closure and
Name transitions are required for its reached-read conclusion. These premises
are reused; neither their existence nor their independent truth is derived.

`H_assoc` names the sought independent interpretation and source introduction
of `(s0,c0)` for this exact operand. It belongs to neither premise set.
If a supplied full kernel interpretation already contains that association,
extracting it consumes `H_assoc` rather than proving it here.

## 3. Direct source/core derivation

Typed-core §6 generates ordinary formal interfaces before the bodies:

```text
P_f = Value(A_f)      Gamma_f(d_f) = Value(A_f) after actual entry rebind
P_x = Value(A_x)      Gamma_fx = Gamma_f, d_x:Value(A_x)
```

These are parameter interface tags, not actual callable Handler/Pure roles.
The selected provisional protection and its inferred-formal refinement do not
change the actual entry or role of a supplied callable.

Apply the disjoint synthesis/normalization clauses in that environment:

```text
f: Value(A_f)       n_f = result(name d_f)
x: Value(A_x)       n_x = result(name d_x)
f x: Computation(E_fx,A_fx)
                   d_fx = reify(call(n_f,n_x))
                   n_fx = eliminate_p(d_fx)
```

The administrative elimination of that reification uses the existing
same-context delay/force law; retaining the pair is also valid. The selected
core writes the corresponding `call(n_f,n_x)` directly. It adds no consumer
of a latent returned value. The application constrains the complete actual
invocation image and whole argument; it does not define `E_fx` as a union of
support rows.

Continue upward once:

```text
A_step = Fun(Value(A_x), Comp(E_fx,A_fx))
step definition: Value(A_step)
                   n_step = result(lambda(P_x,call(n_f,n_x)))
block: Computation(E_bind,A_step)
                   n_block = bind(d_step,n_step,result(name d_step))
apply definition: Value(Fun(Value(A_f),Comp(E_bind,A_step)))
                   n_apply = result(lambda(P_f,n_block))
```

All endpoints remain symbolic with the original checking constraints.
These Function expressions describe body/result skeletons. Typed-core §9
explicitly prevents using them as solved complete-invocation bounds for an
arbitrary incoming argument carrier. `n_block` constructs and returns the
capturing local closure; it does not run `f x`. Actual outer entry may execute
the carrier supplying `f` before this block. Actual later `step` entry may
execute its carrier before `n_x` reads the rebound `x`. Neither carrier is
substituted for the body's `n_x`.

Applying typed-core §3 at the unique body Call gives

```text
J_f = Return(lookup(d_f))
J_x = Return(lookup(d_x))
j_call = rooted expression record for
    J_f >>= (lambda actual_f.
      ExecuteCallable_X(actual_f,Delay(J_x); U, original checking operands))
```

The same rule includes actual receipt/entry, body, designated consumer,
native return delimiters and pending suffix. `ExecuteCallable` retains its
independent actual-provider/entry interpretation. Expression generation
requires no successful `Q` and supplies no claim that those inputs are valid.

The assigned complete-operand construction supplies the original
`beta=(d_f,R_f)`, `p0=outEff(U)`, `e0=(k,beta,u,sigma_x,p0)` and
`ElimOrigin(c_fx,u,d_f,R_f,p0,p_out(c_fx))`, with own-upper provenance.
Under `H_typed`, the assigned composition additionally supplies

```text
chi_read^upper[e0]
  = (M_read o M_cap o M_res)_* chi_receipt^upper[e0]
```

at the actual callee read of this `j_call`. The three maps require their
actual transitions. Pending histories retain their prospective packet and
suffix without inventing a returned value or reached read. Provider/lower
packets retain their separate source tags, even for equal endpoint values.

**Conditional derivation:** `H_gen` constructs the displayed skeleton and
complete rooted operand; `H_typed` constructs the transition-guarded upper
incidence at its exact callee read. Neither conclusion has the original
signature/contribution association sort.

## 4. Constructor elimination and the minimized missing premise

Target coordinates have these sorts:

```text
s0 : original static signature slot
c0 : original complete contribution witness/contract
t0 = (beta,s0,p0,c0) : original licensed incidence
```

`OriginalAssocType` is obligation notation from the assigned attachment note,
not an adopted kernel predicate or selected compiler API. Its interpretation
must type `c0` and associate both coordinates with this original source/view,
typed position and complete operand on `X`.

| Existing constructor or rule | Available conclusion for this task | Why it cannot discharge the target from these inputs |
| --- | --- | --- |
| Name, Result | Resolved descriptor/provider, interface and current-state return | They preserve lexical identity and supplied evidence; no original contribution/slot introduction is displayed. |
| Lambda | Inert closure, actual entry/body/result skeleton and captured roots | Capture retains the same outer `f`; it transports supplied incidences rather than typing a new Call contribution. |
| Bind | Shared result/rebind/state witness and ordered suffix | Rebinding establishes result association in the environment, a different judgment from static signature/contribution association. |
| Call | Complete invocation expression/image and whole checking obligations | Its typed profile/owner/view inputs are independent premises; no displayed original `(s,c)` introduction follows. |
| Reify, designated Eliminate | Inert carrier and execution at a previously identified typed port | Introducing or opening that carrier does not interpret its expression as a contribution contract. |
| Literal/primitive, Operation | Independently declared whole local relation/interface | They do not occur as direct producers in this subtree. A provider's independent kernel may contain relevant facts, but importing them adds a premise; no displayed rule retags them own-upper. |
| Handle | Existing shallow-image relation with typed handler premises | No Handle occurs in the selected core. Ambient independently typed handlers remain inputs, not signature constructors for this source occurrence. |
| Immutable records, aliases, recursive references | Original provider tuple/root or registered relation reference | No extra direct occurrence supplies the target here; preserving or referencing an original kernel does not introduce a missing clause in it. |
| Dir-Protect, Gen-Call-0 | Original upper marking/address and elimination origin | Their conclusions distinguish protection from contribution membership/typing and receipt. |
| Typed images, Receipt/Observe/Path/Inc_C | Transported profile and, with actual event/activity premises, dynamic incidence | They preserve original predicates and introduce no displayed static signature/contribution typing law. |
| Active root interpretation, constructor typing lemma | Interpret retained conjuncts; establish descriptor membership for emitted observations | Source-contracts §2.2 requires independent owner/view contracts. Activation or `DescMem` does not define their missing introduction. |
| Source-allocation coverage, certified generalization/use | Coverage under the retained non-coverage kernel; whole transport | They assume or transport the original kernel and cannot serve as its source producer. |

This table covers the finite ordinary `d/c` constructor kinds displayed in
typed-core §2 and the supplemental relation/transport routes in the assigned
documents. It does not enumerate every possible independently interpreted
primitive or original licensing last rule. The negative conclusion is bounded
to the displayed conclusions and supplied inputs, not the whole repository.

The smallest subtree carrying the unresolved producer is

```text
call(result(name d_f), result(name d_x))
```

with five core nodes and its original environment, `beta,p0,U,e0,X` supplied.
Deleting the outer Lambda/Bind/return and replacing their already justified
capture/read transport by the supplied typed environment leaves exactly the
same target. Deleting the Call loses `j_call`; deleting either Name/Result
operand loses this complete source invocation. This is a minimized **proof
cut**, not a smaller approved source program or language counterexample. It
does not assert that lexical capture is semantically irrelevant.

Thus the residual can be written without unresolved capture or execution:

```text
Known: this source Call, complete j_call, original beta/p0 and exact
       callee-read upper packet under H_typed, on the same X/xi.
Missing: an independently interpreted original kernel constructor typing
         a contribution c and associating an original slot s with precisely
         those source/view/operand coordinates.
```

Fresh dependent unknowns `s,c` plus an association constraint can be emitted
at original scope. This produces a residual demand, not its interpretation,
witness existence or source adequacy. `c=j_call`, `s=p0`, or
`c=chi_read^upper[e0]` would be candidate representation assumptions requiring
the missing interpretation lemma. None is adopted here. Forward licensing
`Attach_C => Lic_C` and original licensing inversion still need separate laws.

## 5. Falsifier, independence and stopping boundary

A concrete falsifier of this bounded localization is a displayed independent
source-owned constructor among the pinned governing clauses whose conclusion
types an original contribution and associates its original signature slot
with this `beta,p0,j_call`, and whose premises are derivable above without
assuming that association, licensing, or successful `Q`. Merely locating
those fields in a supplied typed kernel/certificate is insufficient.

Logical shortcuts fail if they substitute a body image for complete invocation,
an external carrier for rebound `J_x`, profile presence for contribution
typing, a dynamic receiver for static `s`, a provider/lower tag for own-upper,
or a second `xi/world` for the original joint row. Pending-to-Rebound without
the actual result transition fabricates a witness. These are named proof
failure conditions, not executed mutations or witnessed language failures.

No Oracle or executable reference is used. The derivation shares the assigned
source equations, independently stipulated kernel meanings and typed transport
premises with its dependencies; it does not independently validate them.
A checker accepting a proposed association transition as input would establish
rule-relative consistency only. No oracle independence or source-rule proof
would follow from two implementations sharing that transition.

The earlier attachment and composition attempts already left this premise
untouched. This pass strengthens its localization by direct constructor
elimination and then stops. Another enlarged packet model or Call-prefix probe
would not address it. There are no random seeds/ranges, search shards, executed
mutations or numerical coverage counts.

Recommended next action: have the primary obtain the independently interpreted
original owner/view contribution-and-slot clause, with a finite source
introduction inventory, before commissioning another attachment proof. That
is a missing formal premise to investigate, not evidence for reopening the
selected language meaning or weakening the source/production gates.

## 6. Checks, resources, omissions and dependency snapshot

Commands run: bounded `git show <baseline>:<path> | sed -n ...`, `rg -n`
section/constructor reads, Python SHA-256/pinned-byte comparisons,
read-only `git rev-parse HEAD`, and note-local integrity checks. Initial
aggregate captures truncated; decisive rules and sections were reread in
bounded windows. No whole-repository absence search is claimed.

All twelve dependencies below matched pinned bytes at initial and final checks.
The lease path did not exist before this write. No other path was written.
No tests, builds, compiler edits, Oracle/checker execution, formatting,
Git mutations, interactive questions or children. Heavyweight process count
and performance samples are zero. The initial batch issued nine independent
lightweight read requests; subsequent read batches issued at most four.
No numerical CPU/RAM/wall-time budget was supplied;
CPU time, peak RSS and elapsed wall time were not instrumented.

Unverified: independent association interpretation/introduction; existence of
an admitted typed original row; complete original slot/profile inventory;
licensing in both directions; arbitrary source/annotation/capture/recursive
components; source adequacy, principality, production Option A/2 membership
and cutover. This producer has not independently reviewed its own output.

| Pinned dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-07-source-view-to-original-attachment-composition.md` | `a6f8d13d1911ebfaa1b41c60485eab1b303c4f34a661bafca0b742d30418f946` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |
| `notes/progress/2026-10-06-attach-call-contribution-construction.md` | `4261105c8f9a5012a693cc39dc0f7df8c0e70024594a10282046dbaebf851a96` |
| `notes/progress/2026-10-06-attach-c-source-correspondence.md` | `43c5a9ebd85c7b4f1ab644c9278f0b1260437a771033d104027aa00ba87205f9` |

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md`.
- Baseline SHA: `1777ccec8369915ad2829f324e3e6d6dd08f697c`.
- Changed dependency hashes: none; twelve pinned byte/hash comparisons match.
- Review status: compiler-referee PASS, no findings in the bounded conditional
  derivation and constructor elimination; no original attachment theorem or authority.
- Checks already run: direct governing-section/constructor audit; explicit
  source/core derivation; initial/final dependency checks; lease and
  note-local whitespace/hash-table integrity checks. No runtime verification.
- Proposed one-line research-checkpoint commit message:
  `research: minimize original association premise by source constructor elimination`.
- Shared-record deltas intentionally left to primary/curator: record the
  five-node Call proof cut and independent original owner/view clause as the
  exact next premise; retain existing licensing/profile/admission and
  source/principality/production gates. No shared file changed and no status
  promotion proposed.

Writing stopped before frozen review submission; the primary owns integration.
