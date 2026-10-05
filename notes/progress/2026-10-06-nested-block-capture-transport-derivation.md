# Typed capture transport with an independently supplied original receipt

Date: 2026-10-06
Status: frozen unreviewed research-only rule-inversion result
Initial baseline: `90eee6c2a686394e669d0361d825977f82a74f8a`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: constructive proof attempt and inversion of preservation rules
Implementation authority: none

## Objective and scope

Stipulate an independently certified original contract/profile/receipt for
outer `f`, then attempt to derive identity-preserving typed transport through
closure construction, return of local `step`, and its later invocation in
exactly `my apply f = { my step x = f x; step }`.

This attempt isolates a smaller missing premise: attaching the supplied
original certificate to the captured environment entry and the inner name
occurrence. The strongest inspected transport rules preserve an already typed
capture correspondence; they do not synthesize that attachment from an
original receipt and lexical resolution. Original formation is stipulated
here, so it is not the blocker returned by this lane.

Claim classes: the exact lexical/result/capture meaning is an established
user decision. The rule-inversion result is bounded characterization of the
named rules, with a conditional partial proof. A finite identity map on the
supplied certificate is a candidate bookkeeping witness, not a complete
typed capture certificate. No reviewed theorem, accepted-program
counterexample, source acceptance, adequacy, or production authority follows.

## Dependencies and explicit input premise

Governing sources: nested-block-function-source-realization-addendum §§1–3;
typed-computation-core-elaboration §§3,6,9 (its §2 input description is read
as the direct reference needed to invert §3); inferred-function-call-views
§§1–5. The integrated call-view q1/a2 and nested-block q1/a1 receipts preserve
the exact decisions. The typed core remains Draft with reviewed conditional
constructions; its review does not make the missing source producer a rule.

Prior evidence challenged, rather than used as a proof of the conclusion:
latent-callback-receiver-source-trace; nested-block-function-conditional-core-
derivation; nested-block-callview-registration-attempt; nested-block-capture-
evidence-falsification. In particular, their combined decoration or capture
transport assumptions are not imported. Their separation of static capture
and later receiver activation remains intact.

Let `d_f,d_x,d_step` be the three resolved binders, `u_f` the inner use of
`f`, `c` its `f x` call, and `s` the local closure instance returned by one
outer activation `r_A`. Let `g` be the rebound callable provider at `d_f` in
that activation. Later activation of `s` is `r_S`; if its body reaches `c`,
the actual invocation of captured `g` is `r_G`. These labels make no
allocation or boundary-placement decision.

**H_original, stipulated:** there is one finite, independently certified,
Q-independent original receipt certificate `R_f` for `(d_f,r_A,g)`. It
contains the original completed contract `F_cb`, static `beta`, complete
`Slots(beta)`, annotation absence, typed paths, source incidences and scope,
and every reference needed to interpret its jointly scoped original
`xi=(nu,K,D)`. Recursive references are finite graph references, not unfolded
trees. The certificate's owner/activity facts are interpreted at their
original events, not asserted to remain active forever. The value `g` keeps
its original callable definition, role, entry and result consumer.

One fixed source instance is considered. No local generalization,
freshening, independently chosen port witnesses, endpoint-solving theorem,
or source acceptance is assumed. The ordinary `f` and `x` parameter roles
and lexical map are those selected by the governing sources. The original
certificate is not assumed already attached to a `step` closure or its
body occurrence: that is the target judgment.

## Constructive proof tree and its open leaf

Write `Gamma_f(d_f)=Value(A_f)` for the outer rebound interface. Extending
this lexical environment with the ordinary inner formal gives
`Gamma_fx=Gamma_f[d_x:Value(A_x)]`. This retains the outer lexical binder;
it does not by itself define an evidence environment for capture.

Core §6's name/result clauses supply the structural leaves

```text
Gamma_fx |- name d_f : Value(A_f)
Gamma_fx |- result(name d_f) : Comp(empty,A_f)
Gamma_fx |- result(name d_x) : Comp(empty,A_x).
```

Inverting the intended closure proof yields the following obligations:

```text
prove local lambda(P_x,n_c)
  -> prove its body n_c under Gamma_fx
    -> prove the complete call at c, including its typed paths
      -> identify the captured callee occurrence u_f with provider g
         and original R_f under its original joint xi.       [OPEN]
```

The application row can construct the symbolic call/result skeleton and
generate whole-argument and complete-invocation obligations. Generating those
obligations does not prove them. Its callee interface constraint identifies
a Function endpoint; it supplies no rule attaching original receipt evidence
to a captured occurrence. Matching `A_f` or `F_cb` cannot fill the open leaf.

The smallest required judgment, written descriptively rather than as a new
selected rule, is

```text
R_f certifies original (d_f,r_A,g,C_f) at xi
resolve(u_f)=d_f; local closure s captures that original g
----------------------------------------------------------------- ?
the typed environment of s and its u_f lookup retain that same
provider instance together with C_f=(F_cb,beta,Slots(beta),scope,
annotation absence), its complete typed paths, and joint xi.
```

The question mark identifies the missing source attachment premise. It
requires both the association at closure introduction and a lookup
correspondence when that closure's body is entered. It does not require or
assert a later receiver already active. An original receipt certificate has
the correct starting provider and evidence; the missing conclusion concerns
their association with a new captured occurrence.

## Inverting the strongest available routes

**Descriptor construction, core §3.** The translation says descriptors
capture lexical references and typed evidence, and defines
`V[lambda(P,c)]=Closure(entry_P;X[c],lexical references)`. This is a useful
execution/preservation clause for a supplied finite typed derivation. It
does not define which original receipt/profile is the evidence of a newly
resolved captured use. The input description in §2 already includes typed
Flow/receipt correspondence and joint `K,D`. Applying that translation to a
complete decorated `step` body would first require the open leaf above.
Calling the resulting descriptor evidence-preserving cannot construct its
own source input.

**Capture-avoiding renaming and endpoint substitution, core §6.** These
transport binders, profiles, typed paths and payloads together, while
preserving source tags and typing premises. The exact substitution theorem
starts with an existing generated derivation and a substitution that
preserves those premises. Choosing `sigma=id` is admissible on `R_f` and
leaves every old coordinate unchanged. Its conclusion remains a transformed
`R_f`; it is not a derivation for a new closure environment or captured name.
The required identity map cannot add the missing association by renaming.

**Return and local binding, core §§3,6.** The binding clause binds the RHS
result value; the suffix returns the local name's value. If a complete typed
closure descriptor were already supplied, these clauses would pass that
same descriptor through. Inversion therefore pushes the transport question
back to closure introduction. It does not create the descriptor's absent
capture correspondence at return. Administrative contraction also requires
the admitted same-context typed derivation and creates no capture premise.

**Later invocation and latent paths, core §9.** Latent return/storage use
the same primitive interaction clauses when activated and preserve an
already typed path correspondence. The later `step` activation receives and
rebinds its own `x`; it does not certify a historical capture by receiving
that different argument. Sign propagation presupposes resolved typed
correspondences and retains existing profiles; it creates neither a capture
association nor a grant. The original `g` entry remains owned by `g`.

These routes answer different preservation questions but encounter the same
open attachment leaf. Enlarging the supplied certificate or applying another
identity renaming cannot discharge it. This method stops at the leaf rather
than producing another trace or supplied-transition model.

## Finite identity witness: what it establishes and what it lacks

For the finite original certificate, define a proof map equal to identity on
every node/reference of `R_f`, every member of `Slots(beta)`, every original
path/occurrence and every shared constraint/scope reference. No subset of the
profile or tuple is projected away; no new witness is chosen. This map can
be described finitely and preserves the interpretation of the old
certificate at the same `xi` simply because its arguments are unchanged.

That is an algebraic identity fact about the supplied certificate. It does
not prove that a closure's evidence contains it, nor that later lookup uses
it. Those conclusions need the source attachment judgment. Adding a pointer
or association to the proof map as an extra assumption would assume the
first missing premise. The identity witness therefore fails to constitute
the requested typed capture transport certificate, despite preserving all
old data. This is a failure of proof construction, not a semantic witness
against the selected source meaning.

## Activation and remaining-gate boundary

Construction and local return do not invoke `step` or `g`. `r_A`, `r_S`,
and `r_G` remain distinct. Preserving a historical receipt in `R_f` does not
preserve its owner's active status after the original invocation ends.
No expired receiver is reused or revived by this attempt.

If the open capture judgment is supplied later, §§3,6 give the conditional
bind/return preservation route, while §9 still requires the independently
typed current interaction. The mapping from the preserved static profile to
an active receiver for the later call is a separate gate. This note does not
derive it or merge it with capture. Complete direct-query success, all-view
extension, admission completeness, principality, adequacy and production
conformance remain separate. A profile/identity-preserving certificate alone
would not prove any of them.

## Checks, independence, resources, and omissions

Only bounded reads of the stated dependencies and direct core references
were performed. Initial HEAD was verified as the assigned baseline by reading
the filesystem's `.git/HEAD` and referenced ref; no Git command was executed.
The leased output did not exist. Dependency SHA-256 values were recorded
before the write. The primary owns integration-time baseline/hash rechecking
and independent review. No self-certification is claimed.

There is no independent executable oracle. The attempted derivation shares
the Draft core's rule premises and cannot validate their missing source
formation rules by composition. No checker, Cargo, tests, probes, mutations,
seed/range enumeration, or performance measurements ran. Zero heavyweight
processes; peak RAM, CPU, and wall time were not instrumented. No child
delegation, Git operation, shared record, manifest, compiler or test edit.

Coverage is the finite original certificate stipulated above and inversion
of descriptor, substitution, bind/return and later-path preservation clauses.
The original source producer was not searched or proved. No exhaustive
repository absence claim is made. Polymorphic uses, arbitrary captures,
mutation/aliasing, recursive local groups, requests, handler selection,
resumption and arbitrary future clients are unverified. Changed dependencies,
a non-finite supplied certificate, or a demanded conversion outside the
named rules invalidate the scoped attempt.

Recommended next action: investigate a source-level evidence-environment
introduction/lookup judgment that attaches an already certified receipt to
this captured occurrence. Its input must be independent of `Q` and its
output must preserve the whole original certificate; defer later receiver
realization to its own dependent gate.

## Dependency snapshot

Whole-file SHA-256 of the read inputs at this assignment's initial baseline:

| Dependency | SHA-256 |
| --- | --- |
| Nested source addendum | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| Typed computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Inferred Function call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Call-view q1/a2 receipt | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| Nested q1/a1 receipt | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| Latent receiver source trace | `b627674ae67123c74b55ce43da464a7a09435b057b9742fc299029f5aef97d18` |
| Conditional nested core derivation | `fc227427abc438c3d9fb5f07ff97e25cd6f8c4e08d6b1a270fe253a3b80f8746` |
| Nested registration attempt | `31b45bbb95c06dbbe91430fac2107af112b239fac413fac944b3e08623a9b97b` |
| Capture evidence falsification | `0d7dcb8be3d96bdc7c7d8ff3f214f6c83283de51930ee3c3a4782019a5618540` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-nested-block-capture-transport-derivation.md`.
- Initial baseline SHA: `90eee6c2a686394e669d0361d825977f82a74f8a`.
- Changed dependency hashes: none observed; snapshot above. No Git-based
  committed-byte comparison was permitted in this assignment; primary owns
  revalidation if HEAD moves or before integration.
- Claim/review status: frozen unreviewed research-only rule inversion;
  original certification stipulated, capture attachment underived; no
  independent review, theorem closure or production authority.
- Checks already run: filesystem HEAD/ref and leased-path absence reads,
  bounded governing/prior-evidence reads, nine input SHA-256 calculations.
  No tests/builds/probes/Git commands.
- Proposed one-line research-checkpoint message: `research: invert typed capture transport after original receipt certification`.
- Shared-record deltas left for primary/curator: narrow the conditioned
  capture blocker to evidence-environment introduction/lookup attachment;
  retain later active receiver realization and adequacy as separate gates.
  No shared record or authority change was written.

The artifact is submitted frozen. Writing stops before independent review.
