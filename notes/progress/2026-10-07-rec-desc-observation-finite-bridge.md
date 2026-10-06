# Conditional bridge from typed observations to FH histories

Date: 2026-10-07
Baseline: `721006c237f107ec4307a0c0bfb6d308b52ca949`
Status: conditional history translation; REC-DESC and DESC-CLAUSES remain open
Claim class: proof schema with explicit independent premises
Semantic authority: none added; no Oracle semantics used

## Conditional finite-witness schema

For one independently specified descriptor conjunct whose quantified domain
already consists of finite typed eliminations or finite histories, of the form

```text
forall u in U_j(xi,w). C_j(u;xi,w),
```

failure yields a finite witness `u` by classical quantifier negation. If the
clause instead quantifies over complete observations that may be infinite, a
separate finite-prefix/reflection lemma is needed; quantifier negation alone
does not make its witness finite. In either case, the failure contradicts FH
only if the actual descriptor clause also supplies all of the following:

1. `U_j` is independently covered by the exact query-independent admission
   domain, without using the recursive membership under proof.
2. The finite witness translates to an FH history at the same original
   provider and `(xi,w)`, preserving the current state, request witness,
   original raw handle, pending suffix, typed incidence and compatible
   event-local coordinates. Original ownership evidence is retained; current
   executable owners follow the source's live-owner borrowing or fresh
   execution-occurrence rule, rather than preserving expired activations.
3. `not C_j(u)` negates the complete joint local judgment `L` for that
   decorated history, rather than one local proof or one optional witness.
4. Every condition that cannot be observed by such a history is established
   by an independent root/static judgment `S` or an explicit zero-step check.

If FH's actual form is `forall h. exists e. Check(h,e)`, a contradiction
requires a witness `h` for which **every** allowed compatible extension fails:
`exists h. forall e. not Check(h,e)`. One failing extension does not negate
the premise. Original quantifier placement is preserved.

Under these premises, a finite interaction-to-history translation is by
induction on its derivation: retain the independently admitted initial
punctured context; append a response to an already exposed request; append use
of that request's original raw handle; or append a call/force at the original
typed port of an actually returned provider. Bind preserves the ordered suffix
and current resumed state. Resuming a suspended invocation continues its
existing suffix without replaying its prior receipt or boundary entry. A later
new call to the same returned provider performs its own ordinary entry, receipt
and fresh invocation activation. Sibling histories join only through a supplied
compatible extension. No complete-member assumption is introduced.

This proves a conditional clause-to-history lemma. It does not show that all
active ordinary descriptor clauses quantify over finite histories, that
infinite observations have finite bad prefixes, or that its remaining premises
hold.

## Invocation and resumption translation invariant

Source-contracts §3.3 cases 3 and 4 distinguish use of an exposed request's
original raw handle from a new admitted call/force of an actually returned
provider. Typed-core §9 supplies the complete invocation and resumed suffix;
source-owner realization §§2–3 supplies their executable ownership mapping.
Conditionally on these supplied source premises, the translation retains
original receipts, boundary receivers, typed views, request origin and joint
`K,D`. For each saved owner span it borrows the exact still-live occurrence,
or enters a fresh execution occurrence if that saved occurrence has ended.
This changes executable ownership only. It never makes an expired owner,
handler or boundary authority live again. Source-prescribed forwarding may
install a fresh handler; current incidence must be checked for that handler.
Reloading a saved typed binding may create an ordinary `Receive` edge at the
current owner; this does not replay the invocation's prior receipt or boundary
entry. A genuine new call in a later history or saved suffix introduces its
own receipt and activation, and only an actually executed boundary-entry
operation introduces its own fresh boundary instance.

A schematic distinction trace is `f returns g; call g; g exposes (q,k);
resume k`. The call to the actual returned `g` requires its own ordinary
receipt and activation. The subsequent `resume k` preserves `q` and continues
the pending suffix without repeating that entry. If its saved owner has ended,
source-owner resolution allocates a fresh execution occurrence while retaining
the old ownership evidence; that occurrence cannot revive the old boundary.
This is a conditional source-rule derivation, not an executed fixture or an
independent proof that those source rules cover arbitrary programs.

## Observation-shape coverage ledger

| Observation or constraint | Possible finite witness | Additional clause needed |
|---|---|---|
| Prefix or request | Finite admitted progress to the mismatching prefix/request | The mismatch must violate the full local judgment; outward support alone is insufficient |
| Return | Finite execution to the result and immediate shape check | Returning a callable remains inert; latent membership needs its own clause |
| Latent closure or delay | A finite later call/force that exposes a latent mismatch | Exhaustive latent descriptor rule and independent admission of that exact provider use |
| Raw resumption | Finite response/resumption of the original exposed handle | Same operation witness, current state, suffix and original ownership evidence; live-owner borrowing or fresh execution occurrence; no replay of prior receipt/boundary entry |
| State or world | Finite reachability to a state where an active check fails | Full state/world predicates must occur in `L`; arbitrary mutable/import worlds exceed source-contracts §3.1's envelope |
| Authority, path or owner | Root failure in `S`, or a finite event-local failure | Independent typed incidence/permission clause; endpoint equality does not establish it |
| `nu,K,D` dependency | Root failure in `S`, or a finite local failure while retaining the joint tuple | Exhaustive incidence and tuple-transport clauses; an absent outward event does not discharge a retained predicate |

The exact returned provider matters: when `f` returns the captured `g`, a
future-use witness must call that same `g` at its original typed port. A
new admitted call has its own ordinary receipt and activation. A substitute
provider, reset state, replayed prior receipt on resumption, or revived expired
authority is not the admitted counterexample required by reflection.

## Predicate and authority boundary

Source-contracts §2.2 separates the original-scope joint observation
conjuncts:

```text
P_E(h;xi) = { Pi_xi(O) |
  exists w at its original scope:
    M_E(h,O,w;xi) and DescMem(R_E,O,w;xi) }
```

`M_E` and `DescMem` share the same `w`; admission `A_E` separately determines
the challenge domain. Reflection for `DescMem` alone does not prove `M_E`,
carrier/world validity, admission coverage, or simultaneous `CompleteMem`.

The approved Option A basis constrains complete observations with
independently interpreted endpoint, role/entry, typed-path, origin,
continuation, scope, authority and dependency judgments. Option 2 permits
conservative membership extras without source-constructor witnesses. The
source-interface adequacy relation supplies forward coverage of typed source
execution; it supplies no inverse from every descriptor failure to a source
execution. Consequently, the translation above applies to a specified
independent admission/descriptor clause, not automatically to every
production extra. `M_E`/`DescMem`, `A_E`, CarrierMem and WorldMem still require
their exhaustive clauses and one joint SEM-JOINT interpretation.

No source-descriptor clauses were adopted or defined here. In particular, the
proof does not set `DescMem` equal to source execution, define complete
membership by FH, or infer `R subset G` from the positive grammar in source
contracts §3.7. Those sections continue to assume local descriptor typing and
source-base inclusion.

## Status and next proof

This bridge narrows REC-DESC to two linked tasks: first specify and jointly
interpret each ordinary returned-Function, CarrierMem, WorldMem, admission and
`M_E` clause; then prove for each `DescMem` clause either its independent
static/zero-step condition or exact admission-and-`L` reflection. The same
original assignment and scopes must survive both steps. This note establishes
neither task, an exhaustive interpretation, source adequacy, principality nor
production conformance. No code, tests, builds or executable probes were run.

Review status: the spec-auditor found no conformance issue. The initial
compiler-referee MAJOR finding on the invocation/resumption distinction was
repaired; a fresh compiler-referee delta review found no blocking, major or
minor residual finding. Review covers only this conditional schema and its
authority boundary, not exhaustive descriptor reflection or REC-DESC closure.

Inputs: approved Function denotation and membership answers; source-contracts
§§2.2, 3.1–3.7 and 10; source-interface adequacy §§2–3; typed-core source
invocation sections; REC-DESC/FH/SEM-JOINT/DESC-CLAUSES/MEMBER_DISCHARGE; and
the [finite-reflection localization](2026-10-07-rec-desc-finite-reflection-localization.md).
The ownership mapping specifically uses
[source-owner realization](../design/2026-10-02-typed-source-owner-realization.md)
§§2–3 with its retained conditional status and authority boundaries.

This is a narrow continuation of the independently reviewed
[returned-provider constructor derivation](2026-10-06-descmem-provider-derivation.md),
which already builds the conditional `f/g` source/reference spine and locates
the production constructor-typing gap. That source derivation is not repeated
here. The added result is only the clause-to-finite-history translation
schema for a fully specified descriptor conjunct; neither note supplies the
missing exhaustive production clauses.
