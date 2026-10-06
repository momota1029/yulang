# REC-DESC: captured Name lookup does not discharge latent descriptor membership

Date: 2026-10-07
Baseline: `c1e5a0b1bbed5f7ad9e0ae067cb1967ef77b5f18`
Status: bounded last-rule characterization; REC-DESC remains OPEN-PROOF
Claim class: source-rule derivation and missing semantic lookup premise
Semantic authority: none added; no Oracle semantics used

## Result

At the inert `Return(v_g)` in the mutually recursive provider source, the
selected Name and Result rules form the returned value's source interface.
They do not prove the independent latent `DescMem` conjunct for the captured
semantic handle. The missing premise is now localized one step earlier than
general finite reflection: semantic adequacy of looking up the captured `g`
binding under the original environment, binder scopes and `(xi,w)`.

This is not a counterexample, non-entailment theorem, or change to the
descriptor interpretation. It preserves `v_g`, its original latent contract,
and FH's same-assignment condition. It does not infer descriptor membership
from lexical identity, source type shape, or successful result synthesis.

## Governing clauses and exact source derivation

For the original mutually recursive source used by the REC-DESC attack,
`my f x = g; my g y = f`, the selected source-result rule
[A](../design/2026-10-02-source-result-synthesis-choice.md) §4 gives:

```text
Gamma(g) = I                    Synth(body) = I
----------------              -----------------------------------
Synth(name g) = I             Synth(lambda(P,body)) = Fun(P,Result(I))

Result(Value(A))          = Comp(empty,A)
Result(Computation(E,A))  = Comp(E,A)
```

The reviewed [recursive provider-knot construction](2026-10-06-recursive-source-validation-construction.md)
fixes the actual captured
lookup `eta_f(g)=v_g` and the shared source interface
`Gamma_K(g)=Value(R_g)`. The selected Name/Result formation derives:

```text
Synth(name g) = Value(R_g)
Result(Synth(name g)) = Comp(empty,R_g)
```

The [typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
§3 makes data lookup inert: `V[name g] = lookup(g)`. Combined with the
supplied knot equation, this connects the term to the exact semantic handle
`v_g`; it does not, by itself, prove that the value satisfies the
independently interpreted descriptor.

## Last-rule boundary

The [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§2.2 requires `DescMem` to remain independently interpreted and explicitly
requires a constructor-typing lemma for each emitted observation. Section 3.5
uses those local lemmas as premises; it does not derive them from syntax
generation. The recursive finite-history invariant FH
([successor-recursive-synthesis](2026-10-07-successor-recursive-synthesis.md)
§4) retains the original latent contract on the exact returned handle `v_g`
and avoids assuming `CompleteMem`; it does not turn inert Return into a
`DescMem` introduction.

The currently justified boundary is:

```text
Gamma_K(g)=Value(R_g)
  + lexical lookup identity to the captured binding
  + inert Return of the actual v_g
  + FH's pointwise local checks
  ⇏ [not derived here] DescMem(R_g,v_g;xi,w)
```

The exact missing interface is **semantic lookup adequacy**: state the
independent premise relating the captured environment's `g` lookup to the
source binding's descriptor at the original scopes and `(xi,w)`. Then check
whether the existing W predicate independently establishes it. If lookup
adequacy requires the recursive member validity currently being proved, that
route is circular; if it follows from a separate binding/world invariant, its
proof can become a local input to FH/REC-DESC. Neither outcome is selected in
this note.

The current clauses do not yet settle that check. FH treats `W` as a free,
independently interpreted predicate and requires an initial certificate and
each transition to establish/preserve it. K constructs the actual closure
graph and proves `eta_f(g)=v_g` without validated recursive membership. The
source adequacy candidate constructs an exact, potentially infinite interface
for an already well-typed configuration. It does not establish that this
recursive configuration satisfies those typed premises or that the captured
value meets the independently interpreted `R_g`. Therefore, strengthening
`W` to include lookup adequacy would relocate the obligation into
initial-world and preservation proofs; no cited clause currently discharges
it. This is a bounded dependency finding, not a theorem that no separate
binding/world rule can do so.

## Scope and checks

Inspected the exact selected source-result rule, recursive provider-knot
construction, typed-core lookup equation, source-contracts §§2.2 and 3.5, and
FH's definition and premises. No implementation, source acceptance, admitted
witness, complete member, or production behavior was inferred. No code, tests,
builds, Oracle execution or Git operation was used to establish the logical
result.

The derivation is bounded to the selected captured Name and inert Return. It
does not discharge other `DescMem` clauses, `M_E`, carrier/world membership,
independent admission, `INIT_VALID`, or `MEMBER_DISCHARGE`. REC-DESC,
soundness, principality, source adequacy and production cutover remain open.
