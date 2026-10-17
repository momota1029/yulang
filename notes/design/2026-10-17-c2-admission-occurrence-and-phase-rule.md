# c2 native call occurrence correction — typed source candidate

Date: 2026-10-17  
Revision: 2; corrects and withdraws the rev1 `C-AppArg` claim  
Status: source/native correspondence only; no semantic adoption  
Sprint: `c2-typed-call-occurrence-correction-20261017`, contract rev2  
Parent: original FORWARD-FIRST-CALL A/B and c2 admission/VIEW/CHECK remain OPEN  
Compiler-code authority: none

## 1. Fixed source occurrence and source identity

Keep the original source and quantifiers unchanged:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
```

`c1` is `Apply(Name(f), Unit)`; `c2` is the suffix `Apply(Name(g), Unit)`;
`a2` is its actual Unit child. The original target remains `F2@(sigma2,Delta2)`,
`xi=(nu,K,D)`, and the complete original incoming view `B_in`. The enclosing
source path is `Scope(receive, Lambda(f, annotation, Bind(g, c1, c2)))`; c2
stays beneath the actual Bind result. No provider, carrier, world, or context
is selected or projected.

The pinned source constructor `candidate_source` retains the `LocalSourceForm::Apply`
expression and its exact callee and argument children in `ApplySourceInput`.
For that input it records the source owner/expression, child IDs, source level,
callee and argument value/effect endpoints, result endpoints, and
`checking = ConstraintOccurrenceId(c2, 0)` with cause derived from that same
checking occurrence. `candidate_call::observe` re-fetches the same source
Apply and verifies the stored callee and argument identities, occurrence and
cause; it also checks that the native demand's children match the retained
native ports. This authenticates a source/native call record. It does not type
an original semantic F2 inlet.

## 2. Actual native construction and relation

At this Apply recipe, `shadow_apply::admit_candidate_fact` constructs:

```text
callee₂ = candidate_endpoint(Name(g), Positive)
argument₂ = candidate_endpoint(a₂, Positive)
N₂ = NegativeFunction(
       argument = argument₂⁺,
       argument_effect = argument_effect₂⁺,
       invocation_effect = invocation_effect₂⁻,
       result = result₂⁻)
```

The native demand observer verifies that `arg(N₂)` is exactly `argument₂` and
that this port is a `Value/Positive` term. The initial candidate constraint
then admits and records this pair, owned by the same c2 checking occurrence
and cause:

```text
callee₂⁺ ≤ N₂⁻       (ordinary call-check constraint at c2, slot 0)
```

The literal's positive term is used to build the demand's positive argument
child. Construction does not emit a second pair `Unit⁺ ≤ arg(N₂)`; those
expressions name the same retained term, and no distinct source relation is
created by that equality of identity. Therefore rev1's displayed
`Aarg_c2^cand := Unit⁺ ≤ arg(N₂)` and its `C-AppArg` admission claim are
withdrawn as ill-typed and unsupported by the constructor. No replacement
admission predicate is proposed here.

A separate conditional fact applies only if an actual positive Function
endpoint `P⁺` is supplied to and decomposed against this negative Function
`N₂⁻` under the ordinary subtype relation:

```text
P⁺ ≤ N₂⁻  implies the Function argument child comparison
arg(N₂)⁺ ≤ arg(P)⁻
```

This follows from the existing contravariant Function decomposition and is
conditional on the parent comparison and its decomposition actually being
present. The call constructor alone does not supply `P`, prove that `callee₂`
is that Function, or authorize this premise. This child is also an ordinary
call-check consequence, not an F2 admission clause.

The two operand owners are distinct: the whole-call lower operand is the
callee child; its upper operand is the newly built negative Demand. The
argument child is embedded inside that Demand from the Apply's source argument
endpoint, with Positive polarity. A negative Function constructor does not
make all its children negative.

## 3. Retained source-graph facts and their limits

The previous source artifact correctly identified the concrete wrapper graph
and retained the suffix under `Bind(g,c1,c2)`. Keep only that bounded result:
`Scope`, `Lambda`, `Bind`, `Call`, and `Ref` retain their source labels, child
identities and binding edges; `Ref(g)` resolves to the existing Bind result
root; c2's own checking occurrence remains local to c2. The raw c1 Return or
Request substitution acts on the same dependent suffix under the same binder.
This graph-retention calculation does not assert a typed installed `IF(g)` or
a selected IF-Use rule.

Likewise, identity substitution on any already supplied well-formed telescope
preserves that telescope and any already typed witness. It does not build the
telescope, type a new predicate, or prove a semantic insertion. Source-child
identity (`Name(g)` and `a2` into the retained Apply record), native-port
identity (`arg(N2)=argument2`), and a semantic interface substitution
`m_g : IF(g) -> c2` remain different maps. Only the first two are authenticated
here; a complete semantic interface and substitution are not supplied.

The prior graph proof has no source-qualified counterexample and no authority
to assign meaning to the original F2 constructor. Preserve those limits; do
not reuse its conditional `C-AppArg` argument as an admission theorem.

## 4. Admission boundary and parent gates

The corrected relation establishes where an ordinary native call check is
attached and which source/native children it uses. It establishes none of the
following: semantic `IF(g)`, an original F2 clause or introduction, `I2`,
`I2=SAT`, equality of a native argument port with the complete inlet, original
VIEW, or original CHECK. Pending call-check `Q` cannot form F2 admission.
No relation between `N2` and the complete original `B_in` carrier is derived.

Original F2 VIEW still requires the complete carrier action for every original
`(delta,O)` in `B_in`, including its original contexts, worlds, observations,
responses, resumptions and futures. Original CHECK still requires the actual
original clauses and correlated witnesses. Both remain OPEN at original c2;
all original A/B domains, providers, and quantifiers stay intact. Parent
`FORWARD-FIRST-CALL` A/B, source/native correspondence for those full claims,
semantic approval, soundness, principality and production remain OPEN.

## 5. Exact next proof target

An independent proof may establish the source/native equations above and the
conditional Function decomposition consequence from the pinned constructors,
with graph retention used only within its stated premises. It must keep the
conditional premise explicit and state exactly what evidence the actual call
relation contributes. If it contributes no F2 admission, VIEW, or CHECK
premise, that is the correct bounded result. No compiler code, tests, probes,
execution, semantic adoption, expected-output change, or production promotion
is authorized by this artifact.
