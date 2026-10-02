# Source result synthesis and computation interface preservation

Date: 2026-10-02
Status: Authoritative for result synthesis A; proof/implementation gates remain separately scoped
Scope: selecting inferred function-result computation ports before code generation
Approved-by: user; A preserves known source computation interfaces
Approved-at: 2026-10-02
Drafted-by: primary with bounded architect and frozen-source mapping
Reviewed-by: independent compiler_referee and spec_auditor, 2026-10-02; no blocking/major findings; shared minor result-port normalization clarification closed by primary
Selected-rule review: independent compiler_referee and spec_auditor, 2026-10-02; no findings in A authority and source-synthesis theorem delta
Parameter-default review: §2 and charter §21 independently reviewed by compiler_referee and spec_auditor, 2026-10-03; no findings
Supersedes: the pending A/B/C choice in this record; inert introduction and known-interface entry remain fixed

## 1. The selected source rule

Charter §§16–17 fixes whole-argument inert introduction, same-activation
entry, known-interface elimination and preservation of latent results. The
typed-computation core now generates executable code from a finite declarative
port derivation. This record fixes how an **unannotated function result**
preserves the body's known source interface.

A computation-valued name can be observed as data without executing it.
A declared computation consumer can instead eliminate its known interface.
The user now selects interface forwarding for the body occurrence in:

```yu
our h(x: [handled; 'e] 'a) = x
```

For `x : Computation(E,A)`, result synthesis preserves `Comp(E,A)` and
inserts no additional pure layer. Lookup, transport and synthesis remain
inert; only an explicit consumer (`Force`, handling or known-interface
demand) executes the computation. Returning computation data under an extra
pure layer requires explicit inert introduction/lifting. Result interpretation
is not itself polymorphic. Section 4 retains the rejected alternatives as
decision history, not open choices.

This exact source is the frozen `a58eefc3`
`tests/yulang/regressions/effect/effectful_parameter_forwarding.yu` after its
`type handled` declaration. The inference fixture at
`crates/yulang/src/source/tests/case_02.rs:2712–2730` expects forwarded result
effects. It supplies compatibility evidence, not source authority or a runtime
timing assertion. No new execution was performed for this inquiry.

This is a result-synthesis rule, not a new capture selector, operation-family
rule, or permission to run any argument during construction. Every alternative
keeps computation introduction inert and needs an explicit consumer to run it.

## 2. Parameter-role authority and historical frozen evidence

Charter §21 records the user's 2026-10-03 decision: unannotated `x` and
ordinary value-annotated `x:A` have `Value(A)` entry force/rebind; explicit
outer computation annotations `x:[_] A` and `x:[E] A` have
`Computation(E,A)` retention. Missing `A` is a fresh inferred value endpoint;
the wildcard retains its existing symbolic source meaning. Whole-argument
construction is inert in every case. Value entry executes once before the
body even for unused, effectful or divergent arguments; latent returned
values are not recursively forced. Computation-core §6 generates these
roles and bindings before body synthesis. This authority preserves the
separate result-synthesis A decision.

Frozen parameter lowering already distinguishes the **outer annotation
occurrence** before solving value shapes:

| Raw parameter | Source effect-slot initialization | Frozen locator |
|---|---|---|
| `x` | pure argument effect; local effect absent | `lowering/expr/lambda.rs:1252–1264` |
| `x:'a` or another non-Effectful annotation | exact-pure effect slot; value constraints | `lambda.rs:1344–1353`; `annotation/constraints.rs:263–284` |
| `x:[_] 'a` | outer Effectful, fresh effect slot and local stack effect | `lambda.rs:1308–1325,1344–1353` |
| `x:[E] 'a` | same outer-Effectful path, plus concrete row constraints | same lambda locators; `annotation/constraints.rs:709–724` |

Paths in this table are below `crates/infer/src/` at `a58eefc3`. Parameter
creation still uses a fresh value variable and common `Def::Arg`/`Pat::Var`
constructors (`lambda.rs:285–301`, `lowering/pattern.rs:229–268`). Name lookup
uses the binding's local effect (`lowering/name_ref.rs:146–186`). Ordinary
local bindings store a result with no local effect
(`lowering/expr/block_local.rs:1232–1249`). No separate runtime role follows
from these facts alone.

The table is historical characterization, not the authority for current
entry timing or argument-effect admission. An unknown `A`, an empty solved
`E`, or body usage does not change the role selected by §21. Oracle
`StackWeight`, `All`, `AllExcept` and their routing rules do not supply this
source rule. Frozen initialization alone authorized neither implicit source
lifting nor a polymorphic interpretation of the result.

## 3. Independent non-collapse obligation

For a selected source port derivation, two changes cannot be justified by
solved representation equality alone:

1. A value endpoint `A` becomes a latent representation under substitution.
   This does not introduce a consumer of that latent value.
2. A retained computation's effect row becomes empty. This does not convert
   retention into value-parameter entry forcing.

The second has a direct decorated-source discriminator. Let `t` be a pure
diverging computation with interface `Comp(empty,Unit)`, and let a receiver
ignore its parameter. The retained-computation entry returns through its
body without executing `t`; the value-parameter entry forces `t` and diverges
before that same body. Hence empty effect support cannot identify these
entry semantics. This uses ordinary divergence and the selected entry laws,
not a raw-source acceptance assertion or an additional callback fixture.

Similarly, the regular `A = Thunk(E,A)` witness in source-computation-role §7
permits a returning data interpretation and an executing interpretation with
the same erased result shape. `E` is an upper bound, so it does not require
an actual request. Keeping annotation paths can **preserve an already chosen
derivation**; path names and upper bounds alone do not prove which derivation
raw result checking must select. A new source checking rule must close that
coherence obligation.

Capture-avoiding renaming transports a selected port, its original profile,
and all corresponding symbolic `K,D` together. Value/effect substitution
preserves the interpretation when it preserves that source derivation's
consumer premises. This is not unconditional code invariance when a newly
revealed interface requires additional elaboration, nor the as-yet-unproved
generalization/intrusion theorem.

## 4. Selected A and rejected implicit alternatives

Use a concrete input `t : Comp(E,Int)` that emits an `E` request when
eliminated. Consider executing the result computation of the displayed
forwarding function once and then discarding its returned value.

| Policy | Synthesized result interface | First explicit execution of the result |
|---|---|---|
| A. Preserve the expression's known computation interface — selected | `Comp(E,Int)` | Executes `t` and obtains its `Int` result |
| B. Return computation data under a new pure result layer — explicit introduction only | `Comp(empty, computation-data(E,Int))` | Returns `t` as unexecuted data; another consumer is needed to execute it |
| C. Generalize the result interpretation in the public interface — rejected | A public unresolved result-port parameter | Would require use-site interpretation selection |

This discriminator assumes the stated effectful input, not merely an `E`
row bound. It is expressed in the decorated source/core relation. The exact
complete frozen-source execution of this comparison is unverified.

**A is selected by the user.** It preserves the known source
interface of a forwarding expression and does not insert an extra pure layer
in synthesis. It matches the recorded forwarding inference expectation and
uses the existing core's declared callable execution view. Synthesis itself
does not execute anything; a source consumer of the synthesized computation
is what runs it. Ordinary lookup/storage/return of data remains inert.

The source rule is:

```text
Gamma(x) = I                    Synth(body) = I
----------------              -----------------------------------
Synth(name x) = I             Synth(lambda(P,body)) = Fun(P,Result(I))

Result(Value(A))          = Comp(empty,A)
Result(Computation(E,A))  = Comp(E,A)
```

`I` retains source value/computation positions, not just a solved runtime
type. Ordinary value results use the existing pure `result(d)` computation
port. This rule adds no extra pure layer around an already known computation
interface. It does not by
itself prove checking with nested annotations, admitted conversions or
principal inference. Explicit result checking still must derive the selected
typed result path without resurrecting overlapping lift/expose choices.

B would give ordinary data observation priority in an unannotated result.
The user rejected its implicit insertion: the additional result layer must
come from an explicit inert introduction. Its caller impact is semantic,
not merely inference-stage scheme formatting.

C would retain a result interpretation choice, but introduces
a genuine public interface parameter. It needs a principal quantified
interface, coherent code for every resolved port and lifecycle transport.
Neither disjunctive constraints nor a hidden runtime tag proves those facts.
Keeping the choice only in hidden binding provenance would violate the
typed abstraction requirement. Its larger proof/implementation burden is not
justified merely by matching a fixture. The user explicitly rejected this
polymorphism for ordinary forwarding; value/effect type polymorphism remains
a separate requirement.

The A decision closes the result-synthesis choice. It does not certify the
whole successor as sound/principal or authorize compiler implementation.

## 5. Proof work under the decision

Use the selected rule to construct result ports compositionally with
parameter annotations, names, application, ordinary binding and handlers.
Prove checking/coherence for nested results and recursive interfaces together
with substitution/renaming under explicit premises. Then instantiate the
reviewed derivation-core construction; do not add another theorem that
merely assumes arbitrary result ports.

This scope leaves the settled inert introduction, shallow outside handling,
activation-scoped typed-value transport and symbolic-family invariance intact.
It authorizes no compiler implementation and does not relax the finite
principal presentation, uniform-client, acceptance or lifecycle gates.

Provenance: selected A and the entry/inertness laws are Yulang extensions,
not Simple-sub-original rules. Their complete successor inference application
remains a proof obligation. The two non-collapse witnesses
are deductions in the declared candidate source/kernel, not claims that
frozen weight routing is sound.
