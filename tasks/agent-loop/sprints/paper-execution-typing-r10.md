# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r10 — declared perform typing

Status: issued by the primary for the user's continuing inference/executor proof goal.
Branch / baseline: `research/simple-sub-intrusion` at
`9cbf9feaf9a7b1548b4e98af3051fc24c2d8c715`.
Authority: `docs/yulang-operational-type-safety-ja.tex:241` and full arbitrary
simultaneous substitution rule `:953-977`. Preserve the original parent claims
and all omitted-paper/source obligations.

## Fixed outcome

Extend the currently checked partial typing relation with its represented
`perform` computation rule, resolving operation IDs to exactly one declaration
from `DeclarationTable.operations`, checking the declaration arity, typing the
payload at the instantiated payload type, and returning the same instance's
response type. Extend the arbitrary-σ transport theorem across this constructor
using `DeclSubst.operation_declaration_instantiation_subst`; map declaration
resolution and payload together. Do not model `D(o)` as mere list membership,
allow payload/response instances to diverge, or strengthen σ.

The operation resolver must preserve the paper's functional `D(o)` meaning.
Use a source-side relation that records membership, identity equality, and
uniqueness of the matching declaration, then prove it preserved under
`OperationDeclaration.substAmbient` / `mapDeclarationTable`. Do not change the
operational meaning of `perform`, executor behavior, or compiler code. Rename
the typing module's local args-syntax helper so importing `DeclSubst` does not
shadow/collide with its existing helper.

## Exact ownership and dependencies

Primary `/root` owns `PaperExecutionSyntax.lean`,
`PaperExecutionTypingSubstitution.lean`, this contract, `current.json`, and the
R10 outcome. `DeclSubst.lean`, `PaperTypeFormation.lean`, the paper, and the
frozen R9 handoff are read-only inputs. Primary alone owns the Lean/Lake checker
and `.lake` cache. No worker/reviewer is admitted: the eight existing UNKNOWN
reservations remain quarantined and capacity does not permit a fresh assignment.
The implementation lane records `NO_SAFE_CODE_SLICE`; do not touch Rust or
production code.

Input hashes at issue:

- R9 typing module: `f9d8511e66d166319ca6c0b8c49574dc11e436f6142f5ca02fdf272de2953ab9`
- `PaperExecutionSyntax.lean`: `8ad8bc4b1549eadaa73c743438b333c62b44be7bdff0346f690b7da9e6353a97`
- `DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- R9 handoff: `ac20f28dcfef58ec0389bd9da7382ae5033a3cc8190e640f2e42a8a98c10c04e`

Budget: at most 900 active seconds, 8 serial Lean/Lake invocations, and 120
checker seconds; `-j1 -M1024`. Keep one checker process at a time. Existing R1-R9
charges remain recorded. Stop at a concrete declaration-resolution or
instantiation-commutation obstruction, scope/authority change, user STOP, or
budget limit. Never use `sorry`, `admit`, project axioms, Rust/native builds, or
tests.

## Acceptance and remaining boundary

Success requires the focused typing module build, exact theorem type for the new
resolution preservation lemma and all five transport judgments, plus complete
axiom audits for `DeclSubst.operation_declaration_instantiation_subst`, the new
lemma, and all R10 transport/support declarations. No `sorryAx`, `_f`, failed
declaration dependency, or project axiom. Record exactly which typing
constructors remain absent.

The R9 result was checked but not independently reviewed. Keep review status
`NOT_RUN`; no author self-review may be called independent. Full paper typing,
term substitution, capture-avoiding renaming, handler/request closure, inference
and executor soundness, original A/B claims, source/native correspondence and
Rust bridges remain OPEN. This is one declared-operation slice, not whole-paper
closure.
