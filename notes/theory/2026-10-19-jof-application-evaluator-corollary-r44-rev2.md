# Conditional evaluator corollary for JOF Application — R44 revision 2

Status: **conditional source-to-evaluator corollary; q typing OPEN**
Sprint: `call-output-owner-jof-20261019-r44`, revision 1 candidate
Supersedes: the conditional premise list in `2026-10-19-jof-application-evaluator-corollary-r44.md`; preserves it as history
Parent: unchanged inference/evaluator theorem and Simple-sub A/B, **OPEN, 0 → 0**
Author: Luna primary `/root`

## Exact conditional claim

Fix `q = Application(f,a)`. Assume its source derivation independently
provides the following complete typed-core inputs:

1. operand derivations `Code(E,c_f,Comp(E_f,A_f);q_f)` and
   `Code(E,c_a,Comp(E_a,A_a);q_a)`;
2. the actual Application/Gen-Call-0 origin `c`, including its dependent
   `F_c,R_f` indices;
3. the actual whole-argument `ReifyOrigin(o_arg,c_a,r_arg,Comp(E_a,A_a),...)`
   and its `Carrier-Delay` construction;
4. the original symbolic complete Call-result interface
   `Comp(E_c,A_c)` and its independently formed result port `o_c`;
5. the actual emitted `VIncl-origin(A_f,F_c)` and
   `WholeArgCompatible-origin(J_a,CarrierContract(F_c))`;
6. the resolved source roots/scopes, actual provider/current configuration,
   and every ordered entry/body/consumer/return suffix interface required by
   the complete producer's `Suffix_c(U)`; and
7. the designated one-layer consumer and its original typed port/profile.

These inputs must be formed independently of result-inclusion truth,
satisfying assignments, successful queries and `TypedCallCert_Dec`. In
particular, the original typed-core Code-Call rule consumes the symbolic
`Comp(E_c,A_c),o_c` and the listed origins; it does not construct an authentic
source output owner or establish complete semantic Call typing.

Assume JOF adds only a source/type `Desc` record and its relation clauses,
preserving all seven inputs and their original scopes. Then the existing
application translation and evaluator behavior follow exactly:

```text
I_q = Computation(E_c,A_c)
d_q = reify(call(c_f,c_a))
Normalize(I_q,d_q) = eliminate_p(d_q)
X[eliminate_p(d_q)] = Execute_p(V[d_q]) = X[call(c_f,c_a)]

X[call(c_f,c_a)] =
  X[c_f] >>= lambda f.
    let t = Delay(X[c_a], lexical references) in
    ExecuteCallable(f,t)
```

The call keeps the callable's declared result-computation port inside the
complete Call view, with its original receiver entry, receipt, result
consumer and return boundary. JOF adds no runtime force, wrapper, provider
choice or output descriptor.

## Proof

The typed-computation core's Application row gives `I_q` and `d_q`. Its
normalization for a known computation eliminates the designated port exactly
once. `V[reify(c)]` is an inert `Delay(X[c])`; therefore `Execute_p` executes
`X[call(c_f,c_a)]` without recursively forcing the returned `A_c`. The
`X[call]` clause evaluates the callee, retains the whole argument as a
carrier, and invokes the actual callable through `ExecuteCallable`.

Given premises 1–7, Code-Call and the finite typed-computation realization
theorem apply to this same call node. The theorem preserves finite execution
prefixes and admissible finite future-use/raw-resumption histories under its
stated well-formed interface and owner assumptions. JOF's `Desc` metadata is
source/compiler construction data, not an executable tag, so it leaves the
`V/X` translation unchanged when the seven inputs are held fixed.

## What is not discharged

R44 has not constructed premises 2–7 at the target
`q = Application(Name(loop),Name(y))`. In particular, the prior R44
candidate's `Delta_A := Gamma_q` does not construct `o_c`, the exact free
dependency telescope, either compatibility origin, or the full ordered
suffix. The conditional theorem therefore proves neither that q has a JOF
source derivation nor that JOF preserves the original accepted source fiber.
Soundness, principality, source/native correspondence and production remain
open. No compiler code, test, expected output, build, Cargo command or runtime
execution was changed or performed.

## Governing evidence

- `notes/theory/2026-10-07-call-input-construction-proof.md`, §§3.4, 4 and 8; SHA-256 `f7c1b1eb23acb33ab98487097ab67617e1af84964b012b1c951a8805dd9f6`.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md`, §§2–4 and 9; SHA-256 `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §§3.3 and 5; SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.

The original theorem remains **OPEN, 0 → 0**.
