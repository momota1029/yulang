# Conditional evaluator corollary for JOF Application — R44

Status: **conditional source-to-evaluator corollary; q typing OPEN**
Sprint: `call-output-owner-jof-20261019-r44`, revision 1 candidate
Parent: unchanged inference/evaluator theorem and Simple-sub A/B, **OPEN, 0 → 0**
Author: Luna primary `/root`

## Claim

Assume an ordinary Application `q = Application(f,a)` has a complete source
derivation under a JOF candidate, including authentic operand derivations, a
well-formed output descriptor, the complete original Call interface and its
designated result consumer. Assume JOF contributes only source/type formation
records and constraints, while preserving the typed-computation core's
application synthesis and reification clauses. Then the executable term and
its evaluator operation are exactly the existing ordinary Application term:

```text
I_q = Computation(E_q,A_q)
d_q = reify(call(n_f,n_a))
Normalize(I_q,d_q) = eliminate_p(d_q)
X[eliminate_p(d_q)] = Execute_p(V[d_q]) = X[call(n_f,n_a)]
```

By the `call` translation,

```text
X[call(n_f,n_a)] =
  X[n_f] >>= lambda f.
    let t = Delay(X[n_a], lexical references) in
    ExecuteCallable(f,t)
```

`ExecuteCallable` uses the callable's declared result-computation port within
the complete Call view. It preserves the existing invocation entry, receiver,
receipt, declared consumer and return boundary. In particular this corollary
adds no force, callback, provider choice or runtime output descriptor.

## Proof

The application row in the typed-computation core fixes `I_q` and `d_q` above.
The `Normalize(Computation(E,A), d)` clause is the designated elimination of
that known computation port. Its executable translation is one `Execute_p`
step. Since `d_q` is an inert `reify` of the call, `V[d_q]` is a `Delay` of
`X[call(n_f,n_a)]`; the designated `Execute_p` eliminates that one layer and
executes the call code. It does not recursively force the returned `A_q`.
Applying the core's `X[call]` clause yields the displayed order: evaluate the
callee, construct the argument carrier inertly, then invoke the actual
callable through `ExecuteCallable`.

The Generalize constructor represents `Desc` and its typed provenance as
source/compiler construction data, not as a runtime tag. Therefore adding the
candidate output declaration leaves the `V` and `X` translation clauses
unchanged, provided the candidate really is erased from executable code and
does not alter the selected callable or its source owner. This proves equality
of the translated command for the same operand code and Call interface.

The typed-computation core's constructive realization theorem then supplies
the finite-prefix and admissible finite-future simulation for this Application
node, under its stated well-formed-interface, typed-path and owner premises.
The theorem is conditional on those premises. For the target recursive
`q = Application(Name(loop), Name(y))`, R44 has not constructed the complete
q-indexed Call headers or the exact `Desc` dependency telescope, so no source
derivation is yet available to discharge the condition.

## Scope limits

This result proves evaluator translation is unchanged for a fixed complete
Application derivation under the candidate. It does **not** prove that JOF
accepts the same source programs, preserves old source fibers, is sound or
principal, or supplies the missing q typing. The extra source relation may
change which derivations exist even though each resulting call executes by the
same evaluator clause. No implementation, regression test, fixture, build,
Cargo or runtime was changed or executed.

## Governing evidence

- `notes/design/2026-10-02-typed-computation-core-elaboration.md`, §§2–4; SHA-256 `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`.
- `notes/design/2026-10-02-source-computation-role-elaboration.md`, §§3, 10 and 12; SHA-256 `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb`.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §§3.3 and 5; SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.

The original theorem remains **OPEN, 0 → 0**. The output-owner scope audit's
`D_q` premise and the complete q source derivation remain open.
