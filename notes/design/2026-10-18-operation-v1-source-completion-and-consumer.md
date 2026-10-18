# Operation v1 source completion and consumer

Status: r17 primary design candidate, before independent semantic review. This
continues the explicitly authorized, reversible research semantics v1 from
`notes/design/2026-10-18-operation-licensed-field-rule.md` (SHA-256
`1004426d4afa990453d0addc8008f88327166862b63d311be8445eeb4218503d`). The
original `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN,
closure 0. No production rule is changed here.

## Concrete source candidate

Use the existing source-defined operation/handler specimen
`tests/contracts/stable-core/v0/public-signature/pass/nested_data_position_effect_function_public_signature/main.yu`:

```yulang
mod demo:
  act pulse 'a:
    pub fire: 'a -> 'a

  type cell 'e 'a with:
    struct self:
      exec: () -> [pulse 'a; 'e] ()
    pub c.apply(f: 'a -> 'a): ['e] () =
      my loop(x: [_] _) = catch x:
        pulse::fire v, k -> loop:k:f v
      loop:c.exec()

my site = 1
```

This is a source candidate only. The annotation parser currently records the
operation declaration, field signature/positions and concrete row family;
that data is not itself a complete typed-Sigma derivation, fixed contribution,
independent license proof, or whole output map. Sol must verify that a concrete
occurrence in this specimen actually instantiates the r16 `s1,j` judgment. If
it does not, select the nearest already accepted source specimen with the same
declaration/reference and returning-R shape, and record why; do not relabel an
unrelated row or claim the test exercises the new rule.

## Proposed v1 introduction from source evaluation

Add a distinct constructor rather than wrapping an absent old
`d_orig`:

```text
resolve(source, declaration, reference, theta, exact_written_position j)
  -> OperationForm_v1(c) × CompleteTypedSigma_v1 × PositiveWrittenField_v1
     × OpFieldLicense_v1

evaluate_v1(the_same_parsed_source, the_same_operation_occurrence, input,
            continuation, initial_world)
  -> Pending(request, resumed_continuation)
   | Returned(value, whole_output_world, trace, typed_completion)
   | Diverged(finite_prefix)
```

Only the `Returned` branch constructs `CompleteAdmittedOperationDevelopment_v1`.
Its constructor owns the returned value/world, `A_decl` suffix, output typing,
whole substitution/map, admission and exact field action. Every projection is
from this one constructor; tests, candidate family membership, stdout matching
and independently assembled endpoint typings cannot provide any field. Pending
and divergent cases produce no complete-output incidence.

`LicenseAt` is produced by the source declaration/reference resolver at the
exact written field position and scope, before evaluation. It identifies the
authored field itself; it is not inferred from its family, member ordinal,
response, output value, handler match or candidate constraint. `c` is allocated
at that source formation and retained through evaluation and consumer use.

These signatures are proposed interface sketches, not a derivation. The proof
lane must give the operational and typing rules, prove that evaluation returns
evidence for the same source term and field, and state failure/invalid behavior.
If the existing language semantics do not supply a typing/completion premise,
the r17 rule must define it as a new v1 rule and make the observable semantic
change explicit. It cannot silently assert an old derivation.

## Consumer connection

Define an explicit `NPAIR-Consume-v1` eliminator for
`OpFieldAtOutput_v1(c, ..., d_dev, sigma_out)`. Its conclusion must carry the
same `c`, exact field path/ordinal, `d_dev`, output world/future indices and
license into a versioned constraint premise. The implementation must route
that premise through a real constraint insertion and propagation path, then
show the consumer observes it. It may not cast the evidence to old
`contributes-to`, `Contrib`, `Inc`, `Cover`, Permission, selection or removal.

For the selected specimen, the eventual vertical test must parse and typecheck
the real source, execute its real operation/continuation to completion, obtain
the source-produced v1 package, and assert the v1 consumer/constraint behavior.
The test may assert the source's result; it must never inject the result,
development map, license or constraint transition. Expected-output fixture
changes, if needed, require a reviewed source-rule delta and must preserve the
prior v0 expectation separately.

## Implementation boundary and falsifiers

The first implementation is feature-gated. A likely new owner is
`crates/yu-solver/src/candidate_operation_v1.rs`; existing wiring or source
evaluation paths may be added only after the rule and owner map are reviewed
and Luna grants an exact follow-up code lease. This design itself authorizes no
code changes.

Falsify this candidate if (a) the parsed field cannot be tied to one exact
source declaration/reference and pre-evaluation `c`; (b) completion's actual
provider/output differs from the evidence the consumer uses; (c) the output
map/action is synthesized from family/coordinate equality; (d) pending or
divergent execution is treated as returning; or (e) the path requires a test
to inject its own result or constraint. Report the first exact failing owner
and keep the parent open.

## Review and open conditions

Fresh semantic review must check introduction/elimination rules, field and
development identity, pending/divergent behavior, and compatibility changes.
The independent proof must establish source evaluation/evidence correspondence
for the selected example. After any bounded implementation, a different
compiler reviewer must check the emitted evidence against source/HIR, actual
completion and consumer before one focused source run.

Still open: whether the source candidate hits the exact r16 field; a
source-generated same-c completion package; actual complete `A_decl` output
and map; the v1 consumer; whole-use transport; W/Z and all quantified cases;
F1/FK1; old-semantics compatibility; soundness, principality, termination and
production readiness. This one example closes no universal parent condition by
itself.
