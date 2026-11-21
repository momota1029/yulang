# C311 design: historical choice across a late alias

## Source path checked in Lean

The following is schematic source, not output of the Rust parser:

```text
Outer(List[U], List[T])   // U = List[Int], T = Int for this checked goal
  where Receiver(T, item=z)
        Route(U)
Route(List[V])
  where Receiver(V)
Receiver(Int)
  item = Int
```

The root is installed first. The direct Receiver is selected while its peer
does not yet exist. Its installation strictly narrows the live models by
`z ≃ Int`. The route is installed next and emits a distinct occurrence,
also with center source 2 (Int) but no local requested outputs. The actual
merge aliases it to the recorded direct Receiver. The peer now has a live
class request but no historical packet at its own occurrence. Replaying a
recorded plan at the peer is impossible, and the C310 requirement for a
same-name local request representative is false there. Nevertheless the peer
has a current Frame and the route's actual selected dictionary is `3[2]`;
both pieces of evidence and the peer installation semantics hold in every
same final model. The compatibility proof uses the different-occurrence
transport; one-candidate-per-role only proves local selection in the fixture.

## What the generic lemma now consumes

1. A recorded historical packet rechecked at its own occurrence under an
   ordinary extension with its owned keys still valid. This supplies a
   historical Prepared at the current context.
2. Current source-observation equality for the two occurrences, including
   the endpoints that inspection reads, not just an equality of their
   observed center types. This yields the same report, captures and checks.
3. The peer's independently checked linkage and allocation Fresh.
4. Either every used input name has exactly one reported capture (there are
   no aggregate equations), or its private aggregate slots are disjoint from
   the current raw pool. In the latter case preserve raw values, cross
   constraints, self-checks and projections while patching the private slots,
   as in the previously verified finite-equation realization. This gives
   existential Prepared only; it is not a strategy for constructing the
   fixed, universal common-model evidence in (4b).

The choice key now follows from actual selection plus Prepared. It is not
part of a supplied transfer certificate.

## Next proof search, without changing acceptance

- `SameInputs` equates interpretations of stored observed center origins.
  It does not have the current declaration's read-bound list as a field.
  In the next actual source fixture, first determine whether accepted
  alias+refresh with different **endpoint lists** can still preserve the
  checked head's report meaning. If the exact bound list changes, target
  transport of fit/cross/self-check/projection individually rather than
  assert textual equality. Keep the old live model and the new private
  Prepared witness distinct. Look for the actual generated nonpoint and
  versioned aggregate fixtures (e.g. cycles 233, 238, and 239); use an actual
  source transition for either proof or a counterexample.
- In the still-uncovered cases where private aggregate targets already occur
  in the raw pool, patching them is insufficient: it could also alter the
  live constraints. Need either a proof that their installed equations match
  the current aggregate definition, an exact transport under refresh, or a
  precise reachable counterexample. Allocator Fresh alone allows previously
  allocated names and is not disjointness.
- For (4b) do not identify a local empty request list with an empty alias
  request class. The regressed branch shows a genuine non-local request;
  a general step should use the historical output value and its relevant
  declaration/target proof, or explicitly handle newly inherited names and
  defaults, in the same full assignment. For (2), reporting returned-halt
  partial correctness still requires the two independent implementation
  connections listed in the cycle report.

No termination, language-acceptance change, or Rust execution is claimed.
