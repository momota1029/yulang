# R8 dependent-composition diagnosis

Sprint: `EFFECT-PERMISSION-DEPENDENT-COMPOSITION/20261029-r8-diagnosis`. Read-only diagnosis; it proposes a route but proves no theorem.

## 1. Dependent Function composition

In `FormalPermissionExportWitness.lean:77–83`, `decodePort c p source s` returns `Option (PortDecoded c p source s)`. At R7 `FormalPermissionSourceAllocation.lean:249`, after `port_decoder ae`, the context has `hao : ad.out = ao`; after calling `port_decoder re` too early it has `rd : PortDecoded c p reCode ao.state` and `hrd : decodePort c p reCode ao.state = some rd`. Rewriting `ao` in `hrd` alone is ill-typed because the witness's dependent state index is not transported.

Supported source-level route: eliminate `hao` throughout the dependent context *before* invoking the result-port decoder. Then the result witness is indexed by `ad.out.state`; eliminate remaining result output/birth equalities before record normalization. Equality elimination transports the result effect input, helper premises, and goal coherently. An index-free result projection is not required by the inspected types.

Proposed optional helper, if a named sequencing lemma is useful:

```lean
theorem sequential_port_decoders
    {c : Context} {p q : Bool}
    {u v : Option SourceRow} {s : State}
    {ae re : SourcePort} {ao ro : PortResult}
    {ab rb : List Nat}
    (first : SourcePortSuccess c p u s ae ao ab)
    (second : SourcePortSuccess c q v ao.state re ro rb) :
    ∃ (ad : PortDecoded c p ae s)
      (rd : PortDecoded c q re ad.out.state),
      decodePort c p ae s = some ad ∧
      ad.out = ao ∧ ad.births = ab ∧
      decodePort c q re ad.out.state = some rd ∧
      rd.out = ro ∧ rd.births = rb
```

This follows from the existing `port_decoder` plus equality elimination; it adds no helper law. If record equality later needs a standalone lemma, equality of `ValueDecoded` records can be derived from equal shape, entries, state and births; the `events` fields are proofs and proof irrelevance identifies them. This cannot compare records with different state indices.

## 2. Mutual derivation induction

Replace `termination_by sizeOf code` with paired induction over the actual `SourcePair` and `SourceTuples` derivations. For fixed shared context `c`, use motives that quantify polarity and all changing indices:

```lean
MP := fun p a code s out (_ : SourcePair c p a code s out) =>
  decodeValue c p s code = some out
MT := fun p xs code s out (_ : SourceTuples c p xs code s out) =>
  decodeTuple c p s code = some out
```

For allocation, use the same paired motive shape with conclusion `AllocationTrace s.nextEffect out.births out.state.nextEffect`. Decoder and allocation conclusions may also be conjoined in each motive and projected to the four unchanged public theorem statements. Generalize `p`, annotation(s), code, entry state and decoded output; keep `c` shared and fixed. In particular, do not fix polarity outside the motives. Exact eliminator binder order remains for a later executable implementation packet; generated recursor types were not inspected by execution.

The Function case must retain the indices and sequencing:

```text
argument:       s → av.state, polarity !p
result:         av.state → rv.state, polarity p
argument port:  rv.state → ao.state, polarity !p
result port:    ao.state → ro.state, polarity p
```

Its allocation case composes the argument trace, result trace, argument-port trace and result-port trace in that order with `AllocationTrace.append`. Tuple cons composes the head trace with the tail trace starting at the actual `av.state`. The source implementation at `candidate_effect.rs:1617–1704` likewise processes argument value, result value, argument port and result port in that order. This diagnosis preserves that order and the admitted successful-return cut.

`FormalPermissionConstructorRealization.lean:180–234` supplies a source-level comparison: the existing mutual `value_events_refine`/`tuple_events_refine` and `value_events_birth`/`tuple_events_birth` proofs recurse on the paired derivation children, including changed Function polarity and sequential states. This is a pattern for the motive, not an executed inspection of generated recursors.

The proof still depends on the existing explicit `FreshReady` / `FreshStep` availability witnesses, `HelperFrames` equalities and tuple guards. It does not establish concrete helper execution, permission-prefix preservation, native state, or `SourcePair` existence.

## 3. Line 239 kernel mismatch

The raw R7 attempt-2 diagnostic at line 239 is separate from line 249. The generated well-founded mutual-call wrapper fixes polarity `p✝` in its `PSum`/`PSigma` domain, while the recursive argument supplied by the constructor is indexed by current `p`. The kernel therefore expects `SourcePair/SourceTuples c p✝` but receives `… c p`. This is a polarity-index mismatch in the recursive-call package. It is not shown to follow from either the dependent rewrite or the size inequalities. Generalizing polarity in both paired motives addresses the shape of this mismatch, but the exact executable recursor application remains unverified. No mathematical counterexample or kernel defect is established.

## Scope and status

The 17-entry R8 manifest matched byte-for-byte. Diagnosis agent: registered `lean_prover`, read-only, 180-second assignment; no files edited and no Lean/Lake/checker/tests/Cargo or generated outputs. Luna's source-boundary read confirmed source order and unchanged frame/availability assumptions.

This is an unexecuted proof-structure proposal. All original parent, source/native, helper-execution, effect-hygiene, consumer, unequal-transport, soundness, principality, termination, exact-tree `SourcePair`, permission-prefix and production gates remain OPEN.
