# Cycle 287: three distinct obligations for a future row-aware boundary

The checked mixed-kernel comparison uses the same original source
`F(R(row0))`, the same associated parent output `F(F(R(row0)))`, and one
actual generated child. Its registries differ only in the child's head:
one captures its whole input; the other tries to destructure the row
parameter of R. These are Lean fixtures, not new Yulang2 parser tests.

1. **Row inspection versus source admissibility.** The existing Pattern
   catalogue describes a row position but translate defers this nominal
   application; recursive typeArguments also refuses that parameter.
   A future row-aware binder would need typed row observation, scope,
   capture and equation compilation rather than reading a type field in
   place of a row. Independently GroundRoots currently asks for *one*
   closed denotation per root argument across every source model.
   The two models of this fixture with different rows show why its raw
   source-formation certificate does not imply outer Initial. A fix to
   inspection alone cannot close that outer premise. Distinguish a
   parameterized boundary from a fixed-row surface example, and test each
   separately before claiming an integration theorem.
2. **Ledger discharge versus a conditional dictionary.** The whole-type
   leaf has no effects or children, and is semantically committed.
   Nevertheless the current journal discharge only follows installed
   plans and aliases. The actual leaf is not recorded, so the parent
   output fact is unavailable in the versioned trusted slice. The point
   descriptor F(slot1) denotes slot2 in all whole journal models, but has
   no trusted refresh certificate. A possible future administrative
   witness for an inert leaf should recheck the leaf from the prior
   source-supported data, not from any full Models that already assume
   the output. The source-only certificate and negative test in
   `GeneralRebaseRowSourceLeaf287` distinguish these two branches without
   circular reliance on that output. This is a proposed proof obligation,
   not authorization to change kernel priority or when a child is settled.
3. **Output projection versus diagnostic completion.** Both registries
   have the same finite 2-fact output projection and the same full
   model predicate. At the actual raw fixed point the first has a
   complete evidence tree and the second an actual pending child.
   A usable successor observation for dictionaries must include at
   least something that distinguishes these frontiers; an empty
   output queue is not a complete resolver. EvidenceAt is conditional
   on child evidence and alone cannot replace that observation.

No spec, Rust implementation, parser, or existing kernel rule is changed.

## Where to look before attempting the next bridge

- In `GeneralNominalInspection.translate`, the nominal application branch
  requires an all-type constructor layout; in
  `GeneralNominalRecursiveInspection.typeArguments`, a row argument is
  not projected as a type argument. Add a distinct typed readback
  obligation if experimenting with row binders; do not weaken either
  check in place.
- `GeneralNominalFiniteMeaning.build` constructs nominal arguments using
  `Sum.inl`. `RowClosedTerm287.wrapped_not_closed` separates the grammar
  issue from the uniform-over-models issue in GroundRoots. Adding a row
  premise that pins the input does not, by itself, add its closed
  representation.
- Existing `GeneralRebaseRowIrrelevance273` lemmas show that the actual
  versioned expression environment, projection, emitted schemas and body
  class effects depend only on the complete **type** fields of an
  assignment. A type still contains the nested R row argument. To test a
  new independent ambient-row read, identify a typed source equation
  which genuinely accesses the row projection before proposing new
  outcome rules. The mapped arrow calculation in
  `GeneralRebaseSourceRowRegression285` is a useful regression for a
  mapping, not such an installed child.
