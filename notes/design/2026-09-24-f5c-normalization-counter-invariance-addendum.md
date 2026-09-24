# F5c normalization counter-invariance addendum

Status: Authoritative; implementation slice complete, broader F5c closure open
Scope: Preserve §36 normalization-counter invariance under root and
Union/Intersection member permutations while retaining the exact comparison
count for its prescribed stable mergesort.
Approved-by: user selected option B on 2026-09-24
Review context: The user directed primary-only work. No independent reviewer or
benchmark is claimed.
Supersedes: none; specifies the deterministic preordering required by §36.

## Decision

Keep §36's root-order and member-order counter invariance. Before each
counter-measured stable top-down mergesort, place its inputs in a canonical key
order that depends only on the key multiset:

- For each normalized Union/Intersection child list, pre-order by the unsigned
  fixed-width key `(postorder height, rank)`.
- For each postorder-height descriptor group, pre-order by the lexicographic
  sequence of descriptor words.
- For either pre-order, use stable insertion sort for three through eight
  keys. Inputs of one or two keys skip preordering because their specified
  merge and equality-check comparison schedule is already permutation
  invariant. For larger inputs, use iterative in-place MSD radix distribution.
  A descriptor
  word is encoded most-significant byte first; byte values map to `1..=256`,
  and the end-of-descriptor symbol is `0`, so a shorter equal prefix sorts
  first. Fixed child keys encode both `u32` fields most-significant byte first.
- Run the exact §36 stable top-down mergesort after preordering. It remains the
  comparison-counted sort; its output and the subsequent adjacent-key
  duplicate checks determine ranks and child deduplication as before. The
  radix/insertion preordering does not increment the mergesort word-comparison
  counter.

The preordered key sequence is identical for every permutation of the same
inputs. Therefore the specified mergesort and duplicate-check schedule has the
same word-comparison count, while still reporting the exact comparisons those
operations perform. The preordering does not change normalized values,
height-major order, rank equality, or §44's first-member representative.

## Work and scratch model

The preordering adds `O(N + W)` work: descriptor words require at most four
byte positions per `u32`; each child key is two `u32` words; insertion sort is
bounded to eight keys; and the radix alphabet has a fixed 257 symbols. The
existing `O(N + W + C)` bound remains valid, with `C` still the comparisons in
the prescribed stable mergesorts and following adjacent equality checks.

Large-input radix distribution reuses the existing height-node and child
arrays in place. Its additional storage is one explicit frame stack with
`O(N)` peak live entries and one 771-`usize` workspace (three 257-slot
histogram/cursor lanes). Both are fallible, checked, and included in the
normalization-index lane ledger; small preorders allocate neither lane.
The descriptor and child sorts use the same iterative radix kernel, so neither
adds recursive depth.

## Implementation gate

Tests must independently verify the stable-mergesort comparison oracle after
canonical preordering, counter equality for rotated component roots and
reversed Union members, unsigned byte ordering across `u32` boundaries,
variable-length descriptor-prefix ordering, and physical reconciliation of
the new scratch lanes. The approved mixed-height positive/negative tests,
stack-depth witness, and §44 representative linkage remain required.

This addendum closes only the counter-contract choice. It does not certify all
F5c scratch, other availability lanes, the full solver suite, or F5e resource
and public-observation gates.
