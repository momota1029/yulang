# R220 independent falsifier — revision 1

Status: **FROZEN; writes stopped after this submission.** Research-only
conditional characterization and structural separation witnesses; no
source-qualified counterexample and no parent premise discharged. Independent
review of this note is pending. This is a falsifier contribution, not review of
the author's eventual theorem.

## Assignment and dependencies

- Worker: `/root/abstract_generator_denotation_r220_falsifier`; session R220.
  Primary dispatch and subsequent formula clarification supplied the packet.
  Requested/observed model and effort: UNKNOWN (no runtime metadata supplied).
  No descendants, Git mutations, source edits, builds, tests or runtime probes.
- Sole lease and sole changed path:
  `tasks/agent-loop/inbox/abstract-generator-denotation-r220-falsifier.md`.
- Baseline HEAD observed: `6f3656d9ae0214721df9e160e7ae69ba29ee773f`.
- Actual contract SHA-256:
  `42ca0a85107b13af019dd6049e5b92d8bc03dadf51317ada45036af9120db79b`.
  Dispatch text had `...6045...`; on-disk contract and current state both have
  `...6049...`. Primary was notified; no semantic dependency differs.
- Parent: `Contracts.lean:128–130`, unchanged
  `SourceProblem.InferenceSoundness`:
  `∀ s x d a, supported s → generates s x d → solves d a →
   ∃ e, sourceJudgment s x e ∧ sameScoped s x e a`.
- Governing meaning: R199 §§1–4, R213 §§1–5, adopted L1 introduction and proof
  boundary. No new source meaning or concrete semantic sorts were selected.

SHA-256 values actually inspected with `sha256sum`:

| Dependency | SHA-256 |
|---|---|
| R199 abstract model | `33d0cd52fbbf07d7916804f8b8961c102b53cc1cf5e9260ac15d83de9f295aa0` |
| R213 fixed model | `17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e` |
| R219 result | `a88fd7ec4c0e85850a384220776d6c32d1a480e3923ba8b278ac716aea1fbb18` |
| L1 adoption | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration.lean | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceInterpretation.lean | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| SimpleSubConstraintSyntax.lean | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| SimpleSubRegularSolutions.lean | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| SimpleSubRegularPublication.lean | `18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99` |
| PaperExecutionSyntax.lean | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |

All semantic pins match the contract; dependency changes: none. R214/R215
were read only to avoid repeating their one-sided-top attack and to preserve
the distinction between atom shape and reference identity. Their prose is not
used as an oracle or a source-semantics premise.

## Method and exact local claim

I inspected the actual `Regular.expandNodes`, `Approx`, `RegularSub`,
`regular_unfold`, and `regular_of_leaf` definitions, then
`RegularPublication.decodeTerm`, `decodeConstraint`, `ClauseSatisfied` and
`StoreSatisfied`. This is the structural Regular fragment, with no alias or
union/intersection graph nodes; `decodeTerm` explicitly rejects the latter
terms. It is not a claim about every lattice graph or finite-Term valuation.

The primary's clarified candidate Value clauses are
`atom(c) ≤ var(q)` and `var(q) ≤ atom(c)`. No concrete R220 generator/module
or complete endpoint map existed at my inspection. The conditional claim is:
if **that same** `(graph, refs)` satisfies both clauses under the pinned
`RegularPublication.StoreSatisfied`, then
`graph.lookup .value (refs .value q) = some (.atom c)`.

There is no local counterexample. At unfolding depth 1, comparison from an
atom permits only the same atom or top as upper shape. Reverse comparison to
that atom permits only bottom or the same atom as lower shape. Their common
shape is exactly `.atom c`. `decodeTerm`/`findNode_sound` fix the decoded
constant's code, and decoding variables checks endpoint existence. No
coinductive cycle, graph-validity hypothesis or deeper unfolding can bypass
this depth-1 obstruction. This is a paper derivation from inspected rules,
not a newly kernel-checked theorem.

Similarly `var(e) ≤ bottom` forces the referenced Effect node to `.bottom`:
only the lower-bottom branch can expand successfully against upper bottom.
`bottom ≤ var(e)` alone does not force emptiness. Clauses `bottom ≤ bottom`
are satisfiable but constrain **no variable endpoint**. If intrinsic Effect
is instead definitionally fixed to the decoded bottom node, its local shape
is fixed, while its relation to an original source Effect coordinate still
requires the missing endpoint equation. I sent this distinction to the primary.

The uniform argument covers each base code of unit, bool, int, floatBits,
string, bytes, path and character and arbitrary payloads. It does not prove
that an as-yet undefined code function agrees with those eight adopted base
types. `PaperTypes.literalType` gives the eight source cases, not that bridge.

## Small structural witnesses against stronger shortcuts

These are symbolic instances of the pinned expansion rules, not full source
countermodels or executable runs. Every graph below is valid: its nodes have
no child references. Each claimed satisfied comparison expands to `some []`,
so `regular_of_leaf` supplies its all-depth meaning on the same graph/refs.

1. **Reference identity is stronger than atom identity.** Value table
   `[atom 0, atom 0]`, Effect table `[bottom]`, with `refs value q = 1`.
   `decodeTerm (atom 0) = some 0`; the two Value clauses decode to `(0,1)`
   and `(1,0)` and both hold. Thus the assigned node has exactly the correct
   atom shape/code but a different index from the decoder's first match.
   Two Value nodes are necessary to distinguish these indices. This refutes
   only a pointer-equality mutation, not the clarified shape claim.
2. **Intrinsic emptiness does not erase an independent contextual endpoint.**
   Value table `[atom 0]`, Effect table `[bottom, atom 9]`, Value `q ↦ 0`,
   intrinsic Effect `e ↦ 0`, unmentioned contextual Effect `h ↦ 1`.
   Both Value clauses and both bounds between `var(e)` and bottom hold.
   Nevertheless `h` is an atom, not bottom. Two Effect nodes are necessary
   for these distinct shapes. Atom 9 is deliberately opaque: this does not
   claim it denotes `write`, a permission or a residual. The witness refutes
   only inferring emptiness of an unconstrained contextual endpoint from the
   intrinsic clauses. For bottom-to-variable alone, setting `e ↦ 1` also
   satisfies that one bound and refutes its alleged emptiness implication.

## Exact source boundary

`OriginalSourceSyntax.Port` distinguishes `synthesis`, `finalRoot` and
`writtenTarget`. `OriginalSourceGeneration.annotated` retains the boundary
from synthesis to writtenTarget. However,
`OriginalSourceInterpretation.SourceAssignment.row` reads descriptor, value
and root at `⟨site, finalRoot⟩` and carries its separate full `Event`.
`Sorts.Descriptor`, Value and Root are abstract; Event includes fiber,
assignments, history, current configuration, witness, scope, authority,
incidence and dictionary. The structural Store contains only kind/lower/upper;
its references contain no equation for those source components.

Consequently the structural atom/bottom result does not yet produce
`Value(τ(l))`, `v(l)`, original `r,e₀,ξ,ω`, or
`Return = Comp(empty,τ(l))` in the original source model. L1 explicitly
prescribes these facts and explicitly leaves the independent inference
connection open. `LiteralAtom` still consumes `LiteralDeclaration` and ground
facts, while `generated_literal_membership` consumes satisfaction of the
supplied local kernel. Neither derives those premises from this Store.

This is **missing model evidence**, not a satisfying assignment that refutes
L1 or soundness. Arbitrarily attaching a wrong root/event/readout to the
structural graph would not be a counterexample to a defined full model;
no such full embedding is present. Replacing the satisfying assignment,
choosing new sorts, or assuming the desired `LiteralDeclaration` would hide
the same missing premise. Likewise the source literal may provide its exact
payload value, but a graph-only type readout cannot distinguish, for example,
`bool false` from `bool true` with the same Bool type constraints.

Parent-premise delta remains 0; roots 0/4, packages 0/5, hygiene delta 0.
Call, conversions, annotations, other source constructors, complete effects,
solver execution and Rust/native correspondence remain unverified here.

## Commands, resources and next action

Commands: read-only `git rev-parse HEAD`, `cat`, `sed`, `rg`, `sha256sum`,
`date`; one `apply_patch` creating this note; final hash/readback inspection.
Some broad initial reads were output-truncated; decisive definitions and L1
were reread with targeted ranges. Missing R220 candidate paths were reported
by `rg` before any author artifact was available. No Cargo, Lake, Lean,
tests, executable experiment, seeds, randomized ranges or heavyweight process
ran. No oracle implementation was manufactured: the derivation shares the
pinned structural rules, while L1 is the separate source authority; it does
not claim independently validated source transitions.

Budget: ≤600 seconds assigned; exact total wall/CPU/peak RAM was not
instrumented. Tool subprocesses were lightweight, with reported durations
below one second each. No build/cache writes or scratch paths. Observed
clock before final artifact preparation: `2026-11-01 21:07:07 UTC`.

Recommended next action: primary should freeze the actual source endpoint and
Descriptor/Return/Event readout equations before admitting a parent-applying
Lean theorem. A structural local theorem may be preserved with its exact
conditional type, but must leave the parent unchanged until that embedding
is supplied. If the interface remains absent, stop at this interface rather
than run another equivalent toy graph probe.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/abstract-generator-denotation-r220-falsifier.md`.
- Baseline: `6f3656d9ae0214721df9e160e7ae69ba29ee773f`.
- Changed dependency hashes: none; contract dispatch typo recorded above.
- Review status: unreviewed frozen research contribution; no theorem closure.
- Checks already run: pinned source inspection, direct dependency SHA-256
  comparison, symbolic depth-1 classification and the two witnesses above.
  No new theorem type/axiom audit exists in this lane.
- Proposed message: `research: record R220 structural falsification boundary`.
- Shared-record deltas left to primary/curator: retain OPEN parent and all
  counts; record source endpoint/descriptor/event embedding as missing;
  preserve the intrinsic/contextual distinction; reconcile worker STOPPED
  only from this explicit stopped-writes receipt. No descendants remain.
