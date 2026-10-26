# Constructive finite-use generalization transport

Date: 2026-10-26. Producer: primary `/root`. Original parent:
`SourceProblem.InferenceSoundness` and the unchanged full source contract in
`docs/yulang-whole-proof-closure-ja.md`. This component does not close that root.
No compiler, dependency, toolchain or source-language semantics were changed.

## Claim and source correspondence

The governing forward argument is NL5–NL7 of
`notes/theory/2026-10-24-native-level-closure-and-publication.md`, revision
SOURCE-INDEXED-DERIVATION-20261024/r1, SHA256
`37aeacff4a6dc310bedcb5a44db4afcf8329b05ed684df19350487c5e8711c13`.
The original source-preservation argument and October 11 inference principles
retain all source, scope, shared-witness and principal-coverage obligations.

The constructed Lean theorem proves a simultaneous forward solution pullback
for a complete finite clause store, finitely many level-based fresh uses, and
arbitrary later client clauses. The original store is retained in full. Each
use copies all supplied clauses. This is deliberately **not** an assertion
that actual reachable-high native publication copies every clause. Applying
the theorem to that publication still requires its exact correspondence or
an independently proved solution-extension argument.

The original Scala reference path recorded in the NL note is absent here.
It was not freshly inspected. The actual Rust owners were inspected instead:
`candidate_scheme.rs::row`, `expand_row`, `prepare_candidate_fresh_use`, and
the minimum-level/non-generic merge in `candidate_intrusion.rs`. The independent
review records their exact source lines and the remaining native obligations.

## Frozen source and dependencies

| Input | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |

Namespace: `YulangClosure.SimpleSub.Generalization`.

`freshen n b levels use` fixes rows at or below the boundary and assigns high
rows the coordinate `n + use*n + row`. Original rows are bounded by `n`.
Bounded rows from different uses have disjoint high blocks; low anchors remain
shared. `transport` is one total kind-preserving row map: original coordinates
use `q`, copied coordinates decode their use/row and use post-quotient freshening,
and all later client coordinates beyond `n*(count+1)` remain fixed.

`transport_freshen` derives the commuting equation from preservation of low
anchors and finite index bounds. The equation itself is not an input. An old
high row may become low. `base_term_pullback` and `fresh_term_pullback` lift this
to every existing Term constructor, with all four Function ports, labels,
optional bits, tags, tuple order, and rigid atoms preserved.

Core theorem, using the definitions above:

```text
quotient_uses_with_clients:
  StoreBounded n store
  -> PreservesAnchors n boundary before after q
  -> (all requested uses are below count)
  -> Satisfied rho
       (usesStore n boundary after uses (map (rename q) store)
        ++ map (rename (transport n count boundary after q)) clients)
  -> Satisfied (rho o transport n count boundary after q)
       (usesStore n boundary before uses store ++ clients).
```

Every clause, use, root and client shares exactly that same valuation and total
transport. There is no per-clause existential witness or diagonal-lift premise.
Clients are explicitly renamed through the same map in the input; arbitrary
unchanged post-state client syntax is not silently assumed.

## Canonical minimum and review repair

The first independent review accepted the literal broad pullback but found M1:
an arbitrary row map does not make the seeded `quotientLevels` fold the exact
class minimum, nor guarantee post-quotient allocation remains in its reserved
region. Its counterexamples and the original frozen hash are preserved in
`20261026-inference-generalization-review.md`.

The repair keeps the arbitrary-map theorem under the accurate name
`lowered_quotient_uses_with_clients` and describes that fold as a seeded lower
envelope. It adds `Canonical n q`: every bounded row maps below `n`, and
`q(q(i)) = q(i)` there. `quotientLevels_is_minimum` proves the finite-fiber
greatest-lower-bound characterization at an in-scope fixed representative;
`canonical_quotient_minimum` applies it to every canonical image.

`canonical_post_use_bounded` proves every such use image lies below the future
client region; `canonical_post_uses_disjoint` proves distinct eligible uses
remain disjoint. The repaired `minimum_quotient_uses_with_clients` genuinely
consumes Canonical and returns all three results: the one transported solution,
the exact minima of every canonical fiber, and all requested post-use index
bounds. No native union-find correctness is assumed from the word canonical.

The checked `two_uses_one_anchor` example exhibits two independently allocated
uses mapping to one lowered anchor while a later client coordinate stays fixed.
`raising_anchor_breaks_transport` shows the low-anchor condition is substantive.

## Pinned verification and actual failures

Isolated project: `/workspace/scratch/f98087c7ac1a/inference-generalization/`.
Repository pin: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no external packages.
Used the exact task-local Lake, `LEAN_NUM_THREADS=1`, `-j1 -M1024`, 90-second
command limits and a separate cache. No global configuration changed.

Final commands, both exit 0:

```sh
lake --no-cache build +YulangClosure.SimpleSubGeneralizationSoundness
lake env lean -j1 -M1024 GeneralizationAudit.lean
```

`check-07.log` reports all four dependency jobs successful and no warning.
`audit-08.log` inventories **71 originating-module theorem constants**, including
private/generated declarations, prints all complete types and indirect axiom
sets, and rejects project axioms or dependencies outside the standard allowlist.
All authored theorem types were inspected, including the new canonical/minimum
and allocation conclusions. Axiom distribution: **35 empty**, **10 `propext`**,
**26 `propext, Quot.sound`**. No `sorryAx`, project axiom or checker bypass occurs.

| Final evidence | SHA256 |
| --- | --- |
| `check-07.log` | `d8e3d6c573b1528d66ccac5b9518e2998d60c7e49821e218eaba7195756d4991` |
| `audit-08.log` | `f9ca2f65d761a9352043c0ca5f73228448895d874a28939aa6b3187280e35a85` |

Failures are preserved: checks 01–02 exposed arithmetic/rewrite and fold
induction elaboration errors; check 03 and audit 04 accepted the original
literal theorem. After M1, check 05 required `Nat.le_min.mpr` (the theorem is
an iff), and check 06 required the implicit-argument form of `List.mem_cons_self`.
Check 07 and audit 08 accept the repaired frozen source. Failed logs were not
replaced by successful ones. Source now contains no proof holes or bypasses.

## Application and next owner obligations

This supplies the actual shared finite-use pullback map and its complete
structural substitution proof, rather than assuming a commuting square or
choosing separate witness extensions. Applying it to original native publication
still requires current canonical-row bounds, captured-local/non-generic guards,
reachable-high traversal, retained bound closure and all actual published roots
and clauses. NL1–NL7 and source scope are not discharged by copying a larger
store. Mutable type levels are not immutable Value birth levels.

Terminal recursive model construction, native trace correspondence, complete
Call/effect admission, source witness/environment realization, interleaved lets,
principal coverage and termination remain with the unchanged parent owners.
The regular-solution lane and original-certificate lane attack the next concrete
bridges independently. No production or full-inference gate is promoted here.

The primary's source and this receipt are now frozen for narrow delta review.
No checker remains running for this isolated project. Integration and Git are
primary-owned; independent review cannot certify its own construction.
