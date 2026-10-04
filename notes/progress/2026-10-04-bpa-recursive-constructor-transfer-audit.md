# BPA recursive-constructor reduction transfer audit

Date: 2026-10-04
Status: scoped literature-transfer result; no language or solver authority
Scope: whether the guarded-BPA structural-subtyping reduction applies to the
current finite regular structural-constraint package
Authority: none
Primary source: DeYoung, Mordido, Pfenning, and Das, “Parametric Subtyping for
Structural Parametric Polymorphism,” POPL 2024, §2.3,
<https://doi.org/10.1145/3632932>

## Result

The paper's undecidability theorem does not establish undecidability of
Yulang's current regular-completion gate. Its reduction requires a family of
recursive type constructors `t_X[α]`, with a type argument substituted through
the recursive definition. The current normalized Yulang structural package
has finite constructor descriptors and free roots, but no type-constructor
parameter or operation applying one descriptor family to an arbitrary type.
The paper also interprets subtyping as one coinductive structural relation and
allows non-regular recursive type behavior; neither fact can be silently
identified with Yulang's endpoint-dependent concrete comparison solver and
regular-witness question.

This precisely explains why that reduction cannot be cited as a Yulang
obstruction under current authority. It does not prove that no other reduction
exists, and it does not prove regular completion.

## Exact feature mismatch

The reduction encodes a guarded BPA process variable `X` by a recursive
constructor `t_X[α]`. A process stack `X·p` is translated by recursively
applying `t_X` to the translated continuation. Thus one finite definition
denotes a transformation on arbitrary argument types. The subtyping proof
uses this uniformity for the family of premises `κ <: κ'` and corresponding
comparisons between transformed arguments. Repeated transitions can change
the argument at every recursive constructor occurrence; the paper explicitly
discusses why the resulting derivation need not have a finite circular proof.

In the current Yulang structural package:

- the input is a finite descriptor graph whose constructor children are fixed
  graph references;
- a free class is assigned one regular type root in the same structural
  domain;
- recursive descriptor edges preserve their child references, and do not
  receive a fresh type argument at each unfolding; and
- each directed bound keeps its own identity and is checked directly. Success
  of separate concrete comparisons is not closed under transitive
  composition.

A fixed descriptor graph can represent one recursive regular type, including
open children. It does not by itself represent the higher-order mapping
`α ↦ t_X[α]` uniformly for all `α`. Copying a descriptor for finitely many
arguments would not implement the reduction's unbounded stack of changing
arguments. Adding such constructor families would be a language/constraint
extension, not an interpretation already entailed by the current package.

The reduction's central gadget uses Records, so the fact that Yulang's general
concrete comparison may involve non-transitive casts/adaptations is an
additional transfer obligation. Even if a mandatory-Record-only subrelation
were shown to coincide with the paper's structural rules, the missing
parameterized recursive-constructor operation would still have to be supplied.

## Boundary

This audit rules out only the direct transfer of the cited BPA theorem to the
current finite regular package. It does not rule out an encoding using the
existing prefix-shifted descriptor equations and suffix-descent comparisons;
the previously tested fixed-anchor, marker, and active-pair gadgets remain
only scoped failures. It also does not turn absence of recursive constructor
families into a sufficient condition for regular completion. The exact open
gate remains whether every satisfiable current normalized package has a
regular witness, or whether a counterexample/reduction exists within that
package.

No code, tests, source contract, or semantic authority changed.
