# Frozen Oracle Function derivation and typed-path attribution

Date: 2026-10-06
Status: frozen independently compiler-referee-reviewed bounded historical characterization; no findings
Yulang3 baseline: `deb5635ecc895a49b7f13d750374338003fd01e1`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1` at `/tmp/yulang2-oracle-rebuild`
Semantic and implementation authority: none
Method: read-only source correspondence trace; no Oracle execution

## Question and result

The current source producer still lacks
`OriginalAssocType_X(beta,p0,j_call;s0,c0)`: an original signature slot and
contribution must be associated with the source Call and typed position before
forward licensing or exhaustive inversion can be established. Earlier Frozen
Oracle archaeology found source boundaries, application constraints, and
post-solve occurrence provenance. This pass asks whether old Function
structural derivations bridge those records into a complete source-rooted type
path.

The historical chain preserves two distinct forms of evidence:

```text
source ApplicationArgument origin
  -> generated Function demand
  -> labelled structural child-constraint derivations
  -> explanation paths back to the root

projected generalized structure
  -> separately collected TypePositionPath witnesses
```

The first chain can retain origin reachability and labels for a selected
derivation. The second creates typed paths after projection. The inspected
code does not derive a complete source path by concatenating the first chain's
labels, and it does not form the current original slot/contribution judgment.
Oracle semantics remain historical evidence only.

## Governing authority and exact current frontier

The applicable source authority is [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, together with the [directional protection addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4 and [nested-block source realization](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3. These fix a source-formed shared contract, stable beta/slot identity,
typed source paths and one original jointly scoped relation; the exact
construction judgments remain open. The first missing judgment is localized
in the [Attach law construction attempt](2026-10-06-attach-law-construction-attempt.md)
§§3–5. No Oracle rule or output supplies a premise to those judgments.

## Historical chain

Paths below are relative to the frozen Oracle checkout.

1. **Source root and Function demand.** `lowering/expr/tail.rs:535–586`
   submits the callee endpoint against a four-port negative Function built
   from the actual argument value/effect and fresh result endpoints. The
   `ApplicationArgument` origin is supplied to this subtype request. The
   source boundary/origin is allocated before the call at
   `lowering/expr/tail.rs:630–685` and
   `constraints/machine/entry.rs:433–451`.
2. **Occurrence attachment is separate and post-submission.** After subtype
   submission, the lowerer looks up the admitted constraint record and
   registers it under the argument expression's `ExpressionExpected` role at
   the empty structural path (`tail.rs:564–586`,
   `analysis/session/occurrence_provenance.rs:38–67`). Roots can merge and
   deduplicate; absent roots make the entry incomplete. This is provenance
   association, not a typed source contribution.
3. **Function expansion emits labelled children.** The solver's Function
   comparison path emits separate argument, argument-effect, return-effect
   and return child constraints (`constraints/machine/propagate.rs:211–269`).
   The admitted child record retains `(parent, StructuralDerivationRule)`;
   canonical duplicate records accumulate derivations, while trivial
   canonicalization can return without a child record
   (`constraints/machine/entry.rs:1427–1507`).
4. **Explanation traverses to roots.** Explanation expansion exposes root
   origin edges and labelled structural parent edges
   (`constraints/explain.rs:1302–1331`); portable conversion retains Function
   labels and `ApplicationArgument` origin kind (`:1958–1985,2065–2083`).
   Under intact nontrivial records and sufficient explanation budget, a
   selected parent chain reaches its source root. Canonical fan-in, replay
   edges and multiple root origins do not establish a unique source-position
   inventory.
5. **Typed paths come from a different consumer.** The generalized witness
   collector walks projected type shapes and appends
   `GeneralizedTypePathStep`s (`generalize/provenance.rs:204–280,308–338`);
   occurrence export attaches those witnesses and paths to owner/role keys
   (`analysis/session/occurrence_provenance.rs:228–322`). The inspected
   collector does not reconstruct a complete source path from the explanation
   chain. It also skips root Function return/effect witnesses and explicitly
   marks whole-scheme completeness `Incomplete` (`generalize/provenance.rs:23–78,319–338`).

## Discriminator: a derivation label is not a path

One Function comparison suffices to distinguish the records. When the lower
Function's argument-effect port is `Neg::Bot`, the old solver emits an edge
labelled `FunctionArgumentEffect { pure_passthrough: true }` from the upper
argument-effect endpoint to a transformed upper return-effect endpoint
(`propagate.rs:234–245`; the target strips stack wrappers at `:401–410`). Thus
the derivation label describes which comparison branch ran; it does not by
itself assert that the child endpoint is the same structural position in both
parent types.

This is a representation-level branch witness, not an accepted-source
counterexample, an Oracle semantic theorem, or a current-language claim. It
rules out using structural labels alone as the missing source path
constructor.

## Correspondence limits

| Historical mechanism | Useful evidence | Still missing for the current source producer |
|---|---|---|
| Application origin on the Function demand | Source-root reachability for generated constraints | Original `beta`, `Slots(beta)`, contribution typing and source licensing |
| Structural Function derivation labels | Which solver child constraint came from a selected parent branch | A pre-query, complete typed path and occurrence-to-slot association; labels may reflect transformations or fan-in |
| Projected generalized path witness | A post-projection owner/role/path record with explicit partial completeness | Q-independent original profile formation and exhaustive source-incidence coverage |
| Explanation/certificate traversal | Conditional reverse attribution to retained historical roots | Both licensing directions on one original `(nu,K,D)` row, independent admission and source adequacy |

The current successor must retain source identity and typed-path obligations
before projection, with unresolved pieces as explicit premises until their
rules are derived. This Oracle chain can later serve as a historical audit of
attribution preservation; it cannot define those rules or weaken current
origin/guard, soundness, principality, or source-adequacy obligations.

## Scope, checks and limitations

Primary verification re-read the decisive numbered windows in
`propagate.rs`, `machine/entry.rs`, `explain.rs`, and `generalize/provenance.rs`.
Their SHA-256 values were respectively
`8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086`,
`00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8`,
`1138c38113654d1831d3b2e84362c05bbeba97a5f3d7186f4003f4747ec5d4e1`, and
`83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0`.
The frozen checkout HEAD matched the stated Oracle SHA. The current Yulang3
worktree was clean at the stated baseline when this pass began.

An independent compiler-referee reviewed the complete note, governing scope,
cited Oracle windows, and the derivation-label/path discriminator. No findings
remain in that scope. Repository-wide attribution alternatives, accepted-source
realization, and production conformance remain uninspected.

No Oracle execution, build, test, mutation, benchmark, compiler edit or Git
mutation occurred. This bounded trace does not inspect every Oracle
generalization or transport route and proves no repository-wide absence. It
does not establish accepted-source realization, a complete current profile,
admission, soundness, principality, source adequacy or production conformance.
