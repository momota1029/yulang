# Parent-theorem dependency reconstruction — 2026-11-02, revision 2

Status: reviewed research map and replan; not a proof, semantic adoption, or
closure receipt. The user identified that repeated local proof packets had not
closed the original soundness, principality or termination targets, and asked
to rebuild the proof path backward from those targets. This update preserves
the earlier map and records what R184–R190 changed.

## Original roots and measured status

The authenticated Lean contract is `YulangClosure.SourceProblem` in
`notes/theory/lean/YulangClosure/Contracts.lean` (SHA-256
`2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`). The
record is abstract: its declarations are propositions over fields, not an
instance of the Yulang algorithm.

| Root | Original obligation | Status |
|---|---|---|
| `InferenceSoundness` (`:128–130`) | Every supported source, actual generated problem and satisfying assignment yields an original source derivation and `sameScoped` for that same assignment. | OPEN |
| `SourceScopedCoverage` (`:133–135`) | Every original derivation and generated problem has a satisfying assignment preserving its scoped witness. | OPEN |
| `PrincipalCoverage` (`:138–144`) | One principal solution factors every original source derivation through the original `instanceOf` ordering. | OPEN |
| `InferenceTermination` (`:152–154`) | The actual inference transition relation is accessible from each supported initial state. | OPEN |

Native correspondence (`:147–149`) is a later implementation bridge. Program
evaluation termination is not the termination claim. **Parent-root delta in
the inspected R184–R190 outcomes: zero closures and zero refutations.** This is
the honest metric; no exhaustive audit of every earlier R1–R183 artifact is
claimed here. The stable root count is four. A defensible count of all leaf
premises is not yet available because the concrete semantic instance and its
interfaces remain incomplete.

## Backward dependency graph

```text
INFERENCESOUNDNESS
  original source judgment + one shared scoped witness
    ← source-rule induction / reconstruction of complete Build satisfaction
      under the same assignment and telescope
        ← actual generation equations + independent type/effect denotation
          ← concrete mathematical Simple-sub model

SOURCESCOPEDCOVERAGE
  source derivation + actual generated constraint object
    → construct a solving assignment preserving that derivation's scope

PRINCIPALCOVERAGE
  source-scoped coverage
    + source-derived joint strategy across qualifying uses/copies
    + original instance ordering and universal factorization
    → one principal solving assignment for all source derivations

INFERENCETERMINATION
  supported initial states + the actual inference transition relation
    → one well-founded measure covering allocation, callbacks, propagation,
      extrusion, intrusion, repropagation, generalization and continuations

Only after the mathematical algorithm is fixed:
  Rust generation / propagation / solving simulation → implementation bridge
```

The first shared blocker is not a Rust implementation fact. The formal
`SourceProblem` still lacks a canonical, independently defined Yulang
interpretation for its `generates`, `solves` and `sameScoped` fields that is
connected to the accepted source rules. The structural Simple-sub lemmas apply
once their structural hypotheses are supplied; they do not supply this model
or the generation-to-source implication.

Soundness and principality are different directions. The soundness implication
quantifies over every satisfying assignment and returns a source derivation
using that very assignment. Coverage constructs a solution from an existing
source derivation. Principality additionally needs the original ordering and a
single universal factorization. Termination is independent and concerns the
real inference transitions. Call and contextual effects stay inside the
abstract source theorem wherever the accepted rules use them; postponing them
must not narrow the source domain.

## What the recent results actually establish

- R184 (`simple-sub-inference-soundness-r184-v4`): existing structural graph,
  constraint-history and store-satisfaction soundness results are reusable
  components. Its original App existential still needs an admitted candidate
  plus descriptor formation, whole-argument compatibility, complete Call,
  source-call incidence and callable-image clauses. It did not establish the
  source-side denotation or instantiate the original parent.
- R186: incomplete canonical model; no parent premises discharged.
- R187: independently reviewed as an accurate incomplete checkpoint. It
  lacked a complete Call domain, phase/world binding, admission and observation
  interpretation. No parent premises discharged.
- R188–R189: narrowed App to the single solver-selected ViewLogic witness,
  correctly avoiding universal admission over the whole domain. R189 located
  the first unresolved equation at the independent meaning of
  `descriptorFormation`. Review accepted the blocked report, not an App proof.
  Zero App sub-obligations and zero parent premises were closed.
- R190: no outcome artifact exists. `current.json` records contract SHA
  `7911b3d202641682...` and activation SHA `5156f04ee7070740...`; the current
  files hash to `9d498efdb86e161f...` and `1daae541e79ee062...` respectively.
  The references therefore do not authenticate the active packet. R190 is
  superseded here without claiming that either referenced revision was proved
  authoritative. Its App-formation issue remains an unresolved leaf.

The bounded original source-paper read (SHA-256
`2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`, §§ on
source generation and App) confirms that App uses a complete Function
derivation, the argument derivation and direct boundaries, and passes the
delayed argument into complete Call. This fixes source-rule shape. It does not
by itself define the independent interpretation of the Lean `Kernel.atom`
`.descriptorFormation` predicate or prove that generated constraints supply
the required admission. No semantic ambiguity is established by that gap.

## Next proof strategy

1. Fix the abstract mathematical objects from the accepted source and
   Simple-sub definitions: constraint grammar, independent type/effect
   denotation, actual source-directed generator, solution relation and the
   scoped shared-witness relation. Do not define solving as source typing,
   define an atom by `Kernel.atom`, or hide the same bridge in an assumed law.
2. Prove the direct structural soundness implication by induction over the
   original source rules, including App/Call/effects from the start where they
   occur. The success criterion is an application that removes the named
   generation/solution-to-source edge in `InferenceSoundness`, not a
   conditional constructor lemma.
3. Track reverse coverage and principality as separate roots, with the original
   instance order and the birth-level joint-use obligations. Track
   termination against the exact algorithm transition relation, not an
   unrestricted structural transformation relation.
4. Only after those mathematical objects and the relevant theorem are fixed,
   prove Rust simulation against them. No Rust investigation is a substitute
   for the mathematical model.

The immediate next construction is a concrete canonical mathematical
`SourceProblem` instance (or a reviewed exact obstruction to defining one from
the accepted authorities), not another assumed App admission proof. The
adversarial check is whether each field is independently defined from accepted
semantics and whether the resulting induction has any premise not derived from
the actual generator/solver. A missing definition is not a counterexample and
does not authorize changing the source language.

## Review boundary and limits

Independent review must reject a changed quantifier/domain, a denotation defined
by desired typing success, a hidden admission or termination assumption, a
conflation of soundness with coverage/principality, or a next packet whose
conclusion cannot remove a named root edge. This report closes no theorem and
does not select new semantics. It supersedes the R190 standalone dispatch only
because the active references are inconsistent and the user directed the
research back to the parent; the exact R190 App gap remains recorded above.
