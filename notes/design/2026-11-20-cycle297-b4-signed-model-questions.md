# I-54: exact finite model questions at one B4 source state

Start from Lean registry, root, mixed-journal state, generated occurrences
and the existing candidate scan, not Rust or parsed text. Keep the mixed
kernel and the projections unchanged. For each existing candidate plan p,
let F(p,m) be actual versioned plan Holds and current ClassEffects
together. Use two tagged questions on prior Models: **pass** F(p,m) and
**reject** F(p,m). The joint witness must be one assignment; novelty is the
other polarity, and recorded edges are still handled by the existing
structural novelty gate. The theorem for interpreting these questions
uses actual source reachability and a registry/current-snapshot effect
where needed. Raw loss and the opposite query are not identified without
that bridge; in particular do not replace full assignments by a public port
projection.

Intended propositions:
1. For any prior state, plan and model, reject is the exact counterexample
   predicate for semantic non-commitment. For a reached current effect,
   pass is exactly Residual, with no condition on the existence of a
   distinct second witness.
2. For any fixed state, enumerate both signs for every plan produced by
   the existing finite generated-occurrence and ready-plan enumerators.
   There exists a list of at most one assignment per question reflecting
   the two questions on every enumerated plan. Produce it by classical
   selection, not by claiming a constructive solver for arbitrary models.
   Expose the executable row/sign reduction when checked Boolean answers
   for those models are supplied. Represent missing query coverage as
   outside the theorem, not proof of a negative answer.
3. Substitute these replies for the two install guard callbacks in the
   existing observer. Keep head/metadata, diagnostic and merge contracts
   visible; do not supply them by circular invocation of observer
   completeness. Verify conditional strict step equivalence from each
   reached representative. Local finite support does not give a fixed
   across-path rank, a bounded model universe, or B4 termination.

Controls: real 229/233 no-missing-edge install (semantic novelty cannot be
omitted), actual 271 nested output, 239/240 raw windows and the distinction
between one observation problem and the unbounded history. Check an
unsatisfiable base separately: neither sign has a witness there. No
specification or Rust receiver behavior is decided here.
