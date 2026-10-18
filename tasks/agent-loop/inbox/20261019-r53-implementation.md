# R53 implementation/source-audit handoff

Status: static ordinary-route source map only. No implementation slice or runtime evidence. Parent remains OPEN 0→0; R50 remains NOT ADOPTED.

## Finding

`CandidateInference::solve` selects `solve_mode(hir, false, false)`. The recursive initializer's active self-reference is lowered as `Action::Link`; `used`'s reference to installed `forward` is lowered as `Action::Local`. The Apply builder omits scoped-only local-callee analysis in ordinary mode but retains its recipe, source input and `Action::Candidate`. At admission, occurrence/endpoint consistency checks remain, while `authenticate_scoped_apply` is guarded by `scoped_experiment` and therefore does not block ordinary solve.

The ordinary Apply owner constructs and retains its native negative Function demand and admits the typed value constraint. Candidate graph mode dispatches typed Function work through `candidate_apply_value`; qualified extrusion groups use retained Apply source-event evidence. The later loop-local consumer captures the current live scheme and prepares an authentic ordinary FreshUse map. In the bounded trace, successful settlement leaves `q(t),q(n),q(r),q(v)` at level 2 and generic; the loop boundary-1 capture reaches the retained `L₂ → D₂ → A₂ → P₂` chain and argument-side `X₂ → P₂` through one graph/map. This statically supplies the same-lineage scalar chain across this concrete capture, conditional on the successful ordinary constructor prefix and settlement.

## Boundary

This audit does not claim successful complete solve or the later top-level `outer` capture. The proof artifact owns the physical BoundKeys and signed extrusion lineage; its independent review remains required. No general post-merge invariant follows from this one concrete route. Original forwarding-preservation quantifiers, source domain and expected outputs remain unchanged.

See `notes/progress/2026-10-19-r53-ordinary-source-native.md` for the owner-level path. Read-only source inspection only; no code changes, tests, builds, runtime, probes, measurements or Git operations. Primary integration/review remains pending.
