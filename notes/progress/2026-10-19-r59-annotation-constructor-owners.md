# R59 primary source-owner trace: negative Function-argument row

Session: `current-conversation-2026-10-19-r59`  
Contract: `tasks/agent-loop/sprints/negative-function-argument-row-20261019-r59.md`, revision 1, SHA-256 `155d8817f050566f4a51ccbb82dabb4c809bcabb82654fdce07a6fbaf867fdcc`  
Baseline: `2b92f53082e609989b69f22bcbc498a4a2bb089d`; 25/25 pinned dependencies MATCH.  
Parent: original computation-forwarding preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; original quantifiers and source domain unchanged; R50 NOT ADOPTED.

## Scope and source identities

The fixed source is the R58-approved constructor-level candidate. This is an owner trace, not a new parse/solve result. In HIR, `SourceAnnotation` retains a source-root owner and annotation position; each nested `SourceEffectRow` retains its own source position; each concrete atom is a resolved `SourceEffectId { module, declaration }`. The row spelling `io` is not its identity. The following three row occurrences must remain distinct even though they resolve to the same declaration:

| Position | Source role | Selected policy / required relation |
| --- | --- | --- |
| `t:[io] int` | Original formal Computation annotation; its incoming entry effect is `E` | Contravariant local subtraction permission for this formal position. Do not derive a closed input cap from the declaration. Keep ordinary generated constraints and symbolic dependencies on `E`. |
| Function argument `[io] int` in the whole-function annotation | Negative/contravariant Function argument position | Contravariant permission for this annotation position, with its own owner and row identity. It is not automatically the formal permission above. |
| Function result `[io] int` in the whole-function annotation | Positive/covariant Function result position | Concrete allowance at this result position. The allowance alone proves neither actual inflow nor a residual after subtraction. |

Authority for the meanings is annotation-effect-hygiene integration §§1, 1.1–1.2, 4–5. The formal-permission construction note is evidence for its named formal constructor only; it does not by itself implement a whole-Function ascription or identify the two different annotation rows.

## Current ordinary candidate path

`CandidateInference::solve` selects ordinary mode (`shadow_apply.rs:269–271,385`). Before collection or session creation it obtains each source root and calls `candidate_source::preflight` (`shadow_apply.rs:400–405`). Root annotation preflight starts at positive polarity; Function argument recursion flips polarity, so the whole-function argument row is checked as negative (`candidate_source.rs:459–460,603–615`). Any negative row with a concrete atom returns `Unsupported` there. This precedes source collection, `Action::Annotation`, native signature construction, slot admission and capture. R58 independently froze this exact implementation obstruction; it is not semantic incompatibility, a source-domain exclusion or evidence that an annotation is unreachable.

The native guard is independently present in `candidate_signature_effect`: negative variance plus a nonempty concrete row returns `Err(exhausted())` (`candidate_effect.rs:1934–1935`), which is `SolveAvailabilityError::IdentityExhausted` (`candidate_effect.rs:266–268`). This differs from the earlier `CandidateError::Unsupported` returned by source preflight. It corroborates the implementation boundary without claiming the same error owner. R59 has no authority to bypass either guard, and this report does not claim that the following native route executes.

If a future, separately authorized constructor made the row admissible, top-level source planning retains the original annotation and emits `Action::Annotation` after the body actions (`candidate_source.rs:1450–1468`). The action dispatches to `candidate_annotation`, then `candidate_annotation_pair` (`candidate_source.rs:1687–1694`; `candidate_effect.rs:1611–1698`). The native builder currently has these intended source slots:

- slot 40: body/source endpoint positive side is linked to the negative checking signature;
- slot 41: positive exposed signature is linked to the target definition's negative side;
- slot 42: the body's computation effect is checked against the root annotation row.

For the sample, the whole annotation has no explicit root effect row, so slot 42's helper returns without adding a root-row constraint. The nested argument and result rows instead enter through Function-port construction. The exact checking/exposed port equations and how the negative argument permission is represented are the construction question. They cannot be inferred merely from the slot numbers or from the fact that positive covariant rows can create `candidate_signature_view` records.

`candidate_signature_value` composes Function variance by flipping both value polarity and effect variance at each argument edge, while the result keeps both (`candidate_effect.rs:1780–1872`). For a positive root signature the argument row is therefore negative; the covariant result row remains positive. In the concrete result-row branch, `candidate_signature_effect` retains the resolved concrete `SourceEffectId`s and source row position in a view, carries an optional symbolic tail, and installs a polarity-directed bound (`candidate_effect.rs:1941–2004`, `849–890`). A symbolic variable is not erased when concrete members are collected. None of this proves actual effect inflow or subtraction residual.

## Formal entry and open incoming E

Lambda planning retains the formal annotation separately and emits `FormalEntry` (when it has an effect row) plus `FormalAnnotation` (`candidate_source.rs:997–1024`). `candidate_formal_entry_annotation` binds a symbolic tail to the native entry effect using an ordinary equality; its comment explicitly says concrete atoms are permission, not a closed upper bound (`candidate_effect.rs:1448–1462`). The formal annotation path records source owner/scope/path and a `FormalPermission` for supported negative concrete nested ports, then admits value links and stores that permission (`candidate_effect.rs:1330–1435,1464–1538`). For the sample's root Computation row `[io] int`, the existing formal-entry action leaves the generated entry effect open; it does not cap `E` to `{io}`.

That code path is source-position-specific. A derivation must still show what native constructor/consumer owns a permission declared on the original root Computation formal and how it remains distinct from the whole-function argument permission. A formal `FormalPermission` keyed by its parameter/path cannot be reused as proof of a permission constructed at the whole-function ascription's nested argument row.

## Capture and consumer boundary

On a successful future constructor prefix, the source schedule would finish before the enclosing definition graph is captured (`candidate_scheme.rs:1360–1435`). An incoming use then follows live root/use routing and capture/instantiation; `route_candidate_graph`, `freshen_candidate_graph_retained` and `prepare_candidate_fresh_use` establish distinct route/use maps and row freshening (`candidate_scheme.rs:1489–1608`). These are physical owners a complete constructor correspondence must name. The current source is rejected before reaching them, so no R59 evidence yet establishes this sample's `forward` capture, native FreshUse, mapped bound admission, later `outer` argument comparison, handler selection, subtraction, or residual.

The selected policy requires three distinct objects in the derivation: declared permission/interface, constraint-derived incoming effect, and residual after an actual handler. `Support`/`Allowance` views must be typed as one of these roles at every construction and comparison. Same family identity, equal row shape, or scalar endpoint equality alone cannot transfer a grant across the three source positions.

## Primary disposition and exact open seam

The current compiler boundary is exact and pre-collection. Source policy already selects contravariant permission and covariant allowance; this packet must not invent a new policy vote or choose an implementation representation. The proof/design lane has independently reported a candidate first missing coupled premise: same-position/provider transport from the exposed Function-argument row to the checking row (or another actual admitted path), together with source-owned permission transport. That claim remains a producer result pending independent review; it is not established by this source-owner trace.

At minimum, closure needs a reviewed polarity-indexed constructor judgment that supplies the checking and exposed Function ports, preserves all three HIR annotation positions/identities, keeps `E` open without discarding ordinary constraints, distinguishes permission/inflow/residual, and connects the permission to actual propagation/capture/FreshUse/admission owners. If current authority does not determine that relation, stop at that exact missing theorem/source premise. No code slice is authorized until this correspondence is reviewed.

No tests, parser, solver, compiler, build, runtime or probe was run. No implementation or production claim is made. Parent remains OPEN 0→0; A/B remain OPEN; R50 NOT ADOPTED.

## Assignment/resource receipt

Requested Luna/high source-owner lane: 500 seconds; requested/observed model and effort are not inferred beyond the session's requested role; actual elapsed/CPU/RSS UNKNOWN. Static source and authority inspection only. No descendants. This primary lane wrote only the two assigned R59 owner outputs; review and integration remain pending.
