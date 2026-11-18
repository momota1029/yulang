# Independent review: multi-owner observer/run/trace/source

Reviewed exact coordinator commit `755fc5a8d`; no reviewed code edits. This review excludes later source representative construction.

## Findings

No proof or scope defect found in the four target modules or their new helper dependencies. The remaining source integration premises are explicit, not disguised conclusions. The following distinctions are necessary in reports:

- `MultiObserver.completion` is the unvalidated finite settle theorem. It establishes closed-table terminality, not Ready or satisfiability. `MultiRun` validates every currently selected entry before selecting a write, including the terminal state. `MultiRun.outcome` promises success OR a precise validation failure, not unconditional validated success.
- The selection list determines obligation checking. Unselected plans are not checked; all selected plans are checked, even if their facts are already written or they would not be the next effective write. A historical plan selected from the versioned journal may fail current readiness. This is correctly documented in MultiSource.
- `MultiSource.selected` explicitly reads versioned `source.plans`, unlike `MultiSelection.registered`, which is a separate helper for the legacy centered state. The source theorem does not accidentally use the latter helper.
- Requests come from executable requests and are rewritten to actual `HeadOutputs.requests`. Owners distinguish invocation identity AND declaration identity. Distinct owner tags do not impose foreign-owner constraints; duplicate owners are allowed and merely weaken the list-length bound.
- The effective-write count is at most `owners.length * (pool.length + pool.length * pool.length)`. This is not a runtime bound, observer evaluation bound, bound on validation work, or bound on old-source Steps. Unknown/out-of-basis failure is excluded only under the explicit Closed premises derived from listed owners, LayoutCompatible, and actual request coverage.
- MultiTrace records exact `inspect before` plus the chosen owner/root/plan for each effective write. The history is chosen BEFORE `∀ assignment`, so the theorem provides simultaneous exact model semantics for one fixed history, not a model-dependent reconstruction. The resulting semantics conjoins each event's actual ClassEffects with prior finite Models. Final Ready is separately certified.
- Source formation produces owner/pool lists BEFORE quantification over all reachable snapshots. Thus the cover is common to the entire source future, not chosen independently per observation. Inspector functions still remain external inputs; successive observations need not be consecutive old-source Steps. This is finite rebasing, not old-kernel simulation or compiler completeness.
- `BaseCompatible` is a normalized-support premise, not ClassEffects iff itself. However sourcing it from full snapshot Models could assume output effects unnecessarily. The separately reviewed normalized worker now exposes `SourceCenters263.source_compatible_from_heads`, which only needs actual registered head-schema support and avoids assuming output ClassEffects.
- No theorem establishes satisfiability or model existence for arbitrary finite table states. Empty model sets do not invalidate the equivalence; reporting successful settlement as source acceptance would overclaim.

## Verification

`review/build.py` exports the exact reviewed 263 sources from Git into a separate temporary source tree and compiles new helper/target modules into a separate cache with `--trust=0 -DwarningAsError=true`. Already audited normalized modules and old dependencies are reused. `review/source-hashes.json` identifies all freshly built reviewed files. `Cycle263MultiIndependent.lean` imports only Yulang production code and prints axioms for major target/helper theorems.
