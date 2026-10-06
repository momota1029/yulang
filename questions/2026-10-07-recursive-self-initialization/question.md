Question ID: `recursive-self-initialization`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `3209e890a0d3c6d96121f64339e9513905f54875`
Task/thread locator: unavailable; this questioning conversation has no exposed thread identifier
Governing source/section: `notes/theory/successor-proof-obligations.md` REC_INIT and RAW_SOURCE; `notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md` §§1, 5–8, 12; `notes/design/2026-10-02-source-result-synthesis-choice.md` §4; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§3–4, 6; `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` §§2–4, 16–17; approved nested-block source realization `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` clause 4 and `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` §§1–4; guarded closure construction `notes/progress/2026-10-06-recursive-source-validation-construction.md` §§2–3, 6; conditional first-read derivation `notes/progress/2026-10-09-rec-init-boundary-attack.md` §§1, 3–5

## Requested scoped decision

For the exact singleton recursive declaration

```yu
my f = f
```

should the successor's supported executable-source envelope include a first read of `f` while no actual provider value has yet been made available at that member? If included, select what the first unavailable self-read means. This question does not reopen the already selected F4 inference result or define other recursive initializer forms.

## Background and current premises

- Authoritative F4 specifies inference for admitted Integer/resolved-Name binding bodies. An unseeded self-use publishes `Never` within that inference scope; F4 expressly excludes Core IR and does not define a runtime provider or unavailable-read transition.
- Authoritative result synthesis gives `Synth(name f) = Gamma(f)` and `Result(Value(R_f)) = Comp(empty,R_f)`. This forms an interface and performs no execution or provider construction.
- The approved nested `apply/step` source decision covers one sequential local binding, return of `step`, lexical resolution and capture. Its approved scope excludes recursive local groups and does not choose top-level recursive initialization.
- REC-K constructs guarded immutable function closures. Its scope excludes bare alias initialization such as `my f = f`.
- Typed-core lookup/Return translation and preallocated code labels require initial relatedness; they do not establish that an actual value exists at the recursive member. The current conditional REC_INIT derivation proves finite first-publication impossibility only under its explicit candidate premises, not actual source behavior.
- No Frozen Oracle execution or output is used as semantic evidence.

## Options and consequences

1. **Exclude this source shape from the supported executable-source envelope.** Define a deterministic source/admissibility rejection before execution. F4 may still describe its inference result, but source adequacy and production execution need not claim that this candidate runs.
2. **Include it and report an initialization error on the first unavailable self-read.** Specify the error point and preserve the source identity for diagnostics. The inferred `Never` result remains separate from the runtime error.
3. **Include it and define the first unavailable self-read as nontermination.** Specify the operational observation for the unfinished initializer; this does not construct a value at `f`.
4. **Include it with a value-producing recursive initialization rule.** Specify the actual provider constructor and its progress/relatedness obligations; allocation identity or a final inferred scheme alone is insufficient.
5. **Another precise rule.** State source inclusion, first-read behavior and how the rule constructs or fails to construct the actual provider.

## Affected work

Blocked scope: selecting runtime/admissibility semantics for this exact recursive singleton, its source-adequacy proof, and any production implementation that must execute or reject it.

Independent authorized work: prove existing inference results, continue soundness/principality/source-adequacy work for settled clauses, and extend default-off structural/evidence shadow plumbing with unresolved premises.

Required answer: select one option or state a precise alternative for this exact shape. Do not infer the choice from F4's `Never`, code-label preallocation, typed-core Draft execution, or Frozen Oracle behavior.

Pending publication: keep this entire question directory unstaged and uncommitted until the questioning primary validates and integrates an explicitly approved local answer bundle.
