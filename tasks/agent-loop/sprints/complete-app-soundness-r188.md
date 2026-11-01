# R188 — direct App case of original inference soundness

Status: proposed for bounded admission by the primary. Goal remains the
mathematical type/effect inference guarantee for unchanged Yulang source rules;
Rust/runtime correctness is out of scope.

## Original parent and exact target

The parent is unchanged:
`YulangClosure.SourceProblem.InferenceSoundness`
(`notes/theory/lean/YulangClosure/Contracts.lean:128–130`):

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a.
```

Construct the unannotated App induction case at its original site and telescope:

```text
AppCase(s,x,q,f,arg,d,a,η) :=
  supported s → generates s x d → solves d a
  → legitimate IH_f(η) → legitimate IH_arg(η)
  → original App source clause(s,x,q,f,arg,η,a).
```

This is a direct case obligation, not permission to alter the parent, scope,
assignment, accepted source domain, or inference semantics. Written annotation
and conditional singleton-formal App paths must retain their original source
tests and clauses. State precisely how the case is folded back into the parent
induction; claiming this one case closes the whole parent is false.

## Method and hard constraints

Try the compositional App proof directly against the frozen R187 representation
and the exact original Call/IF authorities already authenticated in
`simple-sub-inference-soundness-r184-v4.md` and R187 v7. Use independent domains
uniformly where the authorities permit. Preserve one assignment `a`, one
original telescope, the same returned callable/provider, actual callee Bind,
all retained complete alternatives, dependent Call tuple, effect permissions,
source occurrence and child scopes.

The proof must provide concrete App generation and satisfaction meanings and
derive every original App clause. It cannot assume `C0`, complete admission,
an uninterpreted desired App predicate, source `Build` satisfaction, or the
conclusion. A new parameter is allowed only when it is an independently
declared original domain and every law used is derived from an already pinned
authority. A law whose ownership is merely cited but whose definition does
not supply it remains open.

Stop at the first exact missing equation if the direct derivation cannot
proceed. Report its type, exact already-pinned source locator and the premise
that needs it. Do not add source owners, widen the model, or emit another
conditional theorem. Failure is a formalization boundary in the inspected
inputs, not semantic underdetermination or impossibility.

## Required result and parent metric

Return one of:

1. **APP_CASE_DERIVED** — concrete generation/satisfaction and a derivation of
   every original App source clause from the same assignment, telescope and
   legitimate child IHs, with no extra semantic assumption. Show the exact App
   case expression applied inside the original parent. This discharges that
   induction case only; all other constructors, source coverage, principality
   and termination remain open.
2. **BLOCKED_AT_EXACT_LAW** — the first exact law/equation, why the direct case
   needs it, its original authority locator, and the exact result that cannot
   be derived. No parent premise is counted as removed.

Anything conditional on the missing law is not outcome 1. Progress metric is
the exact App case obligation discharged or the exact missing law identified;
theorem/lemma counts are not a metric.

## Exact outputs and limits

- `notes/theory/2026-11-02-complete-app-soundness-r188.md`
- `tasks/agent-loop/inbox/complete-app-soundness-r188-proof.md`
- Proof owner: fresh `prover`, 1800 seconds.
- Fresh independent `spec_auditor`: 600 seconds.
- Total grant: 2400 seconds; one CPU; no extra budget or further admission.
- No Lean/Lake/checker, build, test, Rust, Cargo, environment, cache or scratch.
- No additional owner pins. Read only frozen R187 artifacts and the exact
  already authenticated direct mathematical inputs in R184 v4/R187 v7 needed
  for this App case. Authenticate hashes before content reads. Do not open
  linked proof-producer bodies outside that set.

The independent review must check exact parent correspondence, source-rule
preservation, assignment/telescope identity, full Call dependency, whether
each used operator law is actually defined by the admitted authorities, and
honest parent-premise accounting. A review cannot promote a blocked result.
