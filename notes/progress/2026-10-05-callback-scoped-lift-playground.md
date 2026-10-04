# Callback scoped total-lift playground

Date: 2026-10-05
Status: bounded executable characterization; no production authority
Review: one independent spec_auditor found no actionable findings.
Governing sources: [source-generated callback/structural theorems](../design/2026-10-04-source-generated-callback-structural-theorems.md)
§2.6 / Theorem C; [source-indexed callback realization](../design/2026-10-04-source-indexed-callback-realization.md)
§§1–2, 7; [production callback endpoint generation](../design/2026-10-04-production-callback-endpoint-generation-draft.md)
§3; [research-playground direction](../design/2026-10-04-inference-research-playgrounds.md).

[`tools/research_callback_scoped_lift.py`](../../tools/research_callback_scoped_lift.py)
models one fixed fiber and one typed observation with binary domains for a
captured old coordinate `s`, rigid challenge `kappa`, arm-local source witness
`z`, and checked fresh coordinate `w`. For each source relation
`R ⊆ S × Kappa × Z`, it checks the rule

```text
Original(s) = forall kappa. exists z. R(s,kappa,z)
Checked(s)  = forall kappa. exists z,w.
             R(s,kappa,z) and w = t(s,kappa,z)
```

where `t` ranges over every total binary map on the eight old tuples. It
exhausts all 256 relations and 256 maps, checking both possible `s` values:
65,536 relation/map pairs and 131,072 old-coordinate admission checks. All
73,728 admitted `(relation,map,s)` triples preserve old-tuple admission. This
is the finite consequence of a total fresh-coordinate extension while keeping
original quantifier scopes.

The model also searches for the smallest failures, ordered first by relation
row count, then relation mask, and then (where relevant) total-map mask and
captured assignment, for three scope mutations:

- **Freshening the captured coordinate per rigid challenge** has the minimum
  relation `{(0,1,0),(1,0,0)}`. No fixed `s` works for both challenges, while
  the mutant chooses a different `s` for each.
- **Hoisting the arm-local witness outside the rigid challenge** has the
  minimum relation `{(0,0,1),(0,1,0)}` at `s=0`. The source relation has a
  witness at each challenge, but no one `z` works for both.
- **Hoisting the checked coordinate despite its tuple dependency** has the
  minimum relation `{(0,0,0),(0,1,0)}` at `s=0`, with `t(0,0,0)=1` and
  `t(0,1,0)=0`. Per-challenge `w` preserves admission; one shared `w` does not.

The two-row minima are exhaustive over the stated finite domain; zero- or
one-row relations cannot cover both rigid challenges. These are counterexamples
to the mutations in this finite logical model, not source counterexamples.
The checker does not generate source constraints, complete Function endpoints,
execute endpoint comparisons, establish challenge-domain adequacy, or prove
production Theorem C conformance. Joint hiding across multiple segments and
arbitrary quantifier structures are also outside the model. The actual-side
production membership-factorization blocker therefore remains open.

Verification: `python3 tools/research_callback_scoped_lift.py` passed; Python
source compilation via `compile()` and `git diff --check` passed. No production
tests or compiler code were changed.
