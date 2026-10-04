# Callback checked-admission hiding playground

Date: 2026-10-05
Status: bounded executable characterization of the reviewed §4.1 lemma
Review: one independent spec_auditor found no findings.
Governing theorem: [certified callback transport and finite constrained uses](../design/2026-10-04-certified-callback-and-constrained-use.md)
§4.1; [research-playground direction](../design/2026-10-04-inference-research-playgrounds.md).

[`tools/research_callback_admission_hiding.py`](../../tools/research_callback_admission_hiding.py)
exhausts the two-witness, one-challenge, one-observation Boolean model. For
each pair of actual/checked domains and bounds it checks the fixed-fiber
condition. There are 256 encodings; 121 satisfy the fixed-fiber condition.
Among those, all 73 cases with checked admission uniform across both forgotten
witnesses satisfy projected domain and bound inclusion.

When uniformity is omitted, exhaustive shrinking by active domain-membership
count, active observation count, and encoding order finds a minimum failure
with cost `(3,1)`:

```text
DA(z0)=DA(z1)={h}       DC(z0)=empty, DC(z1)={h}
PA(z0,h)={o}            PA(z1,h)=empty
PC(z0,h)=undefined       PC(z1,h)=empty
```

Each fixed-fiber comparison holds. After existential projection, the checked
domain contains `h` by witness `z1`, but the actual projected bound also
contains `o` from `z0`; the checked projected bound is empty. This is a
minimal finite counterexample to dropping the admission-uniformity premise in
general. It is not a Yulang source counterexample and does not show that the
premise is necessary for every particular presentation.

The experiment characterizes the exact hiding step in §4.1 only. It neither
derives the theorem's certificates from production generation nor closes
actual-side membership factorization, endpoint denotation, callback
adequacy, or principality.

Verification: `python3 tools/research_callback_admission_hiding.py` passed;
Python source compilation via `compile()` and `git diff --check` passed. The
independent spec_auditor review covered the finite model and its theorem match.
