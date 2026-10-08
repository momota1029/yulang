# Native projection boundary decision: proof, review and executable arithmetic

Date: 2026-10-08
Status: independently reviewed mathematical result and bounded reference implementation
Branch: `research/simple-sub-intrusion`
JOINT_DEC: OPEN-PROOF; no aggregate status or production cutover change

## 1. Accepted result

[SD-NPB](../theory/2026-10-08-source-directed-joint-decision.md) is a complete
termination, soundness and satisfiable-strategy completeness theorem for the
exact **native projection boundary judgment** in its section 3. It constructs
source-owned argument contracts and Car evidence, solves the shared description
choices, and emits an original-scoped strategy and actual ordinary checking
proofs. It takes no satisfying strategy, unknown J/Car supplier, submitted
inclusion proof, EPR/ER package or semantic classifier as a solver premise.

The complete enclosing source Call judgment is outside this theorem. Its
CallMem/C0, callee prelude, source Call consumer and suffix are separate owners.
The algorithm returns OUTSIDE-NPB for a full Build input containing those
owners; it does not silently omit their clauses from a purported full-source
decision. All clauses of the **included local judgments** remain present.

The mathematical construction was preserved independently in commit
`2590b3d07a80c97c6ae8816a558cdeabaab37b40`. Before it, the reviewed
[ObservedPayload obstruction](../theory/2026-10-08-joint-decision-source-fragment-obstruction.md)
was preserved in `a3f90c0200c31d6fe6a7f428a261dead71c72ff3`: an actual Bool
challenge refutes identity at the complete Any-input/Int-result Function
boundary despite a successful observed Int call. It refutes that specific
sampling method, not all direct solvers or EPR/ER.

## 2. Exact decision and mathematical content

Written data endpoints are finite positive Unit/Bool/Int/Any, mandatory records
and unions. The source data graph is acyclic and tight before one optional
initial widening. Checked data cannot be reannotated, projected or inserted
into later records in this envelope. Pick captures have tight ground/record
shape, with their actual provider and free dependencies fixed. New descriptions
are initially unsolved; existing frozen descriptions and proof choices are
outside the algorithm's input.

Each real frame has at least one checked-inlet boundary. All its aliases
contribute their final declared argument endpoints S_j to one union L_i.
The included Function view retains that frame's complete inlet/IF and changes
its result to a written T. It is not a post-Call annotation of a particular
returned value, a changed-input Function view or a chained target-to-target
check.

The exact elimination conditions are:

```text
id:    L_i = union of all S_j routed to frame i;
       every whole-result view requires Inc(L_i,T) = YES.

pick:  use the same L_i for input admission;
       every whole-result view requires Inc(B_capture,T) = YES.
```

The algorithm selects a_i=L_i once above the independent challenge binders.
Distinct real new frames select separately; monomorphic aliases reuse one
choice. It constructs all actual mu and whole-image Delta fields, the complete
generic receiver introduction and whole Function/Value proof terms.

The proof has three new completed parts:

1. **Finite structural inclusion decision.** DNF distributes every record
   field union. Every source atom must be included in some target atom.
   Positive cases construct native checking terms; an exact-field characteristic
   value refutes every target atom when the test fails. The written normal-form
   size is bounded by 2^n, with a computable finite proof/search bound.
2. **Exact joint elimination.** Any original solution, even with a outside
   the written finite grammar or with noncanonical proofs, must satisfy the
   conditions above. For id, a failed condition produces a licensed complete-J
   alternative at the original carrier/world; Echo puts that same result
   outside the whole target. For pick, necessity uses the actual tight capture.
   Conversely the finite lower union and generated proof terms satisfy them.
3. **Source-owned strategy construction.** DataArg is an identity assembly
   of the original registered complete Comp view fields; actual Car evidence
   is separately built from source data, immutable projections and Return.
   Generic id/pick introduction eliminates the universally bound complete
   gamma and constructs each phase/future branch. It does not consume Joint-ID
   with an assumed winning strategy. All original shared operands and proof
   intermediates remain at their own binders.

The source and public checking meanings still include all independent
admission and licensed production alternatives. A source carrier returning
0 at a declared Any payload retains its complete Any contract, including
nonactual results. The generated proof chooses one valid witness; it neither
identifies the other witnesses with it nor removes them from the relation.
An active additional W is outside NPB, not silently erased.

## 3. Independent mathematical and specification review

The producer froze the theorem at SHA-256
`81fea7804f6e78018049655549dbf516fe9cb1bf73b9f088b8364239ea3c10ae`.
The isolated `joint_boundary_math_review` compiler referee and
`joint_boundary_spec_review` auditor inspected the target and its original
semantic dependencies independently. Both returned PASS with no BLOCKING or
major finding. The specification reviewer had no minor finding.

The mathematical review identified one minor presentation seam: the standalone
structural characteristic value was described in an empty test world, while
the joint negative needs it in the fixed original world. The primary made the
existing construction explicit. Ground/record constructor facts work in that
world; Any leaves use the already present native id receiver and its hereditary
Top evidence. No new registration, different world or replacement prefix is
needed. The mathematical delta review passed
`ed03446648ee182579c3b2e7af2691ef83e240558d33f2ea31add2b9195f0b35` and confirmed
that no strengthened premise was introduced. The committed artifact, including
acceptance metadata, has SHA-256
`522e853bff5592f692cc8709eb710e64c6dba060bdfa5836c5bee385ef3ed1ad`.

Reviews specifically checked complete DataArg assembly versus actual Car,
same-prefix negative construction, arbitrary original a, tight capture
necessity, original binder/new/alias ownership, complete Function future-hole
proofs, independent Option 2 alternatives and the source-boundary/whole-Call
distinction. No full compiler or foreign-model correspondence was certified.

The nineteen-path review manifest retained fourteen semantic/theory/owner
files and four policy files byte-for-byte at the original proof baseline
`50d889a2d5f297bc20efef9e094db087adc3de34`. Only the historical joint-dec
review/status record advanced. The primary fetched and inspected subsequent
remote changes through `75ab4ab8c7e5b11ee02ce202e9c59337f2c74e0a`; they added
conditional research/navigation, not changed semantic premises. The theorem
checkpoint was pushed on top of that latest remote.

## 4. Reference implementation and independent code review

[research_source_joint_boundary.py](../../tools/research_source_joint_boundary.py)
implements **only the finite endpoint and frame-alias arithmetic** of theorem
sections 4–5. Inputs are explicit endpoint/frame/handle records. Outputs are
assignments, finite structural proof schemas or characteristic countervalues.
It does not implement source data emission, DataArg/J/Car/world objects, the
full symbolic strategy, complete Function semantics or enclosing CallMem/C0.
Its output includes `scope: finite-boundary-arithmetic`.

It validates the entire input before checking any constraint. Unknown fields,
proof flags, duplicate JSON keys, post-Call views, fixed prior A, missing
lower bounds and non-tight pick captures return UNSUPPORTED. They cannot be
hidden behind an earlier UNSAT result. The explicit boundary marker is
`same-inlet-function-result`; source allocation authenticity remains the
separate constructor theorem, not a fact inferred from user-provided keys.

The code producer froze SHA-256
`31abf8f0166a9f94325af379d1b776b713ee0eff35f8d856e55abd6d07d08fd2`.
Independent `joint_boundary_code_review` and the separate specification auditor
both passed its finite arithmetic and exact claims. The code review found one
minor output-depth error: a nested proof result could solve successfully and
then raise RecursionError during JSON serialization outside the output guard.
The primary added `serialize_result`, which finishes serialization before
printing and returns a shallow UNSUPPORTED object if output depth is exhausted.
The independent code delta review passed the repaired SHA-256
`1ab257ca6592ea61561240fe12f8f55b81a3d1490b342a1956cff606de5c0f33`.
No arithmetic or input-envelope rule changed in that repair.

The primary also made the sample loop evaluate its whole reported grid before
aggregating each pair, so negative pairs no longer short-circuit the reported
implication count. The independent final static delta review passed artifact
SHA-256 `edad872b0a7368862da23bcef3bf97111fa1778c09cd5637a3df74695c9017e9`.
The arithmetic and output-depth verdicts carry forward unchanged.

## 5. Focused verification

The final primary verification ran one Python process with a 30-second timeout
and 256 MiB address-space limit. It exercised the self-test and the reviewer's
actual depth-360 accepted-input/output reproduction.

| Check | Final result |
| --- | --- |
| Boundary/input/output scenarios | 30 passed |
| Inclusion pairs | 400 passed |
| Returned countervalues checked against original types | 301 passed |
| Separately constructed sample values | 84 |
| Bounded sample membership implications | 33,600 checked |
| Original depth-360 output failure | Complete UNSUPPORTED output, no partial publication |
| Process status | Exit 0 |
| Elapsed time / maximum RSS | 0.223050 seconds / 18,464 KiB |

The countervalue evaluator uses original types without calling DNF or
inclusion. These finite checks catch implementation mistakes; mathematical
completeness comes from the theorem, not from the sample universe. The
initial producer separately ran the 29-scenario version, and the independent
code referee used one targeted bounded process to locate the output-depth
issue. No Cargo, broad compiler tests or production acceptance measurements
were run. The reference remains subject to Python depth and finite resources;
no practical production RESOURCE policy is selected.

Reproduce the ordinary bounded suite with:

```sh
python3 -B tools/research_source_joint_boundary.py --self-test
```

## 6. Exact gate and production consequence

For NPB, the unknown source J/Car/gamma supplier, supplied joint strategy,
unbounded inclusion-proof search and joint alias-choice gaps are discharged
by actual constructors and a total finite decision. This route does not need
EPR inhabited-cell reflection or ER challenge classification/replay. It proves
no general EPR/ER construction or impossibility theorem for that alternative.

**General JOINT_DEC remains OPEN-PROOF.** The theorem is not full enclosing
Build/Call decision, arbitrary frozen-prefix solving, all required source
refinement completeness, general recursive/effect/method/State inference or
production conformance. Its input limits are not a language rejection policy.
Canonical aggregate prerequisites and production relevance remain unchanged.

The immediate missing complete-Call constructor law is concrete: each original
anchored or unanchored production arm needs its actual relation and an
output-dependent whole typed-state/descriptor/guarantee proof at the source
Call consumer, with same-provider admission and complete continuation/future
actions at the original callee/argument/world/port/xi telescope. Receiver VP
membership proves none of this for a separately owned arm. Naming this C0,
or assuming every arm is well typed, does not discharge it.

Production still needs effective complete rules for every actually required
source case, completed-contract/profile principality and actual-public-export
factorization, source-to-compiler/independent-production correspondence, and
the freshening/rebuild/resource/atomic-publication lifecycle with Oracle
evidence and concrete rollout approval. These are A/B and engineering
conditions. Encoding every arbitrary semantic strategy, requiring source
executions for production-only alternatives, or equating the independent
world domain with another generated-world relation are not newly imposed
production requirements. The existing proof-economy architecture retains
the exact consumer obligations for any alternative route.
