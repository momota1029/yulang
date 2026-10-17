# Sprint closeout: accepted-call-vertical

Contract: `minimal-cut-and-accepted-source-vertical-20261017`, revision 2,
SHA-256 `95f0f1a3751ffa276c89bedd48d969b430b34771db3f528dbf7473c92a036acf`.

## Parent application

Original unresolved premises genuinely discharged: **0**. The reviewed Astra
source/native contribution and the regression attempt leave the original A/B,
Call, FIRST-RESULT-ADEQUACY, N-Transport, soundness, principality and termination
gates open.

## Implementation evidence

The exact source `my id x = x; my apply f = f 1; my answer = apply id` had no
structural parser recovery. The only authorized test invocation compiled its
target and failed the required zero-HIR-error assertion at line 36 (exit 101,
7.8 seconds) before `CandidateInference::solve`. No solver, propagation, export,
FreshUse, or call-record behavior was exercised. There was no retry, example
execution, or formatter/CI check. Handoff revision 3 corrects an inaccurate
statement that had described intended downstream assertions as established.

## Review and budget

The independent post-run regression review confirmed the hashes, scope and exact
failure boundary. Its one low-severity reporting finding was fixed in the frozen
handoff; code and run receipt are unchanged. Prior Astra/compiler/spec reviews
were clean within their bounded claims. Total charged sprint time: 2280/2400s;
the remaining 120s closeout reserve was retired. Three inherited unknown leases
remain quarantined.

## Next single cut

Establish an authority-qualified structural source-Call to HIR projection and
admission contract applicable to the exact failed source, or identify the exact
HIR admission decision needed before a compiler edit. Structural HIR retention
must remain distinct from semantic Call typing. No original Call theorem or
source T premise is inferred from this step.
