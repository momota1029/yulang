# Yulang cycle261 — recovered final report

## Recovery and publication

Cycle began 2026-11-18T17:30:08Z. Its last remote heartbeat was running at
18:09:58Z; no final report existed when cycle262 checked at18:35UTC.
The last mathematical checkpoint was `3bb7d7734021ac8db05b0aba695d156742ab2a98`.
The retained local committed tree `48a643bc0` exactly matched that remote tree.
No unfinished Lean source was found. Three final notes were untracked and recovered.
Cycle262 reran all six standalone audits and the kernel probe at18:37–18:38UTC,
all exit0. This report is a recovery report, not a claim that cycle261 finished normally.
The original final-stage logs show verification at18:14–18:15UTC; its exact end time
and reason for interruption are unknown. Usage budget: unknown.

## Results and exact scope

22 new modules,200 explicit theorem/def/abbrev declarations,316 including generated
and private declarations;10 usage examples. See
`notes/verification/cycle261/declaration-guide.md` for quantified Japanese claims
and `alltypes-final.txt` for complete Lean signatures.

- BodyTable/ClassTable/ClassCheck/ClassRun: arbitrary fixed request lists compile
  body equations plus EqualOutputs into a finite table; checked readiness rejects
  missing/unknown bodies. This is auxiliary finite rebase semantics, not whole M1.
- MergeRequests/Meaning/Run/Frame/Packet/History: actual two-request alias fixture;
  retained historical parent output makes the full model unsatisfiable while a raw-only
  model exists. Good is needed for raw correctness; Good+Supported for Frame/leaf
  Evidence. The history result preserves the same assignment. Both bodies require Int,
  so EqualOutputs alone is not the cause. This is a scoped soundness/completeness bridge.
- PairKeys/StableBody/StableClass/CandidateDriver/Validation/Trace: pair keys are stable
  under list position/subset changes. Under explicit request coverage, each successful
  write has exactly old models conjoined with the selected effects. Successful traces
  preserve all historical effects. Completion does not assert satisfiability or Ready.
- MergeObservation/StableMerge/Driver/Finish: fixed-plan to actual observed-plan bridge
  for the Int-body family; Good/Supported/raw premises remain. Actual finite execution
  terminates in at most one nontrivial write for the six-fact fixture. Final unsatisfiable
  histories are allowed. Not a general packet compiler.
- SourceSnapshot: the current source's actual finite site outputs automatically cover
  requests for every root, avoiding an extra request-coverage premise for that fixed
  snapshot. Root selection may depend on rebase state; source and Plan remain fixed.
  Each successful step has exact current-snapshot ClassEffects. Alias selection remains
  noncomputable. No global trace-wide fixed basis is proved.
- SourcePool: merge/refresh preserve candidate lists. Installation preserves candidate
  membership under the existing Absorbed premise. That premise is not proved for
  arbitrary new children or new public output targets. Multiplicities may grow.

These are auxiliary and conditional soundness/completeness results. They do not prove
M1's language-wide soundness, completeness, principal types or general termination.

## Verification

`python3 notes/verification/cycle261/rebuild-final-critical.py`: PASS,26 freshly
rebuilt critical modules, unchanged earlier dependency artifacts reused after source
hash checking (1793 source files). This is not a clean repository build.
`python3 notes/verification/cycle261/run-final-audits.py`: PASS, six independent
`lake env lean --trust=0 -DwarningAsError=true Audit/Cycle261*.lean` invocations
and CandidateBoundaryProbe. Recovery rerun also PASS; full recovery output is
`notes/verification/cycle262/recovery261-audits.txt`.
No audit imports another audit. Standard axioms only; exact axiom listings in Full.
No whole-repository build, verify-lean.sh, Yulang2 runtime or independent rebuild.
Independent read review covered21 modules in five batches; SourcePool has author
self-review only because a sixth review could not start. Reach analysis has41 roots
and does not certify that every declaration contributes to a completed language theorem.

## Yulang2 comparison / unfinished work

No new runtime comparison; this cycle concerns representation and finite rebase proofs.
No new language-semantics decision was made. The CandidateBoundaryProbe concerns an
unused internal candidate, not a source rejection. Alias flood experiments are Python
only, not Lean proofs.

Next: executable alias selection equivalent to actual Alias requests; source-wide
candidate closure across installations without assuming Absorbed; dynamic Plan/capture
transport and the general packet/compiler/EvidenceNode bridge.
