# Cycle181 verification recipe and limits

Compiler: Lean 4.35.0. Focused rebuild runner: `build.py` in this directory.
Each child compiler invocation uses `-j1 --trust=0 -DwarningAsError=true` and
has a 180-second timeout. The cache is an isolated layer of links over the
previous verified cache; changed-source modules and downstream importers are
recompiled, never written into the older cache. Local source-change comparison
is against cycle180, and fresh integration changes were first rebuilt.
The old cache is a dependency, not a newly certified full repository build.

Commands from the cycle workspace:

```sh
python cycle181-verification/build.py $(cat cycle181-verification/modules.txt)
# PASS 18, dependency closure 945; all-new-build.log
cd yulang181-public/lean
LEAN_PATH=<isolated-cache> lean -j1 --trust=0 -DwarningAsError=true Audit/Cycle181CompleteGate.lean
# AXIOM-GATE-PASS: 141 declarations; complete-audit.log
YULANG_REACH_ROOTS=<roots-general.txt> YULANG_REACH_OUTPUT=<new-output.tsv> \
  LEAN_PATH=<isolated-cache> lean -j1 --trust=0 -DwarningAsError=true ../tools/ReachCycle181Final.lean
# REACH: 2 roots; 0/141 cycle181 declarations reachable
YULANG_REACH_ROOTS=<roots-local-final.txt> YULANG_REACH_OUTPUT=<new-output.tsv> \
  LEAN_PATH=<isolated-cache> lean -j1 --trust=0 -DwarningAsError=true ../tools/ReachCycle181Final.lean
# REACH: 7 roots; 87/141 cycle181 declarations reachable
```

The two final reach computations briefly overlapped; proof compilation and
axiom gates were sequential. Both exited 0; no long-running compiler remained
at 05:03 UTC. The closure follows both type and term dependencies, including
opaque proof values. It is not a relevance score and does not validate the
choice of target. In particular zero general-root reachability confirms that
the old composition is not wired to these new partial producers.

The axiom gate visits every loaded declaration whose module name ends in 181,
including definitions and generated/private constants, and recursively collects
axiom dependencies. It permits only propext, Classical.choice, Quot.sound.
All eighteen proof modules are imported both by the gate and the additive
Yulang root. The source inventory lists 101 explicit declarations; generated
ones explain the larger gate count. No prior audit is edited.

One initial focused build failed with an unknown source_member namespace;
`new-build.log` preserves the failure. It was fixed before first publication
of that module; all later focused builds and the complete gate passed.

Static gate checks old Lean byte identity against the fresh upstream version
or retained work-only file, frozen root Audit/README/lake config, root imports,
proof-escape tokens and whitespace. It is intentionally not the full
`tools/verify-lean.sh` supervisor gate. No full local lake build or supervisor
verification script was executed. GitHub workflow success is recorded separately
and not substituted for a local full-build claim.
