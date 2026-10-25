# Lean proof skill and specialist

Date: 2026-10-25
Authority: explicit user request to add a Lean proof skill and subagent to
`research/simple-sub-intrusion`, consult sources, run Lean correctly, and push.
Scope: workflow maintenance; no new research sprint or semantic decision.
Mode: M1 tooling, one independent reviewer, focused deterministic verification.
Review/check baseline: `157548a2ba67d5cd2c3bc53e9f7a447d8249d9a6`.
Concurrent upstream through `2b880c73468fc9d44600488445ee3c1cf0b5d534` was
fast-forwarded before publication. Its added research modules and scheduling
records do not change this reviewed diff or the checked theorem/import inputs.

## Result

- Added `.agents/skills/yulang-lean-proofs/` with the proof workflow, original
  Yulang source map, primary Lean documentation and executable troubleshooting.
- Registered `.codex/agents/lean-prover.toml` as `lean_prover`, an inherited-model
  proof/verification leaf with actual checker and axiom-audit duties. Connected
  it from `AGENTS.md`, active orchestration rules, `prover` and `astra_prover`.
- Added a bounded checker that resolves an installed toolchain, verifies its
  version, builds named modules, optionally builds the default target, checks
  theorem declaration kinds, prints types/axioms, and rejects incomplete or
  disallowed-axiom evidence. It preserves complete per-theorem output and reports
  only the named declarations under their printed hypotheses.
- Integrated the leaf role and skill into the existing offline sprint checker.
  No model defaults, implementation rights, coordinator exception or budgets
  were expanded. Configuration is not a claim of live role activation.

The dedicated leaf cannot update shared records, dependencies, compiler code,
root imports outside its lease, or Git. Generic-worker fallback reads the same
role/skill when the current runtime does not expose custom named roles.

## Verification

The official Lean 4.35.0 Linux distribution was downloaded into task-local
storage. Archive SHA-256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean commit: `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb` (Lean 4.35.0).

- `quick_validate.py .agents/skills/yulang-lean-proofs`: PASS.
- `python3 tools/agent_sprint.py check`: PASS (static, not runtime activation).
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`: 59 PASS.
- `python3 -m unittest discover -s tools -p 'test_lean_proofs.py'`: 15 PASS.
- Primary real-Lean check: `PaperTypes.subst_id` and `PaperTypes.subst_comp`
  built and audited successfully, each depending on `propext, Quot.sound`.
- Fresh skill-use worker `/root/lean_skill_use` executed the command below with
  the installed native Lake, exit 0, then inspected original source scope:

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --lake /tmp/lean-4.35.0-linux/bin/lake \
  --module YulangClosure.PaperTypeSubstitution \
  --module YulangClosure.CoreComposition \
  --theorem YulangClosure.PaperTypes.subst_comp \
  --theorem YulangClosure.SourceProblem.native_success_elaborates \
  --full --timeout 110
```

The default target built successfully. `subst_comp` depends on `propext` and
`Quot.sound`; `native_success_elaborates` has no axiom dependencies but explicitly
assumes `NativeCorrespondence`, `InferenceSoundness` and `Elaboration`. The worker
reported the precise source/typing/executor bridges still required. Existing
`ControlComposition.lean` emitted three unused-simp-argument warnings; that proof
artifact is outside this maintenance lease and was preserved. Default-target
success does not establish coverage of every research module.

Five actual-Lean negative fixtures in an isolated temporary project all exited
1 without printing PASS: indirect `sorryAx`, a project axiom, a proposition
definition instead of a theorem, a missing theorem, and a missing build target.
No fixture or build/cache output is part of the committed change.

Material repairs during verification: the initial audit's broad `import Lean`
exceeded the 1024 MiB checker limit; minimal `Lean.Elab.Command` and
`Lean.Util.CollectAxioms` imports passed under the same limit. Disabling universe
printing made axiom-name evidence exact. Installed Elan proxies are resolved
with read-only `elan which lake` before native execution. Restricted sandbox
execution could not discover the Lake installation; an authorized elevated
execution succeeded. No toolchain or manifest changes were made.

## Independent review and scope

Fresh `/root/lean_workflow_review` reviewed the frozen workflow, role, helper,
tests and source locators against the integration baseline. No BLOCKING/major
findings. One minor finding identified a manual preflight that could invoke an
uninstalled Elan proxy; the primary aligned the guide with the helper's read-only
native-tool resolution. Only those documentation lines changed after review;
diff and skill validation passed. The reviewer did not run Lean or claim runtime
activation. Helper construction was by `/root/lean_check_helper`; it was not its
own reviewer. The fresh skill-use worker followed the task with no parent history.
All task workers stopped writing before integration.

No existing `.lean` source, compiler source, theorem status, semantic authority,
or production gate changed. Full Yulang proof closure is not claimed. Rust suites
were omitted because this change affects only proof workflow/tooling. Performance
experiments: none. The sole live scheduling snapshot
`tasks/agent-loop/current.json` remains owned by the ongoing research session;
maintenance did not reset it or reclaim its leases. `tasks/current.md` links this
completion record. Only the primary integrates the exact changed paths and
updates the requested branch without force.
