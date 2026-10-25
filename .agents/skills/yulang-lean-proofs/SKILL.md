---
name: yulang-lean-proofs
description: Formalize, repair, and verify Yulang Lean 4 proofs against governing papers and specifications. Use for .lean theorem work, source-to-Lean correspondence, Lake/import failures, proof-state debugging, and audits of claimed Lean proof completion in notes/theory/lean.
---

# Prove Yulang obligations with Lean

Read the original claim and its definitions, construct the proof, and run the
pinned checker. Return checked declarations with their exact premises and
application to the original obligation. A plausible proof term, a build, and
a proof of the intended Yulang statement are different evidence.

## Fix the claim and source correspondence

1. Read root `AGENTS.md`, `rules/goal-driven-sprints.md`, the assigned packet,
   and applicable proof authority. Follow the primary's exact leases and finite
   budget. This skill does not start a sprint or grant new writes.
2. Use [sources.md](references/sources.md) to locate the relevant manuscript
   section, corrections, original parent obligation and existing Lean module.
   Read their actual definitions. A map, old success receipt or draft status is
   not semantic authority. Search only relevant theory history.
3. Record in the existing assignment handoff: original claim/section and source
   revision; Lean fully qualified declaration; quantifiers, hypotheses and
   conclusion; represented constructors/omitted cases; unresolved premises and
   owners. Preserve full source scope and shared witnesses. Keep candidate
   semantics labeled as candidate semantics.
4. Inspect actual declarations and dependencies before editing. In particular,
   `SourceProblem.InferenceSoundness` and companion roots are proposition
   definitions; `LocalLaws` arguments contain obligations. Neither establishes
   the concrete source instance. Apply useful lemmas back to the parent and
   identify the first remaining bridge.

Never move a difficult conclusion into an assumption, define typing as safety,
silently restrict the supported language, discard optional records, method
selection or effect hygiene, or change approved inference behavior to make a
theorem pass. Report a real counterexample or missing premise when necessary.
Do not register manuscript theorems as project `axiom`s.

## Establish a working fixed environment

Read `notes/theory/lean/lean-toolchain`, `lakefile.toml`, `lake-manifest.json`,
and the relevant README section. The project currently pins Lean 4.35.0, uses
the `YulangClosure` library, and has no external packages. Re-read these files
rather than assuming that this snapshot remains current.

From `notes/theory/lean`, first resolve an installed native Lake: use the read-only
`elan which lake` lookup for an elan proxy, or the exact path of a task-local
distribution. A failed lookup returns installation to the primary; do not invoke
an unresolved proxy that might install automatically. Run the resolved executable
with `--version` and `env lean --version`; both must identify the pinned Lean
version. Follow [execution.md](references/execution.md) for missing tools under
the environment's permissions. Do not change global defaults, run `lake update`
or `lake upgrade`, or add Mathlib as an incidental proof repair.

Assign one verification owner for the build/cache. Include generated and scratch
outputs in ownership; use an isolated project copy when another worker owns the
build or inputs are changing. The project's `-j1` and `-M1024` bound individual
Lean processes; also bound total elapsed time and Lake scheduling. Distinguish
missing tools and timeouts from mathematical counterexamples.

## Construct and check in small steps

- Search existing definitions and lemmas with `rg` before replacing them. Check
  exact types with `#check @Namespace.name` and definitions with `#print`. Search
  pinned `src/lean/Init`, `Std` and `Lean` when library names or tactics are
  uncertain; consult the primary documentation in [sources.md](references/sources.md).
- State the unchanged theorem first. Choose induction variables, generalizations,
  substitutions and invariants from the mathematical argument. For indexed or
  mutual relations, inspect recursors and all constructors.
- Build the selected module after a small change, inspect the first actual error
  and goal, then repair. Use `trace_state` and local pretty-printing options to
  expose hidden arguments. Use `simp?`, `exact?` or `apply?` only when available
  in the pinned imports; replace exploratory suggestions with concrete checked
  terms where practical. Follow [execution.md](references/execution.md) for
  import, namespace, rewriting and induction diagnostics.
- Build import dependencies before `lake env lean File.lean`; `lake env` only
  prepares an environment. A direct file check does not refresh import artifacts.
  Root import edits need that exact path in the lease. The default target does
  not establish coverage of every `.lean` file.
- Do not deliver `sorry`, `admit`, project axioms, `debug.skipKernelTC` or unchecked
  native-evaluation assumptions as completed proof. Temporary holes remain
  unfinished work. Keep resource increases local and explain their cause.

## Verify declarations and the integration target

From the repository root, use the bundled checker, for example:

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --module YulangClosure.PaperTypeSubstitution \
  --theorem YulangClosure.PaperTypes.subst_id \
  --theorem YulangClosure.PaperTypes.subst_comp
```

Repeat `--module` and `--theorem` for the actual changed proof surface. Add
`--full` once at integration to also build the default targets. Use `--lake`
with an absolute path to a task-local Lake and `--project` for an isolated
project copy. Keep `--timeout` inside the assigned budget. The helper supports
ordinary ASCII dotted names; use manual commands for other valid identifiers.

Inspect printed theorem types and every `#print axioms` result. The helper
rejects non-theorem declarations, `sorryAx`, and dependencies beyond `propext`,
`Classical.choice`, and `Quot.sound`. Report actual standard axioms rather than
claiming an axiom-free proof. Passing does not discharge theorem arguments or
establish the intended meaning of definitions. This catches ordinary mistakes;
it is not certification against hostile metaprograms.

Supplement with a source search for `sorry`, `admit`, `axiom` and checker bypasses
in the changed dependency cone. Inspect matches instead of counting comments;
grep is not an indirect-dependency audit. Retain material failure/repair evidence
in the assigned handoff rather than replacing a failed log with success.

## Delegate and hand off

Use registered `lean_prover` for a bounded Lean construction/repair packet; it is
a leaf with no Git, compiler, dependency, scheduling or approval authority. Supply
original source locators, exact declarations, frozen dependencies, exact output
paths, one handoff path, checker/cache ownership, resource limits and stop condition.
Independent review remains with a fresh eligible reviewer.

Use `fork_turns: "none"` on supported launches. If custom roles are unavailable,
pass `.codex/agents/lean-prover.toml` and this skill to a supported generic worker,
or continue in the primary if spawning is unavailable. Do not start a nested CLI
or claim that config edits hot-reloaded the running session.

Return source-to-Lean mapping; files/revisions; theorem names and hypotheses;
actual commands, versions, exits and complete axiom results; represented/omitted
cases; parent application and first remaining premise; all scratch paths and
writes-stopped status. Separate constructed, checker-accepted, independently
reviewed, source-corresponding and production-ready evidence. Only the primary
changes shared status, integrates, commits and pushes.
