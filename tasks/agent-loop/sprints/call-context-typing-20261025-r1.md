# LEAN-CALL-CONTEXT-TYPING-20261025/r1 — typed Call plugging

Status: FROZEN ACTIVE CONTRACT
Branch / baseline: `research/simple-sub-intrusion` / `439ce004493076402e1335489018f8ee2cd53e93`
Primary: Luna
Authority: fixed formal Call syntax and judgments in the pinned modules; source locator is the pinned operational paper. This contract adds no language or semantic rule.

## Original goal and bounded outcome

The unchanged user goal is complete reviewed Lean proofs of Yulang semantics and type inference. Original inference A/B, Call A/B, r9 Call execution adequacy, source/native correspondence, principality, termination, and production gates remain OPEN. The prior `LEAN-COMPLETE-CALL-20261025/r9` outcome is SOURCE_INPUT_BLOCKED/UNACCEPTED and remains so.

Prove one formal syntax proposition: for every suffix type, actual `EvaluationContext`, and replacement hole computation, the stored context and adapter derivations type the exact computation built by `plugEvaluationContext` at `context.resultType`.

```lean
theorem plugEvaluationContext_typed
    {Suffix : Type}
    (context : EvaluationContext Suffix)
    (hole : Comp)
    (hhole : CompTyped Original.emptyContext hole context.holeType) :
    CompTyped Original.emptyContext
      (plugEvaluationContext context hole) context.resultType
```

The proof may establish exactly these helper propositions in the same module:

```lean
ContextTyping env frames a b →
CompTyped env hole a →
CompTyped env (plugFrames frames hole) b
```

```lean
AdaptersTyped adapters a b →
CompTyped Original.emptyContext body a →
CompTyped Original.emptyContext (plugResultAdapters adapters body) b
```

The main proposition composes the actual frame derivation, the stored declared-result consumer under its value binder, and the actual ordered pending result adapters using the equalities stored in `EvaluationContext`. `Suffix` remains arbitrary and untouched. No new syntax, premise, type rule, adapter semantics, or source equation may be added.

## Interpretation boundary and success evidence

This is a theorem about the fixed formal `TypedCall` definitions in the pinned Lean modules. It supports the typed plugging side of Call preservation. It does **not** establish that every source evaluation context has this representation, source/native correspondence, operation/effect preservation, Force/View realization, Call S/C or A/B, or original inference correctness. No Call or Force semantic gate closes from this result.

Success requires all three displayed judgments to typecheck with the exact stored constructor data and order, no extra semantic premise, no proof hole/custom axiom, and independent review. The falsifier is a missing case or required hypothesis absent from the frozen judgments, a reordered adapter/context frame, or an invalid use of the stored result equalities.

## Frozen dependency inputs

Revalidate all hashes before the preflight and author launch.

| Input | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/CoreSyntax.lean` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `notes/theory/lean/YulangClosure/CoreExecution.lean` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `notes/theory/lean/YulangClosure/CoreSubstitution.lean` | `fc73d6d60d28f2abb54049a5715751d27df47ad93dbeb8f52966cf98a747bd2f` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/YulangClosure.lean` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `notes/theory/2026-10-24-lean-core-correspondence.md` | `5aa9c3c417c98b3f6e69e3cb1ecb8872b49db836a10d0ca72e2606c0399dcbb0` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| Prior frozen r9 contract | `tasks/agent-loop/sprints/lean-complete-call-20261025-r9.md`, SHA-256 `6a2a2ce7cce845df7239b790709cdbfe24e15bbacc834d9d3027e9f697131811` |
| Prior r9 outcome | `tasks/agent-loop/sprints/lean-complete-call-20261025-r9-outcome.md`, SHA-256 `66d5f30ee3323b33b6943b5817ee48cdd69e20bfd793ea65b08df125567a7579` |
| Prior r12.1 outcome / active parent obstruction | `tasks/agent-loop/sprints/force-local-applicability-20261025-r12-outcome.md`, SHA-256 `c790537a61232946a2e01c5d67551a05207f2c07f839839902978acf9144a5b4` |

The r9 outcome remains SOURCE_INPUT_BLOCKED/UNACCEPTED. Its candidate modules and local syntax theorem grant no execution-adequacy, source/native or semantic promotion.

## Exact leases and authoring

One Sol/high `prover` receives these exclusive paths only after Luna's dependency preflight succeeds:

- `notes/theory/lean/YulangClosure/CallContextTyping.lean`
- `tasks/agent-loop/inbox/20261025-call-context-typing.md`

Both paths must be absent at launch. No edits to existing modules, root imports, source semantics, tests, expected output, rules/config, manifests, or other files. No scratch, descendants, Git, tests, compiler/runtime execution, or nested CLI. Author cap: 600 seconds. Freeze the theorem module and revision-1 handoff, then STOP.

## Serialized Lean gate

Lean is pinned to 4.35.0, one process at a time, `-j1 -M1024`, 120-second timeout per invocation. Luna owns all checker execution and the explicitly enumerated ignored outputs under `notes/theory/lean/.lake/build/lib/lean/YulangClosure/`:

- preflight: `CoreSyntax.olean/.ilean`, `Contracts.olean/.ilean`, `CoreSubstitution.olean/.ilean`, `CoreExecution.olean/.ilean`;
- target check: `CallContextTyping.olean/.ilean`.

Within a 480-second primary preflight cap, compile only the four pinned dependencies serially in import order (`CoreSyntax`, `Contracts`, `CoreSubstitution`, `CoreExecution`). Stop at the first dependency/hash failure. Do not repair it under this contract and do not start the author. After author STOP and frozen hashes, independently assign one fresh nonauthor proof reviewer (read-only, 300 seconds). Then Luna may run the single target check from the pinned sources and review snapshot, including theorem signatures and `#print axioms`. No Lean write lease is issued to the author; the author's file is source only.

## Lanes, resources and integration

Proof lane: one theorem author with related helper lemmas under the exact contract above. Fresh review is sequential after author STOP. No Astra.

Implementation lane: Luna/high retains `NO_SAFE_CODE_SLICE` for source compiler changes; this bounded formal theorem needs none. FL12-SOURCE-1 remains open and independent.

Fresh cap **1,800 seconds**: Luna dependency preflight 480 + Sol author 600 + fresh reviewer 300 + final serialized Lean target check 120 + Luna integration 300. No carryover. Three unrelated legacy UNKNOWN reservations remain quarantined; maximum active assignments are those three plus Luna, one author, and the reviewer reservation (six total). Requested versus observed model/effort remain separate; missing runtime metadata stays UNKNOWN.

Stop on any changed dependency, failed preflight, missing formal constructor, need for new semantics/premises, exhausted budget, or inability to prove the exact statement. No automatic renewal.

Only Luna adjudicates review, updates compact state and a durable outcome, stages explicit reviewed paths, inspects the entire outbound range, and commits/pushes non-forced. Next consultation: preflight failure, frozen theorem/review result, material authority/lease change, or a new parent-level obstruction—not internal helper lemmas.
