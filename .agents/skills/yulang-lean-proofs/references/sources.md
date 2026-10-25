# Source map for Yulang Lean proofs

Use this map to select the governing sources for the assigned claim. Paths are
relative to the repository root. Read the source's status, scope and supersession
notices; this map grants no semantic authority.

## Repository meaning and original obligations

| Question | Read | Boundary |
| --- | --- | --- |
| Which decision governs? | `rules/design-authority.md`, relevant `notes/design/INDEX.md` entry, then its source | An index or manuscript is not automatically Authoritative. |
| What must inference preserve? | `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | Preserve ordinary Simple-sub generation, accumulation, propagation, levels, extrusion, intrusion and generalization. |
| What is current intrusion qualification? | `notes/design/2026-10-24-birth-level-scc-intrusion.md`, §§2–6 | Fixed Value-birth-level induced graph; do not restore superseded cross-level paths. |
| What are original A/B claims? | `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, §§1, 3, 5, with the birth-level correction | Preserve source scope and one shared strategy/witness. |
| What is the whole-language target? | `docs/yulang-whole-proof-closure-ja.md`, original claim and relevant closure section | Conditional composition is distinct from concrete instances and parent closure. |
| Which semantics/correction applies? | `docs/yulang-semantics-and-soundness-ja.md`, then the named operational/source manuscript | The guide is a research integration draft, not blanket semantic approval. |
| Where are execution types and safety? | `docs/yulang-operational-type-safety-ja.tex`, labels `sec:types`, `sec:machine`, `thm:safety`; `docs/yulang-source-type-safety-ja.tex` | Read opening correction notices; older continuation/evidence behavior may be superseded. |
| Which corrected machine interfaces feed Lean? | Under `notes/theory/`: `2026-10-24-corrected-core-value-continuation.md`, `2026-10-24-corrected-machine-simulation.md`, `2026-10-24-source-core-action-coverage.md`, `2026-10-24-source-core-finite-interface.md`, `2026-10-24-correlated-handler-observation.md` | Open simulation, source coverage, observation and finite-interface premises remain obligations. |
| Where is the remaining gate? | `notes/theory/inference-theory-map.md`, `notes/theory/successor-proof-obligations.md`, assigned sprint contract | Read exact linked evidence, not the entire historical task ledger. |

If an old note names a machine-specific PDF path, locate the actual file or a
verified primary-source URL before claiming to have read it. If unavailable,
record the missing section and continue only on supported premises.

## Existing formalization

Start with `notes/theory/lean/README.md`, then actual `.lean` declarations.
The README's historical checker receipts do not replace fresh verification.

| Source under `notes/theory/lean/` | Inspect |
| --- | --- |
| `YulangClosure/Contracts.lean` | `Machine`, `Analysis`, `Certificate`, `LocalLaws`, `SourceProblem`: separate assumed laws and proposition definitions from proofs. |
| `YulangClosure/CoreComposition.lean` | Root finite-prefix composition and `SourceProblem.native_success_elaborates`, including all explicit premises. |
| `YulangClosure/Control*.lean`, `Core*.lean` | Represented frames, raw constructors, typing cases and correspondence. |
| `YulangClosure/PaperTypeSubstitution.lean` | De Bruijn algebra; `PaperTypes.subst_id`, `subst_comp`, `OperationInstance.subst_comp`. These are not whole typing/executor results. |
| `YulangClosure.lean` | Public import closure and axiom queries; discover omitted modules explicitly. |

Use focused searches, for example:

```sh
rg -n '^(import|namespace)|theorem .*subst|def .*InferenceSoundness' notes/theory/lean
rg -n 'label\{(sec:types|sec:machine|thm:safety)\}' docs/yulang-operational-type-safety-ja.tex
```

## Lean primary documentation

Use installed pinned `src/lean/Init`, `src/lean/Std`, `src/lean/Lean` and
`src/lean/lake` for exact APIs and command behavior. Use these explanations when
needed; `latest` documentation may describe commands absent from the pin.

- [Interacting with Lean](https://lean-lang.org/theorem_proving_in_lean4/Interacting-with-Lean/): imports, namespaces, `#check`, `#print`, implicit arguments and options.
- [Tactics](https://lean-lang.org/theorem_proving_in_lean4/Tactics/): goal-directed construction.
- [Induction and Recursion](https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/): recursors and generalization.
- [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/): targets, `build`, `env`, manifests and updates.
- [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/): meaning, indirect `sorryAx`, standard axioms and stronger validation boundaries.
- [Elan official README](https://github.com/leanprover/elan/blob/master/README.md): selection through `lean-toolchain`.
- [Lean 4.35.0 release](https://github.com/leanprover/lean4/releases/tag/v4.35.0) and [pinned source](https://github.com/leanprover/lean4/tree/v4.35.0/src): current project distribution and version-specific implementation.

Record the relevant consulted URL or local versioned path in the handoff.
Do not copy long manuals into proof artifacts.
