# Structural constraint soundness: frozen construction handoff

Date: 2026-10-26. Producer: generic `lean_prover` fallback,
`/root/paper_allocation_execution`. Assigned baseline:
`0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3`.

Status: constructed and checked with pinned Lean 4.35.0; complete exact-type
and axiom audit passed. Independent review and integration remain with the
primary. This closes a concrete forward constraint-reflection premise. It
does **not** close original source inference soundness, native conformance,
recursive model existence, generalization, principality or combined termination.

## Delivered files and fixed interface

| File | SHA256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean` | `33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293` |

The primary added the Syntax lease so parallel consumers could use a frozen
dependency. It was checked and frozen before the downstream construction.
The only imported project dependency is `Contracts.lean`, SHA256
`2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
Existing sources, compiler, root imports, manifests, shared status and Git
were not changed. No children were launched.

All declarations below are in `YulangClosure.SimpleSub`. The shared API is:

```lean
Kind := value | effect
Valuation := (k : Kind) → Nat → Term k
Renaming := Kind → Nat → Nat
Sub : {k : Kind} → Term k → Term k → Prop
Constraint := { kind : Kind, lower : Term kind, upper : Term kind }
Constraint.Satisfied ρ c := Sub (c.lower.subst ρ) (c.upper.subst ρ)
Store := List Constraint
Store.Satisfied ρ store := ∀ c, c ∈ store → c.Satisfied ρ
State := { obligations : Store, occurrences : List Occurrence }
```

`Constraint.mk` takes explicit kind/lower/upper. `Term.subst` takes valuation
first. The function constructor has four distinct children:
`argument : Term .value`, `argumentEffect : Term .effect`,
`resultEffect : Term .effect`, `result : Term .value`.
Its independent `Sub.function` rule reverses the first two comparisons and
preserves the last two. `Term` also represents variables, unchanged atoms,
top/bottom, union/intersection, ordered record/tuple/variant spines. Records
retain label and optional bit; variants retain tag and ordered payload spine.
No width, optional-weakening or contextual effect-admission rule was invented.

## Original obligation and what was missing

The original all-supported-source claims remain those in
`2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 and
`docs/yulang-whole-proof-closure-ja.md`: successful inference must yield an
original source derivation with its scopes, binders and shared joint evidence;
principal coverage, ordinary progress, termination and implementation
correspondence are separate required results. The immutable Value-birth
correction supersedes older cross-level qualification examples.

Read-only inspection found no concrete inference generator, constraint
solver or subtype semantics in the preexisting Lean modules.
`Contracts.SourceProblem.InferenceSoundness` is the proposition
`supported ∧ generates ∧ solves → ∃ witness, sourceJudgment ∧ sameScoped`.
`CoreComposition.native_success_elaborates` consumes that proposition as an
input. The extensive execution/substitution results start with typing
derivations; they do not derive those derivations from successful inference.
The paper ledger's `SOUND — CONDITIONAL-CLOSED` retains full source/stage
correspondence premises and explicitly does not certify the current compiler.

The new proof formalizes the distinct forward direction in the source
preservation note §4, particularly its directed-extrusion argument. It needs
no diagonal extension or existence proof: satisfaction of positive parent
links gives `old ≤ positiveCopy`; negative links give
`negativeCopy ≤ old`. A solved rewritten demand consequently implies its
original demand. This does not remove the independently required scoped
completeness/principality obligations.

## Source correspondence and exact represented scope

| Source clause | Constructed declaration/result | Boundary |
| --- | --- | --- |
| Source-preservation §4, retained directed parent links | `Copy.link`, `extrudeTerm`, `extrudeCopies`, `extrusion_directed` | Structural traversal with supplied level map and actual memo-coordinate map; allocator and bound-recursion simulation remain open. |
| Four native Function ports `(-,-,+,+)` | `Term.function`, `Sub.function`, `Step.function`, both `function_copy_order` theorems | Both effect ports are retained. Complete Call's correlated semantic relation is not replaced by four independent semantic sets. |
| Native `RecordField` presence, tuple order, variant tag/payload | Structural constructors and their corresponding extrusion/decomposition cases | Exact shape retained. Complete row matching/admission is not formalized. |
| Lower/upper bound accumulation and opposite replay | `Step.insertLower`, `Step.insertUpper`, `opposite_bound_replay`, `replay_solution_iff` | Replay derives its new clause from the two actually retained bounds. No arbitrary step-soundness premise. |
| Rewritten upper/lower demands | `negative_demand_reflection`, `positive_demand_reflection` | Original demand is removed by the modeled rewrite and reconstructed by the theorem; it is not simply kept as a final assumption. |
| Actual retained occurrence-selected intrusion | `Occurrence.source`, `Occurrence.Qualifies`, `Step.intrude` | Selection must be from one retained event's actual recorded copies; qualification reuses `Contracts.Qualifies` and both induced-birth-level paths. Native occurrence/graph extraction is not proved. |
| Clause-retaining quotient | `Store.quotient_pullback`, `History.quotient_sound` | Every retained clause is renamed; valuation is pulled back through the exact kind-preserving map. No clause erasure or fresh independent assignments. |
| Finite retained transformations | `Step.sound`, `History.sound` | Concrete constructors are proved individually. Actual Rust traces are not yet embedded into this history relation. |

Native carriers were inspected in `crates/yu-solver/src/term.rs` (`TermView`,
`RecordField`, `VariantAlternative`) and the actual four-port traversal in
`crates/yu-solver/src/lib.rs`'s `extrude`. That legacy level-lowering routine
is not falsely identified with a proved parent/copy allocator. The selected
parent/copy operation's forward algebra is pinned to the source-preservation
argument. Nat labels/atoms stand for retained identities; actual native
name/atom decoding remains an implementation correspondence obligation.

Important scope details:

- `CopyNames` is keyed by kind, polarity and parent. Repeated visits return
  the same coordinate. `extrudeCopies` may list that coordinate repeatedly;
  this does not allocate independent rows or witnesses.
- The theorem is universal over levels and names; freshness/injectivity are
  not needed for the forward implication. Therefore it applies to lawful
  fresh allocations, but does not prove the allocator generates them.
- Emitted original-term links are explicit. Native traversal of selected
  bounds, mutable memo state, worklist scheduling, availability failure and
  solver termination are not claimed to have been simulated.
- The history has one fixed source-reference graph and immutable birth map.
  It records event origin/receiver and copy list, retaining old events.
  It does not prove source graph generation, event-ID uniqueness, or dynamic
  source graph correspondence.
- `Sub` is independently defined structural derivability. It is neither
  source typing nor the complete semantic relation of contextual effects.
  Opaque atoms carry identity only; resolved type arguments, residual lineage,
  guards, providers and complete Call evidence are not erased from the original
  task or claimed proved here.
- A valuation maps rows to finite `Term`s, with no `mu` constructor. Bounds
  may mention recurrent rows, but the theorem supplies no recursive/rational
  solution or existence result. A final model is a substantive premise.

## Checked public declarations and exact main claims

The Syntax module has ten authored public theorems:
`Term.subst_id`, `Term.subst_comp`, `Term.rename_subst`, `Sub.subst`,
`Store.satisfied_nil`, `Store.satisfied_cons`, `Store.satisfied_append`,
`Store.subset`, `Constraint.rename_satisfied`, `Store.quotient_pullback`.

The Soundness module has sixteen:
`copiesSatisfied_nil`, `copiesSatisfied_cons`, `copiesSatisfied_append`,
`extrusion_directed`, `negative_demand_reflection`,
`positive_demand_reflection`, `opposite_bound_replay`, `Step.sound`,
`replay_solution_iff`, `Step.retains_occurrences`, `History.sound`,
`History.retains_occurrences`, `History.quotient_sound`, `History.empty_sound`,
`positive_function_copy_order`, `negative_function_copy_order`.

The central checked types, with namespace shortened, are:

```lean
extrusion_directed :
  ∀ levels target names ρ {k} (t : Term k) p,
    CopiesSatisfied ρ (extrudeCopies levels target names p t) →
    Directed p (t.subst ρ) ((extrudeTerm levels target names p t).subst ρ)

History.sound :
  ∀ {ref birth initial final}, History ref birth initial final →
    ∀ ρ, final.Satisfied ρ → initial.Satisfied ρ

History.quotient_sound :
  ∀ {ref birth initial final}, History ref birth initial final →
    ∀ q ρ, Store.Satisfied ρ (final.obligations.map (Constraint.rename q)) →
      initial.Satisfied (fun k identity => ρ k (q k identity))
```

`History.empty_sound` separately derives initial satisfaction for every
valuation when this concrete history discharges every obligation. It does
not define native acceptance as emptiness, or claim all successful native
inference has such a history. `replay_solution_iff` proves equality of the
solution sets before/after adding the comparison entailed by two retained
opposite bounds. The final solution and history are the explicit main
premises; no final original-demand satisfaction or abstract local preservation
law is assumed.

## Verification and full audit

Owned isolated project/cache and all logs:
`/workspace/scratch/f98087c7ac1a/inference-constraints/`.
Native Lake:
`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.
Version commands returned Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src with that Lean.
All commands used `LEAN_NUM_THREADS=1`; Lean used `-j1 -M1024`.
No two owned Lean processes ran concurrently. Each focused call had a
60-second timeout. Five focused checks/audits used about 15.6 seconds total.

| Attempt | Command/result |
| --- | --- |
| `check-01.log` | Initial explicit module build, exit 1: unavailable `forall_or` lemma. Replaced with direct constructive proof. |
| `check-02.log` | Syntax explicit build succeeded and was frozen; Soundness exit 1: hidden kind binder annotation and duplicate namespace `end`. |
| `check-03.log` | Soundness exit 1: tactic case names bound trailing constructor arguments. Fixed local elaboration without changing statements. |
| `check-04.log` | `lake build +YulangClosure.SimpleSubConstraintSoundness`, exit 0, 2.812s, complete four-job dependency target. |
| `audit-05.log` | `lake env lean -j1 -M1024 ConstraintAudit.lean`, exit 0, 1.945s. All actual originating-module theorem constants, including generated/private helpers, checked. |

Audit counts: Syntax **90**, Soundness **96**, total **186**, with 186 matching
begin/end receipts and 26 authored public theorems. Exact types and all axiom
lists were printed; all authored types were inspected. Dependencies are:
**145 empty**, **26 `{propext}`**, **15 `{propext, Quot.sound}`**.
No `Classical.choice`, `sorryAx`, project axiom or checker bypass occurs.
Source scan of both modules and `Contracts.lean` found no `sorry`, `admit`,
`axiom`, `unsafe`, `debug.skipKernelTC`, `native_decide` or `ofReduceBool`.

Audit script SHA256:
`333a76c407813e90bec0aaca6f9ba482d985894a47cb035c0e99a37979f9affe`.
Full audit log SHA256:
`de1e3bac51c0afae311d44864fdb0f5e6687bcc06bf964bf530243e5f041fcdd`.
Successful build log SHA256:
`8cd643ccf8bc74c5809851b78f25c16faebc6e2b274bd0606689bfaf5cf359d0`.
Default integration build and independent review are primary-owned.

## Parent application and next exact premises

The primary can import the frozen Syntax module to prove complete clause/root
freshening transport, actual lower-level anchor fixing and independent-use
maps, then consume `History.quotient_sound` for the forward inference route.
The result needed next is an original source-generation reconstruction theorem
that turns satisfaction of those **same original generated clauses** into the
original source judgment and scoped joint witness. A finite structural
certificate checker, if added, must derive terminal satisfaction rather than
assume successful checking means the original constraints hold.

Still required for the original root: actual generator and solver trace
correspondence; original structural/effect/Call semantic interpretation;
successful terminal model extraction, including recursive solutions;
generalization and publication/use scope correspondence; complete supported
source coverage; native decoding/allocator/memo/quotient correspondence;
separately, source completeness/principality, progress and termination.
None is replaced by a smaller original theorem or a new acceptance definition.

Writes stopped after this handoff. Both proof files remain at the frozen
hashes above. No Lean process remains running. All other repository paths
and the earlier allocation/review artifacts remain untouched.
