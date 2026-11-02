# R233 proof handoff — record-width equation obstruction

Revision 2. Producer `/root/r233_cached_constrain_proof`; author, not an
independent reviewer. **Kernel check passed, reported by Luna;
MODEL-INCOMPLETE; independent review pending.**
The prescribed source-equation mismatch stop fired before cached constraining
was defined. The primary explicitly directed preservation of the finite pair
and a kernel-checkable nonderivability proof, without changing the relation.

## Original claim and authority

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:128`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The same source, scope, generated constraint, solution, and one shared witness
remain required. `SourceScopedCoverage`, `PrincipalCoverage`, and
`InferenceTermination` also retain their original quantifiers. No root or
package is closed: **parent delta 0; roots 0/4; packages 0/5**.

Read authority: root `AGENTS.md` and `AGENTS.pre-sprint.md`,
`rules/goal-driven-sprints.md`, `rules/design-authority.md`, the R233 fixed
contract, the Lean skill and its `references/sources.md` and
`references/execution.md`, inference principles §§1–3 and integration boundary,
the current birth-level correction §§2–6, original preservation claim §§1,3,
and root-first plan's model freeze/proof order. Research plans and prior
receipts supply scope/history, not replacement source semantics.

Original paper reread from the persistent official PDF by `pdftotext` to stdout:
§3.2.2, printed pp.124:10–11; Fig.9, p.124:21; §5.3.1 Lemma 2, p.124:27.
Pinned implementation reread directly at
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala`,
especially :88–129 and :134–159. Its import note fixes commit
`9bae772624c23b52a93c1b226157e16898b4d9db`; that commit identity was read
from the frozen import, not independently queried through Git by this leaf.

## Precise first mismatch

Use two distinct required record labels and canonical primitive objects:

```text
lower = Record [(0, A), (1, B)]
upper = Record [(0, A)]
```

Paper §3.2.2 / Fig.9 requires `constrain(lower, upper)` to succeed without
changing bounds: iterate the sole right field, find label 0 on the left, then
successfully compare A with itself. The extra left field is permitted. The
pinned reference does the same field lookup at Typer.scala:108–114; its
identity return at :93 handles the shared A object. No noncanonical primitive
equality assumption is involved.

Cache details remain distinct. Fig.9 caches every comparison before descent,
so this empty-cache invocation retains the record pair and the reflexive
primitive pair. The pinned reference checks object identity first and caches
only variable-endpoint pairs (:93–103), so its empty cache stays empty in
this invocation. Both accept; no equivalence of their cache states is asserted.
The mismatch therefore precedes cyclic or cache-hit reasoning.

The frozen `YulangClosure.SimpleSub.Sub.recordCons` instead requires the same
label, optional flag, and a comparison of the entire tails. There is no record
width rule. Its own source comment explicitly limits it to complete constructor
shape and disclaims complete optional-row/effect admission. This is an
intentional partial relation being insufficient for the proposed stronger
operation theorem, not evidence that the existing local theorems are false.

**First missing equation/owner:** Luna's mathematical-model owner must fix the
independently defined record comparison/consistency relation consumed by the
cached-constrain theorem and its coalescing result so that the actual Fig.9
equation above is expressible and justified. With the frozen ground embedding,
the required target cannot be `SimpleSub.Sub widthLower widthUpper`: it is
refuted by the candidate theorem below. Derive the proper relation/bridge from
the original record rules and obtain the normal model-conformance review before
continuing construction. This leaf has no lease to change
`SimpleSubConstraintSyntax.lean`, core definitions, or semantic authority.
No extra premise, width rule, candidate successful-run certificate, or new
source restriction is installed. A full operation also still needs endogenous
cache state, dual insertion and opposite-bound replay, structural equations,
and the strengthened cache/subtyping consistency invariant of Lemma 2.

## Constructed declarations and full types

Artifact:
`notes/theory/lean/YulangClosure/AbstractCachedConstrainR233.lean`
SHA-256 `3a0de10775554603d9c906bde1ec44c0d53d009044e354e69554e61c3ecff4f4`.
It imports only the unchanged `YulangClosure.SimpleSubConstraintSyntax`.
Namespace prefix for every declaration below is
`YulangClosure.SimpleSub.CachedConstrainR233`.

Definitions:

```lean
recordDepth : {kind : Kind} → Term kind → Nat → Prop
widthLower : Term .value
widthUpper : Term .value
widthDemand : Constraint
```

`widthLower` is
`recordCons 0 false (atom 0) (recordCons 1 false (atom 1) recordNil)`;
`widthUpper` is `recordCons 0 false (atom 0) recordNil`.
`widthDemand = ⟨.value, widthLower, widthUpper⟩`.

`recordDepth` is a separating invariant of the existing inductive relation:
bottom, variables, atoms, Function, tuple and variant constructors map to
False; top maps to True; union/intersection map to disjunction/conjunction;
recordNil accepts depth zero; recordCons consumes one depth from its tail.
It is not a source typing relation or an algorithm readout. Its purpose is
to rule out hidden derivations through transitivity/lattice rules.

Authored theorem types, transcribed from source and subsequently confirmed by
Luna's printed-type audit:

```lean
recordDepth_mono {kind : Kind} {lower upper : Term kind}
    (comparison : Sub lower upper) :
    ∀ depth, recordDepth lower depth → recordDepth upper depth

width_field_reflexive : Sub (.atom 0 : Term .value) (.atom 0)

width_not_sub : ¬ Sub widthLower widthUpper

width_rejected_by_every_valuation (valuation : Valuation) :
    ¬ widthDemand.Satisfied valuation
```

The first proof covers all 16 frozen Sub constructors, including transitivity,
both lattice operations, both kinds, and the Function constructor with all four
distinct ports. No port is deleted or redefined. The separating interpretation
does not test their variance correctness; that theorem is about the existing
relation only. The finite nonderivability proof uses depth 2: lower accepts it,
upper would entail `1 = 0`. The ground pair has no variables, so substitution
cannot repair it. The reflexive field theorem is the one child comparison that
the paper's record-width branch demands, not a formalized complete execution.

## Existing result application and omissions

`AbstractCore.CoreState.insertPendingUpper` was reread: it only handles a
left variable and level check, installs its upper bound, then prepends replay
over retained lowers. It has no comparison cache, lower-insertion dispatch,
or structural comparison. On this ground record pair its left-variable match
returns `none`; adding it to a history would not model Fig.9.

R229 `UpperInsertionR229.History` and `history_invariant` retain successful
partial-operation histories. Its `Invariant.metadata` derives empty lower
bounds; `no_opposite_replay` derives empty replay. R230
`UpperPublicationR230.terminal_solution_factorization` explicitly takes that
history, empty pending work, allocated query, and an independently satisfying
original-store valuation. None establishes the missing width equation.
For this ground singleton demand, the present candidate rejects every such
valuation, so R230's valuation premise cannot supply the required operation.
No theorem from those histories is rebranded as endogenous constrain soundness.

Modeled: exact nonderivability in the unchanged structural relation, a finite
required-record pair, and all that relation's inductive constructors.
Omitted/unproved: cached transition, initial/cache invariants, lower/upper
replay activation, cache-hit cycles, successful-run consistency/coalesced
subtyping, recursive guarded readout, optional-row admission, extrusion/SCC
propagation, complete Call/contextual effects, source-generated solutions and
the shared original source witness. The finite pair is a model mismatch, not
a counterexample to Yulang typing or any unchanged parent theorem. No cycle,
replay, four-port recursive-demand, or extrusion/SCC falsifier was executed;
the earlier record-width falsifier triggered the stop condition first.

Parent application: expanding `SourceProblem.InferenceSoundness` still leaves
the same `p.supported s`, `p.generates s x d`, `p.solves d a` premises and the
same existential source-judgment/`sameScoped` goal. These four candidate
theorems supply none of those source premises. The model relation owner above
is the immediate prerequisite; generation/readout/source reconstruction and
native correspondence remain separate owners/gates under Luna's coordination.

## Frozen dependencies and execution evidence

All admission hashes were checked with `sha256sum` and matched:

| Input | SHA-256 |
| --- | --- |
| R233 contract | `30873001ab25326e8d02b501c245eefab828021ee1a856cb23666bd085484891` |
| AbstractSimpleSubCore.lean | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| AbstractUpperInsertionInvariantR229.lean | `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a` |
| AbstractUpperPublicationFactorizationR230.lean | `ee16a4e68bb6357a51877a83e78239db08a0789eecd090f387760db2c2632a50` |
| paper/source import | `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113` |
| inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| root-first plan | `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16` |
| actual imported SimpleSubConstraintSyntax.lean | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| actual Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| official PDF | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |
| pinned Typer.scala | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

Actual read-only commands: `cat`, `sed`, `rg`, `rg --files`, `pwd`,
`sha256sum`, `ls -l`, `command -v pdftotext`, and `date -u`; relevant commands
exited 0. Two initial guessed module paths were absent:
`AbstractGeneratedHistoryR230.lean` (cat, exit 1) and
`InferenceContracts.lean` (rg, exit 2). `rg --files` located the actual R230
module and `Contracts.lean`; subsequent reads used those paths. These were
navigation failures, not Lean diagnostics or mathematical counterexamples.
Paper reads were `pdftotext -f 10 -l 11 -layout ... -`,
`pdftotext -f 21 -l 21 -layout ... -`, and
`pdftotext -f 27 -l 27 -layout ... -`, all exit 0, stdout only.

The exact pin/configuration files were read: Lean `leanprover/lean4:v4.35.0`,
library `YulangClosure`, `-j1 -M1024`, existing manifest with no external
packages. **Actual native Lean/Lake versions: NOT_RUN on this lane.** The
packet assigns all checker/cache writes to Luna, so this leaf invoked no
Lean, Lake, checker, Cargo, or tests. No actual Lean goal/diagnostic or axiom
output was produced by this author. Luna's separate verification receipt is
recorded below; the author does not self-certify that check.

All four complete audit pairs are embedded in the module:

```lean
#check @YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub
#check @YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation
#print axioms YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation
```

Verification handoff to Luna: use the existing cache and resolved pinned
native Lake only. Requested command (not run by this author):

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --module YulangClosure.AbstractCachedConstrainR233 \
  --theorem YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono \
  --theorem YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive \
  --theorem YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub \
  --theorem YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation \
  --timeout 180
```

The helper's generated audit scratch path belongs to Luna's verification
operation, not this author. Its actual ephemeral path was not supplied to the
author. Independent review is NOT_RUN at author freeze.

### Primary verification receipt, received after source freeze

Luna reported the pinned bundled check passed for the exact source hash above.
Actual tool versions: Lake 5.0.0 / Lean 4.35.0. The command used the options
above with explicit
`--project /home/momota1029/rust/yulang/notes/theory/lean` and
`--lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Build and standalone complete printed-type/axiom audit both exited 0.

The complete transitive axiom results reported by Luna are:

| Fully qualified theorem | `#print axioms` result |
| --- | --- |
| `YulangClosure.SimpleSub.CachedConstrainR233.recordDepth_mono` | no axioms |
| `YulangClosure.SimpleSub.CachedConstrainR233.width_field_reflexive` | no axioms |
| `YulangClosure.SimpleSub.CachedConstrainR233.width_not_sub` | no axioms |
| `YulangClosure.SimpleSub.CachedConstrainR233.width_rejected_by_every_valuation` | no axioms |

Luna confirmed the printed types above, including
`Sub lower upper → ∀ depth, recordDepth lower depth → recordDepth upper depth`
and the universally quantified valuation rejection. There were no Lean
failure/repair attempts reported for this source revision. The existing
`notes/theory/lean/.lake` apparent size was 133,964,417 bytes before and
134,108,449 bytes after: +144,032 bytes, below 64 MiB. Luna reported no new
environment, worktree, or cache. These facts are attributed to the primary's
actual verification message, not to an invocation by this author. They
establish these declarations' kernel acceptance under their printed types;
source/model conformance and independent review remain separate.

## Resources, mutual TODOs, and stop receipt

Author resources: one leaf, no children, no heavy process, no cache/scratch
creation, no installation/dependency changes, no Git or external contact.
Tool read/mutation calls each finished in under one second of measured wall
time; sampling duration, peak RSS and CPU were not measured. Work stayed within
the assigned 1,200-second proof envelope. Only the two exact leased outputs
were written. Existing `.lake` paths were neither written nor cleaned by this
leaf; author-attributable additional cache bytes: zero.

Luna TODO: preserve the successful pinned checker evidence, assign fresh
independent review, adjudicate the source relation
mismatch, and record the next exact model-equation owner. Author TODO after
an explicit repair request: inspect actual diagnostics and make only the
necessary repair within the same lease/bound, then refreeze with a new hash.
No background work is scheduled.

**WRITES STOPPED for both leased paths at revision-2 handoff.** The Lean
artifact hash above is frozen; the handoff's own final SHA-256 is returned
separately to avoid a self-referential hash. A later changed hash invalidates
this frozen revision and requires a new primary verification/review target.
