# R234 proof handoff: finite mandatory-record width/depth branch

Assignment `paper-record-width-r234-proof`, revision 2. Producer
`/root/r234_record_width_proof`; sole author, no descendants. Session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Baseline supplied by contract:
`5deacdac4`. Requested role `lean_prover`, effort bounded; observed
model/effort UNKNOWN. Primary's explicit repair request supersedes revision 1
only for these same two paths. The generic child relation is retained; the
rejected recursive representation and its dependent claims are removed.

**Outcome class: candidate construction, constructed-but-unchecked revision 2.**
Revision 1 had two primary-reported failed builds, preserved below. This leaf
ran no Lean/Lake/checker/cache process. Revision-2 printed types, axiom lists,
kernel acceptance and independent review remain NOT_RUN. The primary owns all
verification and review after the new freeze; no self-certification is made.

## Authority, original claim and source evidence

Read root `AGENTS.md`, preserved `AGENTS.pre-sprint.md`,
`rules/goal-driven-sprints.md`, `rules/design-authority.md`, the exact R234
contract, Lean skill plus `references/sources.md` and `references/execution.md`,
current state and inbox contract, and relevant project README/toolchain files.
Original source: Lionel Parreaux, *The Simple Essence of Algebraic Subtyping*,
PACMPL 4 (ICFP), Article 124 (2020), DOI 10.1145/3409006, actual persistent PDF
`/home/momota1029/rust/simple-sub-reference-paper.pdf`. Read §3.2.2 printed
pp.124:10–11, Fig.9 p.124:21, and Fig.10/§5.1 p.124:24 with `pdftotext` to
stdout, exit 0. The original §3.2.2 explicitly specifies usual record width
and depth; Fig.9 iterates the right fields, finds matching left labels and
calls `constrain(t0,t1)`. Fig.10's S-Rcd/S-Depth and intersection account are
context for the equation, not a claimed complete Fig.10 formalization here.

Actual pinned reference source read directly:
`/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala:88–129`,
particularly :108–114. Import revision is
`9bae772624c23b52a93c1b226157e16898b4d9db`, as frozen by
`notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md`; this leaf did
not query Git. Actual Typer bytes hash matches the primary-supplied
`f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9`.

The original source root remains
`YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128`):

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Read the actual unchanged root declarations, original preservation statement
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1–3 and the
current immutable birth-level correction
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. The original
source domain, scope, shared witness and full source features remain required.
`SourceScopedCoverage`, `PrincipalCoverage`, `InferenceTermination` also stay
unchanged. Neither a research draft nor the current row supplies semantics
or a concrete `SourceProblem` instance.

The immediate R233 parent obstruction is the missing paper record equation
for a candidate cached-constrain/coalesced model. Read actual
`SimpleSubConstraintSyntax.Sub`, `Constraint.Satisfied`, R233 definitions and
its source-qualified review, including the open-tail/top caveat. R234 does
not change `Sub`. The R233 closed ground pair remains rejected there; no
claim excludes alternative source-approved encodings.


## Frozen artifacts and dependencies

Exact leased writes:

- `notes/theory/lean/YulangClosure/PaperRecordWidthR234.lean`
- `tasks/agent-loop/inbox/paper-record-width-r234-proof.md`

Revision-2 module SHA-256: `f11fc30a6fd3e443aae1ccd39c071a02721514b6e3c57f54f046e2920b6325a4`.
The handoff's final hash is returned separately. Prior frozen revision-1 module
hash: `157267f45d989be0853b5166cc4b6c219c475ae40af20d6eb680afce16bc8188`;
prior handoff hash: `ad84a80275a32629ae72c750569c866e671a39c0c0d52ebbf0906f3d7caef109`.
These prior hashes identify the failed original target; the intermediate
primary edit's byte hash was not supplied. Neither prior target is promoted.

Direct imports stay `YulangClosure.AbstractCachedConstrainR233` and pinned
`Init.Data.List.Perm`. No root import, scratch, generated output, compiler,
shared record, configuration, dependency, question or other worker file was
written. Versioned library APIs consulted read-only under installed Lean
4.35.0 `src/lean/Init/Data/List/{Basic,Lemmas,Perm}.lean`, including
`List.Perm.mem_iff`.

| Dependency | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/paper-record-width-r234.md` | `22929f61c35dac9ff1d8d6049df2b8a53a01afd930a01f404613cdac6394c628` |
| `notes/theory/2026-10-11-parreaux-simple-sub-proof-import.md` | `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113` |
| `notes/theory/lean/YulangClosure/AbstractCachedConstrainR233.lean` | `3a0de10775554603d9c906bde1ec44c0d53d009044e354e69554e61c3ecff4f4` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `/home/momota1029/rust/simple-sub-reference-paper.pdf` | `5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698` |
| `/home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |

## Material failure evidence and repair boundary

Primary reported both executions with actual Lake `5.0.0-src+eb6cafb` /
Lean `4.35.0`. This is attributed evidence from the verification owner, not
this author's execution. Exact full build command/log path was not supplied;
the reported command class is the selected-module build via the pinned project.

1. First selected-module build, exit 1: at line 241 the kernel rejected the
   recursive occurrence through `Fields FiniteType` as non-valid. Unknown or
   invalid `FiniteSub` declarations and `sorryAx` audit cascades followed.
   This falsified acceptance of the original recursive representation, not the
   record-width equation.
2. After the primary replaced that field by direct
   `List (Nat × FiniteType)`, the next selected-module build also exited 1.
   At line 246 the kernel rejected nested inductive datatype `Exists`:
   `nested inductive datatypes parameters cannot contain local variables`.
   Subsequent diagnostics included `No goals to be solved` at lines 280/290,
   and `sorryAx` in `finite_record_iff`, `emit_success_iff_finite_sub`, and
   `width_branch_success`. Primary reported that independent generic list
   lemmas still printed types/axioms. Their complete individual axiom lists
   were not supplied in that message; no clean overall module check follows.

These failures reject the attempted recursive inductive presentation.
Revision 2 removes `FiniteType`, `FiniteSub`, `finite_record_iff`,
`emit_success_iff_finite_sub`, `width_pair`, and `nested_width_pair` plus their
stale audit requests. It does not introduce a positivity workaround, bypass,
project axiom, recursive-model substitute or a claim that nested width was
proved. Recursive depth and callback adequacy remain open outside this leaf.
The surviving branch equation stays universally quantified over arbitrary
child relation `R`, and concrete width uses only existing `SimpleSub.Term`
and the real reflexive atom theorem of existing `SimpleSub.Sub`.

## Exact definitions and scope

New namespace: `YulangClosure.PaperRecordWidthR234`.

```lean
Fields (α : Type u) := List (Nat × α)
lookup {α : Type u} : Fields α → Nat → Option α
Functional {α : Type u} (fields : Fields α) : Prop
Required {α : Type u} (R : α → α → Prop) (lower upper : Fields α) : Prop
LookupRequired {α : Type u} (R : α → α → Prop) (lower upper : Fields α) : Prop
Children {α : Type u} (R : α → α → Prop) : List (α × α) → Prop
emit {α : Type u} (lower : Fields α) : Fields α → Option (List (α × α))
widthLowerFields : Fields (SimpleSub.Term .value)
widthUpperFields : Fields (SimpleSub.Term .value)
```

`Required R lower upper` independently requires, for each upper `(label,ty)`,
a lower `(label,lowerTy)` with `R lowerTy ty`. Extra lower fields impose no
obligation. `LookupRequired` requires the first matching lower payload instead.
`Functional lower` explicitly requires equal labels to carry equal payloads;
identical repeated entries are allowed. This is a mathematical premise and
makes no Yulang duplicate-label policy. The main theorem uses arbitrary R;
it proves a finite record lifting, not a concrete recursive child instance.

`emit` decomposes in upper traversal order, returns `none` for missing labels,
and emits `(lowerTy,upperTy)` pairs on successful lookups. Validated branch
success adds `Children R children`; lookup success alone never establishes R.
`emit_success_iff_lookup_required` covers all finite lists, including conflicting
first-match duplicates. `emit_success_iff_required` proves the independent
required-field equation under the explicit functional-lower premise. Every
upper occurrence is checked and needs no uniqueness premise.
`emitted_children_preserved` retains the exact emitted list; it cannot select
unrelated child witnesses or discharge R without the stated relation premise.

Represented: empty upper rows, arbitrary finite mandatory fields, extra lower
fields, missing upper labels at any traversal point, exact first-match behavior,
all upper occurrences, lower-to-upper child comparison, generic R obligations,
functional-row permutation and concrete conflicting-duplicate order. The R233
pair uses labels 0/1 and exact `SimpleSub.Term.atom` payloads, with the sole child
`SimpleSub.Sub.refl`. Numeric labels describe this explicit finite example;
there is no general source-name or Yulang source embedding theorem.

Omitted: concrete recursive record type/relation, nested-width theorem, recursive
callback execution or adequacy, optional fields, Yulang duplicate validation,
full paper Fig.10 subtyping, arrows/variable solver dispatch, caches/cycles,
opposite-bound replay, mutable partial effects before rejection, extrusion,
intrusion/SCC/generalization, complete Call/effects, solver consistency/coalescing,
source/native correspondence, termination, principality and production authority.
This local finite-domain result changes no original parent domain or quantifier.

## Full theorem types and primary audit

All 22 theorem headers below were transcribed by the author and compared by
the primary against the selected-module build and helper-generated printed
type audit. The module contains fully qualified `#check @...` and
`#print axioms ...` for every declaration. The first two failed attempts and
their `sorryAx` cascades remain preserved above; revision 2 has no `sorryAx`.

```lean
theorem YulangClosure.PaperRecordWidthR234.lookup_some_mem {α : Type u} {fields : Fields α} {label : Nat} {ty : α}
    (found : lookup fields label = some ty) : (label, ty) ∈ fields

theorem YulangClosure.PaperRecordWidthR234.lookup_eq_some_iff_mem {α : Type u} {fields : Fields α}
    (functional : Functional fields) (label : Nat) (ty : α) :
    lookup fields label = some ty ↔ (label, ty) ∈ fields

theorem YulangClosure.PaperRecordWidthR234.lookup_required_iff_required {α : Type u} (R : α → α → Prop)
    {lower upper : Fields α} (functional : Functional lower) :
    LookupRequired R lower upper ↔ Required R lower upper

theorem YulangClosure.PaperRecordWidthR234.lookup_required_cons {α : Type u} (R : α → α → Prop)
    (lower : Fields α) (field : Nat × α) (rest : Fields α) :
    LookupRequired R lower (field :: rest) ↔
      (∃ ty, lookup lower field.1 = some ty ∧ R ty field.2) ∧
        LookupRequired R lower rest

theorem YulangClosure.PaperRecordWidthR234.children_cons {α : Type u} (R : α → α → Prop)
    (child : α × α) (rest : List (α × α)) :
    Children R (child :: rest) ↔ R child.1 child.2 ∧ Children R rest

theorem YulangClosure.PaperRecordWidthR234.emit_success_iff_lookup_required {α : Type u} (R : α → α → Prop)
    (lower upper : Fields α) :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      LookupRequired R lower upper

theorem YulangClosure.PaperRecordWidthR234.emit_success_iff_required {α : Type u} (R : α → α → Prop)
    {lower : Fields α} (functional : Functional lower) (upper : Fields α) :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      Required R lower upper

theorem YulangClosure.PaperRecordWidthR234.emitted_children_preserved {α : Type u} (R : α → α → Prop)
    {lower upper : Fields α} {children : List (α × α)}
    (functional : Functional lower) (emitted : emit lower upper = some children)
    (related : Required R lower upper) : Children R children

theorem YulangClosure.PaperRecordWidthR234.children_true {α : Type u} (children : List (α × α)) :
    Children (fun _ _ => True) children

theorem YulangClosure.PaperRecordWidthR234.missing_upper_rejects {α : Type u} {lower upper : Fields α}
    {field : Nat × α} (member : field ∈ upper)
    (missing : lookup lower field.1 = none) : emit lower upper = none

theorem YulangClosure.PaperRecordWidthR234.required_permutation {α : Type u} (R : α → α → Prop)
    {lower lower' upper upper' : Fields α}
    (lowerPerm : lower.Perm lower') (upperPerm : upper.Perm upper') :
    Required R lower upper ↔ Required R lower' upper'

theorem YulangClosure.PaperRecordWidthR234.functional_permutation {α : Type u} {lower lower' : Fields α}
    (permutation : lower.Perm lower') (functional : Functional lower) :
    Functional lower'

theorem YulangClosure.PaperRecordWidthR234.emit_success_permutation {α : Type u} (R : α → α → Prop)
    {lower lower' upper upper' : Fields α} (functional : Functional lower)
    (lowerPerm : lower.Perm lower') (upperPerm : upper.Perm upper') :
    (∃ children, emit lower upper = some children ∧ Children R children) ↔
      (∃ children, emit lower' upper' = some children ∧ Children R children)

theorem YulangClosure.PaperRecordWidthR234.width_emit : emit widthLowerFields widthUpperFields =
    some [(.atom 0, .atom 0)]

theorem YulangClosure.PaperRecordWidthR234.width_branch_success :
    ∃ children, emit widthLowerFields widthUpperFields = some children ∧
      Children SimpleSub.Sub children

theorem YulangClosure.PaperRecordWidthR234.width_required : Required SimpleSub.Sub widthLowerFields widthUpperFields

theorem YulangClosure.PaperRecordWidthR234.directed_child : emit ([(0, 3)] : Fields Nat) [(0, 5)] = some [(3, 5)]

theorem YulangClosure.PaperRecordWidthR234.missing_width_label : emit widthLowerFields [(2, SimpleSub.Term.atom 0)] = none

theorem YulangClosure.PaperRecordWidthR234.lower_order_example :
    emit ([(1, .atom 1), (0, .atom 0)] : Fields (SimpleSub.Term .value)) widthUpperFields =
      some [(.atom 0, .atom 0)]

theorem YulangClosure.PaperRecordWidthR234.upper_order_example :
    emit widthLowerFields [(1, .atom 1), (0, .atom 0)] =
      some [(.atom 1, .atom 1), (.atom 0, .atom 0)]

theorem YulangClosure.PaperRecordWidthR234.conflicting_duplicate_order :
    emit ([(0, 3), (0, 4)] : Fields Nat) [(0, 5)] = some [(3, 5)] ∧
    emit ([(0, 4), (0, 3)] : Fields Nat) [(0, 5)] = some [(4, 5)]

theorem YulangClosure.PaperRecordWidthR234.r233_paper_width_and_closed_row_obstruction :
    Required SimpleSub.Sub
      ([(0, .atom 0), (1, .atom 1)] : Fields (SimpleSub.Term .value)) [(0, .atom 0)] ∧
    ¬ SimpleSub.Sub SimpleSub.CachedConstrainR233.widthLower
      SimpleSub.CachedConstrainR233.widthUpper
```

## Parent application and first remaining premise

`widthLowerFields = [(0,atom0),(1,atom1)]` and
`widthUpperFields = [(0,atom0)]` are the exact fields of the R233 ground pair.
`width_emit` and `width_branch_success` construct the lookup result and its
one reflexive child. `width_required` proves the paper field equation with
existing `SimpleSub.Sub` only at that child. The final
`r233_paper_width_and_closed_row_obstruction` conjoins that fact with R233's
unchanged `width_not_sub` for the closed rows. Thus it does not assert closed
full-row Sub width acceptance, a full type encoding or approved Yulang semantics.

`directed_child` exhibits emitted `(3,5)`, `missing_width_label` rejects label 2,
`lower_order_example` preserves lookup after swapping distinct lower labels,
and `upper_order_example` emits children in swapped upper order.
`emit_success_permutation` proves validated-success invariance for arbitrary
row permutations under `Functional lower`. `conflicting_duplicate_order`
explicitly falsifies unrestricted lower output invariance. These are authored
proof terms awaiting the revision-2 check, not executed solver probes.

**Parent-premise delta zero; original roots remain 0/4, packages 0/5.**
For unchanged `SourceProblem.InferenceSoundness`, the same arbitrary `s x d a`
with `p.supported s`, `p.generates s x d`, `p.solves d a` still needs
`∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`. This leaf supplies no
original source derivation or shared witness. Its conditional arbitrary-R
lifting is not a concrete full source instance.

First remaining premise/owner: Luna's mathematical-model owner must choose
and justify the full child interpretation, including recursive/optional cases,
and compose this finite branch equation into the unchanged endogenous
cached-constrain/coalescing/consistency theorem, establishing the original
Lemma 2 cache/store invariant. No rejected recursive presentation is supplied
as that interpretation. The source owner must separately reconstruct original
source generation/solutions with the same lexical scope and one shared witness;
the native owner must supply actual native correspondence. These open seams
block dependent promotion and are not hidden assumptions declared established.

Falsifiers: a mismatch between emitted validated children and the frozen
Required relation for functional lower rows; a missing required label with
successful decomposition; functional row permutations changing validated
success; or an emitted pair with reversed endpoints. Conflicting duplicates
are outside the functional permutation theorem and have an explicit example.

## Commands, verification and resources

Actual author commands across revisions: read-only `cat`, `sed`, `rg`,
`rg --files`, `pdftotext` for source pp.10–11/21/24 to stdout, `sha256sum`,
`python3` for source/header/hash generation, and the patch tool. All returned
exit 0 / patch success. Primary failures, versions and build exit 1 results
are recorded separately above. No author Lean goal, diagnostic, kernel result
or complete axiom output is invented.

Read pins: `leanprover/lean4:v4.35.0`, package `YulangClosure` 0.1.0,
`-j1 -M1024`, no external packages. Actual author native version commands:
NOT_RUN. Requested primary command, not an execution receipt:

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --module YulangClosure.PaperRecordWidthR234 \
  --theorem YulangClosure.PaperRecordWidthR234.lookup_some_mem \
  --theorem YulangClosure.PaperRecordWidthR234.lookup_eq_some_iff_mem \
  --theorem YulangClosure.PaperRecordWidthR234.lookup_required_iff_required \
  --theorem YulangClosure.PaperRecordWidthR234.lookup_required_cons \
  --theorem YulangClosure.PaperRecordWidthR234.children_cons \
  --theorem YulangClosure.PaperRecordWidthR234.emit_success_iff_lookup_required \
  --theorem YulangClosure.PaperRecordWidthR234.emit_success_iff_required \
  --theorem YulangClosure.PaperRecordWidthR234.emitted_children_preserved \
  --theorem YulangClosure.PaperRecordWidthR234.children_true \
  --theorem YulangClosure.PaperRecordWidthR234.missing_upper_rejects \
  --theorem YulangClosure.PaperRecordWidthR234.required_permutation \
  --theorem YulangClosure.PaperRecordWidthR234.functional_permutation \
  --theorem YulangClosure.PaperRecordWidthR234.emit_success_permutation \
  --theorem YulangClosure.PaperRecordWidthR234.width_emit \
  --theorem YulangClosure.PaperRecordWidthR234.width_branch_success \
  --theorem YulangClosure.PaperRecordWidthR234.width_required \
  --theorem YulangClosure.PaperRecordWidthR234.directed_child \
  --theorem YulangClosure.PaperRecordWidthR234.missing_width_label \
  --theorem YulangClosure.PaperRecordWidthR234.lower_order_example \
  --theorem YulangClosure.PaperRecordWidthR234.upper_order_example \
  --theorem YulangClosure.PaperRecordWidthR234.conflicting_duplicate_order \
  --theorem YulangClosure.PaperRecordWidthR234.r233_paper_width_and_closed_row_obstruction \
  --project /home/momota1029/rust/yulang/notes/theory/lean \
  --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake \
  --timeout 180
```

### Primary verification and independent review

Pinned command: `.agents/skills/yulang-lean-proofs/scripts/check_lean.py`
with project `notes/theory/lean`, Lake
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`,
`--timeout 180`, module `YulangClosure.PaperRecordWidthR234`, and all 22
fully-qualified declarations listed above. Lake `5.0.0-src+eb6cafb`, Lean
`4.35.0`. Selected module built successfully; helper type/axiom audit exited
0 for all 22 declarations, and every source-transcribed type matches its
printed type. The helper accepted only its standard whitelist.

Complete transitive axiom sets by declaration:

- `[propext]`: `lookup_some_mem`, `lookup_eq_some_iff_mem`,
  `lookup_required_iff_required`, `lookup_required_cons`,
  `required_permutation`, `functional_permutation`, `width_required`,
  `r233_paper_width_and_closed_row_obstruction`.
- `[propext, Quot.sound]`: `emit_success_iff_lookup_required`,
  `emit_success_iff_required`, `emitted_children_preserved`,
  `missing_upper_rejects`, `emit_success_permutation`.
- `[]` (no axioms): `children_cons`, `children_true`, `width_emit`,
  `width_branch_success`, `directed_child`, `missing_width_label`,
  `lower_order_example`, `upper_order_example`,
  `conflicting_duplicate_order`.

Fresh nonauthor `/root/r234_paper_record_review` returned CLEAN for bounded
source conformance; full receipt is
`tasks/agent-loop/inbox/paper-record-width-r234-review.md`. It checked the
exact frozen source/contract hashes and the paper/implementation equation.
It did not run Lean or certify axioms.

Existing `.lake` apparent size before R234 verification: `134108449` bytes;
after: `134545883` bytes; growth `437434` bytes, within the 64 MiB cap. No
new environment, worktree, target or cache path was created. No default build,
root import change, Rust edit, Cargo, or tests were run.

One author leaf, no descendants, heavy processes, installation, Git, nested CLI,
external contact, scratch or cache writes. CPU/RSS/elapsed sampling was not
measured; tool-reported shell wall times were under one second per call.
No author-attributable `.lake` bytes were created. Work remains inside the
finite 1,200-second author envelope; no budget reset or extension is claimed.
No unresolved descendant leases exist.

R234-CHECK completed: the two rejected recursive encodings remain documented,
and revision 2 passed the pinned kernel/type/axiom checker. R234-REVIEW passed
for source conformance only. R234-COMPOSE remains open: the mathematical-model
owner must supply full recursive/source equations and the cache/store invariant
before any dependent parent application. Author writes stopped at revision 2.

**WRITES STOPPED for both exact author paths; subsequent edits in this handoff
are primary-owned verification records.**
