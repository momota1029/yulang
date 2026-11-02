# R223 proof construction handoff — revision 2, FROZEN INCOMPLETE

- Assignment: `R223-BOUND-CYCLE-PROOF`; worker `/root/r223_bound_cycle_proof`.
- Contract initially revision 2, SHA-256
  `aa439da47fccf3bcb83423806c95e15b75e30a00b2a4b55ab2b948e40884f20b`;
  primary admitted revision 3 during this assignment, final SHA-256
  `df9393be7ea3432ca8cf28af13610fdded5430b20b6fdf0f49668e2b83edf980`.
  The change grants Luna two exact dependency-cache output groups; mathematical
  scope, leaf leases, theorem gates and the leaf's no-execution rule stay fixed.
- Requested role: `lean_prover`; effective model/effort metadata UNKNOWN.
  Current-session NEW_TASK and parent messages supply the runtime assignment.
- Sole author: this worker; no descendants, reviewer assignments or delegation.
- Exact writes: this handoff and
  `notes/theory/lean/YulangClosure/AbstractBoundCycleNormalizationR223.lean`.
- Outcome: **constructed-but-unchecked abstract proofs and a precise
  owner-local publication counterexample**. No kernel acceptance, independent
  review, source counterexample, production authority or parent closure claimed.
- Source artifact SHA-256:
  `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee`.
  This handoff's own byte hash is returned in the final runtime message.

## Revision-2 bounded repair and preserved failure evidence

The primary reopened the SAME two exact paths for one ≤1200-second repair
pass after its actual revision-1 build failed. No new file, theorem scope,
cache ownership or generic publication claim was authorized. Previous frozen
source SHA-256 was
`075dfe73016317a360470b7257545c58774187f1ad34d5f79930f4bc19e4d1fd`;
previous handoff SHA-256 was
`f99b3e9934af3419b23193ee83261b4ec9b7665faf1c7312ac6c9c79d2574a9f`.

Actual execution evidence reported by `/root` (not executed by this leaf):

- Lake/Lean 4.35, target
  `+YulangClosure.AbstractBoundCycleNormalizationR223:olean`, build exit 1.
  Full `--version` stdout and full exact shell command were not supplied to
  this leaf; do not synthesize them from the expected command.
- First attempt with `ulimit -v 1048576` aborted before writes. Retry used
  taskset on one CPU and the project's `-M1024`; dependencies compiled and
  the target failed. Root reports cache growth 4,241,846 bytes, only whitelisted
  outputs, within the 64 MiB cap. The leaf has not independently measured cache.
- Material diagnostics, in REVISION-1 source coordinates: line 83 unknown `a`;
  line 239 residual dependent-kind equality; line 287 missing `List.Satisfied`;
  line 293 introN had no additional binders, with a generated sorry target;
  line 296's failed declaration therefore carried elaborator `sorryAx`.
  That environment was rejected, not an accepted proof or an authored hole.
- Lines 434/461/470: unexpected identifier, expected `}` in structure updates;
  downstream fixture equalities at 440/467/478 consequently failed rfl.
  Line 595 had a simplification type mismatch. Lines 655–668 attempted `.mp`
  and `.mpr` on `Bool.or_eq_true`/`Bool.and_eq_true`, which are equality rewrite
  theorems, rather than the separate `_iff` declarations in the pinned source.
- Root's captured exact 239 context: `kind : Kind`, two variable identities,
  `h : kind = k ∧ identity1 = i ∧ identity2 = j`,
  `hc : Sub (ρ kind i) (ρ kind j)`, goal `Sub (ρ k i) (ρ k j)`.
- Root reports its first tool output was truncated and no full log file was
  preserved. The full line-595 mismatching term was unavailable. Those limits
  remain part of this receipt; no extra diagnostics are invented.

Source repairs in revision 2:

- Use retained binder `i` after the head-membership rfl substitution.
- Destructure the edge clause's kind and endpoint equalities explicitly before
  applying its original satisfaction proof.
- Write `Store.Satisfied ρ (store.filter ...)` explicitly; the theorem type is
  definitionally the same intended store predicate.
- Put every field of the three affected structure updates on its own aligned
  line. The intended fixture data and quantifiers are unchanged.
- Substitute the special mixed-use index explicitly and change to the exact
  expected equivalence before applying the shared copy witness.
- Rewrite Boolean observation goals/hypotheses with the pinned equality
  theorems, then use ordinary conjunction/disjunction elimination.

These are repairs from actual supplied diagnostics, followed by static source
inspection. The revised source has NOT been rechecked by this leaf. Root owns
that next execution; no claim that the errors are closed is made until its
actual run. All 65 authored theorem audit targets remain present. The generic
reverse owner-local publication theorem remains open; both the unclosed-layout
countermodel (not source-qualified) and closed mixed-level discriminator are
preserved unchanged in mathematical content.

## Governing source and unchanged parent

Read root AGENTS, relevant pre-sprint proof-closure/authority/communication
clauses, `rules/goal-driven-sprints.md`, `rules/design-authority.md`, the Lean
proof skill and its source/execution references, the selected contract,
current state, agent-loop README, actual Lean definitions and project pins.

The original paper is Parreaux, *The Simple Essence of Algebraic Subtyping*,
PACMPL 4/ICFP, article 124 (2020), local original
`/home/momota1029/rust/simple-sub-reference-paper.pdf`, SHA-256
`5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`.
Read §3.5.1, Figs. 11–12 and §5.3.1–5.3.2 by `pdftotext -layout ... -`
through captured stdout; exit 0, no extracted file. Fig.12's positive seed is
under the original seen context. No equivalence between recursive paper syntax
and this finite structural constraint algebra is presumed.

The authoritative inference principles §§1–3 preserve generation, accumulated
bounds, propagation, levels, extrusion, intrusion and generalization. The
2026-10-24 immutable Value-birth-level correction §§2–6 remains binding for
intrusion qualification. The bound graph in this packet is a DIFFERENT graph;
only the generic finiteReach lemmas from `BirthLevelSCC` are reused.

Original A/B claim: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5, with that birth-level correction. The original supported sources,
scopes, complete Call/effects, correlated evidence and joint witnesses remain
unchanged. Research drafts supply locators and candidate equations, not semantics.

The four original roots remain
`YulangClosure.SourceProblem.InferenceSoundness`, `SourceScopedCoverage`,
`PrincipalCoverage`, `InferenceTermination`, in `Contracts.lean` §§128–154.
These are proposition definitions. In particular, principality still requires
the ORIGINAL `instanceOf`; mutual structural Sub does not supply it.
**Parent delta 0; roots 0/4; packages 0/5.** No theorem is applied to a concrete
SourceProblem instance here.

## Constructed mathematical surface

All names below are in `YulangClosure.SimpleSub.BoundCycleR223`.
The source contains 65 authored-theorem `#check @...` / `#print axioms ...`
pairs, covering every authored theorem, including helpers. They are AUDIT
COMMANDS, not execution receipts.

`clauseEdge` matches only complete `.var i` / `.var j` endpoints. Kinds remain
separate. `connected` uses the existing finite Warshall closure. `quotient`
computes the least natural member by finite fold, with no choice of model or
extremum type. It fixes every coordinate outside n. The construction uses no
new axiom, Classical choice, proposition-as-acceptance definition or solver.

Candidate results include `quotient_idempotent`, `quotient_canonical` and
`quotient_exact_scc`. The exact SCC theorem has explicit allocation premises
`Generalization.StoreBounded n store`, `i<n`, `j<n`; this is not a bound on
substitution values or client terms. Its proof reuses finiteReach soundness
and proves closure completeness on the actual allocated edge endpoints.

`normalize n store` renames EVERY clause, then filters ONLY syntactically
reflexive variable clauses. Structural bounds, order, multiplicity and metadata
survive. `retained_clause` supplies clause membership for every nontrivial image.

The principal constructed types are:

```lean
solution_pullback (n : Nat) (store : Store) (ρ : Valuation)
  (solved : (normalize n store).Satisfied ρ) :
  store.Satisfied (fun k i => ρ k (quotient n store k i))

solution_pushforward (n : Nat) (store : Store) (ρ : Valuation)
  (solved : store.Satisfied ρ) : (normalize n store).Satisfied ρ

all_term_factorization (n : Nat) (store : Store) (ρ : Valuation)
  (solved : store.Satisfied ρ) {k} (t : Term k) :
  Equivalent (t.subst ρ) ((t.rename (quotient n store)).subst ρ)

solutions_and_all_terms (n : Nat) (store : Store) (ρ : Valuation)
  (solved : store.Satisfied ρ) :
  ∃ σ : Valuation, (normalize n store).Satisfied σ ∧
    ∀ k (t : Term k), Equivalent (t.subst ρ)
      ((t.rename (quotient n store)).subst σ)
```

Here `Equivalent a b := Sub a b ∧ Sub b a` uses the EXISTING `Sub`.
The explicit normalized witness is ρ itself. Store.Satisfied is the quantified
solution premise being transported, never an assumption that a CoreState was
accepted or a definition of solver success. The all-term result has NO
boundedness premise on t and NO restriction on ρ's values. Contravariance uses
both directions at both negative Function ports. `quotient_substitution` and
`factorization_after_substitution` express subsequent substitution composition
and preservation of both Sub directions under the same later substitution.

## Actual rows, levels and fixture application

`physicalRows` visits every row in zipIdx order. `rowClauses` retains BOTH bound
sides. `resolvedBounds` applies the actual one-step representative lookup to
all clauses. A missing representative entry falls back to its own coordinate;
this total helper is not a claim that such a state is valid. No equality with
`CoreState.retainedConstraints` is assumed or proved.

The bound-SCC `stateQuotient` is distinct from physical member map
`physicalClass = stateQuotient ∘ resolve`. This composition matters for levels:
`classLevels` takes the lower envelope over ALL physical members of that map.
`actual_class_level_le` proves every physical member's level bounds its class
level. `actual_class_minimum_at_fixed` proves the exact finite-fiber minimum
at an in-scope fixed physical representative. Arbitrary CoreState records have
no supplied validity/idempotence invariant for their existing representatives;
that native bridge remains OPEN rather than assumed.

`actual_anchor_preserved` concerns numeric below-boundary anchors only.
`actual_fresh_use_transport` transports all allocated term constructors for
every use through ONE valuation, using existing Generalization.freshen and
transport. NonGeneric flags, actual CorePublication captured lists and their
snapshot/current correspondence are not established by that numeric theorem.

Constructed discriminators:

- `self_upper_actual`: exact R212 inputValid and insertPendingUpper output
  for the emitted self-upper bound. This is one actual partial operation,
  not a completed accepted run.
- `self_upper_quotient_free`, `self_upper_all_terms`: the self class stays
  `.var 0`; the reflexive clause is removed; all-term factorization uses
  reflexivity of the retained store.
- `upper_only_actual_and_preserved`: exact existing R212 upper-only output;
  `.var 0 <: .atom 0` survives.
- `two_cycle_free_external_preserved`: two rows map to one free class and the
  external atom bound survives.
- `duplicate_physical_bounds_and_levels`: representatives `[0,0]`, unique
  upper bounds on BOTH physical rows retained in order, physical members both
  class 0, levels `[1,0]` give class level 0. Row 1 is not dropped.
- `recursive_function_all_ports_and_kinds`: recursive Value Function with all
  four ports and distinct Effect coordinates; an independent Effect self-cycle
  is removed while the external Effect bound survives. No cross-kind SCC is
  invented.
- `mixed_level_shared_anchor`: actual row levels `[0,1]`, class level 0,
  separate old copies 3 and 5 both transport to shared anchor 0.
- `mixed_level_two_use_factorization`: all-Term factorization for both uses
  under the FULL-copy Generalization.usesStore relation, with one valuation.
  This result alone is not actual owner-local publication.

Term scope includes var, rigid atom, extrema, union, intersection, Function
(-,-,+,+), all record label/optional metadata, tuple order, variant tag/payload
order and both kinds. No accepted source constructor is removed from the
parent. Recursive types are represented by stored finite variable bounds here;
paper recursive-syntax equivalence and regular-graph decoding are still open.

## Exact owner-local publication blocker and surviving discriminator

The missing reverse-publication premise is material, not administrative.
`mixedBounds = [lowToHigh, highToLow]` stores:

```text
physical x=0: level 0, upper [var 1]
physical y=1: level 1, upper [var 0]
root y; boundary 0; uses 0 and 1
```

The exact `ScopedPublication.Published` relation keeps both base constraints
but copies only active owner y's upper bound. Its additional constraints are
`copy0(y) <: x` and `copy1(y) <: x`. Owner x is stopped; its bound is not copied.
Thus FULL-store copying would add premises absent from actual publication.

`separatedUses` is a single explicit valuation:

```text
ρ(x)=ρ(y)=atom 0 ∪ atom 1; ρ(copy0(y)=3)=atom 0;
ρ(copy1(y)=5)=atom 1; every other coordinate remains its own Term.var.
```

`stopped_publication_separated_satisfies` constructs the exact Published
satisfaction proof. `sub_observation` supplies a Boolean observation sound for
EVERY existing Sub constructor; `union_not_left_atom` derives
`¬ Sub (atom 0 ∪ atom 1) (atom 0)`. Rigid atoms are not used as free variables.
No Top/Bottom model is selected.

`stopped_publication_no_joint_factorization` proves the exact failure:

```lean
¬ ∃ σ : Valuation, ∀ use, use ∈ ([0, 1] : List Nat) → ∀ k (t : Term k),
  Equivalent
    ((t.rename (ScopedPublication.fresh 2 mixedCapture use)).subst separatedUses)
    (((t.rename (physicalClass mixedLevelState)).rename
      (ScopedPublication.fresh 2 mixedAfterCapture use)).subst σ)
```

Already use 0, t=var 0 and t=var 1 force the same σ(0) mutually Sub with
both the union anchor and atom 0, contradicting union_not_left_atom. The
minimal footprint is two rows and one use; the required two-use fixture embeds
it. The class-level calculation is the actual physical `[0,1]` minimum 0.

**This is NOT a source-qualified counterexample.**
`mixed_bound_levels_not_closed` proves the low owner has a forbidden high
dependency (`1 ≤ 0` would be required). No actual accepted history is claimed.
The first missing native/source evidence is bound/level closure at publication,
preserved through representative merging and the real captured/nonGeneric guards.

Mixed levels themselves are not excluded. `closedMixedLevelState` stores BOTH
directions at high owner y: lower `[var 0]`, upper `[var 0]`; low x has no bounds.
It has IDENTICAL extracted constraints and the same quotient/class level.
`closed_mixed_bound_levels` constructs the level-closure proof.
`closed_publication_supplies_mixed_store` derives, from actual Published
constructors, all premises required by the full-store discriminator.
`closed_publication_joint_factorization` therefore supplies the all-Term,
two-use, one-shared-anchor factorization for that actual owner-local relation.
No supplied Store.Satisfied premise is substituted for the Published bridge.

The surviving results do not establish the generic reverse-publication theorem
for arbitrary closed bounds, nonGeneric captures or real publication histories.
The two layouts show why retaining only the extracted Store loses a real owner
premise. Do not report this packet as having weakened R223's theorem gate.

## Pinned dependencies and execution evidence

All listed original pins were rehashed before construction and matched:

| Input | SHA-256 |
| --- | --- |
| R222 equation artifact | `8435d2610df65be3e547eaedeff8796228dec78628143b1ffe95d982b58e143a` |
| R222 obstruction review | `50365f2c23498acaad58b3409b416bece545d9dd2a3990090f4fed66a397c1d4` |
| AbstractSimpleSubCore.lean | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| SimpleSubConstraintSyntax.lean | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| BirthLevelSCC.lean | `2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0` |
| SimpleSubGeneralizationSoundness.lean | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| SimpleSubScopedPublication.lean | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| lean-toolchain | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| lakefile.toml | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| lake-manifest.json | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

The project pin read from disk is Lean `leanprover/lean4:v4.35.0`, no packages,
project arguments `-j1 -M1024`. **Leaf execution: NOT_RUN. Primary revision-1 build: FAILED, exit 1,
with the actual reported evidence retained above. Revision-2 build, accepted
printed types and complete axiom dependency results: PENDING for all 65
candidates.** No claim of an empty axiom list is made. The parent explicitly reserved all execution/cache
ownership, so invoking the skill checker here would violate the exact packet.

Actual bounded commands were source `cat`/`sed`/`rg`, Python read/hash and
leased-file construction, `sha256sum`, `date -u`, and pdftotext-to-stdout.
The final source token scan command was:

```text
rg -n 'sorry|admit|^axiom|skipKernelTC|native_decide|unsafe' <leased Lean path>
exit 1, stdout '', stderr '' (no token matches)
```

This static scan is not an indirect-dependency axiom audit. An initial discovery
search used nonexistent `*R212*`/`*R222*` source-name globs; its missing-file
diagnostics were resolved by reading the contract's exact AbstractSimpleSubCore
path. Revision 1 had no leaf-owned Lean execution; the primary subsequently supplied
the actual failure diagnostics preserved above. Revision-2 repairs use those
diagnostics; the revised file still needs a primary-owned recheck. Initial
source-only changes such as replacing finite decide calls with rfl must not
be relabeled as checker-driven repairs.

## Exact next handoff and stop

Luna owns the next execution: resolve the installed native Lake, record both
actual versions, check the revision-3 exact output whitelist and 64 MiB cap,
build only `+YulangClosure.AbstractBoundCycleNormalizationR223:olean`, inspect
the first ACTUAL diagnostic, and audit every declared theorem. The module embeds
all 65 complete type/axiom queries; the skill checker can target these same
names if its temporary outputs are inside Luna's authorized envelope. No root
import edit or default build is requested. This leaf has no diagnostic repair
lease after freeze without a new primary handoff.

Mutual TODO **R223-OWNER-LEVEL-CAPTURE**, owner Luna to assign: preserve bound
ownership, establish real publication-cut BoundLevelsClosed and captured/
nonGeneric/representative coherence, then construct the generic reverse
owner-local publication factorization using one valuation. Required falsifier:
retain both explicit layouts above; never silently replace Published by full
usesStore. Mixed-level inputs remain required. Inputs: actual CoreRow,
CorePublication and ScopedPublication definitions; output: checked generic
construction or a source-qualified counterexample, not a newly assumed law.

Mutual TODO **R223-FIG12-GUARDED**, owner future readout lane: connect the
constraint transformation to literal recursive Fig.12 semantics and guarded
graph/reference decoding while retaining all structural spines. This packet
only supplies a prerequisite to the R212/R222 guard obstruction; it does not
remove the original guarded-readout blocker.

Mutual TODO **R223-PARENT-BRIDGE**, owner original source/native proof lanes:
authenticate generated constraints and retained-store/row correspondence, then
apply the SAME original scoped witness and instance relation to the unchanged
SourceProblem roots. All four remain open.

Resource envelope: ≤1800 seconds for this leaf; no measured CPU/RSS claim.
Only lightweight sequential reads and two leased text writes; no Lean process,
cache/generated output, scratch path, environment, dependency installation,
Rust/Cargo/test process, Git operation, child or external contact. Primary owns
resource integration, checking and independent review. Revision-1 source freeze was observed at `2026-11-01T22:01:13Z`;
revision-2 repaired source freeze was observed at `2026-11-01T22:06:24Z`.
The repair grant is ≤1200 seconds; exact CPU/RSS were not measured.

**WRITES_STOPPED** after this revision-2 handoff; no descendants or outstanding
generated/scratch writes. Pending kernel checking, independent falsification,
review and primary adjudication. This is a frozen incomplete research artifact,
not self-certification or production promotion.
