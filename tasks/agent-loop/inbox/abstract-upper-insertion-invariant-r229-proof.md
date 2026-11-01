# R229 constructive Lean handoff — revision 8

- Sprint R229 contract revision 2 SHA-256:
  `1d3ffff03cdeb6f1bbe06fb3f99fb563ebda3a2eb74b74e8c31ba401a425608a`.
- Assignment/actual worker: `/root/r229_upper_insertion_proof`; leaf, no
  descendants. Requested registered `lean_prover`; effective runtime model and
  effort metadata UNKNOWN to this leaf.
- Exact writes: `notes/theory/lean/YulangClosure/AbstractUpperInsertionInvariantR229.lean`
  and this handoff. No scratch files, generated/cache outputs, compiler edits,
  tests, Git, dependency operations, external contact or delegation.
- Outcome: **constructed, unchecked**. No kernel acceptance, axiom result,
  independent review, source/native equivalence or production acceptance is
  claimed. Luna is sole verification/build/cache owner.

## Authority, original claim and authenticated sources

Read root `AGENTS.md`, its base operating map, `rules/goal-driven-sprints.md`,
`rules/design-authority.md`, the Lean skill and its source/execution references,
current-state/README and R229/R223 contracts. Exact governing meaning remains
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3 and
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Original A/B scope
is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5:
every supported original source, lawful finite history and actual qualified
occurrence, retaining shared source scope/evidence and ordinary inference.

Read the original manuscript itself using `pdftotext -f 18 -l 19 ... -` and
`pdftotext -f 24 -l 27 ... -`, both exit 0, at
`/home/momota1029/rust/simple-sub-reference-paper.pdf`, SHA-256
`5ab2bd4122caee17c20134e4cbe8dc8a4848c142de1e576b5fd178aed8787698`.
Relevant sections: Parreaux (2020), §3.5.1, Fig.7, §5.2–5.3 and Figs.11–12.
The paper explicitly omits full constraining proofs and restricts its §5 proof
scope to non-let-polymorphic terms. Neither omission restricts the Yulang
parent. Research drafts and earlier import notes are provenance, not semantic
approval.

Inspected exact `Contracts.SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, `InferenceTermination` at
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. They remain proposition
definitions with original source/scoped/shared-witness quantifiers; no instance
is supplied by this module. Original parent delta **0**, roots **0/4**, packages
**0/5**.

All fixed dependency pins reauthenticated by `sha256sum` (exit 0):

| Dependency | SHA-256 |
| --- | --- |
| `AbstractSimpleSubCore.lean` | `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c` |
| `AbstractBoundCycleNormalizationR223.lean` | `65335f3b8c6834e1e1cd34429a8fd7330162648a62d532c3a45f44305b255aee` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

Material intake failure retained: contract revision 1 syntax SHA omitted `ce`.
The leaf stopped construction and notified Luna before any artifact write.
Luna froze revision 2, authorized continuation with its new hash and reported
state synchronization. No proof was constructed under the malformed pin.

## Constructed theorem surface

Frozen Lean revision 8 SHA-256:
`8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a`.
Revision 7 Lean hash: `644d7c6a8bc0dd43f25a3c8c7f5f581b1bd9c78ce2ea9b91d95bc2b21a8a2189`;
revision 7 handoff hash: `ba8d5f63b920b3250206bcdb787c704d49554af2f6956c47144e1baa1342d673`.
Revision 6 Lean hash: `74adc826285c135948cf46ac042ddf4b3541add4dbbca48cd2c3561f973f5099`;
revision 6 handoff hash: `5b2d4c4c3e8939b104a49812f4da6f1ec33bc4cae1329259b0248062a51606d3`.
Revision 6 was superseded before a requested build; no execution result is claimed.
Revision 5 Lean hash: `3b2abd3d555bcd6b26a51c45c2160524a9fa71945c7e6f004924d5a02c0d074e`;
revision 5 handoff hash: `8bf0b271d8ef262692c0e3d3a96cf4bb74913a14c8aa84ab9b05a118a563f76f`.
Revision 4 Lean hash: `69749427cfedd38895192a4ef9ba8efb6bc96769ce3564371e9af0d93222581e`;
revision 4 handoff hash: `ebdb62a64520466cf75567b717d9024f0b42954dedb5ba52be87ba58d7b5cad5`.
Revision 3 Lean hash: `efce6b2f53a2d389cff274cd8a2f69c19e59faaa7b41f35e27925b73d6a56a99`;
revision 3 handoff hash: `5abbaae296bd5b8d301ece0b2c3184b8aa200f08756206f679cbc17def61576a`.
Revision 2 Lean hash: `2696e8548bf4196015cdf5b152ee6cf5545aee1c7f3e26a7465668081cd35cb5`;
revision 2 handoff hash: `4626dd293545b6a6d5627325464c2753595716f9e75ec00674e9158014d82126`.
Revision 1 Lean hash was `c250693d717a5b32db9c4dd5dd26e9b05ad2a783054de277d92f0a63764371c7`;
revision 1 handoff hash was `1805e49f7b81c1ad663058f618c8ce9761668edb2bfffd0a6905dbb4b889148b`.
All names below have prefix `YulangClosure.SimpleSub.UpperInsertionR229`.
The exact authored types and proof terms are in the frozen module; each of its
37 authored theorems has a fully qualified `#check @...` and `#print axioms ...`
audit command at the end. These commands have **not** been executed.

- `History problem state` is an inductive finite history starting exactly at
  `problem.initial`, followed only by equations
  `before.insertPendingUpper = some after`; no invariant is a constructor
  premise and failed calls have no constructor.
- `successful_view` inverts the actual operation, preserving the physical
  representative lookup, upper term, level guard and original replay list.
- `history_invariant : History problem state → Invariant problem state`.
  Its derived fields are exact per-kind physical lengths and `List.range`
  representatives, original indexed level lookup, `nonGeneric=false`, all
  lowers empty, real dependency lookup with dependency level ≤ owner level,
  and `Perm (pending.map clause ++ physicalBounds state) originalConstraints`.
  Neither input validity nor a solution is needed for this storage induction.
- `rowsFrom_insert` gives one exact physical-clause insertion up to permutation;
  duplicates are retained. `step_invariant` proves replay empty from the
  inductive metadata, then conserves pending plus physical clauses.
- `no_opposite_replay` exposes the lower-list consequence;
  `resolve_identity` proves R223's identity fallback is harmless for all Nat
  coordinates; `resolved_eq_physical` applies it to physical extraction.
- `terminal_store : History p s → s.pending=[] →
  Perm (physicalBounds s) p.originalConstraints ∧
  Perm (resolvedBounds s) p.originalConstraints`.
- `terminal_normalized_iff` applies R223 `normalized_solution_iff` with the
  terminal permutation: normalized actual bounds are satisfied by `ρ` iff
  original demands are satisfied by `fun k i => ρ k (stateQuotient s k i)`.
- `terminal_all_terms` takes a solution `ρ` of original demands and constructs
  one shared `σ` satisfying `normalizedBounds s`, with mutual structural `Sub`
  between `t.subst ρ` and `(t.rename (physicalClass s)).subst σ` for **every**
  kind and structural term. This is the R223 `solutions_and_all_terms`
  application through the proved terminal permutation and identity resolution.
- `physical_allocated`, `resolved_allocated`, `resolved_bounded` derive
  allocation from `p.inputValid=true`, the history, and actual conservation.
- `edge_allocated` bounds each variable edge by its own kind's allocation;
  `reach_allocated`, `connected_no_phantom`, `class_no_phantom` exclude all
  unallocated same-kind coordinates from the class of an allocated row,
  including padding below R223's `max(valueCount,effectCount)`.
- `exact_physical_scc` applies R223 `quotient_exact_scc` with the now-proved
  store-boundedness and allocation premises.
- `class_minimum_real` applies R223 `actual_class_minimum_at_fixed` at the
  allocated, idempotent physical class, and proves every member of this fiber
  is an actual allocated same-kind row. Default-level padding cannot lower it.
- `stored_upper_closed` exposes allocated owner/dependency endpoints, real
  dependency lookup, the operation's level inequality and original dependency
  level, with no source/domain restriction on the stored upper term.

## Checks, coverage and exact remaining bridge

The project files were reread: `lean-toolchain` pins
`leanprover/lean4:v4.35.0`; `lakefile.toml` uses `-j1 -M1024`; manifest has no
external packages. Actual Lean/Lake versions and executable resolution:
**NOT_RUN by leaf**, as required by the fixed packet. Builds/checker/axiom
results: **NOT_RUN by leaf**. Luna must run the frozen module's `:olean` target
and bundled focused checker under the exact output whitelist and aggregate
64 MiB cap. Do not interpret source inspection or the audit surface as a
checker receipt.

Read-only exact API searches used the installed pinned
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/`
and `Init/Notation.lean`. Static `rg` inspection of the changed module found
only intended `#print axioms` matches for proof-hole/project-axiom/bypass
patterns. No `sorry`, `admit`, project axiom or checker bypass was authored.

Represented: both row kinds, all structural Term constructors unchanged,
Function's four ports including both effect ports, labels/optional fields,
tuple/variant order and payloads, arbitrary duplicate bounds, arbitrary finite
successful upper-insertion histories, unequal per-kind allocation and future
client coordinates. No extra typing, finite-language or closed-term premise.

Omitted from the transition domain: lower insertion, actual opposite replay,
extrusion, intrusion, equality/coalescing, publication/use, terminal solver
acceptance and source generation. No theorem asserts these absent transitions.
Remaining R223 blocker (2) is reduced only for this actual partial operation,
pending kernel checks and independent review. Extending the invariant to the
full lawful solver history is owned by Luna's next proof packet. Generic
owner-local publication/capture/query coverage and guarded recursive readout
remain independent R223 blockers. Original `sameScoped`, `instanceOf`, full
Call/effect semantics and source/native correspondence remain open; structural
`Sub` is not their semantic resolver.

## Actual failed-build evidence and revision 2 repair

Luna reported two actual Lake runs against frozen revision 1. The build failed;
synthetic `sorryAx` appeared through elaboration errors. No declaration was
accepted. Leaf did not execute those runs and does not invent command/version/
exit details absent from Luna's message. Material filtered diagnostics:

- line 71 dependent elimination failed at `demand.clause.1 = Kind.value`;
- lines 97–103 dependent `row` type was unknown in `Invariant`, causing the
  later unknown-Invariant and non-Prop existential cascades;
- line 142 permutation endpoint arithmetic did not normalize;
- line 206 the lookup equation had already rewritten the existential goal;
- later fallback/terminal goals cascaded from the unknown invariant;
- terminal all-term renaming was not recognized as `physicalClass`;
- `Bool.and_eq_true.mp` was unknown (the iff API is `and_eq_true_iff`);
- the allocation-to-scope and connected-reach goals remained open.

Revision 2 explicitly types `CoreRow kind` invariant binders; destructures
CoreDemand/Constraint before indexed Term elimination; normalizes insertion
index arithmetic; supplies the rewritten existential lookup by reflexivity;
uses the actual Boolean iff; exposes physical-class function equality; and
makes allocation-to-scope/reach-start reasoning explicit. Every statement and
source domain is preserved. A static source search still finds zero authored
`sorry` or `admit`; the reported `by sorry` was an elaborator-generated failed
proof, which remains a blocker. Revision 2 is **unchecked**, with no claim
that these repairs suffice. All 37 declarations still require actual diagnostic
inspection and complete theorem-type/axiom audit by Luna.

No mathematical counterexample or unsupported conjunct has been found.

## Actual revision 2 failure and revision 3 repair

Luna's actual frozen revision 2 build still failed with six local issues:
reconstructed existential lookup equations were already reflexive after cases;
initial extraction could not refold `rowsFrom` with a reverse simp rule;
metadata elaboration selected the updated row instead of the pre-update row;
case analysis on opaque `demand.clause.kind` produced an ill-typed dependent
generalization; and the out-of-range representative proof did not progress.
The successful-view low guard also remained mismatched after the earlier
existential-field error. No revision 2 kernel/axiom success is claimed.

Revision 3 gives reconstructed equations by reflexivity, proves initial
physical extraction empty with an explicit `change` and `rowsFrom_initial`,
fixes the metadata theorem's old-row arguments, and introduces
`physical_insert` over an independent kind binder before applying it to the
actual demand. Out-of-range representative lookup is now an explicit `none`
equality using `List.length_range`. The existing 36 conclusions are unchanged;
`physical_insert` adds one helper and its audit commands. This revision is
constructed-unchecked pending Luna's next run.

## Actual revision 3 failure and revision 4 repair

Luna reported build exit 1 with exactly one remaining error in successful-view
row lookup. Pending/lower/representative equations were reflexive after cases,
but the actual physical-row lookup still required `hg`; revision 4 supplies
that unchanged lookup proof. Every other earlier error was resolved in that
run. Remaining warnings were unused simp arguments, not source proof holes.
No acceptance or axiom result is claimed until Luna's next successful check.

## Actual revision 4 failure and revision 5 repair

Luna reported the remaining successful-view error at the preceding
representative-lookup field: that field also required its actual `hr` proof.
Revision 5 supplies `hr` before `hg`. Both lookups now retain the exact actual
operation equations; the pending and lower equalities remain reflexive.
The previous failed build is not acceptance evidence.

## Actual revision 5 failure and revision 6 repair

Luna's revision 5 build exited 1 with only the successful-view guard remaining:
unrestricted `simpa using low` generated visually identical quantified
conditions but a hidden type mismatch. Revision 6 restricts simplification to
the two exact Boolean-negation equalities, retaining the original `List.all`
expression rather than normalizing it to quantified dependent matches. No
new premise or cast axiom is introduced. Actual acceptance is still pending.

## Full matcher diagnostic and revision 7 repair

Luna ran read-only `lake env lean -Dpp.all=true` with no generated outputs and
identified the hidden difference: the guard uses
`CoreState.insertPendingUpper.match_1`, while the theorem's re-written match
uses `UpperInsertionR229.successful_view.match_1`. Revision 7 handles every
member of `ScopedPublication.vars upper` separately and cases on its actual
optional row lookup. Both matcher heads then reduce on the same constructor.
The exact successful operation condition is retained and no operation code,
matcher axiom or invariant assumption is added. Luna owns the next actual
build/checker result.

## Actual revision 7 failure and revision 8 repair

Luna's build showed the original guard had already simplified to absence of
an existential bad dependency (`low : ¬ ∃ x, membership ∧ check x=false`),
not a positive universal function. Revision 8 proves each dependency by cases:
a missing row or failed level inequality supplies exactly that forbidden
existential; an existing row satisfying the inequality gives the required
Boolean truth directly. This uses the original successful-call hypothesis and
retains the exact guard rather than assuming its validity. All earlier
locations were cleared in the failed revision 7 run.

## Resource and stopped-writing receipt

At revision 8 freeze, approximately 30 minutes of the ≤2,400-second proof
budget have elapsed; exact active runtime accounting is not exposed to the
leaf. Zero Lean processes, zero build/cache bytes, zero Astra, zero descendants.
All source and handoff writes stop with revision 8. Both leased paths are
frozen for Luna verification; no other owned outputs exist. Resume repairs only
on Luna's exact diagnostics and acknowledgement of the next revision. No
self-certification or review appointment is claimed.
