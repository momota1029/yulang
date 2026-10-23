# R349 primary source census — finite witness input

Disposition: **source correspondence and finalization-boundary check PASS
within the fixed K0 domain; W0 model existence OPEN.** This is a read-only
owner census, not the finite-model proof, an execution observation, or a
compiler defect finding.

## Authority, baseline, and exact target

- Branch: `research/simple-sub-intrusion`.
- Compiler-source baseline: `60cdd28a3941b42d89f9cb602711b4859d2b737b`.
- Census inspected after documentation-only admission commits `a16494600`,
  `3827e8e00`, and `a9021c780`; the ten direct solver sources below match the
  compiler baseline byte-for-byte (`git diff --quiet 60cdd28a -- <ten paths>`).
- Active R349 contract revision 3 SHA-256:
  `f2446b85c2661abdfb03ace13055d22e9ac82e2c5b068c161b6649b1aa807dbc`.
- User audit SHA-256:
  `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- Normative whole-language TeX, latest user-supplied revision SHA-256:
  `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.

This lane checks the actual ordinary `shadow-apply-candidate` path for R336
rev4's authentic K0 domain and R341's same-construction `C_s`, `H₀(S)` and
`NativeComplete₀`. Its result is only an input census for:

```text
∀ authentic s,S.
  ValidK0(s) ∧ CompleteK0Construction(s,C_s) ∧ NativeComplete₀(s,S)
    ⇒ ∃ρ ∈ Assign(R_S). ρ ⊨ H₀(S) ∧ Reifiable₀(ρ).
```

No source valuation is supplied as a premise. R348 transports an already
existing source solution; it does not prove that one exists. The source
correspondence reviewed below does not imply finite satisfiability.

## Frozen mathematical and source inputs

The revision-3 contract pins these exact proof inputs:

| Input | SHA-256 |
|---|---|
| R336 rev4 contract / proof | `080ab51650f88ddb7030e2a9bcb0ebfc9cc9b62de29204910e888365f7d03118` / `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973` |
| R337 J proof / source census | `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62` / `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a` |
| R341 source-retention proof / census / outcome | `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` / `729c224785d42ee3577351e6a001668fe97a17fb2323aa532f52bbc8a1be0eeb` / `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc` |
| R345 proof / census / outcome | `85f8def9fe6e3c07b249c279d14976a428cf15c2d3eba089dbc4f5770e16f8df` / `065fbcd824caa394c4b297159d1ea08925829ad7c608c2814a16e96a9df3126b` / `a8b9b75d41be900060d7ba593bb77aaec738a67674654b6c823e92fac18ac8ce` |
| R346 outcome | `25748200d206c375a2e450aff688f692a4bfc5537ef7ba3fdc953423006b6512` |
| R348 lift proof / source check / outcome | `c4ee2c3cf36301f77c5ea6c941e9257ef52ebca0fd3e90e016d8d0f46b5f3a99` / `61ff50a919ff37f58bf098b87d4044d24cc63f230591e5fa91fb105e8d948829` / `e35d8c6139404da015e981dbc3bc203ece85199b920ce481284df7b3166fe6fd` |
| Audit / newest TeX | `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895` / `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65` |

Direct production-source pins, all rechecked against the workspace at this
baseline:

| Source owner | SHA-256 | R349 use |
|---|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` | K0 constructor recipes, occurrence schedule, source action driver |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` | candidate run/finalization, typed admission/drain, diagnostics, Value dispatch |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` | representative/generation owners already bounded by R336 L0/R348 |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` | typed bound append, exact slot readback, replay |
| `crates/yu-solver/src/candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` | drain/replay-frame retention and acknowledgements |
| `crates/yu-solver/src/candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` | bound polarity and effect-conflict producer |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` | root-Link admission, component initialization |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` | ordinary candidate API, authentic mode and conflict exposure |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` | full Function term identity; structural interning is not a source-occurrence proof |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | registered formal identity and K0 caller coordinates |

## Authentic K0 formulas and their source owners

`ValidK0` is not “whatever the collector accepts.” R336 rev4 fixes one
authentic nonrecursive definition, empty outer environment, ordinary
candidate mode, and only Unit/Bool/decoder-valid Integer/String literals,
parameter Names bound by a surrounding simple Value Lambda, annotation-free
single-binder Value Lambdas, Apply, else-complete If, Group, and binding-free
Block/StatementBlock. The unused Value component allocated for a Name is not
its type; its semantic endpoint is the registered formal. Records, tuples,
variants, local bindings, annotations, modules/imports, recursion, roles,
members, operators, operations/handlers, and Comp are outside this domain.

The fixed Value carrier is finite terms over variables, `⊥V`, `⊤V`, the four
base atoms, finite joins/meets, and `Fun(A,EA,ER,B)` with contravariant
argument Value and entry Effect, covariant return Effect and result Value.
Effect rows are finite subsets of fixed Ω with inclusion; both pure endpoints
are ∅. The complete source formula inventory is R336/R341's `C_s`:

| Source form | Exact constraints retained in `C_s` | Source/admission owner |
|---|---|---|
| Literal e | `Atom(e) ≤ v_e`, `v_e ≤ Atom(e)`, `∅ ≤ ε_e ≤ ∅` | `candidate_source.rs:1558–1573`; `Action::Fact` to `admit_collected_fact` |
| Parameter Name e for formal aλ | semantic `v_e = aλ`; `∅ ≤ ε_e ≤ ∅`; no edge for the unused allocated Name Value component | endpoint registration `candidate_source.rs:1094–1137,1724–1741`; ordinary facts use the same admission path |
| Value Lambda λx.b | `Fun(aλ,iλ,rλ,v_b) ≤ v_λ`; `iλ ≤ rλ`; `ε_b ≤ rλ`; `∅ ≤ ε_λ ≤ ∅` | recipe `candidate_source.rs:2050–2070`; `lib.rs:11557–11700` allocates distinct entry/return Effect rows, admits ports and Function-to-Lambda edge; pure creation via `candidate_local_lambda_effect` |
| Apply c=f a | `v_f ≤ Fun(v_a,ε_a,κ_c,v_c)`; `ε_f ≤ ε_c`; `κ_c ≤ ε_c` | `shadow_apply.rs:4085–4158,4167–4270`; κ is the same fresh row in the demand and slot-2 Effect inclusion |
| Else-complete If e | every condition Value `≤ Bool`; every branch Value `≤ v_e`; every condition/branch Effect `≤ ε_e` | `candidate_source.rs:1632–1655`; `Action::ValueConstraint` and fact actions include both branches and all conditions |
| Group | `v_child ≤ v_e`; `ε_child ≤ ε_e` | retained `CandidateRelation::Group`, `candidate_source.rs:2038–2050` |
| Binding-free Block/StatementBlock | final Value `≤ v_e`; final and every evaluated prefix Effect `≤ ε_e`; prefix values are discarded | `candidate_source.rs:2073–2101` |
| Definition root | `v_body ≤ v_root`; no root Effect coordinate | `candidate_source.rs:2146–2167`; `Action::Link` executor at `2428–2432` |

Every concrete occurrence remains indexed. `ConstraintBatch::emit`
(`lib.rs:2146–2160`) allocates its occurrence identity and appends the fact;
`append_source_facts` (`candidate_source.rs:2220–2223`) schedules every
occurrence in its interval. Lambda/Group/Apply recipes are separate scheduled
actions. `step_candidate_source` executes the exact next action and increments
`frame.next` only after success (`candidate_source.rs:2360–2413`); its dispatcher
sends facts, links/value constraints, candidate recipes and Lambda recipes to
their actual admission owners (`2415–2464`). Term interning may share a
structural node, but it does not erase source occurrences or their receipts.
R341/R348 establish the same ordinary construction and coordinate identity;
this census adds no source form or source equation.

## Native bounds, work ownership, and completion boundary

The relevant physical bound interpretation is the R341 polarity rule:

```text
β(owner, Positive, item) = item ≤ owner
β(owner, Negative, item) = owner ≤ item.
```

`candidate_insert_bound_with_evidence` canonicalizes only under its existing
representative premises, picks the Value/Effect lane, appends the exact bound,
reads back the addressed physical slot and checks the complete `BoundKey`
(`candidate_extrusion.rs:702–875`). `bound_pair` preserves sort and polarity
(`candidate_effect.rs:484–498`). R341/R345/R346/R348 supply the bounded
arguments for live tasks, Function ports, replay children and final-state
owners; a receipt, memo, completion bit or compact projection alone is not a
logical formula.

The candidate drain runs synchronously: `run_candidate_typed_drain` loops
`step_typed_drain` to `Complete`, restoring its saved processing pair and
relation on return (`lib.rs:14235–14257`). Before the frame retires, Diagnostics
replays reachable effect conflicts, completes the diagnostic delta, records
replay witnesses and advances to acknowledgements (`lib.rs:14404–14416`);
R345/R348 audit the live frame/replay owners and final `H₀(S)` interpretation.
This is an owner-chain fact, not a general termination proof. `execute` runs
the SCC plan and then ordinary source schedules (`lib.rs:10637–10664`). The
candidate path subsequently executes field tails and calls
`finish_candidate` (`10672–10691`). `finish_candidate` checks unresolved active
field-tail selections and returns `finish_observations` data; it does not
discard solver diagnostics.

`NativeComplete₀(s,S)` retains R341's mathematical same-construction
predicate: authentic source collection/admission finished; target work and
its concrete K0 obligations are closed; and there are no typing conflicts.
It is not `run_candidate(...) == Ok`, `CandidateInference::solve` returning
`Ok`, `unresolved().is_empty()`, a zero-sized public projection, or a
pre-assumed valuation. In particular:

- `CandidateInference::candidate_conflicts()` explicitly exposes retained
  errors while documenting “Candidate conflicts never establish source
  rejection” (`shadow_apply.rs:2009–2012`). The candidate solve path calls
  `execute`, field-tail processing and `finish_candidate` and can return a
  `CandidateSolvedResult` carrying those errors (`shadow_apply.rs:1921–1932`).
- The `SolverErrorKind` inventory is `RecordMissingField`,
  `VariantMissingAlternative`, `IncompatibleEffect`, `CrossKind`, and
  `IncompatibleValue` (`lib.rs:4122–4135`). The K0 disposition for each is
  below. A finite model proof must still reason about all actual formulas in
  `H₀(S)`; error-freedom is a premise, not a finite-model algorithm.

## Conflict/error owner map for authentic K0

| Error class | Actual producer and K0 disposition |
|---|---|
| `IncompatibleValue` | `incompatible_value_shapes` recognizes a non-Bottom positive lower shape incompatible with the negative upper shape (`lib.rs:14494–14505,16494–16520`); `report_solver_kind` records/deduplicates the diagnostic (`16523–16575`). This class is reachable in K0 and is relevant to `NativeComplete₀`. Function/Function has matching outer shape and is decomposed into all four ordered child ports (`14948–14979`), so the outer local check does not replace port constraints. A conflict-free premise excludes an emitted incompatible-shape diagnostic, but this local check is not a completeness proof for finite satisfiability of cyclic/global bounds. |
| `IncompatibleEffect` | `candidate_effect_mismatch` only accepts a lower `Contribution` or `AnnotationMember`, with an upper `Allowance` or `EmptyNegative`, then records a conflict (`candidate_effect.rs:730–783`); replay reports it as `IncompatibleEffect` (`785–847`). Authentic K0 emits no effect labels/contributions, annotations, operations or Allowances; R337 J/source census pins default flow and no Allowance. K0 Effect formulas are same-sort row inclusions plus pure `∅` endpoints. Thus this producer has no authentic K0 seed under those premises. This does not authorize dropping symbolic Effect rows or their inclusion formulas from the existential model. |
| `CrossKind` | The collected-fact store reports mixed kinds and `lib.rs:11529–11550` records `CrossKind`. Every authentic K0 formula above has Value-to-Value or Effect-to-Effect endpoints, including the Function's tagged four ports. Hence CrossKind is excluded by the authenticated formula construction; no cross-sort relation may be introduced by a witness proof. |
| `RecordMissingField` | Produced by positive/negative record dispatch (`lib.rs:14593–14640`); no record source or record K0 constructor exists. Excluded by `ValidK0`, not by a claim that the global solver lacks this producer. |
| `VariantMissingAlternative` | Produced by positive/negative variant dispatch (`lib.rs:14528–14591`); no variant source or variant K0 constructor exists. Excluded by `ValidK0`, not by a claim that the global solver lacks this producer. |

This classifies the complete declared `SolverErrorKind` list for the exact
domain. It does not conflate errors with availability failures: malformed or
unsupported source, identity/resource exhaustion, deferred selections and
other `SolveAvailabilityError`/`CandidateError` paths do not certify a
completed conflict-free state.

## Theorem input versus API result

Source inspection verifies the identities and owners needed to state
`NativeComplete₀(s,S)` over the same authentic construction and actual native
rows. It does **not** find a single exported Boolean with that mathematical
meaning. The implementation has source scheduling, typed drains, diagnostics,
field-tail completion, and output projection as distinct steps. Therefore the
proof lane must use R341's exact predicate and the actual `S`, not infer it from
one API return or one empty list.

R348's reviewed correspondence can be reused only under its exact premises:
same source, source occurrence map, kind-tagged live coordinates, physical
bounds/work interpretation, and `NativeComplete₀`. Its result handles the
relation between an already-given satisfying source assignment and actual
state. It leaves the current existential construction open. For R349 the proof
must enumerate every Value and Effect row in `R_S`, including final native-only
rows, and verify each actual bound/work/frame clause of `H₀(S)`. The
`CandidateSolvedResult` output projection is not `H₀(S)` and supplies no
finite-reification witness by itself.

## Newest whole-language semantics boundary

The latest TeX distinguishes (i) finite certificate checking from the search
for a certificate, (ii) semantic domain from its implementation, and
(iii) finite principal output from the separate completeness result
(§§2760–3006). It defines the whole-language judgment over the elaborated
plan/packet, all source identities, complete Call graphs, effect/name/world
correlations and closed-root role evidence. Its function comparison requires
the same assignment and the same complete Call relation (§§969–995,
2547–2669); whole-IR preservation separately retains the App/Catch call
obligations (§§1459–1471).

R349's finite Value/Effect rows are the deliberately smaller R336 K0 solver
algebra. `H₀(S)` is not the TeX evidence-hole `H`, a semantic world, `Y_H`, a
complete Call graph, a finite certificate, or a search procedure. Even a
reviewed R349 PASS would supply only this K0 model/reification lemma; it would
not close BuildLocal, certificate-search completeness, Z/termination, Q1–Q8,
whole-language preservation, principal-package factorization, original A/B,
or production.

## Result, uncertainty, and handoff

No source-owner discrepancy, authentic additional K0 constructor, or
source-qualified completed-state counterexample was found. The source pins
match; generation, formula admission, diagnostic producers, physical bound
owners, typed-drain stages, and finalization are mapped above. Disposition:
`NO_SAFE_CODE_SLICE`.

The mathematical W0 target is **OPEN**. No finite assignment `ρ` has been
constructed here, no unsatisfiable authentic `H₀(S)` has been shown, and no
claim is made that every authentic source reaches a completed state. This
census only freezes the authentic source/formula/error/finalization reading
for the separately assigned constructive proof. No tests, builds, Cargo,
runtime probes, source edits, or user-document edits were performed.
