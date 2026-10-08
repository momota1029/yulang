# Original Name evidence versus composed capture placement

Date: 2026-10-08
Status: non-authoritative bounded source/artifact derivation; producer-only, frozen on submission
Baseline: `3b126a98ba53ba4b0cb54237cbb847c6d13ce37f`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Scope: the two Name leaves of the fixed ReadInvoke initial/lookup branch
Full H-factor, representation selection, production implementation and gate closure: none

## 1. Result and governing construction

The selected construction retains the **original** `(b,edge)` Name payload. Its complete contextual slots therefore support projection of that same payload; no new evidence-equality lemma is needed to retrieve a retained field. The selected text does **not** identify `edge` with only the composed Resolve/Capture parameter map. Reducing the retained payload to that map needs the precise evidence and action law in §4. Neither evidence irrelevance nor failure of such a reduction follows from the inspected sources.

This resolves a distinction in [early evidence maps](2026-10-08-readinvoke-early-evidence-maps.md) §§3–5: the resolution proof tree is not an explicit Data-Name payload, and complete IF retention already keeps its original output evidence. The remaining question concerns deleting or reducing that output, not reconstructing the whole resolution tree. The phrase “typed use-to-binding incidence” in [prefix projection](2026-10-08-pure-read-prefix-projection-audit.md) §3 must be given one exact meaning before claiming either equality or an omission.

Exact governing inputs:

| Source | Sections / scope used |
| --- | --- |
| [Source-input construction](2026-10-07-call-input-construction-proof.md) | §3 introductory Name definition; §§3.1–3.2 Data-Name and Capture-Lambda; §4 source induction and syntactic whole-substitution |
| [Selected source-interface definition](../design/2026-10-08-call-source-interface-definition.md) | §§2–3 complete operand/evidence retention and actual scoped reference placement |
| [Source-interface construction](2026-10-08-call-source-interface-construction.md) | §§3.1–3.3 complete evidence telescopes, IF-Use and field projections; §§4–5 inserted original source derivations and Name/capture composition |
| [ReadInvoke definition](../design/2026-10-08-pure-read-call-result-constructor.md) | §3 initial/lookup formation retention |
| [Selected closure definition](../design/2026-10-08-captured-closure-constructor-definition.md) / [closure construction](2026-10-08-captured-call-closure-introduction.md) | definition §4; construction §4.1 original resolved read edge and current binding projection |
| Prefix projection / early evidence maps | projection §§3–5; maps §§3–5, especially the exact original Name edge omission frontier |
| HIR / candidate crosswalk | `module.rs` NameResolution, identity ownership and captured-local construction; `shadow.rs` structural carriers and ownership lookup; `shadow_candidate_source_crosswalk.rs` exact captured ownership/position checks |

The integrated [q1/a1 answer](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md), decisions 1–5, and [receipt](../../questions/2026-10-08-successor-generalize-root-policy/receipt.md) select a transformed displayable scheme with proved necessary additional information and source-free use. They do not select a reduced edge representation or authorize implementation. Dirty shared task/index/theory records are navigation only. The baseline and every direct dependency in §7 were verified byte-for-byte.

## 2. Explicit hypotheses and claim classes

Fix the original joint index `j`, telescope `E`, one actual Name use `u`, original root/binder/capture origins and the original assignment `xi=(nu,K,D)`. For captured `f`, retain its outer `(d_f,R_f)` root under the actual import into the step context. For `x`, use its actual post-entry/rebind Value binding. Neither endpoint equality nor source-position identity supplies these premises.

Assume a genuine finite acyclic resolved source derivation on source-input §4's envelope, with the actual Capture/Resolve edges, complete original binding certificates and shared dependency graph. Assume each relevant IF slot was formed by the selected insertion/reference constructors from those same operands, not from a matching endpoint. Syntactic action statements assume one supplied legal sorted substitution on the whole graph, preserving fixed imports and incidences. Semantic current/future use separately assumes the original valid world, binding membership, live guards and lawful event/evidence actions.

Claim classes:

- **Established inputs:** the selected source and contextual-slot constructors, within their independently supplied semantic contracts.
- **Bounded derivation:** full retained Name payload can be projected and locally reintroduced, with syntactic whole-substitution naturality (§3). This note has no independent review.
- **Candidate assumption:** the original edge evidence is completely represented by a proposed composed map and its specified evidence fields.
- **Conditional theorem:** reducing the Name leaf is lawful if the equality/action or evidence-equivalence premise in §4 is proved.
- **Open:** that premise for a reduced map, full retained ReadInvoke formation elimination, all other origin/suffix evidence, transformed-export sufficiency and production correspondence.

## 3. Derivation at the construction owner

Source-input §3 defines `Name(E,u)` by induction on the **actual resolution derivation**. Local resolution selects the declared binding; imported resolution follows a retained capture edge to its original binding. Its result is `(b,edge)`. Data-Name then takes precisely that result:

```text
Name(E,u) = (b,edge)
n_u = Data-Name(b,edge) : Data(E,name u,b.interface).
```

The source does not give a separate grammar or normalization equation for `edge`. In particular, “result of induction along edges” is not the equation “the result is only their composed substitution.” Capture-Lambda retains actual capture edges, original bindings, aliases and dependency order. It supplies no equality of alternative proof payloads.

The selected IF-Use forms a contextual slot containing the complete instantiated interface. IF construction §3.3 explicitly states that its projection recovers that interface and maps every evidence field to the same unchanged field under its dependent indices. Its Name case follows the actual Resolve/Capture chain, instantiates the same original interface and composes generated use inclusions. The full Call frame inserts the original source derivation. Consequently, for a slot constructed from this `n_u`, projecting its source operand and then applying Data-Name inversion yields **this same** `(b,edge)`.

Write `S_u(n_u)` for that introduced contextual slot and `P_u` for its specified operand/payload projection. On this constructor image:

```text
P_u(S_u(n_u)) = (b,edge)
N_u(P_u(S_u(n_u))) = Data-Name(b,edge) = n_u,
```

where `N_u` is the local Data-Name introduction with the original indices. The equality is equality of the displayed constructor and unchanged operands. It does not assert pointer identity, uniqueness of arbitrary derivations or equality of an unspecified opaque proof decoration. Additional independently declared evidence remains in the complete retained payload. A slot containing only a descriptor output is outside these hypotheses.

The original source-input §4 induction transports the binding/root and capture edge jointly. The resulting syntactic projection commutes with that action:

```text
P_(theta u)(theta S_u(n_u)) = theta(b,edge)
N_(theta u)(theta(b,edge)) = theta n_u.
```

This retains the same source role and binding evidence. Noninjective endpoint substitution does not merge distinct uses or roots. Arbitrary semantic/event restriction actions still require their original supplied laws; this syntactic equation proves none of them.

Thus a leaf certificate that literally retains the complete original `(b,edge)` and its lawful actions can supply this Name constructor without reopening the resolution derivation. This is local evidence retention and constructor reintroduction. It does not reconstruct the full q retained by ReadInvoke, prove that its other fields are eliminable, or show that retaining a complete imported binding certificate meets the transformed-export size objective.

## 4. The exact reduced-map premise

Let `rho` denote the actual resolution/capture derivation, `edge(rho)` its original Name evidence output, and `m(rho)` the typed map obtained by composing its actual Resolve/Capture substitutions. IF contextual inclusions may be composed alongside `m`; they are not automatically the same object as `edge`. Source-input describes the former evidence output, and IF describes the latter placement construction. Neither cited passage specifies an equation identifying them.

Two interpretations of the proposed `b_pre.read_f/read_x` must be distinguished:

1. If “typed use-to-binding incidence” retains `edge(rho)` in full, §3 already supplies the leaf projection/reintroduction. The composite map is an additional retained field or derived readout. No evidence abstraction has occurred at this leaf.
2. If that phrase retains only `m(rho)` and the binding/root/path conclusions, the source evidence has been reduced. The preceding derivation cannot invert that reduction.

For the second case define the reduced record explicitly as `k_u = (j,u,b,m,original sharing/source-role fields)`. A sufficient **candidate equality/action lemma** is an independently justified constructor

```text
recover_u(k_u) : Edge(E,u,b)
recover_u(project_u(b,edge(rho))) = edge(rho)
recover_(theta u)(theta k_u) = theta recover_u(k_u).
```

The first equation uses the original evidence equality, which must be specified; it cannot be inferred from agreement of target roots or endpoints. For every compatible later event restriction `r`, also require the corresponding square to commute with the original edge/binding evidence action. If the edge is static under restriction, that fact must follow from its original declared action; the world/membership certificate still restricts by its own law.

An evidence-equivalence lemma could replace literal equality, but must provide forward/back maps preserving every original Name/ME-Result consumer projection and their lawful actions. The selected closure construction §4.1 consumes the **original resolved read edge** and actual current binding projection `(v,r)`. A proof that its consumers depend only on `m` is therefore substantive. No proof-sensitive extra consumer is invented here, and no proof-irrelevance rule is assumed.

If an existing selected construction defines `edge := m` with exactly these indices, fields and actions, the lemma is definitional. The inspected governing passages do not contain that definition. This is a localized source-signature gap, not a repository-wide absence theorem or an actual separating source pair. The useful next supplier is the edge's precise type and action signature at its owner, not another model that starts by assuming the desired transition/evidence rules.

## 5. HIR correspondence and failure conditions

Production `NameResolution` in `crates/yu-hir/src/module.rs:414` contains `Resolved(DefId)`, `Parameter(HirParameterId)`, `Ambiguous` or `Unresolved`. `ResolvedExpr::Name` additionally carries occurrence, spelling/range and source range. The inspected `lower_leaf` selects a parameter identity or module definition by lexical lookup. It exposes no typed Resolve/Capture substitution, complete binding certificate, semantic evidence equality or lawful event action. `Resolved(DefId)` is a retained lexical target; this inspection does not establish every backend's runtime lookup representation.

The captured-local route retains `ShadowLocalBind` with occurrence, enclosing-root-branded local ID, initializer, continuation, captured `HirParameterId` list and range. Its source identity map additionally records the local owner of the inner parameter. The candidate captured crosswalk requires the callee's exact `Parameter(outer)`, argument's exact `Parameter(inner)`, `captures == [outer]`, matching local continuation and local parameter owner. It joins exact declaration/parameter/Call/callee/argument positions and requires no ordinary fresh-row route for the captured callee. These checks retain useful structural correspondence. `CaptureUseIncidence` explicitly declares lexical incidence only, with no typed capture transport or receipt. `SourceViewPremiseLocator` leaves typed paths, profile, joint constraints and admission unresolved.

One equality distinction matters: `NameResolution::PartialEq` compares Parameter ordinals, whereas `HirParameterId::PartialEq` compares enclosing root plus ordinal. The captured crosswalk pattern-matches Parameter and compares its IDs directly, preserving the owner check. Equality of the enum alone would be inadequate evidence of that ownership. Neither equality proves the semantic Name edge law. No compiler change is proposed.

Failure conditions for the §3 derivation are a slot that discards the original edge, changed original indices/sharing, missing origin evidence or replacement of the original binding by a shape-equivalent root. Failure conditions for §4 promotion additionally include a recovery map lacking the required equality/equivalence, an unaccounted edge consumer, or an action square that does not commute. A different output provider, false live guard or missing semantic binding membership cannot be repaired by either construction.

## 6. Coverage, checks, resources and next action

Method: constructor-owner elimination and exact source/artifact field correspondence. No independent operational oracle was used. The argument shares the selected constructor/evidence signatures and independently supplied contracts with the audited ReadInvoke route. A checker that encodes `edge := m` would assume the precise missing premise and prove only consistency of that encoding. No executable experiment, seed/range enumeration or mutation was run. No genuine counterexample or evidence-irrelevance theorem is claimed.

Coverage is the fixed two-Name early structural branch and the exact captured HIR crosswalk. Arbitrary semantic maps, event evidence actions, opaque binding interiors, recursion, effectful/computed callee cases, original Call/W/Z alternatives and later suspended suffix consumers are unverified here. The previous two audits left the evidence signature open; this assignment reduces its Name leaf to an explicit retained-field-versus-reduced-map choice and one recovery/action obligation. It does not repeat their proof-sensitive toy model.

Checks: read-only Git baseline/status inspection; SHA-256 and baseline/live-byte comparison of each direct dependency; scoped `git diff --check`; relative Markdown-link existence and trailing-whitespace checks; final frozen artifact SHA-256. No tests/builds, children, network access, Git mutations or additional output paths. Sequential lightweight shell/Python processes only; CPU/RSS and total wall-time were not measured. The packet supplied no numerical CPU/RAM/wall-time budget. Some initial captures were truncated and relevant governing sections were reread narrowly; no exhaustive search is claimed. Unrelated shared edits were preserved.

Recommended next action: have the primary supply or approve the exact original `Edge(E,u,b)` evidence/action signature and decide whether the proposed leaf retains it or reduces it to `m`; then independently review the matching §3 retention derivation or §4 recovery/action lemma. Full ReadInvoke formation remains a separate obligation.

## 7. Dependency snapshot and commit packet

All direct dependencies below matched the pinned baseline and live bytes. Historical dependency hashes inside them do not replace this snapshot.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/2026-10-08-pure-read-prefix-projection-audit.md` | `a629637bbae12a15e8d363d9f09f37cba05e7f2b290683aa782975f9b0d88ba9` |
| `notes/theory/2026-10-08-readinvoke-early-evidence-maps.md` | `9af02550663ca1ea4555c0f7725f70e10c589168498f69226a1c6813119d787d` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-hir/src/shadow.rs` | `5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f` |
| `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` | `e17ab376c46575fc780fe79412cedf147cce7542b8e7ea2f8e09017db360bd10` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-08-name-edge-projection-correspondence.md` only.
- Baseline SHA: `3b126a98ba53ba4b0cb54237cbb847c6d13ce37f`.
- Changed dependency hashes: none; final artifact hash supplied in the handoff.
- Review status: producer-only bounded derivation and conditional leaf reduction; no independent review, theorem/gate closure or implementation authority.
- Checks already run: dependency baseline/live equality and SHA-256; scoped whitespace and local-link checks; final hash. No tests/builds or executable semantic probe.
- Proposed one-line research-checkpoint message: `research: distinguish retained Name evidence from composed capture map`.
- Shared-record deltas intentionally left for primary/curator: record that full selected IF retention preserves the original Name leaf; reducing that leaf to a composite map still needs its exact recovery/equivalence and action law. Do not close full Early/H-factor, adopt an export representation or change canonical DAG status. Task/index/authority/question files remain untouched.

The producer stops writing before submission for frozen review.
