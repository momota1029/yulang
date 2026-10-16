# Receiving Function formal: original source supplier frontier

Date: 2026-10-16
Status: frozen bounded source characterization and conditional derivation;
bounded static `compiler_referee` review was CLEAN.
Original checked-source supplier OPEN. No source-invalidity conclusion, theorem
promotion, architecture choice, compiler edit or production authority.
Pinned baseline: `fae7be0c62f5df4660567fb91561523ccac41b20`.
Exclusive lease: this note only; static leaf, no further delegation.

## 1. Frozen objective, quantifiers and original binders

Keep the original component, interpreted by its selected source constructors:

```text
receive(f:Unit->alpha+) = let g=f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit)->[ctrl]Int
```

The notation abbreviates authentic resolved annotation/expression nodes. It
is not a claim that this text was parsed or executed in this investigation.
Fix the original Lambda L/formal x, annotation a/shared root R_f and scope S,
Name n_f, first Unit t_1/Apply c_1, unannotated binding b_g, Name n_g and second
Unit t_2/Apply c_2. Keep the original binder tree and coherent instance
substitution. `ctrl` names the resolved declaration, not identifier text.
The formal is Value(Function), with no outer computation annotation. Its
outer result row is omitted/open; the two concrete rows belong to alpha+.

Required supplier: construct an independently legal source derivation T for
that original component, with one joint interpretation/strategy for the
formal, c_1, actual ResultBind and c_2. Keep xi=(nu,K,D), original generated
A1/E1 and A2/E2, each fresh invocation-effect coordinate, annotation ports,
current worlds, actual providers and all scoped witnesses correlated. An
inference assignment cannot be selected again after observing a return.
Aliases retain their actual instance; real source instantiations retain their
original scopes. The desired result must supply the actual operands needed
by the reviewed Entry/Exec/Return extraction, not only an erased Function
shape or a conflict-free constraint graph.

Quantification retains arbitrary compatible original assignments, opaque or
nonliteral providers, their actual entry roles, captures/private contracts,
all admitted carrier/context alternatives, complete/pending observations,
responses, raw resumptions and finite future/reuse histories. An actual
Return uses that return's single z/current-world witness and both tagged
packet inputs; a pending/divergent prefix supplies no fictitious return.
This is not an assertion that every raw contradictory assignment is legal.
The supplier must establish the original checking clauses at the original
assignment; it cannot insert MODEL or T itself as the missing success premise.

The genuine external primitive/world/environment/lifetime laws L1–L5 in
[source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md)
§2 retain their scope. In a body-checking rule, the admitted formal's full
hereditary membership is the legitimate Parameter hypothesis; constructing
receive's Lambda requires body checking uniformly over its independent
admitted inputs. This note establishes neither an inhabited initial world
nor a concrete external provider. It does not replace full formal membership
with the existence of four Function coordinates.

Exclusions: no new guard, annotation, provider restriction, empty inherited
profile, independent marginal witness, changed actual/logical field ownership,
source-domain narrowing, eager per-constraint solving, production implementation,
source rejection, soundness/principality/F5 closure or runtime representation.

## 2. Exact governing source premises

The following existing results are reused within their actual boundaries:

| Governing section | Supplied result and retained premise |
| --- | --- |
| [Source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–3; construction §§3.1–3.3,6 | Independent Parameter/Name/Lambda/Call/Bind/checking schemas and scoped rule closure. One satisfying joint rule program yields a derivation; generation alone does not prove satisfaction of its L1–L5 clauses. |
| [Contextual Function](../design/2026-10-08-contextual-function-membership-definition.md) §§2–3 | Same actual Act(v,U,r), hereditary immutable binding, Return/Delay. Membership eliminates only after an independently admitted complete challenge is formed. |
| [First-call receiving profile](../design/2026-10-16-known-function-first-call-profile.md) §2 | Outer complete-call position and first-use correspondence. Actual execution requires original validity/admission/entry premises. |
| [Receiving actions](../design/2026-10-16-receiving-profile-introductions.md) §2; grammar §§4–7 | Actual current-carrier E, outer O and matching nested N instructions; original future-entry and two-input transport. Antecedent interfaces stay complete, with their independent laws. |
| [Source Application](../design/2026-10-16-source-application-checked-result.md) §§2–3 | Complete generated AppTarget at original c_1/A1/E1. Its guard-introduction table identifies original environment, context, admission, full provider, same-value and RE evidence; it does not prove native MODEL. |
| [Unit inlet construction](2026-10-16-written-unit-arrow-inlet-construction.md) §§3–5 | Actual Return/Delay Unit filling plus independent punctured-context/world/path and AE formulas construct the checked challenge. Its §4 explicitly distinguishes generated Phi_B^H from its satisfaction. |
| [Fixed first-Call forward theorem](2026-10-16-first-call-joint-forward-preservation.md) §§1–2,4–6 | Original full c_1 conclusion under an independent hereditary formal, compatible punctured caller context and ONE anchored MODEL. MODEL existence and solver-success-to-MODEL are excluded conclusions. |
| [ResultBind](../design/2026-10-16-source-result-bind-projection.md) §2 | Retain same J_z and logical Value(A1) proof separately, including every genuine installed/private contract. Does not establish eligibility or c_2 applicability. |
| [Source export](2026-10-16-runtime-function-result-source-construction.md) §§1–6; [callable-view handoff](2026-10-16-runtime-callable-view-construction-and-transport.md) §§1,3,7 | Extract Entry/Exec/Return from independently typed T. Neither supplies T from HIR/candidate success. |

## 3. First actual implementation stop: exact annotation noncoverage

This bounded characterization follows directly from the inspected functions.
For any authentic LocalSource containing the exact annotated formal above,
`CandidateInference::solve_mode` calls `candidate_source::preflight` before
`collect_candidate_mode_scoped`, both for ordinary and scoped modes
(`shadow_apply.rs:271–307`). Its formal branch starts
`preflight_formal_value(&a.ty.value, false)` (`candidate_source.rs:423–426`).

Expand that recursive Boolean check at the original annotation nodes:

```text
F0 at false
  argument Unit at true: no row, accepted
  result F1 at false: omitted outer result row, accepted
    argument [ctrl]Unit at true: <=1 row variable, accepted
    result   [ctrl]Int  at false: concrete is nonempty, rejected
```

`preflight_formal` at `candidate_source.rs:457–463` allows a present row at
false only if its concrete list is empty AND it has exactly one row variable.
The fixed nested result has its original concrete ctrl atom. Therefore
`preflight_formal_value(F0,false)=false`, the Lambda branch returns
`CandidateError::Unsupported`, and collection/solve does not produce a
CandidateInference for this exact constructor instance. This proof depends
only on the stipulated HIR annotation shape; no parser run or fixture is
asserted. Other earlier errors may also stop a concrete module.

The solver-side paired constructor agrees: `candidate_formal_annotation`
starts at Negative (`candidate_effect.rs:1191–1217`), Function results retain
variance, and `candidate_formal_pair`/`candidate_formal_effect_port`
(`:1120–1164`) reject a negative concrete row. Removing only preflight would
therefore leave the owning construction unsupported. These negative checks
are implementation coverage conditions, not selected source laws.

Consequences are separate:

1. The current native path does not cover this exact annotation. No actual
   successful native run for it was supplied or inferred here.
2. The original checked T still needs a constructive source supplier.
   Noncoverage does not discharge or refute that supplier obligation.
3. There is no conclusion that the original source is ill typed, that the
   receiving-action rules conflict, or that its accepted domain should shrink.
   Replacing [ctrl] with a variable, changing polarity or omitting a row would
   change the assigned source component and is not a proof repair.

## 4. Direct source derivation attempt and precise semantic stop

Independently of native noncoverage, the source-rule construction reaches
these genuine partial conclusions at one unchanged xi:

- Parameter/Name retains the supplied f's whole certificate and its actual
  decomposition. Selected receiving formation emits E/O/N and their original
  future-input instructions; formation supplies no live receipt or admission.
- Each literal t_i has the original ground Unit/Return proof. Delay retains
  that exact computation, lexical references and reify/scope evidence; the
  actual source diagonal has empty evaluation effect. The broader independently
  admitted whole-carrier domain remains intact.
- Source-interface formation constructs the callee/whole-carrier/receiver/
  return/future slots and pending Bind at their actual owners. Its incidence
  maps do not assert that arbitrary tuples satisfy the original guards.

The first unprovided semantic premise before eliminating f membership is
an independently valid punctured caller-context witness for c_1, including
Phi_B^H with the hypothetical `g:Value(A1)` and its actual c_2 obligations,
at the SAME original A1/E1, xi, paths, current world and scoped strategy.
The Unit inlet proof §4:177–225 states this premise explicitly. Allocating
that context's slots, retaining g's future constraint or copying an IF handle
constructs a schema; it does not prove Phi_B^H or world/history compatibility.
Full formal membership can then supply actual-U acceptance only after this
challenge exists. It cannot serve as its own challenge-admission proof.

For a native-to-source route, the first-Call forward theorem additionally
requires its ONE anchored MODEL: sigma(alpha) subset sigma(A1) over complete
decorated values, the original effect inclusions under the same xi, every
incident predicate and lawful canonical/copy maps. The reviewed theorem
explicitly does not establish this premise from conflict absence. The current
`NativeInterface` contains endpoints and demand; it contains no proof of that
joint source interpretation. Setting A1=alpha+, E1=E_R, choosing models per
Call, or postselecting sigma(A1) from returned values is not available.

**Stop:** this note has not constructed that context satisfaction/strategy
or the native semantic MODEL. They are independent source/model inputs of
the reusable first-Call theorem, not outputs of the receiving profile grammar.
Consequently that theorem cannot be instantiated here to obtain full c_1,
and no complete T for the pair of Calls follows. This is a precise unprovided
premise, not a counterexample to the conditional theorem or a new typing rule.

## 5. Both Call owners and the later-use frontier

| Original constructor | Actual native construction/consumer | Established correspondence and remaining evidence |
| --- | --- | --- |
| Formal x / n_f | `candidate_source.rs:594–608,619–625,650–656,715–748`; `candidate_effect.rs:1191–1231` | Authentic registration, Parameter endpoint, Value role, formal Name and annotation action; no OmittedFormal seed. Exact paired annotation is stopped as in §3. |
| Unit t_1,t_2 | `candidate_source.rs:853–869` | Unit value bounds and Bottom<=effect<=Empty generated at each original occurrence. A source Unit/Delay proof exists under genuine scope/license/world inputs. |
| c_1 | `candidate_source.rs:1008–1049`; `shadow_apply.rs:1531–1650` | Apply recipe authenticates its actual operands, A1/E1 and fresh invocation i1, retains NativeInterface before admission, then submits/propagates the demand. This is actual constraint generation/activation, not proof of complete Function/admission semantics. |
| b_g actual ResultBind | `candidate_source.rs:825–846`; `candidate_scheme.rs:1476–1500` | Unannotated Install retains initializer's original positive root/boundary. Source J_z additionally requires both current W_z and consumed-view result input with the same z; native root retention is not that proof. |
| n_g / c_2 | `candidate_source.rs:960–1005`; `candidate_scheme.rs:1515–1683`; same Apply owner | Ordinary mode routes the installed local through capture/FreshUse and bound restoration before root linking; c_2 then has its own demand/i2/A2/E2. Its source certificate and original instance/copy maps are not inferred from c_1 endpoints. Scoped mode explicitly refuses a Local-name callee before retaining c_2's Apply. |
| Public executable handoff | playground `lib.rs:142–153,189–280`; `runtime/program.rs:55,382–407`; `runtime/receiving.rs:22–42` | prepare runs candidate first; execute then discards it. RuntimeEvidence is Name consumption only; Lambda selects Value role and RootCompSchema supplies none for Value(Function). These are later import gaps, not suppliers of source T. |

Thus both Calls retain obligations beyond annotation support. c_1 lacks
complete source context/model/admission evidence described in §4. c_2 has a
further **scoped-mode implementation noncoverage** at the Local Name guard;
it also needs a source-level same-binding/instance and full complete-call
checking proof in ordinary mode. This latter statement is not an ordinary-mode
rejection finding or a claim that its code fails to propagate native bounds.
Neither Call executes in the actual current path of §3, so their constructor
analysis is conditional source coverage, not an observed trace after failure.

If generalization of the inferred A1 checking view is needed to identify the
actual n_g FreshUse, the accepted [local-result characterization](2026-10-16-first-call-local-result-view-generalization.md)
§§2–4 leaves the recursive checked-challenge/IF/observation projection OPEN:
the complete original d may retain hypothetical g:A1 in fixed dependencies.
This note neither assumes A1 eligible nor silently chooses a monomorphic source
replacement. A monomorphic derivation at alpha+ would not establish the actual
A1/FreshUse bridge. The selected ResultBind projection alone proves neither.

## 6. Economy audit, residual gates and one next action

The earlier source export and callable-view attempts are conditional on T;
repeating their metadata induction cannot affect this supplier premise.
The source-owner audit narrowed it to the original Value(Function) formal.
This pass changes method to exact constructor inversion and finds the earlier
negative-row coverage stop, with a distinct later Local-callee stop.

Classification under compiler-engineering's proof-obligation economy:
source/native semantic satisfaction and same-instance Call checking are A/B;
keeping their original domains is mandatory. The missing typed export is D
where the source constructor already owns a proved fact, but retaining a
certificate cannot manufacture the unproved source context or MODEL.
No stronger arbitrary-view C theorem is introduced. No third equivalent
export reconstruction is proposed, and no parent gate changes classification
or status because this obstruction was recorded.

One next action: primary assigns the exact negative formal-row construction
and preflight seam to the existing authoritative conformance/design owner,
with the fixed two-Call source unchanged and both genuine semantic premises
explicit; resolve that owner before another native-to-T supplier attempt.
A production repair requires its own authorized packet and independent review.
Original T, context/MODEL, c_2 correspondence/generalization, runtime import,
Catch/Initial/primitive embedding, soundness/principality and F5 remain OPEN.

## 7. Verification, frozen dependencies and resources

Static checks only: bounded `rg`, line reads, `git show`/`git diff` and Python
SHA-256 byte comparisons; no compiler/test/build/probe/network/benchmark and
no Git/index/ref mutation. One producer, no children, maximum three concurrent
lightweight static-read processes per batch. Assigned wall cap 25 minutes;
elapsed wall time and CPU/RAM uninstrumented. Requested normal Sol/high; observed runtime model/effort
metadata unavailable. Inspected pinned prover role has no model/effort pins and
pinned config defaults are gpt-6.1-sol/high; no override, hot reload or
escalation is claimed.
Primary retains sole executable verification, review and integration ownership.

All proof/code dependencies below are pinned at the assigned baseline. Initial
live-byte comparison detected the import-owner audit's review-status-only edit;
its semantic body was compared against the pinned object and is unchanged.
The table uses the pinned audit bytes, not that later review-status revision.
The two routing files also changed concurrently: their resident-loop prose
changed while their Sol/high defaults and absent prover model/effort pins
remained. These live changes are not adopted as a new packet or lease here.
All other listed live dependencies matched their pinned bytes at the final
check. Observed changed dependency hashes (baseline -> live):

- Import-owner audit: `d7183dd9a182dda11d4b139ea2a00c276978df574d35c86c6bd0eaf7a1e4a557`
  -> `4a6b3b9a17e64a63667c49842c1d4962b26949a26bc73dd4751a5f9406771948`.
- `.codex/config.toml`: `993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1`
  -> `7dc1e5d1814b41c87e3dfccc8663f035af0fd8fa3030c8c656725dfd2c98ebab`.
- `.codex/agents/prover.toml`: `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98`
  -> `508d33aaa06bdef3d12f74143fb881017a12627c08567b10143ce4b45663c049`.

The first fail-fast dependency comparison stopped at the audit edit; the
subsequent complete comparison covered all 36 dependencies. Dependency edits
made by this leaf: none. Source-shape and function-body coverage
is static, with no parsed concrete fixture, actual assignment, trace, source
admission, complete T or arbitrary native solver-history theorem established.

| Dependency at pinned baseline | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/agent-orchestration.md` | `8b418f8ed02606205ecdfedcf5da72dae074e1c799237b8cc034fdfbd71ab7a1` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-16-source-application-checked-result.md` | `c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076` |
| `notes/design/2026-10-16-known-function-first-call-profile.md` | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| `notes/design/2026-10-16-receiving-profile-introductions.md` | `401ac9eee69f27a863cd08ea24eea6fbbd3388ada9d5366bd5818ee966d73b6f` |
| `notes/design/2026-10-16-source-result-bind-projection.md` | `f943e28a57e1a18cb22ec3e63a892f08711a3422293a240b168ea6dba5a082aa` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-16-written-unit-arrow-inlet.md` | `c1795a909b74ff6baa9c3597a11a471783e23dec1b670ac5c8a8280efaa55ddc` |
| `notes/theory/2026-10-16-written-unit-arrow-inlet-construction.md` | `ce0846a783af6029c346a6bc82664bd920b6a46429601a4030dd656a3fb07099` |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` |
| `notes/theory/2026-10-16-first-call-checked-result-construction.md` | `89fb62b1fe9e10d6972a79f17399d4a0332cf57817bb06a07f5e054ecb4b9dfa` |
| `notes/theory/2026-10-16-known-function-first-call-profile-construction.md` | `7051eafe3221b97229a760e52639f6a5c329860175ded210e7953a77a395e42a` |
| `notes/theory/2026-10-16-receiving-profile-introduction-grammar.md` | `ec3375229f956d678c64003a43bdb68c70a77c6b8e614e9348bdca6bde9d5a8c` |
| `notes/theory/2026-10-16-first-call-local-result-view-generalization.md` | `a37cd471c26c9936118282afe2eec295380a02b5197159d787f7d3ef75a50b47` |
| `notes/theory/2026-10-16-runtime-callable-view-construction-and-transport.md` | `8a3abd17cd26162c689a592e3f855580663d53bead80e8904ac964a16e1dfcb0` |
| `notes/theory/2026-10-16-runtime-function-result-source-construction.md` | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| `notes/progress/2026-10-16-runtime-entry-plan-import-owner-audit.md` | `d7183dd9a182dda11d4b139ea2a00c276978df574d35c86c6bd0eaf7a1e4a557` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `tools/inference-playground/src/lib.rs` | `bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `.codex/config.toml` | `993d4c2a7743669b4c7a6c46f054c4caae492873f0a5f20a1ea566ebf9dea3c1` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-16-runtime-receiving-formal-source-supplier.md`.
- Baseline: `fae7be0c62f5df4660567fb91561523ccac41b20`; this leaf changes no
  dependency. Concurrent changed hashes are recorded in §7; revalidate those
  audit/routing deltas at integration. No runtime setting change is inferred.
- Review: bounded static `compiler_referee` review by
  `receiving_pair_referee` was CLEAN on this artifact at SHA-256
  `413c7639540d1fd5d4e0aa7643072d0014ffbb9ea855fdedf353d048403afd1e`;
  it confirms the stated conditional frontier and does not certify completed T
  or source invalidity.
- Checks already run: static exact constructor/rule trace, dependency hashes
  and live-byte comparison, local Markdown integrity; zero executable checks.
- Proposed checkpoint: `research: pinpoint receiving Function source supplier frontier`.
- Shared-record deltas left for primary/curator: retain T/native-to-source
  OPEN; record the exact negative nested result-row preflight/paired-constructor
  noncoverage and separate scoped Local-callee guard; preserve source validity
  as undecided, and keep source context/MODEL and actual ResultBind/FreshUse
  correspondence separate from runtime importer and metadata transport.

Writing stops at this frozen handoff. No shared-record, compiler or question edit.
