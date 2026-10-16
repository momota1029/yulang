# Receiving Function formal: original typed-source supplier audit

Date: 2026-10-16
Status: frozen research characterization and static falsification; bounded
static `compiler_referee` review by `receiving_pair_referee` was CLEAN at the
artifact hash recorded in the commit packet.
No source-typing counterexample, theorem closure, compiler change, architecture
selection or production authority.
Baseline: `fae7be0c62f5df4660567fb91561523ccac41b20`, branch
`research/simple-sub-intrusion`. Exclusive lease: this note only.

## Objective, authority and result

Determine whether the original constructors and existing retained HIR/native
records supply the independently valid T required by the
[callable-view construction](../theory/2026-10-16-runtime-callable-view-construction-and-transport.md)
§§1–3 and [source export theorem](../theory/2026-10-16-runtime-function-result-source-construction.md)
§§1–5, for exactly

```text
receive(f:Unit->alpha+) = let g=f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit)->[ctrl]Int.
```

Here alpha+ abbreviates the original explicit nested Function annotation,
as in the selected construction; it is not an unknown type variable assigned
that shape after solving. Ctrl names its authentic resolved family.

Governing selections: [source Application](../design/2026-10-16-source-application-checked-result.md)
§§2–4; [first-call profile](../design/2026-10-16-known-function-first-call-profile.md)
§§2–3 and its construction §§3–5; [receiving actions](../design/2026-10-16-receiving-profile-introductions.md)
§§2–3 and their grammar §§3–5; [ResultBind](../design/2026-10-16-source-result-bind-projection.md)
§2; source-Generalize construction §§2–3.3; source-interface construction
§§2–5. Top-level inference principles §§1–4 preserve ordinary constraints,
open unknowns and necessary safety. No selected language meaning is changed.

**Static falsification:** the exact explicit annotation is outside the current
`CandidateInference::solve_mode` preflight envelope: its negative nested
Function result `[ctrl]Int` contains a concrete member. Thus this candidate
entrypoint cannot already supply T or both native Call records for this exact
retained source. This is an implementation-envelope fact, not source rejection
or a contradiction to the selected source constructors.

**Unresolved supplier:** the selected rules construct the bounded local profile
actions and maps. They do not establish the independently valid formal-binding,
complete checking and hereditary environment premises needed to assemble T
from the retained native records. No impossibility of supplying those premises
is established. The existing [import-owner audit](2026-10-16-runtime-entry-plan-import-owner-audit.md)
owns the separate VM seam; it is not repeated here.

## First owners and exact retained fields

Fix one original source graph, Lambda L, formal x, annotation a, scope tree S,
shared formal root R_f and joint xi=(nu,K,D). Keep c1/f-read, g-bind and
c2/g-read distinct. Every row below requires those same original indices;
neither equal native endpoints nor spelling equality establishes that join.
Native rows describe the constructors' available outputs **when reached**;
the exact witness below stops at preflight before they run.

| Required premise/output of T | First source owner | Actual retained HIR/native field and remaining obligation |
| --- | --- | --- |
| Authentic L/x/a/S and two Calls | HIR lowering/`form_ordinary`, annotation parsing, original source Name/Apply | `LocalSourceExpr.{occurrence,source,scope,form}`, `LocalSourceParameter.{id,scope,annotation}`, `SourceAnnotation.{owner,position,ty}`, nested Function argument/result, row position and resolved concrete IDs; `LocalSourceBinding.{id,initializer,scope,annotation}`. These identify the original graph; they contain no independent membership proof. |
| Full formal contract and same actual callable under each admitted challenge | Parameter/Lambda and original immutable binding certificate, source-Generalize §3.1 | `FormalRegistrationInput.{owner,lambda,parameter,scope,recipe_position,native_root,role,entry_effect}`; `candidate_formal_annotation` forms paired native terms and `formal_domains`, with links 43/44. Those links do not themselves prove full Function membership, actual provider/world admission or whole xi compatibility. |
| Local E/O/N profile actions at receive's actual entry, original annotation permissions | Selected KnownFunctionReceive and receiving Enter/Val | Original annotation identifies Value(Function), outer omitted row and nested Ctrl rows. Native omitted-formal `DirectionalIntroduction` is created only from `omitted_formals`; this explicitly annotated formal is not inserted there (`candidate_source.rs:721`). That absence is not absence of its selected protection. The selected complete-call/action output needs a corresponding checked export; a scalar native row is not that output. |
| c1 full callee/whole-carrier/entry/consumer interface and M1 | Original formal Name/Result/Call, source-interface construction and selected first-call §4 | `FormalNameInput.{owner,expression,registration}`, `ApplySourceInput.{owner,expression,callee,argument,level,recipe,callee_value,callee_effect,argument_value,argument_effect,result,application_effect,checking,cause,formal_name,native}`. `NativeInterface` retains callee/argument/demand/result and their scalar effects. It does not contain the full original IF/Gen-Call-0 evidence tuple or actual provider decomposition. |
| c1 two same-return inputs and maps, followed by complete g binding | Actual Result and sequential ResultBind | Source result is `J1=Image(mu1,W1) union_tagged Image(rho1,V1)`, with one return z1/current world and complete `ValueMem_A1` plus environment proof. `Install` retains the initializer's positive endpoint. `LocalScheme` retains `{capture_region,id,root,boundary}`. There is no field here for W1/V1, their tags, mu1/rho1 or the complete binding certificate. This says what this inspected record contains, not that the complete source theorem is false. |
| g read/actual instance and c2 M2, with all original dependencies | Original Name/Alias or legitimate source Instance, then second Call | `route_candidate_local_run` captures the graph and prepares `FreshUse`; it retains rows/terms, scope, relation, effect, bundle, context and evidence remaps during restoration; `LocalFreshRoute` retains occurrence/local/graph/rows. These are useful native constructor maps. They are not a proved whole semantic binding/instance map on the original packet and xi. Name/Alias cannot be silently replaced by a new semantic instantiation merely because this native path freshens rows. |
| c2 return and later developments | Original c2 Result/Call and its complete interface | c2 needs its own W2/V2, mu2/rho2, dependent return/world and complete producer entry/body/designated-consumer recipe. Its `ApplySourceInput` has a distinct result/demand and no direct formal-name registration for local g. Equal endpoint shapes cannot supply these fields. Future input instructions retain their actual later producer/formal/annotation, not receive's permission. |
| Lambda body typing and complete invocation | Original Lambda under its full admitted formal binding | `admit_lambda_fact` builds native Function fields from argument/body endpoints and entry/body effect constraints. It does not retain a proof of body validity for every independently admitted original challenge or the complete source invocation interface. This is the remaining semantic constructor obligation, not discharged by native graph conflict absence. |

The source rules retain arbitrary valid providers, complete original guards,
opaque indexed/private contracts and every admitted alternative. Slot formation
does not prove their laws. In particular, no empty ambient environment removes
the universally admitted formal's actual contract or the g-binding obligations.

## Static falsifier and its exact domain

Hypothesis H is deliberately narrow: a `LocalSource` presented to
`CandidateInference::solve_mode` contains an annotated Lambda with the exact
explicit type above, and the Ctrl occurrence is retained as a resolved concrete
row member. No parser execution or source-admission certificate is claimed.

Let FV(v,p) denote `preflight_formal_value(v,p)` and F(t,p) denote
`preflight_formal(t,p)` at `candidate_source.rs:457–464`. Direct reduction gives

```text
FV(Function(Unit,F1),false)
 = F(Unit,true) && F(F1,false)
FV(F1,false), F1 = Function([ctrl]Unit,[ctrl]Int)
 = F([ctrl]Unit,true) && F([ctrl]Int,false)
F([ctrl]Int,false)
 requires row.concrete.is_empty() && row.variables.len()==1
 but row.concrete contains the original Ctrl ID
 therefore F([ctrl]Int,false) = false.
```

Consequently the annotated-Lambda test at `candidate_source.rs:424–427`
returns `CandidateError::Unsupported`. `shadow_apply.rs::solve_mode:289`
calls this preflight before `collect_candidate_mode_scoped`, session execution
or native Call-interface retention, for both scoped and ordinary modes.
Earlier refusals can only prevent reaching this test; they cannot produce a
successful candidate for H. No satisfying assignment or choice of xi changes
this syntax/provenance predicate. The operational pair constructor agrees with
the same envelope: `candidate_formal_pair:1119` rejects negative concrete rows.
That agreement shares the same restriction and is not independent semantic
validation.

The structural discriminator needs only the annotated formal and its nested
result row; both Calls are retained in the assigned source component because
the supplier claim concerns them. Removing a Call is unnecessary to make the
preflight false. This is a minimal failing *field path*, not a minimized
well-typed executable counterexample.

A separate downstream obstruction exists even if that annotation envelope were
lawfully extended: the scoped experiment's Apply walker explicitly returns
unavailable on a callee `Name(Local(_))` (`candidate_source.rs:1003`), which is
g at c2. The ordinary mode instead has a native local-use route. Neither route
establishes the original full semantic fresh-use correspondence. This audit
does not bypass preflight, run either route, or claim observed diagnostics.

## Lawful route to T and the exact remaining premise

There is a genuine conditional source route. Start with the original full
valid environment/formal binding under its independently admitted challenge,
primitive laws, original scopes and one xi. Use the selected first-call rule
to construct M1/profile applicability; use independent whole-Function checking
and the selected checked-result rule to establish c1; fill that same return's
two tagged inputs; extend the environment with the complete ResultBind packet
and its hereditary proof; follow g's legitimate original Alias/Instance map;
then type c2 and its own return before closing Lambda's complete invocation.
The reviewed export construction can then extract the plans from that T.
This does not assume export validity as an extra premise.

What is unprovided from the inspected retained data is the bridge establishing
those source premises: the original annotation/entry's complete formal binding,
MODEL/lawful-map applicability of c1's native demand, and the full ResultBind
to g-use/c2 correspondence with the same scoped xi and all original contract
fields. `shadow_apply::UNRESOLVED` explicitly retains SourceTypingAndAdmission,
CompleteFunctionInterpretation, WholeArgumentProviderCompatibility,
WholeTupleScopeTransport and GeneralizationAndFreshUseCorrespondence.
`PendingCallSupplier` names the complete registration, introduction, checking,
Gen-Call-0, whole-carrier and result/future suppliers. Authentic IDs or those
pending names do not prove the missing conclusions.

The candidate-envelope falsifier does not refute that conditional source
route, show the program untypable, or establish an information-theoretic
impossibility for a checked exporter. Conversely, selecting source receiving
actions does not prove the native bridge. The prior import audit and this
supplier audit leave their respective parent gates OPEN.

One recommended next action: assign the exact original-annotation-to-full-
formal-binding correspondence at `preflight_formal` /
`candidate_formal_value_pair`, retaining the negative nested Ctrl permission
and original challenge domain; consume its result in the constructive T lane
before assigning a dependent runtime exporter. Any code work needs a separate
explicit implementation lease. Repeating Comp-root observations or conflict-
free toy candidates cannot affect this first failing premise.

## Checks, coverage and dependency snapshot

Static only: targeted `rg -n`, bounded `sed` reads, baseline `git show`, and
Python SHA-256/byte comparisons. No tests, builds, executable probes, mutations,
network or children. No semantic oracle or random/exhaustive seed/range exists.
The attack derives the actual Rust predicate; it does not independently prove
the chosen source semantics. Its shared assumption is the selected explicit
annotation structure. Source parsing/admission, executions, generic alpha
holes, foreign laws, full Catch, general native MODEL, soundness/principality
and negative eligibility remain unverified. No code or cfg(test) edit.

At most four concurrent lightweight reads; zero heavyweight processes and
measurement samples. CPU/RAM and exact elapsed wall time were not instrumented;
the assigned wall cap is 25 minutes. No Git mutation. Review belongs to primary.

All direct semantic/code dependencies below matched baseline bytes at freeze.
The prior import audit changed concurrently only in review-status prose and its
commit packet; a baseline `git show` reread and narrow diff confirmed unchanged
technical content. Its observed live hash was
`4a6b3b9a17e64a63667c49842c1d4962b26949a26bc73dd4751a5f9406771948`.
This note uses its baseline hash, not the live review claim. HEAD advanced to
`d7e85a25f90d5ea23ee1c64e805d66c612aaa6f9` during the audit; the result remains
pinned to the assigned baseline and unchanged technical dependencies.

| Dependency | Baseline SHA-256 |
| --- | --- |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| source Application selection | `c9207625887d78aaccef988324e8505f6dd08fdfe076e0f564f8b7dca3c54076` |
| first-call selection | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| receiving selection | `401ac9eee69f27a863cd08ea24eea6fbbd3388ada9d5366bd5818ee966d73b6f` |
| ResultBind selection | `f943e28a57e1a18cb22ec3e63a892f08711a3422293a240b168ea6dba5a082aa` |
| callable-view construction | `8a3abd17cd26162c689a592e3f855580663d53bead80e8904ac964a16e1dfcb0` |
| source export construction | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| first-call construction | `7051eafe3221b97229a760e52639f6a5c329860175ded210e7953a77a395e42a` |
| receiving grammar | `ec3375229f956d678c64003a43bdb68c70a77c6b8e614e9348bdca6bde9d5a8c` |
| source-Generalize construction | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| source-interface construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| prior import audit | `d7183dd9a182dda11d4b139ea2a00c276978df574d35c86c6bd0eaf7a1e4a557` |
| HIR local_source.rs | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| HIR source_annotation.rs | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| solver candidate_source.rs | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| solver candidate_call.rs | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| solver candidate_effect.rs | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| solver candidate_scheme.rs | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| solver shadow_apply.rs | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| solver lib.rs | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-16-runtime-receiving-formal-source-supplier-audit.md`.
- Baseline: `fae7be0c62f5df4660567fb91561523ccac41b20`.
- Changed semantic/code dependency hashes: none. Prior import-audit review-only
  delta: `d7183dd9a182dda11d4b139ea2a00c276978df574d35c86c6bd0eaf7a1e4a557`
  to `4a6b3b9a17e64a63667c49842c1d4962b26949a26bc73dd4751a5f9406771948`;
  it is deliberately excluded from the proof dependency snapshot.
- Review status: bounded static `compiler_referee` review by
  `receiving_pair_referee` was CLEAN on this artifact at SHA-256
  `a153d54ca04cee83ca4351c3441e15eef4a7faff82301483d0566af9b8877241`;
  it confirms the bounded falsification and does not establish source
  invalidity, completed T or parent-gate closure.
- Checks already run: static predicate reduction and source-owner trace;
  20 baseline hash/byte comparisons; prior-audit delta inspection; local note
  integrity checks. Zero executable checks.
- Proposed checkpoint message: `research: audit receiving-formal typed-source supplier`.
- Shared deltas left for primary/curator: record the exact negative nested-row
  preflight mismatch, preserve the original source semantics, and assign the
  full formal-binding/first-result/g-use supplier bridge. No source/native,
  runtime import, architecture or production gate is closed by this note.

Writing stops at this frozen handoff.
