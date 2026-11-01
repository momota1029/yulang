# R226 design handoff — declared callback acquisition

Sprint/contract revision: R226 / 1, SHA-256
`514c6c40fbfcb5ee7980f0dca0846dc0dc7b11e1f083cbe02c6777680aca7ff0`.
Assignment/handoff revision: `r226-source-owner-design` / 1.
Baseline: `c4e263b923368c4c20fdaba95ddbe960f502b967`.
Worker: `/root/r225_source_owner_trace`, resumed for this exact R226 lane;
registered `researcher`; session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`.
Requested model/effort: `gpt-6.1-sol` / medium; observed model/effort: UNKNOWN.
Lease: precisely the proposal and this handoff. No descendants or coauthors.

Outcome: **candidate design plus source-native evidence**, incomplete acquisition.
No Lean theorem, original source judgment, complete interface/profile
constructor, executable counterexample, impossibility claim, implementation
authority or parent-premise discharge is established. Parent delta **0**;
roots **0/4**; packages **0/5**. Independent review is pending.

## Candidate and original parent

The companion Draft is
`notes/design/2026-11-02-source-callback-interface-acquisition-proposal.md`.
It proposes composing original declaration/formal/use identities with a single
symbolic source-use instantiation, forming the original complete callback
contract/profile there, and delivering that result to selected B before body
generation. It deliberately identifies which computations already exist and
which source equations still lack constructions. The mathematical proposal
does not use a native Rust graph as a premise for source soundness. Native
mapping/commutation is a later correspondence obligation.

The unchanged parent roots are in `Contracts.lean:128–154`. The relevant
original App is `OriginalSourceGeneration.lean:111–123`, with its original
five atoms, two checks, source children, viewLogic binder and full source
scope. Selected B comes from callback delivery §§2–3 and §2.1. The joint
Function/effect interpretation remains governed by compatibility boundary §8
and its candidate-source-owner section. Source role and entry remain separate.

## Established static source/native path

This path is grounded in the current source constructors and source-use
machinery; it is not a new test or execution receipt.

1. Actual annotated-formal source fixture:
   `my ident x = x; my apply (f:int -> int) = f 1; my answer = apply ident`
   (`crates/yu-solver/tests/candidate_annotated_function_formals.rs:93–103`).
   Its `apply` Name has a `ModuleDef` resolution. The exact callee occurrence
   supplies the artifact-qualified `DefinitionUseId`; collection records
   target provider, receiving source owner, use level and use component
   (`crates/yu-solver/src/lib.rs:1435–1469`). No solved shape chooses the
   declaration.
2. `LocalSourceNamedGroup.formals[0]` retains the formal's exact parameter ID
   and Lambda index (`local_source.rs:109–123`). The Lambda parameter retains
   parsed `f:int -> int` with its source owner/annotation position
   (`:1142–1182`). `SourceAnnotationValue::Function` contains recursive
   argument/result syntax and separate effects (`source_annotation.rs:125–160`).
   This is an actual declared Function-valued formal; no `F_cb` was supplied.
3. Source collection registers that exact owner/parameter/recipe position
   (`candidate_source.rs:1104–1116`). Formal annotation construction builds
   both polar terms from the annotation, sharing named rows by source scope
   (`candidate_effect.rs:1675–1714,1805–1878,2125–2204`). It publishes the
   negative domain `N_f^-` at `formal_domains[recipe_position]`. This is
   native constraint syntax, not yet the original complete Function meaning.
4. `admit_lambda_fact` selects that exact declared domain as its argument
   term (`lib.rs:11621–11634`) and places it in the positive callee Function
   (`:11760`). Capture recursively interns Function children
   (`candidate_scheme.rs:2227–2285`). After capture,
   `negative_formal_roots` retains encountered declared composite roots by
   their actual term (`:3096–3114`). Thus the declared domain has a concrete
   structural retention route; a totality/identity theorem is still required.
5. `route_candidate_graph` authenticates the target and captures its graph
   (`candidate_scheme.rs:4441–4466`). `instantiate_candidate_graph` freshens
   using the original use's level/occurrence/cause and retains an exact
   `FreshRoute` with use ID, provider, receiving owner, graph, rows and maps
   (`:4995–5061`). `prepare_candidate_fresh_use` gives equal source
   representatives one image, freshens only generic eligible rows, retains
   non-generic rows, and rebuilds all Function children using the same vector
   (`:4526–4613,4765–4782`). It also keeps scope/context/evidence remaps.
6. Therefore, when `j = route.graph.negative_formal_roots[N_f^-]` exists,
   the candidate native projection is exactly `route.retained.terms[j]`.
   It does not independently instantiate the annotated formal, search arbitrary
   Function nodes, or infer which formal is intended from numeric row equality.
   The raw/native projection is a concrete representation target for the
   source-acquisition equations; it does not constitute complete `F_cb`.

This route preserves a genuine useful fragment of the missing bridge. It does
not assert that the current completed native route is available during initial
literal-body generation. Existing source traversal generates argument body
actions before App Finish (`candidate_source.rs:1228,1270–1273,1280–1350,
1867–1923,2092–2113`). The new proposal cannot call that late route early or use
its final solved answer as the input to initial checking.

## Proposed early composition and exact missing equations

At declaration annotation construction, associate existing source coordinates
with the native rows/terms just constructed: owner, formal ID, annotation
position, structural path and value/effect coordinate. This association is a
constructor byproduct; it is not a new meaning of `beta` or a permission grant.
Storage/API remains unselected. A proof-level source elaborator can describe
the corresponding symbolic coordinates independently of Rust storage.

For a known declaration use, the proposed composition is:

```text
Name resolution -> exact provider and formal annotation coordinates
  -> one source-use substitution respecting ordinary generalization/sharing
  -> original source Function formation and original slot/profile formation
  -> expected callback boundary delivered to the argument before its body
  -> selected B; synthesize F_lit; check F_lit <: F_cb,u
  -> original App descriptor, carrier, Call/image and checking obligations
```

Repeated `'a` annotations share one source binder; all their images use one
`alpha_u`. A hole keeps its own source position. Omitted effect ports remain
symbolic, with distinct original port coordinates. Literal argument/result
variables remain independently synthesized. Ordinary constraints relate them
to the instantiated formal. Retain non-generic sharing rather than freshening
every variable syntactically. The proposal neither requires final solved types
nor silently rejects unknown callees; their contextual boundary rule remains
unresolved, outside the selected bounded B path.

The source-use substitution must commute with the existing generalization and
FreshUse operation. An early source coordinate cannot be allocated independently
and later replaced by a second route image. Factoring the declaration-owned
part before body generation, with the same use identity and source scope, is
E3; no theorem or current implementation provides that factorization here.

Likewise, a source coordinate is not a complete static slot template. Full
original `beta, Slots(beta)` must come from the original source formal's
Function/profile formation. `FormalPermission` retains certain concrete
negative-port source permissions (`candidate_effect.rs:422–438,1882–1970`),
not every symbolic/omitted profile path, actual receipt, provider, admission or
consumer. Their union cannot define the profile. No runtime receiver activation
is created during acquisition.

The Draft labels all remaining equations E1–E9. In dependency order:

- **E1, source declaration/annotation formation:** construct the original
  complete declared Function interface from original syntax/declaration data.
  Native polar terms are insufficient semantic evidence.
- **E3, source-use instantiation:** one symbolic substitution with the original
  generalization/non-generic conditions; later native commutation is a separate
  correspondence obligation.
- **E4, source Function/profile formation:** construct the original template
  and complete profile from the declared formal and transport them under that
  same substitution. Do not assume a supplied profile or derive it from rows.
- **E5, source App/Lambda contextual checking:** deliver E1/E3/E4's result before
  body constraints, select receiver Handler independently of parameter entry,
  synthesize the literal interface, and preserve original source judgments.
- **E6–E9, original App interpretation/checking:** connect the constructed
  boundary to all unchanged consumers detailed below.
- **E2, later native correspondence:** prove that the exact native annotation
  term, capture root and use projection represent the same source construction,
  including canonicalization/absence/refusal cases. It is not an abstract
  source-theorem premise.

No semantic equation is turned into an assumed `LocalLaws` field, arbitrary
Kernel admission or an already-resolved-interface constructor argument.
The exact first semantic blocker is E1/E4 at the declaration/profile owner;
the first scheduling/instantiation blocker is E3/E5. The path no longer rests
on a claim that current Rust has no annotation or application data.

## Worked original App use

For the literal variant `apply (\x -> x)`, retain `s` for that original App,
`c` for its resolved `apply` Name and `a` for the literal argument. This is an
unexecuted worked shape, not a claimed accepted fixture. The fixture with
`ident` establishes the declared-formal acquisition input; existing-value
adaptation must not be substituted for literal introduction.

`F_cb,u` is the known callee's formal interface; it is not `descriptor(s)`.
The latter is the entire original requested Function descriptor. The original
App keeps the inert carrier for `a`, fresh result obligations and jointly
resolved effects, under `viewLogic(s)` and the same source assignment.

| Original premise/check | Exact contribution and unproved equation |
|---|---|
| `descriptorFormation(s,c,a)` | E1/E3/E4 identify the correct formal; E6 must form the whole App descriptor using the original complete demand, and connect its formal/use to that identity. No equation sets the whole descriptor to `F_cb,u`. |
| `wholeArgumentCompatibility(s,c,a)` | B supplies the literal/formal completed-interface query. E7 must additionally show formation/admission of the actual whole inert argument and all its outcomes; an endpoint query alone is insufficient. |
| `completeCallCertificate(s,c,a)` | E8 must construct the same actual provider's complete invocation at its genuine receipt/world, retaining Value-entry `Force(D_arg) >>= B_receiver`. |
| `sourceCallIncidence(s,c,a)` | Existing source operands determine `CallOwner.application(s,context,c,a)` (`OriginalSourceEnvironment.lean:140–174`). E6 must join this owner to the acquired declared use. Shape coincidence is insufficient. |
| `callableImage(s,c,a)` | E8 must establish the complete same-invocation image, including return, pending/request suffixes and body observations. |
| `Checking .value c.returnedValue s.descriptor` | E9 must prove the original whole-callee check, connecting B's final query in that same derivation. It cannot assume that check merely because the argument satisfies `F_lit <: F_cb,u`. |
| `Checking .computation s.callableImage s.synthesis` | E9 must preserve the complete result/effect/readout check. |

`generated_application_ports` exposes those original checks;
`generated_application_checking` obtains one from supplied satisfaction
(`OriginalSourceChecking.lean:941–977`). They do not prove satisfaction or
acquisition. `PortReadout.application` (`:1255`) selects the returned callee
as the callable subject. `OriginalSourceCallerSchema` retains provenance,
without allocating the original bindings/contracts. None fills E1/E4/E5.

Keep one provider, carrier, receipt/world, source scope and assignment, and the
same correlated `nu,K,D`/joint witness across these equations. Joint Function
compatibility is not four independent port inequalities. Value entry retains
receipt/force/rebind/body; Computation entry retains its carrier for actual
body consumers. Both force and body observations, complete Call/effect/readout
obligations and the approved mixed-row scope remain open and explicit.

## Falsifiers and scope boundary

The proposal fails if any claimed input is selected from a solved Function
shape, the native domain is renamed a complete source contract without E1,
raw coordinates or permission lists are named `Slots(beta)`, the early map
freshens a non-generic/shared variable, the later route uses another
substitution, App consumes a different formal, or B receives the boundary
after body generation. It also fails if the expected endpoints replace literal
endpoints, receiver role comes from parameter entry, Call/effects/witnesses are
dropped, or a conditional descriptor/acceptance law is presented as proved.

Annotation/callback overlap, retained computation callback-formal acquisition,
unknown/inferred-callee contextual role selection, member/import interface
acquisition and general source acceptance remain unresolved. They are not new
rejection or annotation requirements. If defining E1/E4 reveals genuinely
different source meanings, return the exact alternatives to Luna. This Draft
selects no compiler API or source semantic alternative and authorizes no
follow-on proof or compiler change.

## Authentication and resource receipt

All fourteen explicitly pinned authority/Lean/Rust inputs matched the contract
hashes before writing. The three R225 evidence pins also matched:
contract `4d5cea5c80080f4fbe196ca7cba7312bfb88986b8736673388ddfa143ab913a8`,
proof stop `ef586f6af2e1c5233b2d4980533817c5dc0ae7badcf09308ccc4cbcab3fec511`,
owner trace `e58c149bace45d3738d039065b2a8e4cecbfd561d5d24cb88b65e5ff4a91b27e`.
R225 reviewed outcome hash:
`aeebeecfcd9baeef4db411ba16fa1a2c84655afa7cf936c3983382351f748c84`.

Supplementary direct inputs were hashed and compared byte-for-byte with the
pinned R226 baseline; each matched:

```text
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132  notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean
ced364cdbca6c19752e0aa2e36b1516f9337484a8c10323fd632fb81a04163d0  crates/yu-solver/tests/candidate_annotated_function_formals.rs
6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646  crates/yu-hir/src/module.rs
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3  questions/2026-10-05-function-effect-row-denotation/receipt.md
```

Checks were static source reads, SHA-256 authentication, baseline byte
comparisons and source locator inspection. No executable semantic oracle,
simulation, seed/range enumeration or mutation experiment was used. The
derivation is grounded in source constructors, independently of tests' reported
success; it is not machine checked. No Lean/Lake, compiler/Rust execution,
Cargo, tests, build/cache write, Git mutation, scratch file, new directory or
environment was used. CPU/RAM peaks and precise elapsed time were not
instrumented; no heavyweight process ran and work remained within the
1,800-second lane budget.

## Frozen delivery and commit packet

Writes stopped before submission; both outputs are frozen for fresh review.
The proposal's byte hash is sent with this handoff's byte hash in the runtime
receipt, avoiding a recursive file hash. Parent-premise delta remains 0.

Recommended next action: independently review the composition and E1–E9.
Admit no theorem packet that assumes the acquired contract/profile; select the
smallest original source-formation equation only after the proposal's exact
construction and authority boundary are adjudicated.

Commit packet: exact leased paths
`notes/design/2026-11-02-source-callback-interface-acquisition-proposal.md` and
`tasks/agent-loop/inbox/source-callback-interface-acquisition-r226-design.md`;
baseline `c4e263b923368c4c20fdaba95ddbe960f502b967`; pinned dependency changes:
none; status: candidate, incomplete, review pending. Checks already run:
static source/hash/baseline inspection only. Proposed checkpoint message:
`research: propose source callback interface acquisition`.
Shared-record deltas intentionally left to Luna: frozen hashes, stopped worker,
review adjudication, unchanged App premise/parent metrics, E1/E3/E4/E5 source
frontier and separate native E2 correspondence, Git/push disposition.
