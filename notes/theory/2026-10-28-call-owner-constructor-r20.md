# R20 Call constructor audit — missing semantic supplier

Status: frozen source-inspection result, revision 1; **MISSING_SUPPLIER / NO_SAFE_CODE_SLICE**. No new theorem, source-qualified program counterexample, native correspondence, independent review or production authority is claimed.

Author: `/root/call_owner_constructor_r20_proof`, sole writer; no descendants or coauthors. Requested model/effort: Sol/high. Observed actual model/effort: UNKNOWN. This is the assigned source audit, not an independent certification of the combined R20 result.

## Fixed parent and authority

Contract `CALL-OWNER-CONSTRUCTOR/20261028-r20`, revision 1, SHA-256 `0b19ec601ee40765fdd1f74235d0b6f35e0c6e195a4a032672f40c7358c410f1`; manifest SHA-256 `ebd5164460314d7b6a940e9a9caf2bbbe385c105bc8f4ff15f13e7daa9eec57d`; baseline `d33805eb5`. All 25 manifest entries matched before source inspection and again immediately before writing this revision. This authenticates bytes, not their semantic correctness or authorship.

The unchanged declaration is `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Here `x` is the original complete scope/shared package, written `xi=(nu,K,D)` in the sprint. The arbitrary source, generated constraint and satisfying solution quantifiers remain. No source form, annotation case, lawful allocation, foreign continuation, independent F1/FK1 case, complete consumer, provider alternative, effect or future is removed. Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization remain unchanged.

The pinned owner definition, `2026-10-07-original-call-owner-definition.md`, is Authoritative only for its declared paired static source-owner formation. It expressly preserves independent typed images, contributions and joint incidence. The pinned source manuscript begins as an unreviewed research manuscript and marks its later policies as candidates. It cannot supply blanket adoption of new source semantics.

**Authority locator gap:** neither literal rule label `C-Call` nor `J-Owned` occurs in the pinned original Lean modules, source manuscript or owner definition. The R19 outcome names these remaining obligations but does not state their rules. The pinned source-construction note §5, lines 182–208, cites `notes/progress/2026-10-06-source-call-generation-construction.md` §5 as the exact semantic Call template. That progress note is not in the R20 manifest and was not read. Luna was notified and directed this lane to remain within current pins. This artifact therefore gives an exact local construction obstruction; it does not certify conformance to an unavailable complete C-Call/J-Owned rule text.

## Stage 1 — actual source construction and inversion

`OriginalSourceSyntax.lean:305–354` defines the three names as distinct `AtomKind` constructors. An `Atom` retains kind, source site, complete local context and ordered operands; it has no certificate, semantic provider, typed port map or derivation field.

`OriginalSourceGeneration.sourceRules` (`:111–124`) constructs App as a view-logic existential around a local App rule with:

```text
atom descriptorFormation       site context [callee.site, argument.site]
atom wholeArgumentCompatibility site context [callee.site, argument.site]
atom completeCallCertificate   site context [callee.site, argument.site]
atom sourceCallIncidence       site context [callee.site, argument.site]
atom callableImage             site context [callee.site, argument.site]
check value       (callee.site, returnedValue) (site, descriptor)
check computation (site, callableImage)         (site, synthesis)
```

Both child source trees are retained. The selected `roleAndInitialCallOrigin` is added only for `singletonFormalCall`; it cannot supply ownership for every App. A written annotation wraps this rule with its actual annotation boundary; it does not erase the inner App obligations.

This is construction of premise syntax. `OriginalSourceGeneration.Kernel.atom` (`:670`) is the interpretation parameter. `Local.atom` consumes a proof of that predicate. `Satisfies` interprets a local premise by `Local`, rather than constructing its proof from the atom name. The generic reconstruction theorem transfers an already satisfied formula into the corresponding independently defined rule grammar. It does not establish that native success satisfies the complete original meaning.

`OriginalSourceEnvironment.localCallOwner` (`:163–178`) reads the App's actual local `sourceCallIncidence` atom, requires exactly two operands, and constructs `.application site context callee argument`. `sourceCallOwners` traverses the source-generated tree. `Root.withSource` installs this static registry. `CallOwner.subject` selects `callee.returnedValue`, while its initial goal points to the distinct App descriptor. This is genuine syntactic source ownership, not a term-equality inference.

The consumer `Decoded.callOwner` uses the registered list, `Decoded.callSubject` reads its subject, and `Decoded.callRow` retains descriptor, value, root and event separately (`OriginalSourceEnvironment:328–335,534–542`). Logical-frame preservation retains this owner. Registration does not assert a semantic provider, source contribution, complete Call certificate, operation observation or native Function origin. The root App equations cited below are for an unannotated App at that root; this audit does not silently promote them to a complete theorem over all nested and annotated occurrences. Actual resolved-site legitimacy remains part of the original source correspondence, not a consequence of `Site := Nat`.

## Stage 2 — strongest constructor result and exact limits

`SourceSignatureConstruction.installCall` (`:639–646`) appends, in order, the supplied callee, whole argument, callee-return, receiver, returned and future nodes, then every supplied arm, then the actual Call node. The caller supplies complete node catalogues and local introductions. `CallRegions.addresses` assigns the corresponding ordered indices; no solver or inhabited license is used.

The source contains these declarations. Types below are transcribed from source with ordinary implicit parameters shown by their context. **They were not rechecked in R20. Their transitive axiom dependencies are UNKNOWN; historical checker receipts are not substituted for this packet's audit.**

```lean
-- YulangClosure.SourceSignatureConstruction.raw_call_static_incidence
-- context: Joint : Type
(graph : Graph Joint) (context : Context) (mark : Mark)
(callee argument : Source .expression) (regions : CallRegions Joint)
(locals : List (Introduction Joint)) (result : Catalogue Joint) :
  StaticCallIncidence (installCall graph context mark callee argument regions locals result)
    (callAtom context mark callee argument)

-- YulangClosure.OriginalSourceEnvironment.registered_app_subject
-- context: s : Sorts, View : Type
(root : Root s View) (context : Context) (site : Site)
(callee argument : Source .expression) :
  ((root.withSource context (.app ⟨site, none⟩ callee argument)).decoded.callSubject
    ⟨site, .invocation, 0⟩) = ⟨callee.site, .returnedValue⟩

-- YulangClosure.OriginalSource.generated_constraints_imply_source_judgment
{Value : Type} (kernel : Kernel Value) (environment : Environment Value)
(context : Context) {category : Category} (source : Source category)
(solved : Satisfies kernel environment (Build context source)) :
  SourceJudgment kernel environment context source
```

`installed_region_node`, `installed_call_arm` and `call_phase_incidence` preserve the actual registered nodes and phase edges, including every original arm index. `Catalogue.Packet` and `Introduction.License` remain arbitrary dependent fibers over the whole tuple. The module expressly does not supply complete C0, semantic licenses, authentic registration or correspondence from Rust allocations. `StaticCallIncidence.source` stores a graph lookup; it has no typed invocation/provider/consumer equation. `installCall` leaves the registration and whole substitution maps unchanged. It does not prove those supplied maps are authentic or legal.

The 2026-10-07 owner definition §§4–5 supplies paired lexical/checking `OwnUpper` facets from the same source/O0/seed attachment. It keeps `u_f` and `u` distinct. It explicitly supplies no lower/provider ownership, typed image, contribution, joint incidence, runtime receiver or provider validity. Its `Generic K-Incidence` boundary requires a separately supplied full typed source image at the same coordinate. This local positive owner construction cannot supply the missing lower producer or collapse lexical/checking/provider lineages.

## Stage 3 — semantic consumer and the first absent equation

The inspected semantic adapters leave the relevant three atoms untouched:

- `OriginalSourceInterpretation.literalKernel` and `nameKernel` (`:855–889`) interpret only authentic literal / selected ordinary-formal Name clauses; their else branches call `original.atom`.
- `OriginalSourceEnvironment.foldedLiteralKernel` and `foldedNameKernel` (`:965–980`) do the same after decoding. `admissionKernel` and `functionKernel` update admission / Function-shape fields, not the three Call atoms.
- `OriginalSourceChecking.kernel` (`:842–852`) installs finite primitive, structural and Function checking constructions. `atom`, original admission, direct conversion and tags remain supplied.
- `SourceSignatureConstruction.callAtom` names the exact generated `sourceCallIncidence` atom; no adapter in these inspected modules installs `StaticCallIncidence` as its whole semantic meaning. No complete certificate or callable-image constructor accompanies it.

Thus the first absent semantic supplier is the **original meaning and introduction/elimination of the complete decorated Call certificate at the very same source App tuple**, carried as:

```text
original.atom env
  (atom .completeCallCertificate site context [callee.site, argument.site])
```

The generation constructor emits this goal but does not supply its proof. The pinned construction note's displayed intended relation is `TypedCallCert_Dec(c,F_c,e;xi)` together with its original profile/operation/observation/correspondence premises. It is not a Lean definition in the inspected modules. There is consequently no supported concrete Lean theorem type connecting it to the native producer within this packet; inventing such a type would invent the missing interface.

Two coupled absent equations remain equally explicit: the full original interpretation of `.sourceCallIncidence` must identify the typed source image, owner and incidence at the correct lexical/checking coordinates; `.callableImage` must identify the original `ExecuteCallableImage(J_f,Delay(J_x),F_c,e;xi)` at the App callable-image port. The resulting trace must retain callee evaluation, inert whole argument, actual receipt, provider-owned entry, body, complete designated consumer, requests/pending suffixes and invocation return. Static region addresses alone establish none of those equations.

For source/native application, the required equation is construction-directed: the actual source producer's retained owner/registration and complete ordered port tuple, transported by the **same lawful whole-tuple action**, must equal the consumer's original typed owner/incidence and ordered tuple. Each of the four native Function positions needs its own equality, with value/effect sorts and polarity preserved. No four-position native readout is defined in these pinned Lean modules. This audit deliberately leaves that tuple schematic; Luna's parallel Rust audit owns its exact symbols and order. Establishing only the callee-subject equation is insufficient.

The semantic consumer is complete. `OriginalSourceInterpretation.FunctionAt` (`:418–427`) retains existence and universal quantification over actual providers, every independent checked challenge, actual admission, and every raw executed observation. `PhiV` retains every compatible later event. `Challenge` / `CallInput` retain context, foreign continuation, carrier/root/view, receipt, path, consumer and incidence. `CheckedDomain` and `ActualAdm` retain distinct checked/actual inlet relations and independent preconditions. `Inputs.actualTypedPath`, `actualContext`, `checkedIncidences`, `execute` and `checkedObservation` remain original suppliers. No one local frame action resolves independent F1/FK1 or foreign continuations.

`OriginalSourceChecking.generated_application_value_action` (`:1270–1301`) gives a same-callable descriptor action conditional on already satisfying the generated complete formula and already having the lower value membership. It neither introduces that membership nor constructs the three Call atoms. It cannot discharge the missing certificate by circularly assuming the generated solution already has its intended semantic Call meaning.

## Discriminating falsifiers

These are source-inspected separation arguments / requested falsifiers, not checked Lean results or counterexamples to the original supported-program theorem.

1. **Static support versus inhabited license.** Instantiate `Joint` by `Unit`; choose a catalogue with `Port := Unit`, `Packet := fun _ _ => Empty`, and primitive introductions with empty license fibers. Use such primitive nodes for all six `CallRegions` fields and any arms, and an empty original graph. `installCall` still appends every region and Call node; `raw_call_static_incidence` has exactly the same constructor application. There is no packet inhabitant at any port, hence no licensed field. This directly falsifies a proposed universal inference from that static construction alone to an inhabited typed packet / licensed contribution. An authentic original-source hypothesis might rule out some such input, but then its constructive proof is a separate missing premise; it is not supplied by the static theorem. This example asserts nothing about whether an actual original source program creates the empty-license graph.
2. **Equal endpoints versus same source owner.** `SourceAssignment.descriptor/value/root` are independent endpoint maps. Hold them constant while changing the actual `CallOwner.application` site/context or callee/argument source identities. The static owner data changes while descriptor/term-like readouts can agree. Neither endpoint equality nor matching descriptor shape recovers owner equality. This is an interface separation, not an assertion that arbitrary altered maps satisfy the original source rules.
3. **Ordered-port falsifier for a future implementation proposal.** At the actual producer and replay consumer, preserve the producer identity and all unrelated row/route data, but exchange the images of two distinguishable same-sort ordered ports (or supply a second distinct same-route producer with equal terms). A purported ownership proof must reject the first by the exact per-position equations and distinguish/reject the second using retained constructor ownership. Reconstructing an endpoint from polarity plus an equal term, counting matching graph nodes, or accepting a native solve cannot decide these equations. This is a requested discriminating check under a future lease, not an executed mutation or claimed source execution.

## Application to the unchanged parent

For an arbitrary `s,xi,d,a` in `SourceProblem.InferenceSoundness`, the source builder determines the App obligations and the static source owner; `installCall` can preserve a complete supplied static region inventory. These results remove the need to rediscover that **static** App subject from solved endpoints. They do not establish `p.solves d a → Satisfies concreteOriginalKernel env (Build context s)`, the full semantic interpretation of the Call atoms, or the original `sameScoped` witness. Consequently the reconstruction theorem has no newly established original semantic `solved` premise to consume. No existential source witness for the original parent is produced by R20.

The exact parent obstruction is therefore retained, rather than renamed as a conditional theorem: produce the authentic original Call certificate/incidence/image from actual source generation and actual native producer evidence at the same shared witness, lawful allocation and complete consumer, then prove their legal transport to the consumer with all four ordered native equations. Complete original C-Call/J-Owned source text also needs an authenticated pin before claiming a rule audit. The whole parent and source/native/effect-hygiene/production gates remain OPEN.

## Prior evidence, next owner and mutual TODOs

Reused: the pinned 2026-10-26 construction note's semantic Call template and explicit supplier boundary; existing static source-owner and graph-construction declarations at their actual premises; the pinned R18 outcome's finite four-row failure only as historical failed selection evidence. No R18 trace is used as a universal theorem. The pinned R19 review rejects endpoint reconstruction and records that the overlay adds no producer ownership; its incomplete diff review is not upgraded to full certification. R19's edited overlay is excluded from R20 source.

Rejected as completion: an atom name as its proof; graph membership as an inhabited license; `OwnUpper` as lower/provider evidence; one same-callable checking action as all foreign continuations; native success or finite trace as complete source satisfaction; equal terms as original owner identity.

- `R20-SOURCE-CALL-SUPPLIER-1` — parent: original InferenceSoundness / Call shared witness. Owning source symbols: `sourceRules` App, `Kernel.atom`, the three Call atom interpretations. Required input: authenticated original C-Call/J-Owned rules and actual decorated constructor premises. Requested output: original certificate/incidence/callable-image introduction and eliminators on one tuple, with complete profiles, receipts, operations, consumers and futures. Falsifier: empty-license static graph or any omitted original consumer case. Luna must admit any new dependency/lease; this lane grants no code edit.
- `R20-NATIVE-ORDERED-PORTS-1` — same parent. Owner: Luna's parallel R18 producer/capture/FreshUse/replay audit; exact Rust symbols belong in that handoff. Required input: actual producer emission, same whole transport and actual consumer port projection. Requested output: retained producer identity and four separate ordered typed equations, or owner-specific NO_SAFE_CODE_SLICE. Falsifier: equal-term distinct producer, duplicate same-route node, or swapped distinguishable same-sort ports. Source owner registration alone is insufficient.
- `R20-AUTHORITY-PIN-1` — Luna intake. Required input: exact C-Call/J-Owned source rules; the already-pinned note cites `notes/progress/2026-10-06-source-call-generation-construction.md` §5. Requested output: authenticate the governing rule source for a later packet or confirm the exact alternate locator. No new read or authority was inferred here.

This assignment stops at the missing supplier. The next meaningful step requires Luna's authority/dependency decision and a producer-owned construction packet; another endpoint-selection lemma would leave the same premise untouched. Fresh independent review belongs to Luna. There is no authorized production code slice from this source evidence.

## Checks, dependencies, resources and cessation

Checks performed: read-only source/authority inspection with `cat`, `sed`, `rg`; SHA-256 authentication with Python 3 over the contract, manifest and all 25 manifest entries (no mismatches). An initial `python` hash command failed with exit 127 because that executable is absent; the same read-only authentication was completed with `python3`. This was not a proof/checker execution.

No Lean, Lake, build, Cargo, formatter, test, Git, compiler edit, central-state edit, external contact or descendant dispatch was performed. New theorem declarations: NONE. New proof terms: NONE. Pinned checker/version execution and theorem axiom audits: NOT_RUN by explicit contract. Transitive axiom dependencies of cited existing declarations: UNKNOWN in this packet. No historical axiom union is claimed as a fresh audit.

The exact 25 dependency hashes, sizes and roles remain in the authenticated R20 manifest. Key proof/source dependencies are:

| Dependency | SHA-256 |
| --- | --- |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalSourceSyntax.lean | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| OriginalSourceGeneration.lean | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| OriginalSourceEnvironment.lean | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| OriginalSourceChecking.lean | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| OriginalSourceInterpretation.lean | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| SourceSignatureConstruction.lean | `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` |
| Original Call owner definition | `0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110` |
| Source-generation construction note | `e9027e317deb5cd5c34cc3892f332a06910a6ff93f1890a82e59faf31d643283` |

The producer did not authenticate historical human/model authors; the pinned files retain their own authorship statements. Sole R20 artifact author is the worker identified above.

Budget: 450 seconds maximum. First clock observation: `2026-10-28 14:00:24 UTC`; first-command start/actual launch time UNKNOWN. Last pre-write clock observation: `2026-10-28 14:03:21 UTC` (177 seconds observed interval). CPU, RSS and total active runtime from launch: UNKNOWN. This packet uses no automated CPU/RSS measurement and makes no in-place model-switch claim. Exact output hashes and final observation are delivered in the frozen handoff/STOP receipt.

All new paths are exactly this note and `tasks/agent-loop/inbox/call-owner-constructor-r20-proof.md`. Scratch/generated paths: NONE. No unresolved descendant leases. Writer stops after creating and hashing these two final artifacts; they must remain unchanged under review.

Freeze-write UTC observation: `2026-10-28T14:06:44.653699+00:00`.
