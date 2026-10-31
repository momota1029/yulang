# Independent review — MODULE-SUPPLIER-NATIVE-CORRESPONDENCE/r1

Reviewer: `/root/module_native_semantic_review`, fresh nonauthor `compiler_referee`.

**Disposition: source receipt requires correction; proof receipt and both OPEN supplier conclusions accepted within bounded scope.** BLOCKING: 0; major: 2; minor: 1. No compiler defect or semantic counterexample established.

## Authentication and method

The reviewer authenticated the semantic contract `13ef212b621918137054906ad8c7624b21d8fc855a57635368f5424ae2cc4a04`, source receipt `b7ef38b3e841372b34176f582e991a3daddbc3f6de519b230c63cdb59193037b`, proof receipt `707358daa9abab9830a3a2da71f1d47cce04d6c612802ea344bdecec83a2de0b`, accepted package review `2accece307d35ccc8dfb67fd171fa24a3a37d62a16d7cc6b56934e07acad998c`, outcome `679e182608764dbc1e4f4e5c9048062c5985fd204c3cb190c3594fe32b414a5f`, manifest `6c2c9fe80b294518b6ea8c8995e28a1b2604c3bb5e43f28e301c388219eb2c0a`, generator `e2990124a88099298abc5279a751c68ab87fefb2d066b5831bc59ff6bc249202`, consumer `4b50306376d8bafb187d400db7d683a6abdcb0aebfec6341c28e58804d63a6c7`, governing slice contract `6ab211856d460e4c31fdcadd0f4c0576444444630eb9bcd380a53e4aec7f7435`, adopted authority `d5d03de8b80eb2792cc35690f3fc3c871f9704f4aee8df815bce40b1f49f9d4d`, selected candidate `f1971e53ef62a5b3d94897ca9774d67c021d21524d9774b14439748a00fee9eb`, and module-expression authority `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`. It also authenticated draft-note and r4a2 historical pins; these supplied no implementation evidence.

The reviewer independently read all 18 admitted pages through the pinned consumer before reading either semantic handoff. Each invocation exited 0 and emitted at most 4,096 bytes. No raw owner expansion occurred. Source claims below are checked against those pages and adopted authority.

## Findings and primary correction

**Major M1 — unsupported native index join.** Source handoff § inventory row “Definition registration / use resolution” says “pending target resolves through that index.” Page 006 shows `definition_by_hir_id` construction, but page 007 begins at `.get(&pending.target)`; the receiver and assignment introducing `target` are outside admitted coverage. The pages also do not show complete definition-record insertion establishing ordinal/table alignment. The exact equation `target = definition_by_hir_id[pending.target]` is therefore not established by this package. This is an evidence ambiguity, not a claim about unseen code. Correction: treat the visible lookup suffix as observed and retain receiver/assignment plus registration alignment as uncovered.

**Major M2 — dispatch predicate conflated with later validation.** Source handoff § inventory row “Action and route dispatch” says active-use plus active-root conditions select open-use, otherwise incoming. Page 003 selects open-use solely when the indexed use ID is in `active_uses`; page 012 then validates definition parent, active parent root and active target root. If an indexed use is active but validation fails, open-use returns an error; it does not fall back to incoming. Correction: indexed active use invokes open-use and propagates its validation failure; indexed inactive use invokes incoming; absent index performs no routing in this arm.

**Minor m1 — cause-validation page attribution.** The same source row attributes `cause.id == id` to page 010. Page 010 invokes `validated_route_use`; the equality guard body is page 009. Correction: attribute the guard to page 009 and its invocation/endpoint construction to page 010.

The frozen source handoff is preserved byte-for-byte. The corrections above govern this adjudication; they are not a replacement source receipt or new source evidence. No additional owner/page read is authorized by these corrections.

## Accepted bounded conclusions

The proof receipt correctly limits page-supported equations to retained identities, call arguments, branch guards and successful local stores. Pages 001–005 retain ModuleDef target/occurrence and action identity; Imported uses a separate lookup and does not establish the same source-constructor branch. Pages 006–008 show component assignments, receiver checks and retained use fields subject to M1. Pages 009–012 support cause validation and target-root to occurrence-value argument direction, while route/transaction meanings remain uncovered. Pages 011 and 013–015 show conditional incoming dispatch, target-ordinal graph selection, capture/freshening calls, receiving-owner selection and successful `FreshRoute` retention; capture, freshening, activation and route semantics remain uncovered.

Page 016 exports `CandidateGraphExport` through `root_scheme_positions`; incoming graph selection uses target ordinal. Their alignment and receiving-graph membership are unproved here. Pages 017–018 describe an observer returning `CandidateExport`, partial for nondefinition receiving roots; this does not establish actual graph-export correspondence.

`ModuleNameSourceTypingAndAdmission` remains **OPEN** at the interpretation of the actual occurrence as lookup of the genuinely formed typed entry under lawful `theta_C`, preserving the actual constructor, dependencies and branch-specific use/admission. The adopted rule supplies formation authority, not an automatic interpretation of native IDs.

`ModuleUseReceivingExportCorrespondence` remains **OPEN**. Even granting retained identities, the first unsupported semantic equation is:

`freshening lower = Phi_u(actual whole branch allocation root)`

with complete dependent fields, original scopes and shared witnesses preserved. Downstream routing realization and actual receiving-export joins remain open.

The adopted fixed Published derivation may supply mathematical premises; absence of runtime tags does not refute it. Neither handoff uses successful routing to manufacture its missing typed premise or closes a supplier circularly. No source-domain or quantifier narrowing is accepted. Both suppliers, parent/native/production gates, A/B, complete Call/effects, N-Transport and F1/FK1 remain OPEN. `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE` remains binding.

## Runtime and STOP

Read-only review: no file edits by reviewer, raw owner expansion, tests/builds, Cargo, Lean/Lake, Git, descendants or background work. First measured timestamp `1793163819.728941`; final measured timestamp `1793163878.7448695`; elapsed lower bound **59.0159 seconds**, plus unknown startup and final-report time. Requested role: fresh nonauthor `compiler_referee`; effective model/effort UNKNOWN. Full assigned 200-second charge applies.

**STOP.** The source receipt is not accepted as an exact inventory until the bounded corrections are carried in adjudication; the proof receipt and bounded OPEN conclusions are accepted.
