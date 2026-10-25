# R30 complementary source audit — frozen research handoff

Objective: audit the paper guard boundary for every `PaperExecutionSyntax.Value` constructor without importing a guard projection from a different grammar. Method: source comparison, constructor inventory and a minimal symbolic discriminator. Claim class: bounded source characterization plus an exact missing definition; no new theorem, semantic decision or production authority.

Baseline: mathematical/source `f7a8ade138d1abec51a204b36fe5e4b06f856ce9`; contract admission `b6f365d2a` supplied by primary (no Git query performed). Contract r1 SHA-256 `77d1512967f84808ea7bffe1a488e3b2d34b4aaa50ea3475a3753aa99236a3b6` matches current bytes. Author `/root/r30_source_researcher`; primary is sole adjudicator/integrator. This is a complementary producer report, not independent review. The sprint skill applies only as its bounded child packet; no team or descendant was started.

## Exact source facts and limits

All operational locators below refer to `docs/yulang-operational-type-safety-ja.tex` (O); source locators refer to `docs/yulang-source-type-safety-ja.tex` (S). These are frozen research manuscripts, not production semantic approval.

- O184–185 names actual data constructors, lambda and delay as guards and excludes cycles made only of aliases, roll or type evidence. O260–267 defines finite graph observation and the graph typing/guard requirement; O268 gives reference typing from Xi. These specify the intended criterion but supply no constructor-indexed edge/guard judgment.
- O151–164 supplies the full paper value grammar, including wrap, polymorphism and runtime continuation. O210–240 supplies introduction premises. Raw Lean syntax `PaperExecutionSyntax.lean:39–63` has 20 constructors; the matrix below has 21 rows because lambda's two modes are distinguished. Its `both` stores one Value, without explicit derivation fields; its raw `wrap` adapters are Computation fields, unlike the separate Adapter sort in the accepted HigherOrder grammar.
- O362–376 defines call entry stripping wrap before actual callable entry; argument adapter code has not yet executed at O376. This is a computation transition, not an explicit graph guard definition.
- O485–494 preserves underlying constructors under views and names graph-reference/type-application/view removal administrative. O1002–1006 names the corresponding shape arguments, including lambda/wrap at callable type and explicit continuation at Kont. Being a canonical callable outer form is not itself an explicit recursive-cycle guard classification.
- S133–135 admits guarded finite source SCC tables and forbids uninitialized computed-root reads. S1043–1068 computes finite lexical capture sets, including adapters and nested/delayed code; S1081–1084 registers closure/structure values before publication and explicitly does not prove all linker correspondence. S1104 retains the environment judgment for saved continuations. None identifies these capture dependencies with O's transparent graph edges or classifies every paper Value constructor.

## Constructor matrix

“Barrier” means a supported genuine data/code guard for one observation; it does not prohibit references inside the retained payload/code. “Transparent candidate” means evidence favors following the listed child, with the precise graph rule still absent. “No explicit decision” prevents promotion of that candidate to a paper guard theorem. Typed evidence listed is required evidence, not a claim that raw syntax already stores it.

| Value constructor (syntax line) | Recursive positions / references | Source-supported status and exact evidence | Evidence needed for typed observation | Does source explicitly decide guard classification? |
| --- | --- | --- | --- | --- |
| variable (40) | Binder index; no syntactic child. Can designate a recursive binder before substitution. | Alias, not a genuine barrier: O184–185; substitution/closed lookup O258–260. | Gamma lookup O215; actual simultaneous substitution and binder correspondence. | Alias cycles excluded; precise binder-to-graph-edge relation still required. |
| graphReference (41) | Heap lookup target H(r), not a syntax child. | Follow reference: O260,268; aliases must reach an actual constructor O1004. | Xi(r)=A and H(r):A, immutable lookup, guard descent. | Yes for following references; finite descent remains the open guard premise. |
| literal (42) | None; Literal inventory lines19–27 has no Value/code children. | Terminal base value O151,215. No recursive cycle can be carried by a literal alone. | Its corresponding base introduction O215. | Terminal status follows from no recursive positions; not a solution for another constructor. |
| tuple (43) | All element Values. | Genuine structural data barrier: O151,184,216,260. Payload refs retained without evaluating them. | Every component derivation, order and arity O210,216. | Supported as data; paper gives no enumerated graph-edge function. |
| sequence (44) | All element Values. | Genuine structural data barrier O151,184,217,260; finite sequence is required. | Fixed native List identity, element derivations, finite length O217. | Supported as data; enumeration not formalized. |
| record (45) | Every present field Value, including fields marked optional; label/presence are metadata. | Genuine structural data barrier O151,184,218,260. | Required-label presence, domain bounds and all present payload typings O218,1007. | Supported as data; absent-field behavior is not a payload edge. |
| variant (46–47) | Every payload Value; type arguments have no Value refs. | Genuine tagged data barrier O152,184,219,260. | Constructor/tag, arity and payload derivations O182,219. | Supported as data. |
| nominal (48–49) | Every payload Value; type arguments separate. | Genuine nominal data barrier O152,184,220,260. | Same declaration identity and instantiated payload template O126–130,220. | Supported as data. |
| lambda value mode (50–51) | Computation body, containing arbitrarily nested Value references; parameter binds locally. | Explicit code barrier O153,184,302. Do not unfold body to observe lambda. | Body B under x:A and receipt/profile evidence O160,222. | Yes for lambda; typed code/capture correspondence remains separate. |
| lambda computation mode (50–51) | Same body positions, with thunk parameter. | Same explicit lambda barrier O153,184,302. | Body B under x:UA O223; retained mode/profile. | Yes; mode does not authorize changing the cycle criterion. |
| delay (52) | Computation body and its nested refs. | Explicit code barrier O153,184,302. | Body A O221; finite closed code/captured refs O264. | Yes. Force may later execute body O307, without proving termination. |
| wrap (53) | function Value; argumentAdapter and resultAdapter Computations, each with nested refs and binding context. | **First unresolved constructor in syntax order.** O224 supplies typing, O366–376 strips function wrappers at call entry; O1005 calls lambda/wrap callable forms. None explicitly says wrap is a graph guard, that function is the unique transparent child, or how adapter-code refs count. | Inner C(A,B), outer C(A',B'), input code under z:A', output code under z:B O224; typed function observation if traversal is selected; capture/binder evidence for both adapters. | **No explicit graph classification.** Transparent function traversal and delayed adapter code is a plausible candidate only. |
| typeAbstraction (54) | body Value; adds a type binder, no term binder. | Type-evidence-only cycles excluded O185,1008; introduction O238. Candidate traverse body, not a new data/code guard. | Body typing under fresh type variable, freshness against D/Gamma, type substitution evidence O238. | Exclusion of evidence-only cycles is explicit; exact child/graph observation rule is not. |
| typeApplication (55) | function Value; type argument separate. | Administrative elimination O493–494; normalization O316,321; candidate traverse function then instantiate abstraction. | Polymorphic function derivation and simultaneous type substitution O238,1003. | Administrative status explicit; graph guard transition over arbitrary nested applications not defined. |
| injectLeft (56) | payload Value. | Candidate data barrier from O155,184 and introduction O233; paper's producer-alternative view interpretation O137–139 also applies. | Left payload derivation at A, retained union alternative O233. | No constructor-specific guard clause. Classifying this proof/view introduction as “actual data” needs explicit confirmation. |
| injectRight (57) | payload Value. | Same ambiguity as injectLeft O137–139,155,184,233. | Right payload derivation at B and union alternative. | No constructor-specific guard clause. |
| both (58) | One underlying Value; two typing derivations conceptually, not two separate payloads. | Evidence-only barrier disallowed O185; same-underlying-value O140,234; choose removes evidence O314. Transparent underlying traversal candidate. | Both separate derivations d1,d2 at A and B of identical raw v O234; syntax alone does not store them. | Not a genuine data barrier on cited evidence; precise graph edge rule absent. |
| roll (59) | underlying Value. | Explicit nonbarrier O185; unroll removal O235,315. Candidate follow Value while changing its type. | Derivation at A[mu a.A/a], roll/unroll type equality O235. | Yes that roll alone cannot guard; typed traversal relation still must be constructed. |
| topView (60) | underlying Value. | Erasable view O142; arbitrary underlying typed value O236; evidence-only cycles excluded O185. Transparent candidate. | Existential underlying A and derivation v:A, not a fabricated top payload eliminator O236. | Nonbarrier evidence supports exclusion; no complete graph rule. |
| view (61) | underlying Value; metadata contains identities/types/type args, no Value child (syntax32–33). | Underlying constructor preserved O239,489–494; administrative outer removal. Transparent candidate. | Underlying v:A, valid metadata/path evidence and preserved constructor/type; metadata retention alone is not live effect correctness. | Constructor preservation/removal explicit; its use in a graph guard derivation remains unformalized. |
| continuation (62–63) | Computation body with response term binder and owner binders; nested graph refs/captured environments. | Explicit raw runtime constructor O163,273,350–354,1006, but O184/260's guard list does not mention continuation. S1104 supplies saved-environment coverage, not a graph-cycle rule. | Body A under z:Q; owner freshness/binding scope O350–354; same graph for captured refs; saved environments S1104. | **No.** Code-barrier similarity to lambda is not authority to classify it. |

The first unresolved row is wrap after the explicitly named data/lambda/delay cases. Later unresolved rows remain recorded rather than being filled by the accepted research projection. For injections the data classification is deliberately a candidate: O137–139 describes union evidence, so the generic phrase “actual data constructor” alone is insufficient to claim an explicit row-specific decision.

## Minimal discriminating witness and derivation boundary

Candidate graph with one reference r and identity adapters:

`Xi(r)=C(A,A); H(r)=wrap(r, z.Return z, z.Return z)`.

By O268 the inner reference has C(A,A); by O224 both adapters type at A and the RHS has C(A,A). This is therefore locally payload-typed, conditional on ordinary identity-code typing. If wrap is a guard barrier, the single-node cycle is accepted. If its function child is transparent, it is rejected. O372–374 unfolds call entry into another enter of the same function reference before the result adapter can execute. That distinguishes the operational consequences, but does **not** establish rejection under a missing paper guard rule: general computation divergence is allowed, and O1005 recognizes wrap as a callable shape. This is a symbolic discriminator, not an executed experiment or an established counterexample to an authoritative theorem. It has one heap node, one recursive occurrence and the minimum two required adapter fields; no data/lambda/delay is on its graph cycle.

A code-only reference must also be distinguished from that function reference: `wrap(lambda x.Return x, z.Call(r,delay(Return z)), z.Return z)` contains r only in deferred argument code. Copying a rule that follows all syntax children would wrongly conflate these locations with head lookup; a rule that follows no children would conflate this example with the preceding function-self-cycle. These are proposed authority discriminators, not approved classifications.

## Accepted outcomes do not supply the missing paper rule

- FiniteGuardDecision, accepted guard-interaction outcome §Accepted mathematics: `guarded_iff_noCycle` (module206–212), total `decideGuard` (240–254), and allocation equivalence (322–329) operate on actual `GuardedValueGraph.Node.next`. They do not prove that a paper constructor should expose any particular Node.next edge.
- HigherOrderRecAllocation `frontier` (165–176) explicitly follows ref/recvar and the sole Value child of both/top/view/wrap, stopping all other constructors. `projectNode` (215–223) uses unit only as an untyped terminal token; `projection_edge` (230–232) proves correspondence to that very frontier definition, not to the paper. The accepted handler-recursive-RHS outcome retains this exact research boundary and separately records rejection of a wrapper self-cycle.
- HigherOrderGraphObservation `ObservedTyped` (11–40) recursively observes wrapped function and both intersection premises, retaining independently typed input/output adapters and distinct inner/outer callable types. `CallableTerminal.wrap` (171–173) can nevertheless be an outer callable terminal. Thus terminal callable observation and transparent graph guard traversal are distinct even in the accepted research grammar. The graph-handler-interaction outcome accepts this grammar only; it explicitly leaves full-paper/source/native obligations open.
- R29 adjudication accepts finite heap payload allocation only. Its locally typed self-alias witness deliberately does not establish graph guardedness.

Oracle independence: no checker or runtime oracle was used. The operational/source manuscripts are distinct documents but share their assumed guarded-SCC premise; the source manuscript cannot independently establish the omitted operational guard definition. Accepted Lean outcomes prove their own explicit graph rules, and are not an independent oracle for these source rules. No random seeds, ranges, mutations or search enumeration apply. Failure condition: any claimed classification whose only evidence is HigherOrder.frontier, a callable type, code resemblance, or local payload typing does not meet this packet's source-authorization test.

## Exact blocker, owner and next evidence

Missing definition: a proof-relevant paper graph-edge/guard judgment for `wrap(function, argumentAdapter, resultAdapter)` stating whether observation stops, follows function, and how references in adapter code are retained. Its owner is the operational manuscript's rec/graph judgment O184–185,240,260–267 and shape proof O1002–1006. Luna owns authority intake; a reviewed in-scope manuscript correction or explicit user decision must resolve a new semantic choice. The source manuscript's C-Free/C-Close owner may supply capture evidence but cannot silently decide the operational graph guard.

Recommended next action: primary present the one-node wrapped self-reference together with the adapter-only reference discriminator to the authority owner, requesting one explicit constructor-indexed rule and its intended observation judgment. Do not start a new equivalent rank checker. Full paper guard, graph extension, typed observation, source/native and A/B parents stay OPEN.

## Hashes, execution and cessation

Current SHA-256 values were computed by `sha256sum`; all match the contract pins:

| Dependency | SHA-256 |
| --- | --- |
| operational manuscript | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| source manuscript | 2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166 |
| PaperExecutionSyntax.lean | e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932 |
| PaperFreshHeapAllocation.lean | 7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925 |
| GuardedValueGraph.lean | 4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55 |
| FiniteGuardDecision.lean | a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa |
| HigherOrderRecAllocation.lean | 30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd |
| HigherOrderGraphObservation.lean | 8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc |
| HigherOrderGraphSafety.lean | de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533 |
| guard-interaction outcome | 9bffe30363b2830eb8fafcb5af837541cb7ba3314e9daa73013e4865f56fd4e5 |
| handler-recursive-RHS outcome | e79ad59f2a27f211b0e487823a7cf3fdd148f5d4b1d6905d539514e582c97ecf |
| graph-handler-interaction outcome | c355f3625401ae8c23834adf298833e24b194ddc9895c14c0aefbb2b78adf418 |
| R29 adjudication | d6523cba7a7b68871f56d359168f37d83bef27fa8ae2081777094e794b3cbea7 |

Observed activity: source reads (`cat`, `rg`, `nl`, `sed`, `head`), source hashing and one UTC clock read; one leased handoff write. Some batched read output was truncated; targeted reads recovered the exact governing clauses and constructor/projection/observation lines used here. No exhaustive repository search claimed. No Lean/Lake, cache access, Rust/build/test/runtime/benchmark, Git calls, network, descendant or compiler edits. Requested role: registered researcher; observed runtime ID `/root/r30_source_researcher` from assignment; effective model/effort UNKNOWN (not authenticated by tool metadata). Exact elapsed active seconds and peak RSS unavailable; no heavy process launched; each completed read/hash command reported about 0.1 s wrapper wall time. Work stops at this frozen handoff; assigned cap 180 active seconds, actual elapsed UNKNOWN to this author because the launch timestamp was not exposed; primary must charge its observed receipt. No further writes planned after submission; no child/background process exists.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-research.md` only.
- Mathematical/source baseline: `f7a8ade138d1abec51a204b36fe5e4b06f856ce9`; contract admission `b6f365d2a` (primary-supplied).
- Dependency hash changes: none observed; all named contract pins match.
- Review status: unreviewed research producer handoff; ready for fresh nonauthor review after primary freeze. No self-certification.
- Checks already run: source/hash comparison and full 20-constructor inventory; zero executable proof/test/runtime checks.
- Proposed one-line checkpoint message: `research: identify paper wrap guard authority gap across all value constructors`.
- Shared-record deltas left for primary/curator: record exact wrap blocker and authority owner; preserve all full-paper/source/native/A/B parents OPEN; record source-only activity, worker STOP and downstream fresh review. No shared files changed.
