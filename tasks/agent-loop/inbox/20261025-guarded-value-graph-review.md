# Guarded value graph independent review — revision 1

Verdict: CLEAN within the explicitly represented research syntax. No blocking or nonblocking defect found. This does not close ENV-GRAPH-1, the full paper graph/value-form claims, or any native/compiler/inference A/B gate.

Reviewer: /root/guarded_value_graph_review_astra_r1. Requested gpt-6-astra/medium; observed model/effort UNKNOWN. Fresh nonauthor: no construction, repair, or prior certification contribution. Authors are /root/guarded_value_graph_astra_r1 and PRIMARY (elaboration repairs). Sole write lease is this report. No delegation.

## Frozen scope and provenance

Sprint PARALLEL-THEORY-20261025/r1; contract SHA-256 0751276e8eedf50d113475a0ef1c41b27b7ffd77cc4ccc28761e3cc9e792ff76. Supplied contract baseline 98118c2933694a03fcbf443a4cd638e350f76394 and current HEAD b4fbebb66ad0d915e757c36d06456fef1eaa1910; no Git executed by reviewer.

All following bytes independently hashed and matched the dispatch:

- notes/theory/lean/YulangClosure/GuardedValueGraph.lean: 4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55
- notes/theory/2026-10-25-guarded-value-graph-theory.md: 26bdad3548c07ed74119821239cbb3677f60cc14940b7f8170b86c6bf1278164
- tasks/agent-loop/inbox/20261025-guarded-value-graph.md: fec899ddc720efc7350d18ffc733be57b60cb854d0bb1b6cd0b0e98b03ce3df8
- tasks/agent-loop/inbox/20261025-parallel-theory-r1-verification.jsonl: 14c23653177f139f9f8d875cb1005b5e08d07c23622c016fcd3cc15cb57631be
- notes/theory/lean/.lake/parallel-theory-r1-run.py: 0493d59666b964f94cf62507ab5e9d48bb832b0e79e10ff289a783b787a9ac18
- notes/theory/lean/.lake/parallel-theory-r1-check.lean: f2eae75fc180fa081aec0409bdb67f5b97d61f369cdd465fe23ce726e2344587

Read root AGENTS/base, sprint/proof skills, governing sprint contract/rules, compact state/README, design-authority rule, full target Lean/note/handoff, relevant paper sections, runner and query/receipt evidence. Unknown legacy leases remain quarantined and untouched.

## Mathematical and statement audit

1. Guardedness is a concrete certificate over Node.next, not an observation premise. Only alias/view/roll/evidence supply transparent successors; unit/pair/lambda/delay terminate this one outer observation. finite_observation decreases an explicit natural bound along transparent successors. Its proof needs no evaluation termination assumption and no graph-wide acyclicity. TransparentPath is nonempty; strict rank descent excludes exactly the claimed transparent cycles. FiniteGraph uses Fin; generic helpers intentionally allow arbitrary reference sorts with a bounded certificate.

2. Typing is checked against actual node bodies. transparent_type follows by inversion of the four identity-typed transparent rules. observation_typed retains both node typing and terminality. terminal_canonical follows by inversion of the remaining concrete constructors, and reference_canonical composes these facts. no_bottom_reference excludes bottom at every reference of a guarded well-typed graph. It does not exclude bottom-typed computations or claim recursive evaluation terminates. Canonical records outer shape; payload/body typing is retained separately by observation_typed and WellTyped, rather than being smuggled into the shape predicate.

3. allocate maps every old node through Sum.inl, including references inside lambda/delay bodies. Old nodes cannot gain new outgoing edges. Sum constructors make old/new collision impossible. node_map derives typing preservation using typed_subst, joinTy preserves old types definitionally, and allocation_observation inducts on actual observation derivations. This is immutable extension up to the explicit injective renaming, not mutation of old cells.

4. allocate_guard genuinely constructs post-allocation ranks. Old ranks remain below the old ceiling; fresh ranks add that ceiling to their supplied local ranks. Old-to-old descent follows from next_map; fresh-to-old descent follows from the old ceiling; fresh-to-fresh descent uses only the stated local transparent-edge inequality. The new ceiling is the sum. No hidden post-allocation Guarded hypothesis occurs. allocate_typed similarly assembles global typing from old typing and explicit individual fresh-node derivations; it does not assume the final graph typing.

5. typed_subst is a genuine induction over the five Term constructors. closeBody_typed simultaneously replaces recursive variables with fresh references, and old_body_weakening renames old references. rec_extension consumes the constructed typing and guard plus the body substitution theorem, producing typed canonical observations for all old and new references and typing the closed body. The fresh-node derivations and local rank facts remain explicit premises. There is no derivation from full paper rec RHS syntax or its binders hidden here.

6. Distinguishing constructions were inspected, not merely their names: mutualLambda bodies actually call the other node; allocatedMutual allocates both together; equal ranks at genuine lambda guards are accepted. sharedPair uses the same child twice with equal ranks. transparentCycle has a bottom typing but no guard; badFresh has fresh per-node bottom typing while its allocated self-alias cannot be guarded. The query additionally checks every transparent self-loop form, actual old observation preservation, fresh-to-old alias allocation, body substitution, and an instance of rec_extension. No whole-graph DAG condition has entered.

## Recorded checker evidence and repair audit

No Lean, tests, build, checker runner, native audit, or Git was run by this reviewer. This is independent static proof/claim review with inspection of the primary's recorded checker evidence. A read-only metadata command initially failed because `python` was unavailable; it was repeated with `python3`. Neither invocation was a proof checker.

The receipt contains all nine calls, totaling 8.041126445998088 seconds. Calls 4 and 5 retain graph failures (reserved binder cascade, then successor/type argument inference); graph calls 6 and 8 pass. Final module calls 7/8 and query call 9 pass, with identical before/after input hashes. Independently rehashed every input/output named in final rows 7/8/9: no mismatch. The runner statically pins 75 dependencies, seven prior receipts and 42 accepted prior module chains; its chain logic was inspected rather than rerun. Query has 105 #check/#print axioms pairs (99 public declarations, six named query declarations) and 38 examples. There are 66 graph public declaration queries. Recorded axiom output contains only empty dependencies or [propext].

Compared original recorded graph source in call 4 against final call 8: changes are the reserved binder name, explicit successor in allocation_observation, explicit joined assignments/reference constructors, and dependent Empty elimination. No theorem premise, constructor rule, or conclusion was weakened. The author's old hashes remain correctly historical; the present note records primary coauthorship and the new checked artifact.

## Parent application and precise remaining gates

The paper passages at 150–196, 258–267 and 980–1010 require finite guarded immutable graphs, simultaneous rec allocation, observation, weakening and value forms. The present result supplies a concrete restricted-model implementation of that mathematical proof step and useful sublemmas. The note accurately keeps the original parent OPEN and lists these missing premises:

- GVG-GUARD-COMPLETE-1: bounded rank construction from finite absence of all-transparent cycles; future graph proof owner. A sufficient numeric certificate is proved, not equivalence to the paper criterion.
- GVG-FORMS-1: actual mu/roll and type-changing evidence/views, plus missing full-paper value/eliminator forms; full-paper proof owner. Current roll/view/evidence preserve the identical type, and Nat metadata has no interpretation theorem.
- GVG-REC-RHS-1: derive new-node typing from full paper RHS derivations under all actual binders; full-paper syntax owner. The independent Term grammar has no nested binding constructors and is not HigherOrderSyntax.
- ENV-GRAPH-1: native recursive/shared readback, initialization/current cells and preallocated uninitialized states; Luna/source intake. No native bridge was audited or certified in this independent theory review.

These are explicit scope limitations and subsequent proof obligations, not defects in the stated conditional theorems. No parent quantifier or supported source behavior is narrowed; no implementation or production authority follows. Primary may accept the frozen restricted mathematics and mark its local checking/review gate complete after adjudication, while retaining all above parent gates.

## Resources and cessation

Grant: 300 seconds from actual dispatch acknowledgement. Primary's current record places actual spawn acknowledgement before 2026-10-25T06:44:49.916273+00:00; exact dispatch timestamp was not independently exposed. First review acknowledgement was sent in this session after reading AGENTS. No budget renewal or reset. Report freeze UTC: 2026-10-25T06:45:50.190664+00:00. This bounded review completed well within the grant.

STOPPED after this report write. No spawned descendants, background processes, pending tools, or additional writes. Only this exact report path was created. Primary owns adjudication, central records and Git integration. Report hash is returned externally to avoid self-reference.
