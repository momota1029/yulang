# R35: occurrence-local Apply extrusion declarations

Status: frozen provisional rule and source/native obstruction; independent review NOT_RUN. The rule below is not adopted semantics. No original parent clause, allocating conservativity theorem, source-qualified counterexample or production gate is closed.

Author: `/root/r35_apply_source_proof`, sole author; no descendants. Handoff ID `R35-SCOPED-APPLY-SOURCE-PROOF`, revision 1. Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. Session `current-session-r35`; actual assignment receipt is Luna's direct R35 task message. Baseline supplied by Luna: `3f3bfca3a1e37cd8fa574e40ea6382bac6b1c1d9`; no Git operation was used.

## Parent application and outcome

The unchanged parent is intrusion preservation, required principality and N-Transport for `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, within the full inference/executor goal. All original source/provider/context/world/assignment/occurrence/event/continuation/future/history quantifiers, full Call/effects, arbitrary well-scoped client W, and independent F1/FK1 remain. R30's independent `j0/a0` guard/world-action premise stays OPEN. Parent clauses discharged: **0 -> 0**.

R32 retention is applied to the complete joined tree now: both Call occurrences, their whole clauses, original scopes/event cursors and W are retained. This removes record loss as a possible explanation of the present failure. R35 then follows the actual Apply elaboration and drafts a different, occurrence-local candidate. Unlike R33's receiver-owned candidate, its lexical anchor is derived from HIR. It still cannot derive a logical type-scope/telescope and publication action for the actual native C/D copies. A frame-local diagonal would preserve the old clauses by equality substitution; identifying that diagonal with the actual retained native copies is unproved. A single base witness additionally needs one common extension of both frames. No complete original witness defeating that extension was obtained.

The first exact missing premise is `ApplyExtrusionScope(q,e,parent,T)`: a typed interpretation of the actual lexical scope and parent-dependency closure into the original source binder tree, together with its incidence in the active root and at helper publication. Native kind, target level and HIR lexical scope are genuine inputs; none alone is this output. This is a source inference/extrusion-owner obligation, consumed by Generalize §§5.1–5.2. Do not dispatch another proof that merely assumes it.

## Concrete source and maximal actual elaboration

The selected baseline fixture is `candidate_local_self_recursion.rs::nested_helper_uses_active_outer_root_without_freshening_it`:

```text
my outer = { my loop x = { my helper y = loop y; helper x }; loop }
```

Let f=loop, g=helper, q be the actual `loop y` Apply, and t the distinct `helper x` Apply. The final outer `loop` is a Name, not an Apply. The literal fixture has one helper Name use. The theorem's two independent incoming frames are symbolic original client events `new(p_g,i0,g)` and `new(p_g,i1,g)`; the fixture is not evidence of two executed FreshUse routes. Its historical success assertions were read, not executed here.

Write o for f's one active root, B for y's existing parameter endpoint, R for q's result endpoint and A for x's parameter endpoint. The source registration components K_f and K_g stay distinct; a Value SCC does not merge them. Publication p_g(h) remains under its actual enclosing f event h. Its action relative to o is precisely what must be justified.

The constructor trace, with no invented declaration output, is:

| Actual owner | Supplied input/output | Limitation |
| --- | --- | --- |
| HIR `Work::Initializer` in `local_source.rs` | Registers helper and Lambda y; starts `LocalInitializer(helper)`, then passes `LocalSourceScope::Parameter(y)` to its body | Lexical scope tag, not an original logical type telescope |
| HIR `Builder::expression`, OperatorChain Apply case | q and both Name children receive that same scope tag, with original occurrence/source identities | No inference-description or capture classifier |
| `candidate_source::emit_candidate_source` | Parameter endpoint B; expression positions R/application effect; active Name action links the existing o; `ApplySourceInput` retains q, callee/argument/endpoints, effects, checking and cause | q's callee is Local(f), not the unannotated formal of the compositional `invoke` candidate |
| `shadow_apply::admit_candidate_fact` | Builds the four-port negative demand from argument, argument effect, fresh invocation effect, result; admits the callee/demand constraint and both application-effect contributions | Allocates an invocation-effect row; does not allocate C/D as q's expression endpoints |
| `candidate_extrusion::candidate_extrude` | On a high-level Value row, allocates `fresh_value_at_level(target)`, calls `retain_extrusion_parent(copy,parent,p,target,occurrence)`, then admits the one-sided link and transforms selected bounds | Native ValueRow kind, copy identity, polarity, level, parent and operation are retained; no source `Desc(...,sigma,Delta)` output |
| `candidate_scheme::install_candidate_local_term`, `route_candidate_local_run`, `prepare_candidate_fresh_use` | Stores live root/boundary/capture region, recaptures per occurrence, maps canonical rows using the stored-local/above-boundary/generic guard | Supplies operational map action, not a typed interpretation of it in Generalize |

For the approved nested-call occurrence e, retain origin G, receiver F and actual signed Value-coordinate incidences `(C,B,+,1)`, `(D,R,-,1)`. Qualification contributes C=B and D=R at those same incidences. This is the adopted operation's source discriminator; this leaf does not assert that a fresh runtime join for this fixture was observed. Function extrusion visits all four ports with their actual polarities; associated effect pairs/residuals cannot be discarded because only C/D are displayed.

## One provisional rule: Apply-Extrusion-Desc

Luna expressly requested one research-only rule attempt after the existing-owner audit. The following is that single candidate, not an amendment to the governing documents.

For exact `Apply(q,Name(active f),Name(y))`, anchor candidate scope `sigma_q^lex` at the actual HIR `Parameter(y)` occurrence region. Process each actual copied coordinate a in e in its native typed sort. Propose its source sort `ValueDescription` for a Value coordinate, and the actual corresponding effect-description sort for an effect coordinate; the sort correspondence itself must be exhibited. Let P_a be the retained *parent operand*, not a later solved shape. Compute

```text
Delta_a^cand = ordered transitive free-dependency closure in T of P_a
q_a = (actual q, actual e, actual signed pair ordinal)
Desc(K_g,q_a,sort_a,sigma_q^lex,Delta_a^cand) : Copy_a
Description(K_g,q_a) occurs at every actual transformed operand incidence.
```

The dependency computation uses the parent's actual typed operand/declaration references and their original dependent telescopes; it does not use arbitrary Call witness fields, a future choice of frame, target level, successful Q or desired equality. The newly allocated copy is an output, never a prior dependency of itself. A transitive cycle must use the original registered recursion, not fabricate a topological order. For C the seed is B; for D it is R. R must first have its genuine owning inference introduction and dependencies. The rule retains the entire original Call clause and every original effect/guard/provider/receipt/entry/return/future/resumption/suffix field. It adds no early scheme, new provider, new extrusion occurrence or `Internal(K_g,f)` edge.

This schema exposes its first formation obligation instead of silently solving it: `sigma_q^lex` must map to a definite original *type* scope in T, with scope inclusions for Delta_C and Delta_D and a justified validating-component/dependency action. HIR proves the lexical anchor `Parameter(y)` but does not specify whether R's full descriptive dependencies sit before g's invocation challenge or inside its event telescope. Allocation of native expression positions before traversal does not prove that logical placement. If a parent operand has an actual event dependency, the candidate must retain that dependency; it cannot hoist it because its row has a small level. Thus the schema cannot presently construct an authentic `Desc` record by the Generalize §3.3 rule.

Publication reveals a second field of the same missing source action. If these are ordinary own-component descriptions not fixed by any authentic dependency, Generalize gives images C_i,D_i in each independent frame and aliases share that frame. If the active-root incidence instead retains them in the base, the walk needs the authentic typed edge that fixes their dependency contract. Active o is not an installed `Mono/Established` certificate; K_f is not K_g. The candidate cannot choose whichever classification makes its equality proof work.

## Erasure and extension test on the whole joined tree

Retain both complete source Calls and all original local laws L1–L5, alternatives, event operands and W by R32. Erasing added declaration/metadata/duplicate transformed clauses from any well-formed candidate derivation leaves the unchanged original clauses and strategy. This statement does not establish candidate formation or the converse.

The occurrence-local total-definition sanity check is useful and limited. At a scope where the actual parent terms are well typed, set each new copy equal to that same parent, simultaneously for the complete transformed tuple. On the whole joined tree, put C_i:=B_i and D_i:=R_i at their original permitted scopes, and apply the same substitution to every affected effect/residual operand. Every retained complete Call clause is unchanged; a transported duplicate is the same clause after equality substitution. Aliases route to their existing i. Original event strategies, providers, raw resumptions, world transitions, foreign continuations and W are unchanged. Hence such a *lawfully scoped diagonal* needs no independent Call-safety oracle and introduces no changed old strategy.

This checks the proposed total coordinate definition against full-clause retention, rather than inferring complete Call from a scalar inequality. It does not prove that the actual extrusion transformations, typing scopes or capture maps implement this diagonal. Those are exactly the missing constructor/correspondence fields. In particular C_i:=B_i is not one retained base C if the actual capture action shares C across i0 and i1.

For that latter action the necessary projection of a common lift is

```text
one strategy for C,D at their original base telescopes,
C=B_i0 and C=B_i1 and D=R_i0 and D=R_i1,
plus every original signed transformation, complete Call and effect clause.
```

If C or D originally has a legal event dependence, keep that event index; do not quantify it away. Choosing C after inspecting each client frame is illegal when that frame is absent from Delta_C. A single syntactic declaration schema is distinct from a single shared witness. Preserving one does not prove the other. The actual native guard permits shared images at/below boundary; an occurrence-local source declaration therefore needs an explicit commuting publication/map square, not just the same q label.

No universal common extension follows from the supplied source records. Conversely, this necessary projection is not a countermodel: arbitrary unequal B_i assignments need not extend to one complete original source strategy. Both F1 and FK1 remain independent. A local type-coordinate action cannot establish a foreign-continuation transport theorem.

## Concrete original-witness attempt and why it does not refute the parent

Try two independent helper descriptions with incompatible argument descriptions, while retaining f's one root with a common broader argument demand. Scalar Simple-sub permits such an arrangement before the added cross-frame equalities. To turn it into a complete original witness for the selected source, however, one must supply the original recursive member/world introduction for f, both complete q/t Call clauses, all admitted challenges/futures, and a single joined strategy satisfying W. Neither a successful reference typing nor the candidate's algebraic scalar values supplies those fields. Even describing `loop y` as divergent does not discharge its complete pending-prefix/future/recursive-introduction obligations.

The historical correlated wrapper specimen and its int/bool scalar history are not substituted for this witness: they are a different source/history, and their producer explicitly excluded a complete Yulang Call proof. The compositional Call candidate is context only: its declared domain is an unannotated Value *formal* applied to an integer literal. Here the callee is an active recursive Local and the argument a Name; adopting its newer scope placement or local contracts here would enlarge its actual premises. Therefore no complete original witness with an empty lift fiber has been constructed. This is an unresolved constructor/publication premise, not a source-qualified refutation or proof of impossibility.

## Mutual TODOs and stop boundary

- **R35-SOURCE-SCOPE** — Luna/source inference-and-extrusion owner. Input: exact q/e, HIR `Parameter(y)` anchor, retained typed parent operands, their original declaration telescopes, and the original T. Output: adopt/reject the provisional rule with an explicit source type-scope inclusion for each coordinate and its active-root/p_g typed dependency edge. Exact falsifier of the reported gap: exhibit these derivations from an already adopted owner, then run the unchanged §5.1 walk. If Delta needs a later witness, reject the attempted placement rather than erase that witness.
- **R35-CAPTURE-SQUARE** — existing native owner and subsequent Luna-assigned source bridge owner. Input: that frozen source decision and the native lane's exact occurrence/pair/publication/two-map join. Required output: a commuting action for every retained Call/effect/residual incidence, including aliases. Falsifier: an eligible source C_i mapped to one base row without a source fixing edge, an actual pair from another occurrence, or one-use-only evidence. No additional instrumentation/code lease is requested here.
- **R35-COMMON-LIFT** — Luna-assigned proof owner only after the source action is fixed. Prove one total strategy extension for the unchanged joined source tree and arbitrary W, or construct one complete original witness with an empty fiber. Falsifier: any inaccessible dependency, changed old operand, or incompatible required frame incidences. Repeating the displayed common-extension condition as an assumption is not this result.

No safe production slice follows. The useful next step is source-owner adjudication of this specific rule and publication action, with fresh review assigned by Luna. The two methods, R33 receiver placement and R35 occurrence-local elaboration, now leave the same source-scope/capture seam unresolved; further equivalent conditional proof packets should not be scheduled without new owner evidence. This assignment stops at that precise source formation/correspondence boundary.

## Frozen dependencies, checks and authors

All hashes below were recomputed from working bytes. The fixture and scheme file matched the pinned baseline when read; concurrent native-lane deltas are excluded from this proof's evidence. Additional code owners are existing in-repository constructor dependencies, not new external premises. No current native-lane result is certified here.

| Path | SHA-256 | Author / use |
| --- | --- | --- |
| `tasks/agent-loop/sprints/scoped-apply-extrusion-20261018-r35.md` | `638b4b884a4927eac82f1c24ccbd9bc312a8b5f87ff6627845197b4a3c73e3b8` | Luna; revision-1 contract |
| `notes/theory/2026-10-18-active-capture-allocating-lift-r33.md` | `c9edf92f63511617dda2ce99cef668491adbc1894a4ab2a5f9e27148350d7a9c` | `/root/r33_allocating_lift_proof`; obstruction only |
| `notes/theory/2026-10-18-active-capture-conservative-extension-r32.md` | `fa0e0f25dfd454a51c924b505e847b02133a37b38689e033d34ae5796b24eb8b` | `/root/r32_conservativity_proof`; retention within reviewed premises |
| `notes/progress/2026-10-18-r32-active-capture-closeout.md` | `01f3e21402d6b5df9e85579f3d763af3fc750c23f347dea4f6921ac1c458f1cb` | Luna; retention review/observer correction |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | Primary/architect; adopted scope |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Researcher; reviewed subsystem, L1–L5 remain |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | User/primary; October 14 algorithm clarification |
| `notes/design/2026-10-10-local-self-recursive-binding.md` | `38d42183fdc4f2c0136112d8b305816241d8f449367b473e4de3a5135dc49895` | User/primary; active-root rule |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89` | User/primary; occurrence qualification |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` | Reviewed original Call/relation scopes |
| `notes/theory/2026-10-14-invoke-compositional-call-introduction.md` | `1cc473e9d0cb454f3f6725b7ce103456af6011bffd9729e3bbf3445c688ac9bb` | Historical producer, individual author UNKNOWN; context only |
| `notes/theory/2026-10-13-nested-live-root-generalization-derivation.md` | `f72404c661736ee9e0b6226dfc471724795836510c7aa3a0582d209be47f8dd9` | Historical proof leaf; rejected counterwitness reuse |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | Author UNKNOWN; lexical constructor |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Author UNKNOWN; source actions |
| `crates/yu-solver/src/shadow_apply.rs` | `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb` | Author UNKNOWN; actual demand formation |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Author UNKNOWN; retained source inputs |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d` | Author UNKNOWN; actual copy producer |
| `crates/yu-solver/src/candidate_scheme.rs` | `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd` | Author UNKNOWN; pinned production capture/map slices |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a` | Author UNKNOWN; selected source only, no run |

Checks: bounded static constructor reads, lexical scope derivation, full-clause retention/erasure audit, typed dependency and joint strategy substitution checks, exact-source counterwitness attempt, byte hashes. No compiler/test edits, tests/builds/probes, Git, network/external contact, nested CLI, Astra or descendants. This producer cannot independently certify the combined result. No withdrawn bypass, source restriction or weakened ordinary inference was introduced.

Resource cap 900 seconds, Astra 0. Exact launch-relative active duration and CPU/RSS are UNKNOWN; conservatively charge the 900-second reservation, remaining 0, without claiming a measured duration. Sole new paths: this artifact and `tasks/agent-loop/inbox/20261018-scoped-apply-extrusion-r35.md`. Scratch paths: none. After the revision-1 hashes are emitted, writes are STOPPED; no descendants or unresolved descendant leases, and no claim of RUNNING while awaiting intake.
