# Native Context closure and the remaining global inference progress obligation

Date: 2026-10-26. Frozen source: `45d307a0aa01722b5aac289b07d71953630abca7`.

**Result:** checked source-constructor Context closure, including complete Context consumption after parsing. **The original whole-inference termination theorem remains open.** The result removes an arbitrary recursive Context-shape hypothesis from this owner segment; it does not establish a finite set of weights, rows, views, scoped identities, relation keys, or generations. The source-to-projection extraction described below is also still required.

## 1. Original obligation and authority

The unchanged target is `YulangClosure.SourceProblem.InferenceTermination` in `notes/theory/lean/YulangClosure/Contracts.lean:151–154`:

```lean
∀ s x n, p.supported s → p.inferInitial s x n →
  Acc (fun next prev => p.inferStep prev next) n
```

The definition explicitly concerns algorithmic inference, not termination of program evaluation. This packet neither claims full runtime strong normalization nor presents a runtime divergence result.

The original top-level algorithm is `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, especially §§1–1.1, read with `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–4 and §6. The latter fixes immutable source Value birth levels and qualifies an actual retained parent/copy occurrence using reachability inside the graph induced by one birth level. Current row levels, lexical scopes, generalized captures and source Value births remain separate. This packet changes none of those rules and does not certify the frozen implementation's complete correspondence to the birth-level correction.

The already checked `OriginalInferenceTermination.scanTotal` removes a fuel premise from the actual stack scanner. It ends before the native consume callbacks. `NativeDrainOwnership.Step` permits unbounded external `reserveOther`, so its state conservation theorem is not a whole native drain progress theorem. This packet goes through the next actual owner: parsing followed by every filter and the remaining Effect continuation.

## 2. Why identity-only bounds were wrong

An original annotation path can create a negative closed Allowance bound before its Context is consumed. In `crates/yu-solver/src/candidate_effect.rs`, `construct_candidate_local_annotation` calls the negative signature constructor at 1749; `candidate_annotation_pair` does so at 1911. `candidate_signature_effect` starts at 2161 and installs the negative Allowance bound at 2210–2222 or 2281–2291.

In `candidate_context.rs:3898–3936`, `candidate_context_bound_for` selects Identity when the matching allowance filter is currently being checked. Otherwise it uses the matching parent's actual post-check Context, or the source Context if there is no matching parent. The source constructor at 3366–3372 creates `PrefixLeft(weight, Identity)` for the relevant closed upper view. Therefore an initializer can lawfully attach a nonidentity source filter. Restricting the original source to identity-only fibers would discard this case.

The corrected descriptor predicates are:

```text
Atom    = Identity | PrefixLeft(weight, Identity)
Shallow = Atom | Replay(Atom, Atom)
```

The Replay constructor carries its actual ordered operands and strict child-ID inequalities, and requires at least one nonidentity operand. The native both-identity branch returns Identity without allocation. Weights are arbitrary natural identifiers with actual table readback: there is no finite weight universe assumption.

These predicates describe the constructor projection being proved. They are not a new `supported` predicate and do not restrict the raw native Context API. The full parser and renamer retain all six native Context constructors, including directed contexts, suffixes and certificates. Establishing that every original source execution projects into this grammar is a separate remaining extraction theorem, rather than an asserted premise of the original `InferenceTermination` contract.

## 3. The exact checked consume result

The principal native statement is `YulangClosure.NativeInferenceProgress.native_expand_context_closure`:

```lean
∀ {t : Tables} {a : Availability} {levels q : Nat → Nat}
  {fuel : Nat} {parent : Key} {body : Body},
  Shallow t parent.context →
  NativeContextExpansion.expand t a levels q fuel parent = some body →
  body.postContext = 0 ∧
  (∀ fiber ∈ body.fibers, fiber.key.context = 0) ∧
  (∀ child ∈ body.children, Atom t child.context)
```

This is quantified over arbitrary tables, availability, representatives, levels and complete parent keys. The existing `expand` computation is retained exactly: the entry gate, current-pair equality check, parser availability, relation guard, allocation/publication gates, endpoint cases, inline filters, conflict children and unconsumed continuation all remain in that function. No success is concluded for a rejected input. `fuel` is the already-existing finite parser interface, universally quantified here; it is not an assumed global execution bound or a new acceptance cap.

The proof first refines a successful existing `expand` result to `consume`, which uses the previously proved total scanner and then the existing `decompose`. On a successful shallow parse, the residual is Identity, there is no directed residual, and an empty filter list implies that the original Context was Identity. This includes repeated equal operands and repeated equal weights, so parser deduplication does not introduce a missing case. Invalid weights take the actual rejecting branch.

`decompose_fibers_identity` then handles both origins of every bound fiber: a checked inline filter and the optional continuation. The latter is the part excluded by the earlier scanner theorem. `decompose_children_atom` follows the actual aligned child admissions and their source Context constructor. It does not choose a convenient child list. Complete `Body`, `Fiber` and `Key` objects retain endpoints, sources and transformers; the theorem observes only their Context coordinates.

`consume_context_closure` has the same conclusion for the total-parser segment itself. `expand_consumes` connects the existing native expansion result to that segment. This is successful-result closure, not a proof that native callbacks or their nested drains return. The existing completion and readback owners remain necessary to obtain a `Body` from an actual callback execution.

## 4. Constructor cases and source map

All Rust locators in this section refer to the frozen revision above, under `crates/yu-solver/src`.

| Native owner | Frozen location | Checked representation / boundary |
|---|---|---|
| Complete Context interner | `candidate_context.rs:2630–2655` | Full expression identity and strict earlier-child topology, reused from the existing table/interner proofs; no semantic quotient is introduced. |
| Source seed/admission | `candidate_context.rs:3366–3372`, `3458–3481` | `source_context_atom`, `admitted_context_atom`; actual source availability/readback is consumed. |
| Negative signature bootstrap | `candidate_effect.rs:1749`, `1911`, `2161–2291`; `candidate_context.rs:3898–3936` | `signature_fiber_atom` preserves the lawful singleton prefix. Initial bounds need not have passed Context. |
| Inline filters plus remaining Effect continuation | `candidate_context.rs:3800–3885` | `native_expand_context_closure`; both registered and newly inserted filter branches, all emitted bound fibers and admitted operand children. |
| Post-check lookup | `candidate_context.rs:3297–3302` | `post_atom`; only actual completed consume results contribute the proved zero residuals. Pending memo membership is not treated as completion. |
| Lower/upper bound Replay product | `candidate_context.rs:3992–4077` | `replay_context_shallow`; preserves operand order and the both-identity allocation shortcut. Source-set union and scoped composition remain in the native key owners. |
| Canonicalization, copied-bound transport and FreshUse transport | `candidate_context.rs:4230–4356`; `candidate_extrusion.rs:368–397`, `619–633` | `transport_atom` retains exact source and transformer coordinates. Other payload/ownership laws are not replaced by this shape theorem. |
| Context renaming during FreshUse | `candidate_context.rs:1556–1694`; `candidate_scheme.rs:4587–4634` | `RenamedAtom` describes the actual Identity and singleton-prefix successful branches. `fresh_prefix_constructed` supplies an actual full-expression interner output; it does not posit a pre-existing mapped prefix. The full Rust renamer-to-`RenamedAtom` extraction remains open. |
| Value port Context construction | existing `NativeValuePorts.buildContext`, corresponding native Value port owner | `value_port_context_atom`: with the actual inherited post-context zero, either Identity or a fresh source prefix is returned for either swap flag. This is not a theorem that every native Value request already has zero post-context. |
| Growing tables | `NativeContextTables.TableExtension`, `run_table_extension` | `atom_extension`, `shallow_extension`, `invariant_extension`; old readbacks survive arbitrary witnessed append-only extensions. |

`Step` stores complete request keys, actual bound fibers and completed post-context entries. Its constructors are source, signature, complete Context consume, Replay, transport and the atomic FreshUse renaming branch. `step_invariant` proves each case. `GrowingReachable` additionally permits real table extensions between any steps; `growing_context_closure` proves the grammar over this growing construction history. A final fixed table, finite transcript, finite universe and eventual result are not assumed.

The projection deliberately records historical created objects, so it does not model queue pops, allocation rollback or native callback scheduling. It can admit arbitrarily many constructor steps. Its invariant is consequently not an accessibility theorem. The missing full native extraction must cover source initialization, all eight Value/Effect bound lanes, replay construction, retained readbacks, FreshUse, rollback, generation invalidation and the nested drain order. It must also connect the Value request invariant to the zero-post premise of `value_port_context_atom`. No K0 or `scoped_experiment = false` restriction is used or proposed.

## 5. The concrete global growth obstruction

The actual outer loop is `lib.rs:14235–14259`, `run_candidate_typed_drain`. `step_typed_drain` begins at 14290. With no queued item, its Transport stage settles intrusion; Context execution runs before Dispatch. A Context callback can add bounds, enqueue replay children or enter a nested drain before the later current-pair memo check. Therefore a rank on the pending parser stack or the current queue alone cannot be the global rank.

The repeated sibling allocation issue is explicit in `candidate_extrusion.rs:28–160`. Each extrusion invocation starts new `rows` and `structure` memo maps. `Work::Visit` reuses an endpoint when its current level is at most the target, but otherwise allocates a new row at the target, records the parent/copy occurrence, adds the one-sided source link and visits the selected snapshotted bounds. A strict decrease holds along that new parent/copy edge. It does not bound the number of siblings allocated by separate invocations with the same source endpoint, polarity and target level: the memo is deliberately local to one invocation and does not survive source mutation.

The actual duplicate guard is also stronger than an endpoint pair. `lib.rs:13507` and the surrounding `pair_is_current` implementation require the exact processing relation to be completed at the current intrusion generation. Different Context/source/scoped identities or a new generation can require more work. `candidate_intrusion.rs:568–725` processes pending equalities, merges distinct representatives, copies their retained bounds, canonicalizes bound contexts, increments generation at 694 and marks the state dirty at 695. A merge consumes a distinct pair of existing representatives, but fresh rows replenish the population. Consequently initial row count does not bound the total number of merge generations.

The corrected Context grammar cuts off one syntactic recursion: a replay request cannot produce a deeper retained bound Context through the represented consume segment. It leaves unbounded identifier births possible, including the weights in those atoms. No bound on total row copies, views, relation fibers, scoped transformations or generations has been derived here. There is no demonstrated divergent original source program; the obstruction is a concrete missing progress argument, not a counterexample.

## 6. What the actual source Name schedule does and does not supply

The source action list is already a finite stored object. `candidate_source.rs:2403–2461` selects the action at `frame.next` and advances that cursor after successful action completion or publication. Its Local and Module branches are at 2490–2498. `candidate_scheme.rs:4911–4947` checks the local occurrence publication table before allocating a new FreshUse. Open recursive module uses go through `route_candidate_open_use`/`route_internal` (`candidate_scheme.rs:4102–4108`); source collection retains active local function initializers as monomorphic endpoints (`candidate_source.rs:1197–1200`, `1796`). This supports a future proof that the successful original source actions are visited once. It does not prove that an action's drain finishes, or that retry/failure branches have no externally repeated execution.

The crucial copy input is the current live graph. A module use captures it at `candidate_scheme.rs:4128–4133`; a local use calls `capture_candidate_graph_owned` at 4944 before `prepare_candidate_fresh_use`. `prepare_candidate_fresh_use` at 4199 begins a new Context use and, when scoped mode is enabled, a fresh scope mapping over the captured regions. At 4259–4261 it allocates fresh rows for local, sufficiently high, generic captured rows at the use level. Its finite local `graph.rows`/`graph.bounds` loops do not bound the size of graphs captured by later source actions. Bound restoration at 4185–4187 and the local-use cursor around 5070 call the actual nested drain machinery; they do not lower the AST again.

The next original construction must establish birth ancestry and a finite descriptor supply for the graph captured at each source action. It must charge each *new invocation* of extrusion, including repeated siblings, to a genuinely new demand descriptor generated from original source uses, retained source shape, polarity, current/birth-level information and actual scoped maps. It must then show that merging and copied-bound replay do not create an unbounded new descriptor supply, and combine that with the generation-sensitive complete relation memo and nested drain return order. Merely assigning every copy a smaller level, or assuming a finite final set of rows, leaves the repeated-sibling case unproved.

Fresh scope map allocation/injection is another concrete owner obligation. Proving that allocator supplies a lawful rename map would close a formation premise; it would not by itself bound the number of allocator calls or their captured supports.

## 7. Validation and exact claim boundary

`NativeInferenceProgress.lean` was built against an isolated frozen copy using Lean 4.35.0 and Lake 5.0.0-src+eb6cafb. The skill's named-declaration helper checks all 28 authored theorem roots, complete printed types and transitive axioms. A separate module-origin census checks **117 originating declarations and 50 theorem constants**, including private/generated theorems. Every declaration's type and transitive axioms are printed. The theorem distribution is 16 with no axioms, 8 with `propext`, 21 with `propext` and `Quot.sound`, and 5 with `propext`, `Classical.choice` and `Quot.sound`. There are no project axioms, `sorryAx`, kernel bypasses or unchecked native evaluation.

All 178 frozen input hashes were revalidated. The 14-file import dependency cone was scanned: 31 text matches were ordinary native `admit` function/constructor names or explanatory prose; no proof holes or bypasses were found. The complete census, commands, failed repairs, resource incident, hashes and audit output are retained in `tasks/agent-loop/inbox/20261026-whole-global-termination-r2.md` and its cited isolated logs.

The exact consumed premises are the existing scanner's `ScanRun`/total-scan equivalence, the actual `expand`/`decompose` successful computation, actual source availability/readback, actual filter/child construction, exact transport and full-expression interner readback. The new theorem derives the zero post-context and all fiber/child shapes instead of asking the caller to assume them. The remaining semantic premises are the full native execution-to-constructor projection, actual completion of callbacks, the finite original birth/descriptor construction, and a combined generation/nested-drain progress argument. `Contracts.InferenceTermination` is not instantiated or closed, and no other original soundness, hygiene or principality root is claimed closed.

Checked module SHA-256: `d22167d330ce1bb000677e2915a85beddb0e7a483600ac8c6a92cfdf37c79b12`.
