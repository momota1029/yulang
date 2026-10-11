# Captured `run`: contribution routing and the missing source/use join

Date: 2026-10-12
Status: frozen, independently reviewed conditional application derivation; concrete contribution join OPEN
Y3 baseline: `c1041f8f4706e847bf709e36728211965be24980`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle inspection tree: `/home/momota1029/rust/yulang2-oracle-capture`
Exclusive lease: this file only; leaf producer; no delegation

## 1. Frozen objective and hypotheses

The original H statement in [Oracle global effect hygiene](2026-10-11-oracle-global-effect-hygiene-proof.md) §1 remains universal over its original successfully lowered source domain, negative annotation occurrences, original scopes/binders, actual copies and actual Call/output routes. This note does not restrict H to the captured example or promote H, complete Call, soundness, principality or replacement of F5.

The bounded objective is to join **the actual operation application at line 64** of `/tmp/yulang2-run-projection.yu`, its actual source/Call parent, annotation instance and residual lineage, to the selected `run` definition interface and the actual instantiated output route. Required evidence is a jointly derived map or an exact obstruction; output membership is a conclusion to determine, not a hypothesis. In particular, this explicitly handled `send` is not supplied as H's independent same-family survivor. A contribution accepted at the formal row head need not occur in the positive return Effect.

The captured input is exactly the `int` variant in [constructor derivation](2026-10-12-native-negative-residual-constructor-derivation.md) §11, with input SHA-256 `73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9`. The original `(str,int)` fixture is outside this local result. Its declaration, handler operation pattern and line-64 operation application are three distinct source occurrences. Comment examples are not executed occurrences.

Operational hypotheses: pinned bytes, valid arena handles/fresh allocation before exhaustion, and normally completed calls to the identified constructors/consumers. The existing successful capture supplies the selected-query and accepted-generalization observations stated below. It does not supply a source application record, actual instantiation map, complete replay, a concrete contribution-to-bound association or observational equivalence of instrumentation. Whenever an operational replay or instantiation is needed but not captured, it is explicitly conditional below.

Governing authority: annotation-effect-hygiene-integration §§1–4; contextual-attachment-admission-design §§3–6; contextual-residual-lineage-selection “Selected policy”; complete-call-contribution-definition §§2–5; top-level inference principles §§1–5. The original contribution/attachment/provider/context/world binders of those judgments remain distinct; the plain Function interface below is not identified with their complete Call semantics. The pending Value-copy question supplies no premise.

## 2. Two binder maps, with their different scopes

First preserve the constructor coordinates of constructor-derivation §9:

| Coordinate | Owning occurrence |
| --- | --- |
| `v` | full Effect slot for the annotated formal `action` |
| `u` | inner stack coordinate of that same formal annotation instance |
| `s` | that instance's subtraction identity with declared payload `{ev}` |
| `t` | actual catch result Effect |
| `r` | defined-function body Effect after any recursive-skeleton forwarding |
| `c_send` | computation Effect of the **line-64** `ev::send (1,42)` application |

The Value binder `'a` is separate, as are source payload names `s,n`, value-arm name `v`, provider identities, attachment identity, and each residual constructor's lineage. The formal constructor emits `Push_s(u) <: v`; it does not emit its converse. Catch emits `v <: Row({ev},t)` and the weighted local view. None of these names is numerically identified with a captured TypeVar in this note: the transcript does not print their source constructor allocation records.

The second map is the **observed generalization map**, on the captured compact variables, in the inference arena:

```text
mu(11)=mu(14)=mu(29)=mu(30)=9; mu(9)=9
mu(21)=mu(31)=mu(33)=absent
```

The complete substitution table is constructor-derivation §11. Here “absent” means the compact occurrence is omitted by the rewrite, not that the original semantic row equals empty. Distinct original variables map to one scheme variable; `mu` is not injective and is not an attachment/lineage map. `SubtractId(0)` appears on compact variable 31, which is omitted. No stack quantifier occurs in the finalized scheme. This does not identify `SubtractId(0)` with source coordinate `s` merely because both are unique in the displayed fragment.

The scheme arena separately has:

```text
p6 = Fun(arg=n4, arg_eff=n7, ret_eff=p4, ret=p5)
n4 = Var('3); n7 = Row([Con(ev,[])], Var('9))
p4 = Var('9); p5 = Var('3)
quantifiers=['3,'9]; stack_quantifiers=[]
```

For one actual later instantiation, the constructor supplies a third, fresh map `rho`: `rho('3)=A`, `rho('9)=B`. These two fresh variables differ and every occurrence of `'9` in that use has the same `B`. Numeric values of `A,B`, use reference, owner and source application are not captured. Scheme `p4` and inference `PosId(14)` are different arena handles.

## 3. What the actual selected records establish

The existing transcript `/tmp/yulang2-run-projection-min.log` selects `run=DefId(2)`, root `TypeVar(1)`, accepted iteration 1 at epoch 291. Root records 256 and 258 have empty directed/incoming weights. Record 256 has endpoint 45 and Original/Standalone proof with producer constraint 163. Record 258 has endpoint 44, binary replay at pivot 34, premises 255/257, `UpperBoundAdded`, result constraint 164. Both decisive proofs use coverage root/representative claim 998. These are actual selection facts, not source-expression attribution.

Endpoint 44 is the reached Function with return Effect endpoint 14. Its positive collection queries variable 11 and selects:

| Bound | Endpoint | Pivot; lower/upper premises | Rule; result constraint |
| --- | --- | --- | --- |
| 140 | 41 | standalone | Original; producer 104 |
| 148 | 38 | 9; 160/155 | LowerBoundAdded; 108 |
| 150 | 27 | 9; 162/155 | LowerBoundAdded; 109 |
| 152 | 34 | 9; 164/155 | LowerBoundAdded; 110 |
| 154 | 10 | 14; 112/141 | UpperBoundAdded; 111 |
| 156 | 39 | 9; 166/155 | LowerBoundAdded; 112 |
| 158 | 36 | 9; 168/155 | LowerBoundAdded; 113 |

Every selected record is Qualified with a decisive claimed-arm proof and no independent support. The standalone uses coverage/representative 232; the six replay proofs use 4. All weights are empty except record 158's left PUSH of `SubtractId(0)` with `Empty` family and count one; its right side is empty. The exact differing uncovered-claim sets remain in the frozen transcript. The listed binary premises are not recursive source ancestry transcripts.

`compact/collect/mod.rs:849–894` queries these records and then **clones only their bounds**, discarding record/reason/evidence from the compact value. Lines 920–935 fold their positive compact images. Lines 1107–1140 treat a bound endpoint `Pos::Var(z)` as a secondary occurrence of `z`, rather than recursively querying `z`'s lowers. Consequently the seven selected records do not promise a transitive concrete-effect query. Their endpoint shapes and per-entry images are not printed; an ordinal guess associating each endpoint with one secondary variable is not evidence.

`compact/collect/type_nodes.rs:13–30,203–239` sends the reached Function's `ret_eff` into positive Effect collection. The completed observed image is exactly:

```text
Primary: 11
Secondary: 14,29,21,30,9,33,31
weight(31)=[SubtractId(0): pops=0, floor=[], stack=[Empty]]
all other weights empty; no concrete rows or constructors
```

The source-supplied `mu` above maps the retained unweighted occurrences to 9 and omits 21/31/33. `generalize/simplification.rs:99–120` follows substitutions, omits absent targets, and rewrites the actual Function return Effect; duplicate target occurrences merge weights. The observed accepted generalized port is the single unweighted variable 9. The empty ancestor chain means no supplied parent scheme transforms it. `generalize/mod.rs:837–870`, `generalize/finalize.rs:3–28` and `compact/finalize.rs:415–426,542–549` finalize that observed port as scheme `p4=Var('9)`, installed by `analysis/session/instantiate.rs:54–82`.

This establishes the recorded aggregate Effect image and its final scheme position. It does **not** establish that any of records 140–158 has the line-64 `send` as parent. `Original` is proof attribution, not the identity of that source operation; a binary replay proof cannot substitute for the missing source origin and endpoint-node contents.

The transcript later generalizes `DefId(8)/TypeVar(36)` at epoch 313 with an empty compact root. It supplies no source label or Effect observation for that root. The ordering shows that a later component exists; it does not prove which exact line-64 constraints were already present at epoch 291. Therefore neither “line 64 is a selected run bound” nor “its contribution arrived only after run generalization” is asserted from epoch numbers alone.

## 4. Deriving the actual consumer route, conditional only at activation

This route uses the **captured finalized interface**, not the guessed pre-generalization `v/u` graph.

`lowering/name_ref.rs:83–115` creates the global `run` reference with fresh use Value, pure reference-evaluation Effect, original source span and `ApplyRefResolution`. `analysis/session/lifecycle.rs:1092–1101` passes its exact parent/target/use Value to the SCC owner. `scc.rs:266–288` selects InstantiateUse if the target is quantified; otherwise an appropriate OpenUse path applies. `analysis/session/selection.rs:1048–1106` and `analysis/session/instantiate.rs:345–525` consume that exact event and the actual installed scheme. The capture does not print the line-64 event, so this branch's activation remains a missing observation.

For a completed InstantiateUse of that scheme, `instantiate.rs:625–636,732–760,788–910` **derives**, through its memoized fresh-variable and node maps, the positive provider:

```text
F_use = Fun(Var(A), Row([Con(ev,[])],Var(B)), Var(B), Var(A))
```

This is one per-use map, preserving the shared tail/return binder `B`. It creates no annotation subtraction identity from this stack-free scheme and retains no independent choice of `B` for the return port.

`lowering/body/signature_helpers.rs:217–260` constructs the operation signature's return row with `ev`. For the actual completed `send` application, `lowering/expr/tail.rs:535–627` creates a four-port demand, then forwards its actual call-return Effect to `c_send`. For the actual completed outer `run` application, the same owner emits demand

```text
D_outer = Fun(PosVar(arg_value), PosVar(c_send), NegVar(K), NegVar(V))
```

and emits `callee_evaluation <: O` and `K <: O`, for its fresh result Effect `O`. `tail.rs:740–755` uses the bare `K` route for a global callee; the special unannotated local-argument stack branch is not justified for this global `run` reference. Source application origin/boundary/span is retained at `tail.rs:638–682`; the source-boundary record itself is not in the transcript.

When the actual provider `F_use` meets `D_outer`, the **owning Function consumer**, `constraints/machine/propagate.rs:210–269`, emits, with the actual replay context `W`:

```text
arg_value <: A                  @ swap(W)
c_send <: Row({ev},B)           @ swap(W)
B <: K                         @ W
A <: V                         @ W
```

The provider argument Effect is a Row, not `Neg::Bot`; the pure-argument passthrough branch is not selected. No `c_send <: K` or `c_send <: B` edge is emitted by that Function transition. These assertions follow by matching real constructors; they are not transitions merely stipulated for a checker.

On a reached replay of the **concrete nullary `ev` contribution** against `Row({ev},B)`, `propagate.rs:1007–1042` finds the matching head and invokes `enqueue_derived_row_item_neu_args`. The latter's loop at 955–985 has zero iterations because `ev` has no effect type arguments. That replay emits **no subtype to `B`**, and no matched argument subconstraint. A nonmatching effect family would instead produce the actual `DirectToUpperTail` derivation to `B` under the same weights. This local consumer fact is stronger than an empty-row or family-partition argument: it identifies the branch and its exact absence of a tail-producing child.

This proves the route produced by those completed constructor/consumer calls, conditional on this actual instance being activated with this captured provider. It does not prove global absence of `ev` at `O`, exclude another independent derivation, or attach a source witness to the matched event. No positive output occurrence of this explicitly handled contribution is furnished by the matched-head transition. Its legitimate local outcome can be handling; mandatory positive retention would be an extra hypothesis absent from H.

## 5. Minimized operational obstruction

The remaining premise is not a missing family shape or selected root. It is the actual **source-use/contribution join**:

```text
J64 = one source-boundary/application record for the line-64 send,
      its returned concrete ev lower and computation c_send,
      the enclosing run reference's parent/target/use Value,
      the actual InstantiateUse (or OpenUse) event and its provider,
      the one actual rho map and Function replay parent,
      the same concrete lower's reached RowItem match/tail event,
      plus any alternative actual output derivations at O.
```

For the requested stronger connection to pre-generalization selection, add actual endpoint shapes and source/derivation ancestry of the relevant selected return-Effect records and their binary premises, under the epoch-291 view. The capture supplies none of these source application IDs, `rho` images or concrete-parent joins. Thus it cannot decide whether a selected pre-generalization record represents this source contribution, nor whether its actual output fate is matching-head handling, another output path or exclusion. No falsifier of H is obtained.

The earliest inspected retention omission is at the source application itself. `tail.rs:614–627` admits the callee-evaluation and return-Effect forwarding constraints with `OriginId::internal()`, with no structural parent linking those admissions to the source Call demand in this owner. It then returns the result Effect in an ephemeral `Computation`. The application provenance inserted at `tail.rs:654–663` stores the ExprId-keyed module and spans, not that Effect slot, boundary, origin or forwarding record. The primary supplied the frozen complementary [source-owner audit](../progress/2026-10-12-run-origin-lineage-audit.md), which additionally identifies `typing.rs:1–5,18–24` and `expr/chain.rs:17–26`: computation slots are ephemeral and ExpressionActual registers the Value alone. This is an omission at the inspected owners, not a repository-wide impossibility or proof of effect loss. The forwarding constraints still exist and propagate; an inverse reconstruction has not been shown to identify the exact source/output pair uniquely.

There is a concrete retention boundary: `generalize/provenance.rs:23–78` reports scheme completeness Incomplete, and `collect_pos` at 309–338 explicitly omits root Function argument-Effect, return-Effect and return witnesses; only nested Function positions traverse those ports. The instantiation sidecar reads only available witnesses. This is why a root-return source parent cannot be inferred from that sidecar, even though cloning preserves binder sharing. `constraints/mod.rs:3126–3158` retains generalized witness paths/incoming derivations and instantiation owner/target/use Value, but it does not itself store `SchemeInstantiator.vars` or supply an omitted witness. The maps and parents exist at their constructors; the supplied output does not expose them.

## 6. Economy audit and one different next method

The earlier local gamma countermodel and complete-row partition did not join an actual source output. The selected-root capture now supplies `P_sel` for this variant, so repeating either earlier argument would leave `J64` untouched. H and ordinary effect inference retain their original A/B responsibilities. Reconstructing exact source lineage from merged compact variables, numeric IDs or absent root witnesses is D debt; this classification closes no gate and authorizes no new representation.

The next method is a **single bounded source-owner capture of `J64`**, authorized and executed by the primary's verification owner: observe the already-held source application/boundary and returned computation at `make_source_app`; the actual `instantiate_use` tuple and `SchemeInstantiator` map; then the reached Function replay and row-head/tail transition, recording the same parent constraint and actual weights. If a pre-generalization contribution claim is retained, inspect the selected record's actual endpoint shape and recursive ancestry rather than guessing from its compact occurrence. Keep nullary matched-head events observable even when they emit zero children. Stop once the original concrete parent is joined to a reached match/tail and actual `O` observation, or an authentic alternative/excluded path falsifies the proposed mapping.

This method retains an owner fact already available; it neither adds a semantic edge nor a reconstruction layer. No Oracle rerun or instrumentation change was performed here. A new capture requires its own exact lease and bounded process budget from the primary. This packet stops at the localized missing owner evidence.

## 7. Checks, resources and exclusions

Checks already run: static `rg`/`sed`/`cat` owner reads; inspection of the three existing capture files; complete-byte SHA-256 snapshot and final recheck; direct reading of repository ref files confirming both supplied baselines. No Git command or mutation, build, Cargo/test, Oracle execution, checker, measurement, external tool/contact, configuration change or delegation occurred. Each command was one lightweight process at a time. Broad temporary-path enumeration initially overmatched the checkout prefix; the exact capture files were subsequently read directly. No inference conclusion rests on truncated search output.

Resource allocation: at most 30 minutes and one lightweight process; no heavy process or numerical experiment. CPU/RSS were not instrumented. Requested runtime: normal `gpt-6.1-sol/high`; observed model/effort metadata unavailable (unknown); no Astra assignment. One leaf producer; primary retains verification and independent-review ownership.

Unverified: actual line-64 instantiation/replay/source attachment and residual lineage; per-selected-bound endpoint images and ancestry; complete replay/activation; final expression Effect; alternative output paths; original string fixture; universal H, complete Call, soundness, required principality, normal progress/termination and F5 replacement. This artifact is independently reviewed within its conditional scope and remains research-only. No production behavior changed.

## 8. Dependency snapshot and commit packet

Exact dependency hashes follow in the table below. The five instrumented-owner hashes and three capture hashes agree with constructor-derivation §11 where applicable. No dependency was intentionally modified by this producer.

| Dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-12-native-negative-residual-constructor-derivation.md` | `d4dff22c2d5f171d8236e9a7e8a9e144ee3e12dc9a1e8642cc9f89f8740eb2d3` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `Oracle/crates/infer/src/analysis/session/generalize.rs` | `4ea4821eb197ceecb82db9c8520458ea1b14f40f2d1e8e7b0c79566279e3e988` |
| `Oracle/crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| `Oracle/crates/infer/src/analysis/session/selection.rs` | `18865934a6b9d5a86e246f45f9cf6cfe950d7867d4ec533d79ff3490c03c5b33` |
| `Oracle/crates/infer/src/analysis/session/lifecycle.rs` | `196b0f1eeef891e3547bf77e3d00f5f0574399e24bc59c4697219df6ff93d5ed` |
| `Oracle/crates/infer/src/compact/collect/mod.rs` | `23dce0d501aac161b0bd4d702ba6eda65c45a38f23c53965b62b32537a084b7a` |
| `Oracle/crates/infer/src/compact/collect/type_nodes.rs` | `405a1bf9b40a2dff55cbd20a22902f1acb244efb39578ebabac9f341954f1cf8` |
| `Oracle/crates/infer/src/compact/finalize.rs` | `53a2452b109ddb461d98f6124d410fa2e771e700e272084f3b83ed87b4f3d272` |
| `Oracle/crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| `Oracle/crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `Oracle/crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `Oracle/crates/infer/src/generalize/provenance.rs` | `83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0` |
| `Oracle/crates/infer/src/generalize/simplification.rs` | `13936efe8423630581ccf7f813ee9b3fcc82ca2cbba4a7fd9284fc741b53536a` |
| `Oracle/crates/infer/src/generalize/finalize.rs` | `a8e5a1c8e6ad57d1fac7e25a1ab6a329093e5c76e6d84c0625c124c349f07492` |
| `Oracle/crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `Oracle/crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `Oracle/crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `Oracle/crates/infer/src/lowering/body/signature_helpers.rs` | `8302de665ec38ef4a1cf2e00b762b74c7f5fb85e866526224ec527d487cea4cd` |
| `Oracle/crates/infer/src/scc.rs` | `5c0c70a4681db1c9687bc0da5c5ac70cfcad9f9f286778d87811b832dc4506e6` |
| `/tmp/yulang2-run-projection.yu` | `73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9` |
| `/tmp/yulang2-run-projection-min.log` | `d60677637dcd82aed0bce2796a4804f09c53d45b2747b98b9e9855f2e7a2acb9` |
| `/tmp/yulang2-run-scheme.log` | `f8d06b5de73c8399987d4a79d34da6ca3ce07896dd97979142928fc75b910178` |
| `notes/progress/2026-10-12-run-origin-lineage-audit.md` | `34507207ff1ebec8dd75d54ad37897c56f13241b2d99bf26589bdb925f6a9c5b` |

Commit packet: exact leased path `notes/theory/2026-10-12-run-effect-contribution-proof.md`; baseline `c1041f8f4706e847bf709e36728211965be24980`; Oracle baseline `a58eefc31e22141574b6f20c6a5748151c6d79f1`; claim class independently reviewed bounded owner characterization and conditional application derivation; concrete source/output join OPEN. Checks are §7. Proposed checkpoint message: `research: localize run send contribution to source-use replay join`. Shared-record deltas left to the primary/curator: retain H and complete Call OPEN; record `P_sel` supplied for the int variant and `J64` as the next owner evidence; distinguish the concrete matched-head route from residual/output membership. No shared record was edited.

Independent review: a compiler-referee found no blocking, major or minor
finding within the stated conditional scope. The review confirmed that the
captured substitutions, shared fresh-use map, four-port obligations and
nullary matched-head result follow from the inspected owners. It also confirmed
that `J64`, attachment/residual correspondence, actual output fate, H,
complete Call, soundness and required principality remain OPEN.
