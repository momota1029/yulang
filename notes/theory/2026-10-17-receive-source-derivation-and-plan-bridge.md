# Two-Call receiving source derivation and proposed plan bridge

Date: 2026-10-17  
Status: Draft candidate for independent review; no source admission, semantic adoption, runtime implementation or production authority.  
Parent: `型推論と実行器が証明込みで実装できるまで続ける` remains OPEN.  
Sprint: `receive-source-derivation-and-plan-bridge-20261017`, contract revision 1.  
Baseline: `6dbb6ad2511b182c1761ecea73f25640eee68899`.

## 1. Fixed source component and claim

Keep the selected authentic component and all original source identities:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

The occurrence notation is shorthand for resolved source nodes. Keep Lambda
`L`, formal `f`, annotation `a`, shared root `R_f`, scope `S`, formal Name
`n_f`, Calls `c_1,c_2`, their respective Unit operands `t_1,t_2`, the sequential
binding `b_g`, and Name `n_g`. Preserve one coherent source substitution
`xi=(nu,K,D)`, both original parameter/result endpoints, provider identities,
worlds and every opaque indexed premise. Do not identify either Call result
with the annotation endpoint merely because they are compatible.

This note records the constructor derivation that follows from frozen rules,
then the first premise that is not supplied by those rules. It drafts a
source-owned plan-export/import bridge for review. It does not manufacture a
complete source derivation `T` from annotation syntax or a successful native
constraint solve.

## 2. Constructor-by-constructor derivation frontier

| Source node | Constructor consequence | Required input still independent |
| --- | --- | --- |
| Lambda formal `f` | Its original annotation fixes the formal's declared Value(Function) interface and its original formal/annotation identities. The selected KnownFunctionReceive constructor emits the outer complete-call profile at `beta.p_call`; the omitted outer result row contributes no concrete permission and stays open. | The Lambda's full source derivation still includes its body judgment and the independently valid source context. Annotation syntax alone is not `T`. |
| Formal Name `n_f` | Name/read refers to the actual formal binding at `R_f`; it preserves the same callable/provider certificate and source path. The first-use constructor composes the original Name/Result/Call map into `c_1`'s complete-use slot. | The selected callable membership is discharged only for a challenge formed from an independently valid punctured caller context; it cannot establish that context's satisfaction by itself. |
| Unit `t_1` | Ground Unit formation and its source Return are available at the original occurrence. Delay retains this same inert carrier and lexical references. Its source diagonal is pure; this does not restrict other whole-carrier clients. | Compatibility with the original call's full dependent slot and valid execution remains part of the exact Call premises. |
| First Call `c_1` | The source Call constructor forms distinct callee, whole-carrier, receiver, entry, invocation, return and future-provider slots. `Applicable(beta,c_1,p_call)` records the source-origin map. A schema does not imply that those slots satisfy the Call guards. | At the same original `A_1,E_1,xi`, the independent punctured caller context must satisfy its whole predicate `Phi_B^H`, including the hypothetical `g:Value(A_1)` and its actual `c_2` obligations. The original source supplier audit identifies this as the first missing semantic premise. The native route additionally lacks its single anchored full MODEL. |
| Binding `b_g` | At an actual `c_1` Return `z_1`, selected ResultBind combines the actual returned packet `W_1` and the consumed callee/carrier packet `V_1` using their two tagged maps at that same return/world. It binds the same actual returned value/provider. | No Return packet can be populated before the actual source Call premises and Return constructor hold. ResultBind does not prove `c_1` admission. |
| Name `n_g` | Reads the actual binding certificate installed at `b_g`, preserving its provider, packet, paths and scopes. It creates no receiver or profile introduction. | Inherited premise: the authentic `b_g` binding exists from the preceding source derivation. |
| Unit `t_2` | Ground Unit formation/Delay repeats at the distinct source occurrence and argument slot. | Keep its independent Call-specific dependent interface; do not reuse `t_1`'s identity or prove the caller context by equality. |
| Second Call `c_2` | The source Call constructor forms its complete second actual use and future-provider slots from `n_g`, `t_2` and the actual provider in `b_g`. | Requires the bound callable's original same-provider contract and the complete independently admitted challenge for `c_2`. `c_1`'s formation or successful first use does not imply it. |
| Lambda/Generalize | Given an independently valid body derivation and its original local laws, source-Generalize retains the actual binding/result/provider, whole profiles, scopes, `xi`, contracts, and live-to-published dependencies. | The missing body source derivation above prevents constructing this premise from the current evidence. Generalize is not a rule for accepting its own unproved body. |

Thus the selected constructors give a real partial derivation skeleton and
source interfaces, but not a complete judgment `T` for this component. This
is an OPEN premise, not source invalidity and not a reason to narrow the source
domain.

## 3. Existing selected profile actions used in the skeleton

For the actual `Value(Function)` formal, KnownFunctionReceive produces the
outer complete-call component at the original `beta.p_call`. The direct outer
result row is omitted, so local permission is empty while the coordinate stays
open. The nested `[ctrl]` rows remain attached to their own original paths.
Name/Result/Call composition makes the first source-use map available as a
constructor output. Neither operation asserts provider acceptance.

The selected receiving grammar contributes the current whole-carrier entry
action at its actual entry `e_r`, the matching received callable/result action
at the original `beta` path, and future-input instructions whose real origin
is the later actual producer entry. It retains every inherited `Ante` packet.
It does not stamp the earlier receiver onto a hypothetical future carrier.

At each actual return, keep the source result packet and the consumed-view
result packet distinct until applying the actual typed maps:

```text
J_z = (mu_z)*W_z union_tagged (rho_c)*V_c
```

For `c_1`, this is the packet later installed at `b_g`; for `c_2`, it is the
result packet of the body's final expression. `mu_z` and `rho_c` are the
original producer-result and consumed-view-result maps. No local rebinding,
observation or importer is allowed to mint another receiver or erase a tag.

## 4. Proposed source-owned plan bridge

The following is a candidate missing bridge definition, not a source-typing
rule and not an assertion that the current HIR/runtime already implements it.
Its purpose is to make the source constructor outputs consumed by the reviewed
callable-view algorithm explicit.

```text
T : Gamma |- e : I under xi
OriginalNodeRefs(T), OriginalMaps(T), OriginalInterfaces(T)
---------------------------------------------------------- ExportPlan
Plan(T) = (EntryPlan, ExecPlan, ReturnPlan, source-indexed references)
```

The output is a finite graph built by recursion over original derivation nodes
and registered interface references (not by unfolding recursion or enumerating
all effect-family members):

```text
EntryPlan = (original Lambda/formal/role/annotation/slot,
             actual carrier Force and result-value schema,
             original boundary/profile introduction,
             actual future-input source interfaces)

ExecPlan  = (original Apply/Name/consumer occurrence,
             actual callee/provider and whole-carrier slots,
             complete callable port and execution delimiter,
             designated producer entry/body/native-return/consumer)

ReturnPlan = (original dependent return binder and world,
              actual returned-value map mu,
              consumed-view result map rho,
              two tagged source inputs and source binding destination)
```

### 4.1 Required constructor cases for this component

1. **Lambda/formal:** join the plan only to the original `L,f,a,S,R_f` and
   resolved role. EntryPlan includes the `Value(Function)` formal component at
   the result-side complete-call path and its separate current-carrier Force
   path. Preserve the omitted outer permission as absent/open.
2. **Name:** reference the exact `n_f` or `n_g` binding certificate. Carry its
   original provider and packet; do not infer a plan from the Name's solved
   type.
3. **Apply:** one ExecPlan per original `c_i`, with the exact callee and
   whole-argument nodes `n_f/t_1` or `n_g/t_2`, the actual complete-call port,
   actual producer entry mode, and its designated consumer. No duplicate
   execution or shape-directed fallback is permitted.
4. **Result and sequential bind:** one ReturnPlan per original return binder.
   Retain `W_z` and `V_c` in separate tagged fields and apply the source rule's
   original `mu_z` and `rho_c` maps. Install the resulting packet only at its
   actual `b_g` binding after Return; a pending request has no completed
   packet.
5. **Future input:** store an instruction tied to the actual producer's
   original interface. Instantiate it only at that later actual entry and
   preserve its independently genuine annotation/role. Never create a
   hypothetical receiving event at `receive`'s earlier entry.

### 4.2 Import contract and soundness obligations

An importer consumes `(HIR, Plan(T))` only when each plan reference resolves to
the same original source root, occurrence, formal/binder, annotation,
substitution, slot and interface recorded in `T`. The importer rejects missing,
foreign, duplicate, cyclic-unregistered or mismatched references before the
plan can drive execution. It may index/compact the finite plan graph but may
not synthesize semantic fields from HIR shape, solved supports, tags, or
successful matching queries.

Required erasure: erasing the plan recovers the original source expression,
evaluation order, provider/entry role, typed operand maps, source result,
observation points and guards. Required execution simulation: each imported
EntryPlan/ExecPlan/ReturnPlan action is matched one-for-one with the original
source constructor event; both Return inputs and their tags are preserved at
the same actual return/world. On any invalid/missing plan reference, execution
is unavailable and publishes no partial source result.

This contract depends on original source `T`; it cannot prove `T`, establish a
native MODEL, authenticate arbitrary providers, establish a caller context,
or authorize a runtime policy. A separate reviewed design decision is needed
before its rules become selected semantics or code requirements.

## 5. Concrete playground seam and exact implementation frontier

At the pinned current source, `execute` binds `prepare`'s second return value
to `_candidate` and calls `RuntimeProgram::from_hir(hir,
RuntimeEvidence::default())`. `RuntimeEvidence` contains only
`name_consumption`. `RuntimeProgram::from_hir` walks HIR local source into
`Instruction::{Lambda,Apply,...}`; the Lambda currently stores parameter,
role, optional RootCompSchema and body. The machine's `Frame::Callee`, entry
and Return frames consume those instructions, but no imported Entry/Exec/
Return plan exists at this seam.

The proposal's implementer handoff is therefore narrow and concrete: retain a
source-qualified plan produced from an independently valid derivation, pass it
through `execute` into `from_hir`, validate source joins while lowering, and
let Lambda/Callee/actual entry/Return consumers read only the corresponding
validated plan nodes. Current producer code does not emit those nodes, and
current runtime consumers do not preserve the complete callable result recipe.
This sprint does not lease compiler source files or approve a manual record
construction as a substitute.

## 6. Parent application, falsifiers, and remaining gates

For the selected component, the constructor skeleton establishes where the
formal, Calls, actual `g` binding, and two return recipes belong. The proposed
ExportPlan makes source provenance available to a future importer iff an
original `T` is supplied. The first incomplete source premise remains the
independently satisfying punctured context for `c_1` (and the related anchored
native MODEL on that route). The second Call remains dependent on the actual
`b_g` binding and its own complete challenge. Neither gap is filled by this
proposal.

Falsifiers for the proposed bridge include: a source constructor action absent
from its plan node; a plan reference joining to another source occurrence or
annotation; a Return packet losing either tag or using different return worlds;
a future input receiving an earlier receiver's identity without an actual
entry; an omitted row becoming concrete permission; an importer accepting a
missing/foreign source node; or erasure changing source order/provider/guard.

The parent theorem, source admission, native/source correspondence, runtime
representation, soundness, principality and production cutover remain OPEN.
Reviewing this candidate can reject or refine the proposed bridge; it does not
adopt it.

## 7. Frozen inputs and work boundary

Sprint contract pins the direct source/design dependencies and current
playground owners. The most relevant pins are:

| Input | SHA-256 |
| --- | --- |
| KnownFunction first-call design | `b779ba779b66515eddb7e44ba1d0772a6853e69a1aa13a6c4528dbd8ea0852a1` |
| receiving introduction grammar | `ec3375229f956d678c64003a43bdb68c70a77c6b8e614e9348bdca6bde9d5a8c` |
| source supplier frontier | `4528791a9020278623fe271c3616c7cec9156d2324f41b68bea37563b33eb90e` |
| conditional source-export construction | `bfec4f6aad05711b580ceac69b242de502342c31bc09fabc701ad17c583c4961` |
| callable-view algorithm | `8a3abd17cd26162c689a592e3f855580663d53bead80e8904ac964a16e1dfcb0` |
| playground `lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| runtime `program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| runtime `machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` |
| runtime `receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |

No compiler edits, tests, builds or executable probes were performed. This is
an unreviewed research candidate, not a closed source derivation.
