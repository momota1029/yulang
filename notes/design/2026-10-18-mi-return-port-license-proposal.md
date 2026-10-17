# Candidate: source-owned MI Return ports and licenses

Date: 2026-10-18
Sprint: `mi-return-port-license-construction-20261018`, revision 1
Contract SHA-256: `9855a9dea3da71281c44b464f3d5383f8aee182de32d1e83c0d5757a43070f69`
Baseline: `8f7e5c6fe`
Status: **candidate definition; not adopted; actual application not yet checked**
Original/local/fixed-family conditions closed: **0/0/0**

## 1. Decision being proposed

At the actual normalized source Name occurrence `site_f=(u_id,ResultName,...)`, use its real `Data_MI` formation plus the original Return/prefix clauses to introduce a **two-phase local operator schema**: one completed-result phase and one unfinished-prefix phase. The schema is declared by the actual local operator introduction at `site_f`; its fields are the complete original phase tuples and their dependent evidence. The completed phase alone is the Result port consumed by `Code-Result`; the prefix phase remains in the complete operator interface and preserves zero/admin prefixes without asserting a result.

For the independent local contribution license, propose one new source rule: an actual source-owned Result operator declaration at `site_f`, with the actual `Resolve(u_id,d_id)` edge and `q_data_M`, introduces a static `ReturnDeclLicense` for that declaration's local result port. This license means only that the source declaration may contribute its declared static port. It does not claim a Return tuple exists, execute the Name, create an event authority, or license a native runtime action. `ReturnDeclLicense` is separate from `ReturnMem`, port support, PortProv, and owner equality. This is a new static source rule and remains a candidate until reviewed and adopted.

This makes a specific, falsifiable interpretation choice instead of treating an arbitrary evidence family as semantics. It preserves all existing completed and prefix observations. It does **not** yet prove that the complete typed port schema, actual dependent maps, or every original license field can be constructed; §5 records the exact outstanding type boundary.

## 2. Pinned owners

All dependency bytes were checked before writing:

| Owner | SHA-256 | Role here |
| --- | --- | --- |
| `notes/theory/2026-10-18-mi-return-local-declaration.md` | `c810618a02533b04fd94c3c212438cb3b441f2d00885a440b426f622ccfb1e91` | prior corrected obstruction |
| `notes/theory/2026-10-18-mi-return-local-declaration-source-audit.md` | `483515ce93aea592e19049ec397b3e6ffbd4c4ecba870ae63eb42cb74fd78c3a` | independent source falsifiers |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` | original whole Return/prefix meaning |
| `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` | actual typed ports, PortProv and Op evidence |
| `notes/theory/2026-10-10-source-owned-original-registry-construction.md` | `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb` | source owner, port and Result consumer staging |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` | fixed choice A |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` | existing adopted interfaces; no Return law |

## 3. Proposed local schema and introduction

Use the following source-local declaration, indexed at the already allocated occurrence and actual operand, not at a new nominal use:

```text
q_data_M : Data_MI(E_MI,name u_id,Value(A_id_use))
n_f = Normalize(Value(A_id_use),name u_id) = result(name u_id)
I_result_f = Comp(empty,A_id_use)
B_f = actual Name operand at u_id
site_f = (u_id,ResultName,actual original scope and dependency graph)
```

The candidate phase index is exactly:

```text
H_Return(site_f) = { completed, prefix }
```

`completed` has the original whole tuple shape `Return(v,r,C_e,w_e)` and its dependent field evidence. `prefix` has the original unfinished/zero/admin prefix tuple at the same current configuration/world and original code incidences, with **no result field**. The phase tags distinguish clauses; they do not quotient or identify witnesses. The complete family admits all original tuples, including non-source completed Returns and every original prefix. It is not restricted to the source execution image.

Proposed operator introduction:

```text
Return-Local-Intro
  q_data_M at the actual u_id -> d_id resolution and C_use
  actual source ResultName operator occurrence site_f
  full original Return and Prefix clause meanings at their declared indices
  ---------------------------------------------------------------
  intro_Return(site_f, B_f, H_Return, Port_Return, maps_Return,
               typing_Return, license_Return)
```

This is an introduction at the source operator occurrence, not at its receiver/root. `C_use` is reused by identity. The `u_id -> d_id` resolution, `b_use`, `mu_id`, `reg_M`, `ref_M`, and all dependencies keep their adopted owners. `intro_Return` does not create a new `mu_id`, `u_x`, provider, world, event, force, or result witness.

### Field-to-consumer map

| Candidate field | Proposed type / dependency | Actual consumer argument | Status |
| --- | --- | --- | --- |
| `h_done` | `h_done : H_Return(site_f)` tagged `completed` | `Cat(Image_Return(B_f))` result/phase occurrence; `Port_Return(h_done)` | tag proposed; port payload still needs the exact telescope below |
| `h_prefix` | `h_prefix : H_Return(site_f)` tagged `prefix` | complete Return/Prefix operator interface and `PortProv`; never a Result port | tag proposed; no result field allowed |
| `B_f` | exact antecedent operand catalogue `Cat(B_f)`, owner and full dependency maps | `Operand(0,Cat(B_f))`; operand interfaces of `DeclContribution.Op` | established at same `u_id`; identity on `C_use` |
| `Port_Return(h_done)` | candidate whole completed phase schema at actual original scope | `Cat(Image_Return)` and Result header/`Declare-Owned-Port` | dependent field types/incidences not complete yet |
| `Port_Return(h_prefix)` | candidate whole prefix phase schema at actual original scope | complete operator phase schema, PortProv, original Prefix application | dependent field types/incidences not complete yet |
| `maps_Return` | actual ordered dependent operand/result/phase maps and shared equations | `rho`, `fields_Omega`, `PortProv`, insertion route | must be constructed from original declaration; no identity is assumed after changing types |
| `typing_Return` | original complete Return/Prefix interface law, including whole-tuple completion and unfinished/zero/admin cases | `DeclContribution.Op(...,typing_Return,operand_interfaces,original_license_fields)` | original observation meaning is pinned; its precise fieldwise typed judgment is not |
| `license_Return` | new `ReturnDeclLicense(site_f,h_done,intro_Return)` introduced by the actual source rule in §1 | the independent Return-local license field of `DeclContribution.Op`; then `L-DeclaredPort` | explicitly proposed new static rule, not derived from support, observations, provenance, or OwnerPortLicense |
| `o_f` | actual registered completed Result port from the whole declaration and actual Data formation | `Register-Result`, then `Code-Result` | not present until all prior fields and consumer premises typecheck |
| `q_f` | `Code-Result(q_data_M,o_f) : Code_src(...,result(name u_id),Comp(empty,A_id_use))` | original §7.2(2) at the same source occurrence | conditional only; not derived in this proposal |

## 4. Proposed phase payload and owner maps

The completed payload preserves the named original fields as separate dependent coordinates:

```text
Done_Return(v,r,C_e,w_e;
  wf : JointWF(C_e,w_e),
  value : ValueMem_A_id_use(v,r,e),
  i_result : original result incidence,
  i_provider : original provider incidence,
  i_root : original root incidence,
  i_world : original world incidence)
```

The unfinished payload is:

```text
Prefix_Return(C_e,w_e;
  wf : JointWF(C_e,w_e),
  i_code : original code incidence,
  i_provider : original provider incidence,
  i_root : original root incidence,
  i_world : original world incidence,
  no result coordinate or result proof)
```

These are schematic field layouts, not claims that the five incidence fields have been given the right source types. Their actual types and binder order must be recovered from the original complete declaration before the schema is usable. The whole `ValueMem` and `JointWF` evidence remain dependent fields; they are not erased to endpoint values.

The proposed operand map is the actual existing operand map at the same use:

```text
operand map: B_f -> site_f via the actual Name/use edge
C_use map: identity on the allocated C_use
resolution: u_id -> d_id via the adopted Resolve and actual b_use/mu_id
```

The completed Return relation preserves its actual `v,r,C_e,w_e`; the prefix relation preserves its actual current configuration, world, and original code incidences. A provider/future coordinate is mapped only by its antecedent field map. No provider, root, world, or future map may be set to identity until the exact dependent types and original shared equations are checked. The actual source-local fields, if any, receive `LocalOrigin(intro_Return,k)` only after the whole typing/interface law identifies them. Reused fields retain `Operand(0,Omega_f,rho_f)`.

## 5. Exact unresolved typed inputs

The source audit and prior owner decomposition do not enumerate the actual dependent types or order for `i_result`, `i_provider`, `i_root`, `i_world`, `i_code`, or the complete original `Port_Return(h)` field telescope. The pinned ReturnMem formula names `JointWF` and `ValueMem` and refers to “original result/provider/root/world incidences”; it does not define those incidences. SIG §3.4 requires their complete typed field maps. Therefore the schematic payload above cannot yet be passed to `PortProv`, `DeclContribution`, `L-DeclaredPort`, or `Register-Result` as a well-typed record.

The proposed `ReturnDeclLicense` also needs an owner-side derivation from the actual source signature. The candidate rule in §1 gives its intended introduction, but the current source-owner documents contain no such result-local syntax/typing judgment. It is a proposal for that missing owner rule, not a proof that current `my answer = id 0` supplies it. This is the first semantic adoption question after the exact incidence telescope is recovered.

No candidate choice here converts the source observation into static license. `typing_Return`, all original semantic license inputs, and the new syntax-owned declaration permission are distinct fields. If the actual SIG `Op` requires an additional independent license not supplied by `ReturnDeclLicense`, retain it as another unsupplied field rather than identifying the two.

## 6. Consumer application obligations

A successful application must derive, in order:

1. Both exact phase payload types and their full scopes/field maps.
2. `PortProv` with every operand occurrence and every genuinely local `LocalOrigin(intro_Return,k)` occurrence; no arbitrary field-owner assignment.
3. `DeclContribution.Op` with the actual whole `typing_Return`, complete operand interface, and each independent original license field.
4. The source-local owner declaration and scope map; `L-DeclaredPort` at the actual origin/receiver/route indices.
5. `Header-Result` and `Register-Result` without requiring `o_f` to construct itself.
6. `q_f=Code-Result(q_data_M,o_f)` at the same `u_id`, with the fixed A type `Comp(empty,A_id_use)`.
7. Immediate substitution of that exact `q_f` into original §7.2(2), retaining every other original independent premise and quantifier.

Neither the new local license nor registration proves old opaque-consumer compatibility. Any old consumer use requires its original complete argument and interface; otherwise record a separate premise. The Result port and its local operator declaration remain distinct objects.

## 7. Falsifiers and review request

Reject or repair this candidate if it: drops a completed non-source Return tuple; omits zero/admin prefixes or a result/provider/root/world/code incidence; puts a result coordinate in the prefix phase; treats `ReturnDeclLicense` as event authority; derives it from `ReturnMem`, catalogue support, PortProv, root equality, or `OwnerPortLicense`; omits an independently required SIG license; changes the owner of an operand field; uses identity on an unverified dependent map; forms `o_f` circularly; changes A; or narrows any original theorem quantifier.

Review should first decide whether the phase separation and source-owned static declaration license are a coherent candidate interpretation of the existing source grammar. Separately check the actual telescope and all consumer argument types. A CLEAN review can certify the proposal's scope only; adoption and proof/application remain separate. No code or expected output changes are requested.
