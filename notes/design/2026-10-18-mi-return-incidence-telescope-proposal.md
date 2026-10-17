# Candidate MI Return incidence telescope with a noncircular introduction key

Date: 2026-10-18
Sprint: `mi-return-incidence-telescope-20261018`, revision 1
Contract SHA-256: `850c243c9123b31d440270f1706dea82133107de8986fbfcc2163735011e68eb`
Baseline: `9c2718db9`
Status: **new MI candidate; not adopted; old consumer bridge absent**
Original/local/fixed-family conditions closed: **0/0/0**

## 1. Result of source-owner recovery

The pinned old owners do not supply a fieldwise incidence telescope for the original Return operator. The source Return meaning fixes a completed observation by whole `ReturnMem_A(Return(v,r,C_e,w_e))`, whose displayed conditions include `JointWF(C_e,w_e)`, hereditary `ValueMem_A(v,r,e)`, and original result/provider/root/world incidences. It does not give the dependent field declaration/order or typed projections for those incidences. Prefix meaning says same current world, environment and original code incidences with no result, including zero-step; it does not expose a typed prefix field declaration. SIG §3.4 and Registry §4.1 require those actual telescopes before old catalogue/provenance/license or Result registration can be built.

This proposal therefore defines an explicitly **new MI consumer interface**. It does not claim the unknown old incidence field types, fill old `Port_Return`, or bridge to old `DeclContribution.Op`. The candidate can be reviewed as a concrete typed extension with a sharply bounded source-compatibility gap.

## 2. Bare source introduction identity, before license

Use the actual already established values:

```text
q_data_M : Data_MI(E_MI,name u_id,Value(A_id_use))
resolve_f : Resolve_MI(u_id,d_id)
n_f : Normalize_MI(q_data_M) = result(name u_id)
C_use : the actual previously allocated dependency-closed source scope
site_f = (u_id,ResultName,scope C_use, original dependency graph)
```

Define a bare nominal identity record:

```text
ReturnIntroId_MI(site_f) :=
  (source_use = u_id,
   result_role = ResultName,
   resolve = resolve_f,
   data_origin = q_data_M,
   normalized_endpoint = n_f,
   scope = C_use,
   dependencies = the actual original dependency map of C_use).
```

`ReturnIntroId_MI` contains no `H_Return`, port, typing proof, license, registration, result witness, provider, world, or completed record. It is formed from the actual source occurrence/Data/normalization inputs. Its scope map is the already established map; the allocated `C_use` occurrence itself is identity by its actual allocation. It creates no second allocation and does not identify any other dependent map with identity.

Then define the license index only from this earlier record:

```text
ReturnDeclLicense_MI(id,h_done)
```

The proposed static rule is `ReturnDecl-Intro_MI(id,h_done)`, whose premise is exactly the already formed `ReturnIntroId_MI` and the declaration's actual syntax tag. It concludes only source-static permission to declare this MI result port. This type is not indexed by the whole record that contains its proof, so the introduction is not self-referential. It grants no event authority or runtime action.

## 3. Fully typed new MI phase payloads

The candidate phase index is:

```text
H_Return_MI(id) = Done_MI | Prefix_MI
```

The new MI **support schemas** have these explicit ordered products:

```text
PortMI(id,Done) =
  (v : Value,
   r : Root,
   C_e : Configuration,
   w_e : World)

PortMI(id,Prefix) =
  (C_e : Configuration,
   w_e : World,
   env_e : Environment,
   code_occ : CodeOccurrence_MI(id,C_e))
```

`PortMI(id,Prefix)` has no `v`, `r`, result incidence, ValueMem, or completed-result evidence field. `CodeOccurrence_MI(id,C_e)` is an explicitly new index family naming the original source Name code occurrence under that current configuration; it must not be inhabited from a type-shape test or a successful result.

The separate **observation fibers** retain semantics:

```text
ObserveMI(id,Done,(v,r,C_e,w_e)) :=
  ReturnMem_A(Return(v,r,C_e,w_e))

ObserveMI(id,Prefix,(C_e,w_e,env_e,code_occ)) :=
  JointWF(C_e,w_e)
  × EnvAt_MI(C_e,w_e,env_e)
  × CodeOccurrence_MI(id,C_e)
```

`ReturnMem_A` is the exact existing whole-tuple predicate. It retains its internal `JointWF`, hereditary `ValueMem`, and all original result/provider/root/world incidences, without selecting a source witness. Thus its fiber continues to admit every original completed tuple, including non-source tuples. `EnvAt_MI` and `CodeOccurrence_MI` are new typed MI relations; the current sources supply no introduction or projection law for them. Prefix fibers retain the same actual environment/current world/code occurrence and never assert a result. Empty fibers remain valid schemas.

The field types above are types in the new MI candidate by explicit declaration. They are **not** identified with old `Port_Return(h)` because the old result/provider/root/world incidence constituent types, observation-position schema, complete contribution schema and sharing maps remain unknown. Likewise the new Prefix observation formula is a candidate new MI law; it is not certified as the old original prefix judgment.

## 4. New MI consumer and separated evidence

The proposed well-typed interface is:

```text
PortSchema_MI(id) =
  (H_Return_MI(id), PortMI(id,Done), PortMI(id,Prefix),
   ObserveMI(id,Done), ObserveMI(id,Prefix), source_scope_map(id))

Op_MI(id) =
  (PortSchema_MI(id),
   intro_id = id,
   local_whole_typing_MI = both ObserveMI fibers,
   operand_interface = the actual complete antecedent Name/Data interface,
   license = ReturnDeclLicense_MI(id,Done))
```

This defines a candidate **new** MI operator consumer. The license and observation/typing components are distinct and separately typed. `ReturnDecl-Intro_MI` licenses declaration of a schema even when an observation fiber is empty; no execution is inferred. Its eligibility rule does not state that a new MI license inhabits the old SIG `original_license_fields` type.

The order is noncircular:

```text
actual Data/Resolve/Normalize/C_use
  -> bare ReturnIntroId_MI
  -> H_Return_MI and PortMI schemas
  -> observation/local typing laws
  -> ReturnDeclLicense_MI
  -> Op_MI packaging
```

Every `LocalOrigin` in a future new MI PortProv must cite this bare `id` and a field actually introduced by its local typing law. Reused fields retain their actual operand/reference routes. No port, license, or complete record is used to define `id`.

## 5. Exact remaining source and old-consumer bridges

The new interface is typed, but the following **introduction evidence is not supplied** and must remain explicit inputs or new rule proposals:

1. `EnvAt_MI(C_e,w_e,env_e)`: the old owner does not expose its fieldwise type/projection even though prefix prose says the environment is unchanged.
2. `CodeOccurrence_MI(id,C_e)`: no pinned source-owner rule introduces the occurrence at every original unfinished/zero/admin prefix.
3. A total same-occurrence map from original Prefix observations to `ObserveMI(id,Prefix,...)`, including the old source's entire ordered code incidence and all hidden fields.
4. A total typed decomposition of `ReturnMem_A` into the **old** `Port_Return` slot/position/contribution telescope and its ordered field maps. Naming the tuple and whole predicate does not give these projections.
5. A lawful mapping from `ReturnDeclLicense_MI(id,Done)` to the actual old SIG `DeclContribution.Op.original_license_fields`. No such map is inferred. A model with nonempty Return observations and empty old independent license fiber refutes any total map unless an explicit meaning change is adopted.
6. A new MI source execution/Code-Result constructor and its soundness bridge to the original `Code_src` conclusion. `q_data_M` alone is static Data evidence, so this proposal derives no code result.

If owners supply items 1–5, the old interface may be retried from authentic types. If they do not, a complete new MI rule can be proposed only after its prefix/source constructors and same-source operation are independently derived. New MI construction is not old-family closure. Item 6 is required before any `q_f` can be substituted into the original §7.2(2).

## 6. Actual boundary and review questions

At `site_f` the new bare identity is concrete, and the candidate new MI phase product types are explicit. However the old application still stops before `Port_Return(h_done)`: its original field telescope and old incidence maps are not reconstructed. The new Prefix schema adds explicit candidate `env_e` and `code_occ` fields, but has no source introduction/map yet. Neither new license nor new MI `Op_MI` has an old SIG bridge. No actual old Result port `o_f`, source code judgment `q_f`, or parent condition is derived.

Review should check:

- Is `ReturnIntroId_MI` genuinely formed before and independently of all license/output evidence?
- Are the new MI products correctly typed while retaining all old completed/prefix fibers and original quantifiers as separate compatibility goals?
- Does `ObserveMI(Done)` retain non-source Return tuples and complete hereditary `ValueMem` without selecting witnesses?
- Does the Prefix schema retain environment/code/current-world incidence with no result, while honestly exposing missing intro/maps?
- Are new MI declaration permission, observation typing, old SIG independent license, and runtime authority kept distinct?
- Is the exact old-family boundary honest: no `Port_Return`, `DeclContribution.Op`, Result registration, `q_f`, or theorem closure?

Any new source constructor or bridge law remains a candidate until separately reviewed and adopted. No code or expected-output changes are requested.
