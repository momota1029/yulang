# MI incidence telescope: same-site construction and first missing source map

Date: 2026-10-18; revision 1; frozen application producer
Author: `/root/registered_root_proof`; no descendants
Sprint: `mi-return-incidence-telescope-20261018`, revision 1
Contract SHA-256: `850c243c9123b31d440270f1706dea82133107de8986fbfcc2163735011e68eb`
Contract baseline: `f91645e1c`; proposal historical baseline: `9c2718db9`
Status: conditional new-MI syntax checked; source/old-consumer bridge absent
Additional closures before/after: local0/0; unchanged-family0/0; original global0/0

## 1. Parent and frozen inputs

The original parent is §7.2(2) at arbitrary original
`B,X,xi=(nu,K,D),Delta_c,d_id,u_id`, source
`my id x=x; my answer=id 0`. Original source/client/assignment/strategy,
provider/world/future, guard/arm and independent F1/FK1 quantifiers are unchanged.
No candidate interpretation is adopted by this application check.

Final proposal author `/root` (Luna), correction/freeze commit supplied by Luna
`6f15cb580`, not inspected with Git:

| Frozen dependency | SHA-256 |
| --- | --- |
| Contract `tasks/agent-loop/sprints/mi-return-incidence-telescope-20261018.md` | `850c243c9123b31d440270f1706dea82133107de8986fbfcc2163735011e68eb` |
| Proposal `notes/design/2026-10-18-mi-return-incidence-telescope-proposal.md` | `0d1baa9aed2b88b33ce596485008d5e9294873fc4f4dfb8b0f18314063cbb722` |
| Proposal inbox `tasks/agent-loop/inbox/20261018-mi-return-incidence-telescope-proposal.md` | `324bd429f967c91a2a766097dec773774715c7755c19ea67514954a11776a478` |
| Prior application by this worker `notes/theory/2026-10-18-mi-return-port-license-application.md` | `2da6f04e003ad159973e1c04e64c11029ec27c6f8bf8edd3077993e034081d8d` |
| Prior application inbox | `2a3f7418d2f131f1e2c501e4334603728e4fc324641c49e445a29db1b3895a6f` |
| Meaning `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| SIG `notes/theory/2026-10-08-source-signature-incidence-construction.md` | `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a` |
| Registry `notes/theory/2026-10-10-source-owned-original-registry-construction.md` | `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb` |

All listed hashes matched. Inspected only these proposal/prior-result and
specified source-owner sections. The prior application is reused for actual
old-consumer argument types and independent-license separation, not as a
constructor of its missing field. No withdrawn auxiliary-tag argument is reused.

Actual fixed inputs at the same occurrence are

```text
q_data_M : Data_MI(E_MI,name u_id,Value(A_id_use))
resolve_f : actual resolution u_id -> d_id
n_f : Normalize_MI(q_data_M) = result(name u_id)
I_result_f = Comp(empty,A_id_use)
site_f = actual (u_id,ResultName,allocated C_use,original dependency graph).
```

The scope occurrence is reused by identity, without rerunning `mu_id`, moving
to another Name occurrence, choosing a provider or solving an event/world.

## 2. Constructible new syntax and exact limitations

### 2.1 Bare introduction identity

Within the proposed new MI definition, ordinary dependent record introduction
forms the specific record

```text
id_f = (u_id,ResultName,resolve_f,q_data_M,n_f,C_use,dependencies_f)
     : ReturnIntroId_MI(site_f).
```

The normalization equality is formed after its Data operand; the dependency
map is the actual already retained source map. No field needs `PortMI`,
`ObserveMI`, a license, a completed result, registration or a local law proof.
Therefore the former whole-record/license dependency cycle is absent. The
record stores the actual Data derivation as a source-origin field; this is
not a claim that it contains no proof object whatsoever. It contains no later
local typing/license proof. No equality of different Data/normalization
witnesses, canonical nominal-key uniqueness, or old registration identity
follows from record formation.

### 2.2 New phase support types and declaration permission

In the candidate's explicitly declared abstract sort context, ordinary product
and dependent-product formation gives

```text
T_done = Value × Root × Configuration × World
T_prefix = sum C:Configuration. sum w:World.
           sum env:Environment. CodeOccurrence_MI(id_f,C).
```

`CodeOccurrence_MI` is a newly declared type family, so forming its type does
not require an inhabitant. An empty such fiber is a perfectly formed support
schema. This is new-MI schema formation, not construction of an actual prefix
observation or an old port. The finite phase constructors `Done_MI,Prefix_MI`
are well-formed at the earlier `id_f`. Thus the candidate rule can produce

```text
ell_new = ReturnDecl-Intro_MI(id_f,Done_MI)
        : ReturnDeclLicense_MI(id_f,Done_MI)
```

inside the proposed extension. This is the newly defined static source
declaration permission only. It is not an adopted source rule, an old SIG
license, event authority or an assertion that either observation fiber is
inhabited. It is formed after the bare identity and phase tag, so does not
require the later `Op_MI` record.

The new `Op_MI` can package these new schemas, the named observation families,
actual antecedent interface and `ell_new` as a container in that candidate
context. Calling its two predicates `local_whole_typing_MI` does not turn
them into the original operator's complete-interface theorem or action law.
No original field/arm/guard catalogue or old typed occurrence is thereby
constructed. This is syntax-level local progress, not an old theorem closure.

### 2.3 Completed meaning and dependent-map discipline

On every original well-formed completed tuple `t=(v,r,C_e,w_e)`, the definition
is literally `ObserveMI(id_f,Done,t)=ReturnMem_A(Return(t))`. Its map on the
whole original membership witness is identity at those identical arguments.
It therefore does not restrict completed observations to Name executions;
every original non-source Return tuple and its complete hereditary membership,
provider/root/world incidence and hidden evidence remain in that fiber.
No provider or compatible future witness is chosen or retyped.

This pointwise reuse is not a decomposition of that original witness into
static incidence fields. The old ordered argument domains and scopes remain
unspecified, and no cross-family identity map follows from matching names.
Interpreting the entire new Cartesian product as the original well-formed
Return argument domain also needs its original typed tuple formation rule or
a total compatibility map; this packet proves pointwise equality on the
original domain, not an unprovided totalization of the old predicate.

| Field/map | What is genuinely retained | What remains unproved |
| --- | --- | --- |
| Source use/role/resolve/Data/normalization | Actual corresponding source inputs in `id_f` | No old port identity from this record. |
| Allocated source scope | Identity on the same `C_use` occurrence | No blanket identity on changed dependent result/phase types. |
| Done `v,r,C,w` | Same original tuple arguments; entire ReturnMem witness retained | No decomposition into old slot/position/contribution fields. |
| Prefix `C,w` | Candidate tuple has these explicit coordinates | Must prove these are exactly each original prefix's live coordinates. |
| Prefix `env` | Explicit new Environment coordinate | No `EnvAt_MI(C,w,env)` introduction/projection from old prefix evidence. |
| Prefix `code_occ` | New family indexed by this `id_f,C` | No constructor from the actual original source code incidence. |
| All operand provider/future fields | Remain in actual antecedent interface with original route | No new local ownership or full old PortProv map is supplied. |

## 3. First source application failure and concrete falsifier

For an original zero/unfinished/admin prefix `z` at the actual same source
occurrence, application must first construct a tuple of `T_prefix`. Even if
its original current `C_z,w_z,env_z` are projected, the last support field needs

```text
chi_z : CodeOccurrence_MI(id_f,C_z).
```

This is the **first new-prefix constructor argument without a supplied term**.
The proposal deliberately declares the family but supplies no source
introduction or projection rule. Data, Resolve and normalization construct
`id_f`, not `chi_z`. A static permission or complete Return witness has no
eliminator into this newly introduced type.

After that support field, observation membership would additionally require
`EnvAt_MI(C_z,w_z,env_z)`, JointWF at the same original current event and the
observation formula's further `CodeOccurrence_MI(id_f,C_z)` factor. None is
manufactured by schema formation. Original meaning §4.2 does prove that old
prefixes keep the environment/code/world; it does not introduce these newly
named predicates or their field maps.

Concrete consumer-level counterinterpretation: take an admitted original
current event with a valid original zero-step prefix `z`; retain its actual
world/environment/code fields. Interpret the new declared family
`CodeOccurrence_MI(id_f,C_z)` as empty. This interpretation is allowed by the
proposal because it gives no introduction or projection law for the family.
Then `T_prefix` has no tuple over that `C_z`, so there is no same-current-world
map from that original prefix to the new Prefix support/observation family.
An arbitrary different current configuration cannot repair the map. This
falsifies derivability of a total source-prefix bridge from the supplied
premises. It is not a claim that the actual Yulang source has an empty prefix
set, nor a full original-kernel countermodel or an impossibility result for a
future explicitly defined predicate.

There is also a separate coherence issue: the support tuple already contains
`code_occ:CodeOccurrence_MI(id_f,C)`, while ObserveMI adds a second factor of
that type without indexing it by the first witness or requiring equality.
In a permitted two-element interpretation, the tuple may store `chi0` and its
observation witness may carry distinct `chi1`. No proof irrelevance is given.
A source map could use the same witness twice, but preservation of the whole
new family and its independent evidence still requires an explicit law.
Likewise no internal zero/admin/original opaque-arm tag telescope is declared
by the three-factor prefix relation. Full arm/guard/witness retention is a
compatibility goal, not proved by the absence of a result coordinate.

The Prefix schema correctly contains no result `v,r` or ValueMem field. That
negative check does not by itself prove that every original prefix is admitted
with the same complete original code incidence and hidden witness lineage.

## 4. Old consumer attempt, parent application and STOP

The old route stops even earlier than any license bridge:

```text
Cat(Image_Return(B_f)) = Operand Cat(B_f) + actual old result/phase ports
```

SIG §§3.1,3.4 needs actual `Port_Return(h_done)` containing old slot schema,
observation-position schema, complete contribution schema and scope/dependency/
sharing maps. `T_done`, ObserveMI and `id_f` do not have this type. Original
incidence fields, beginning with the residual `i_result` of the prior attempt,
still have no declared typed application in the inspected owners. No map from
this new MI product/fiber to that complete old telescope is supplied.

| Old consumer | Missing actual argument |
| --- | --- |
| `PortProv` operator image/result | Actual old port plus local field set/introduction, complete local law and every dependent field map. |
| `DeclContribution.Op` | Actual old `typing_Return` and each `original_license_fields`, not two new observation predicates and new declaration permission. |
| `L-DeclaredPort` | Actual clause insertion/old catalogue port, complete PortProv and `d:DeclContribution`. |
| Registry `Fam_Return` / `Register-Result` | Whole original ordered family at actual source/Data/interface/incidence arguments, full scope map and local operations. |
| `Code-Result` | Genuine registered Result port with its required complete source interface. |

No implicit new-license bridge is introduced. In particular a supported old
port and nonempty Return observations can coexist with an empty independent
old license fiber, while the proposed new declaration permission is inhabited.
No map from the latter to the empty fiber exists. Keeping the new/old judgments
separate correctly avoids that inference; it does not supply the old license.
A complete new MI Code-Result constructor and its original-Code compatibility
are absent too, so bypassing the old family does not yield a parent code term.

Literal parent substitution is therefore

```text
Data/site/normalization and actual inherited route: retained
id_f and phase products: formed only within the unadopted MI proposal
new source Prefix map: absent at chi_z : CodeOccurrence_MI(id_f,C_z)
old Port_Return / Fam_Return application: absent
Result o_f / genuine q_f: NOT CONSTRUCTED.
```

All closure counts stay0. The original §7.2(2) callee Code premise remains open,
then Call demand `rho_c/F_c`, argument Reify/site/root/license/attachment and
whole carrier, all three checking clauses/origins, guards/arms/provider/world/
future fields and authentic elimination/`e_c` remain. F1/FK1 independent
contexts, arbitrary W/empty fibers, GC order, N-Transport, admission/observation
correspondence, soundness/principality/termination/production remain OPEN.

Next owner via Luna: the new MI prefix/source owner must supply actual
CodeOccurrence and EnvAt introduction/elimination laws and a total same-source
map retaining every original arm/guard/hidden field and witness. A claim of
full new/old equivalence needs coherent handling of both code-occurrence
witnesses. The old Return source-law owner separately supplies the complete
original telescope and typed maps, or a reviewed new-family Code bridge must
be constructed. Any new law remains candidate pending fresh review/authority;
this producer cannot certify the combined result or enlarge dependencies.

Source/native/production status unchanged: no total Phi_u, lifetime/invalidation
contract, safe implementation slice or code authority. Implementation WAITING;
quarantined compiler paths not read/written. Simple-sub generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization, and all provider/residual/witness lineages remain intact.

Four stages: pins/actual inputs; candidate record/product and meaning check;
source/old-consumer applications and falsifiers; parent substitution/freeze.
Grant300s/4 stages, requested Sol/high; observed effective model/effort UNKNOWN.
First recorded checkpoint `2026-10-17 16:06:07 UTC`; launch/exact active runtime
UNKNOWN. Full300s charged, remaining0; descendants0/Astra0. Final checkpoint
in handoff. Only exact artifact/inbox leases written, no scratch. Narrow reads,
field/map reasoning, parent substitution, readback/SHA checks only; no tests,
builds/probes/code/Git/external contact/nested CLI. Fresh review/Luna adjudication
pending. Writer STOP after handoff freeze; no continuing write activity.
