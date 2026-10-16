# Choose operation: structural source instantiation and complete-clause boundary

Date: 2026-10-17
Status: candidate conditional derivation and source-owner evidence; independent review pending
Assignment: `assignment-choose-operation-source-instantiation-20261017`, revision 1
Author: `/root/choose_operation_instantiation`; sole author; no descendants
Sprint: `source-constructor-instantiation-and-export-cut-20261017`, contract revision 1
Contract SHA-256: `0395ca891612e1f28750f6d764a3a00b206bc6a57c55fb266211be4c2258df9b`
Supplied baseline: `cba9d794d1f0498262b3668f9d5cc055c16749e9`
Authority: exact two research paths only; no semantics, compiler or production adoption

## 1. Parent application and actual advance

The original parent is Call/effect H1/H2/JOINT_DEC with all original declarations,
ordered binders, shared assignment/evidence strategy, whole carriers, actual
providers, guards, pending continuations, foreign alternatives, dependent
futures and every lawful current/later bound and admission. Preserve

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin),
xi=(nu,K,D), beta=(d_f,R_f).
```

The selected instance is precisely the mathematical source fixed by
`choose-source-declaration-initial-installation.md` §1 and the selected
remaining-root constructor §§1–3:

```text
choose : Unit -> alpha+
alpha+ = ([ctrl] Unit) -> [ctrl] Int
f0(u:Unit) = ctrl.choose(Unit)
receive(f:Unit->alpha) = Bind(g, f(Unit), g(Unit)).
```

The cut is the choose request emitted by the declaration-derived result
consumer inside f0, after choose's native invocation return and before its
response. The first-f Call and future g Call remain different source nodes.
The incoming f carrier and the literal carrier used by choose are different
operands. Value-entry f0 Forces its incoming carrier despite not reading u.

**Advance.** The newly pinned operation-source construction supplies the
structural request-carrier body, its response equation and finite source
expansion. Sections 2–5 specialize those equations to choose and construct the
conditional declaration/IF placement expression; §6 applies them to the
structural D_tail branch. This removes the prior packet's lack of an available
structural operation rule. It does not instantiate the complete original
Sigma_choose or its nonstructural clauses. Their exact missing field and
compatibility obligations are in §7.

No concrete source file/CST, ModuleId, SourceNodeKey or semantic registered-root
value for this example is present in these supplied proof inputs. The original
installation note §3 expressly records that limitation. Accordingly the
address expressions below are constructor-indexed, conditional on the genuine
source occurrence; they are not fabricated numeric addresses or an executed
HIR instance. Neither a complete choose IF witness nor a complete D_tail
membership theorem is claimed. This distinct source-authentication premise
also remains for the sequential export lane.

## 2. Declaration and resolution at the inspected HIR owners

`module.rs::lower_module_with_counters` (line 1052) invokes
`source_annotation::declarations` before root planning when local source is
active. Its two passes first install every family header, then parse operation
signatures. For the original family/member nodes n_ctrl/n_choose and module M,
the emitted identities would be exactly

```text
E = SourceEffectId { module:M, declaration:key(n_ctrl) }
p = SourceOperationId { family:E, declaration:key(n_choose) }.
```

These expressions are projections of the original nodes, not names allocated
by this proof. The signature-only operation member must have no BindingBody
and no binding parameters, and its annotation must parse as Function. The
record retains p, spelling, visibility, name_position, signature_position,
range and the entire SourceAnnotationType tree. Headers exist before the two
nested ctrl row references are resolved, so those references use E without
unfolding alpha+.

For the displayed signature, its structural annotation projection is

```text
Function(
  Unit with no written effect row,
  Function(Unit with row [E], Int with row [E]))
```

with each written row's own original SourceNodeKey. The inner Function itself
has no extra outer row in this projection. This is a projection calculation
using `parse_type_source`, `parse_group` and `parse_row`, not a parser run or
proof of the full semantic Lambda. Unit is represented by the empty type
group, Int by `int`, and operation lookup uses `::` in the inspected syntax;
the earlier mathematical dot notation is not reported as a parsed token.
There are no displayed type-variable occurrences and the family is nullary.
Neither fact deletes any binders or evidence in the independent complete
Lambda. In particular the absence of binding parameters is a syntactic member
condition, not proof of an empty semantic telescope.

At the selected operation use, local_source's application construction
(lines 938–966) calls `resolve_operation` (1088 onward) with the actual family
and member spelling. Exactly one family and one nonprivate member yield
`Resolved` with that same declaration Arc. Missing, ambiguous and private
results are separate outcomes. Catch independently uses that resolution
function (1155 onward), preserving its operation_source, arm source, payload
binder and ordinal-1 continuation binder. Thus matching names do not merge
use positions, arm binders, future calls or dynamic request events.

This is direct evidence of generic source constructors. A concrete emitted
record for the selected choose source still needs its original parsed source
and successful formation; neither the old note nor this inspection supplies
that missing instance. No alternative source program is substituted.

## 3. Original telescope and conditional IF derivation

Operation-instance binding §2 gives the governing declaration form:

```text
Delta |- choose : forall rho_family, beta_local.
                 Sigma_choose(rho,beta) = (A,B,Lambda)
i = OpInst(p,theta) = (p,E,A theta,B theta,Lambda theta).
```

Here rho_family has empty projection, A's displayed projection is Unit, and
B's is alpha+. `beta_local` and the full preceding dependent interface refer
to the original complete declaration; their complete values are not supplied
by the public projection. Theta is the ONE original capture-avoiding use map
fixing Delta. It fixes the shown ground types and E. This note does not choose
unknown beta coordinates, introduce new binders or move an original binder.
The HIR value/effect-variable maps do not prove that theta is empty.

The operation-source construction §§3–4 supplies this ordering of the
structural fields, subject to the original supplied Sigma/typing premises:

1. Original declaration/scope, Sigma and theta; actual use/root/origin;
   role and typed path; original world and shared xi.
2. Actual operation provider, whole input carrier t, receiver/receipt/entry
   and their original admission evidence. Value entry is the selected case
   for the displayed Unit payload when its role derivation is supplied.
3. Original Force(t) development, including each Request or divergent finite
   prefix. A Return branch binds the same a:Unit and live C1, then its typed
   rebind. No a exists in the earlier pending branch.
4. The inert carrier T(i,a), its retained original references/K/D, native
   return delimiter, then the distinct declared consumer in its full view.
5. At emission, the actual event/origin and C2; the original pending witness
   and guard. Under these binders, each admitted r:alpha+ at Cnow and each
   dependent remaining observation/future is interpreted. Output-provider
   fields are indexed by that same r and subsequent actual result.

This ordered structural spine is not an exhaustive replacement list for
Lambda. Original guards and indexed families stay at their actual binding
positions, which must be supplied by Lambda. If beta_local is nonempty,
`exists beta_local.Packet(A, B=>J_q, Lambda,K,D,dependencies)` retains its
original witness; the arm opens fresh rigid names uniformly and cuts at that
same theta. A fresh event is not a fresh declaration instantiation.

For clarity name t_choose the genuine semantic registration of this original
declaration, c_src its structural operation clause and v_op its actual typed
reference use. These are *conditional input names*, not additional emitted
HIR fields. The selected IF rules give the following explicit construction:

```text
reg(t_choose,T_choose), actual typed c_src at original binders
  -> IF-Insert(t_choose,c_src)
     ins_src : IF(c_src) -> IF(t_choose) at that clause slot

actual Ref(t_choose,theta) at v_op
  -> IF-Use(v_op,t_choose,theta)
     use_op : IF(t_choose)[theta] -> IF(containing producer/source frame)

placement_src = enclosing_source_slots o use_op o ins_src[theta].
```

The enclosing slots are generated by Producer/entry (native-return THEN
consumer), operation Call, f0 body, f0 return/receiver, first-f Call, and
Bind-first in receive; the selected outer Catch receives that scrutinee.
At each Call retain callee, whole argument, actual returned provider/current
world, receiver, complete result and its dependent future slot. Original
O0's Inv receiver edge stays distinct from full Call and p_out(c).

The pending address expression is the consumer's Request phase within the
c_src slot of t_choose at v_op, followed by those actual enclosing slots.
It is not slot42, the native body-return phase, a reference to the future
G_call, or the newly created `Ref(t_e,m_cap)` of R_e. Projection from the IF
records returns the original full fields, including witnesses/licenses;
incidence alone supplies no satisfying tuple or admission.

For every other original clause c_j, IF-Insert(t_choose,c_j) and the SAME
actual root use would place its own complete interface at its own slot.
No source execution for c_j is required. However no complete c_Z/c_W value,
original telescope or action is supplied here, so this statement of the
constructor's application is not a completed full Theorem IF instance.

## 4. Choose Request, response and gluing calculation

Conditional on the original source-operation derivation, set T(i,a) to its
inert request carrier and A_decl to the actual remaining declaration-consumer/
view completion through its OWN result port. Preserve every administrative
frame; A_decl is not silently identified with identity. The equations are
specializations of operation-source §§3–5 and typed-core §3:

```text
Lookup(choose,theta,C) = Return(Operation(p,decl)[theta],C)
Native_i(t,C) = Invoke(receipt; Force(t) >>= (a,C1).
                       Rebind_i(t,a,C1); Return(T(i,a),C1);
                     native_return_delimiter)
Completed_i(t,C) = Native_i(t,C) >>= Consume_decl
Force(T(i,a),C2) = Request(q(i,a,event,origin,K,D),C2,k0)
k0(r,Cnow) = Return(r,Cnow)
D_tail_src(r,Cnow) = Return(r,Cnow) >>= A_decl.
```

The last line is the structural action at the cut, with its retained pending
witness/guard and actual same-port completion map. It is not the definition
of the full D_tail. The cut is after native return; no receipt/native body
is replayed. Native entry's Request instead has its own earlier raw
continuation followed by rebind, native return and the consumer. It cannot
be changed into choose's later Request. Divergence keeps all finite prefixes.

For the original literal Unit challenge, when its ground/Delay/entry premises
are provided, Force returns Unit and the operation emits the choose packet.
For every admitted response r, k0 returns exactly r in Cnow. Functional r is
inert here: its alpha+ latent behavior is not executed or reconstructed from
the signature. An arbitrary response provider keeps its own future contract.

The structural Request gluing is exact state-threaded Bind:

```text
Request(q,C2,k0) >>= (A_decl ; S_outer)
 = Request(q,C2,(r,Cnow). Return(r,Cnow) >>= A_decl >>= S_outer),
S_outer = F_ret ; J_res ; C_c ; B_g ; G_call ; A_ret.
```

The notation uses complete ordered constructor images with shared middle
tuples; J_res/C_c/B_g are their original logical relations, not new runtime
checks. Request introduction retains the original structural derivation,
receipt/entry history, i, event and pending evidence. Eliminating this
introduced structural witness returns those same fields and k0; it does not
invert an arbitrary independently licensed primitive witness. Gluing with
any admissible response uses the original response evidence and current
world, then the original A_decl and outer relations. It preserves the old
pending witness instead of existentially choosing a convenient replacement.

At Catch, the callable raw-k's Value-entry Force of an arbitrary incoming
response carrier remains OUTSIDE R_e. Its Force behavior is not erased by
k0's same-response equation. On raw resumption the current store and source
completion frames apply; no emission-state snapshot or automatic selected
shallow handler is restored. Ordered matching/guard computation outside H
can itself request, resume or diverge. Its behavior, accepted-arm OpCompat,
visibility and primitive hard guards are distinct obligations.

## 5. Lawful transport and exact finite-expansion scope

A supplied legal whole-map action mu acts on theta, carriers, guards, pending
witnesses, response/current-state indices and dependent futures together.
It fixes required imports and retains original origin/lineage references.
The IF constructor's naturality composes its incidence maps; the source
Request/Bind equations commute with that action under the original typed
map laws. This derives structural source transport only when those original
laws are supplied, and never supplies a law for an opaque primitive by itself.

Apply the reviewed local expansion lemma to this choose structural body:
replace only its lookup/entry/native carrier/consumer/Request nodes by §4,
retaining opaque incoming carriers and future provider references. This is a
finite template, with the inherited O(s+|theta|) signature/map construction
bound and constant local phase nodes. It does not enumerate responses,
worlds, histories, future calls or nonreturning carriers.

At fixed original H,U,xi and all the same original witnesses, the source
image relation before and after this substitution is equal under the named
source laws. Hence its exact upper-demand formula is equivalent on both
sides. If independently fixed G/W/Z are retained identically, replacement
also leaves that complete production operator pointwise unchanged. This is
preservation of those supplied clauses, not satisfaction of their U demands.

Native demand transport is still unproved. The finite equality does not
compile a universal upper formula into supported Simple-sub operations.
Current/later admissions must retain every new obligation on the original
joint evidence strategy; a source equality or stored Pending reference is
not an effective preservation/reflection or completion law.

## 6. Application to D_tail and the original parent

The selected remaining-root constructor consumes

```text
R_e = CompleteSeq(D_tail; F_ret; J_res; C_c; B_g; G_call; A_ret).
```

Section 4 now identifies its structural D_tail action, same-response port
and original Request/Bind gluing. The new t_e and its map
`sigma_cap o delta o m0` remain the *outer* remaining-root reference. They
cannot fill t_choose's absent complete declaration. Historical maps stay
historical; delta is not applied a second time at Resume.

For alpha+, immediate structural k0 adds no Request, while the original
g ReadInvoke is the later full invocation with its own provider/guard/future
premises. This supports the structural branch of the earlier remaining
Ctrl/Int calculation. The universal readout still requires the genuine
complete declaration result guarantee at the SAME port for every alternative,
as the selected construction §6 explicitly states. The full-f certificate
already assumes that complete Sigma and original world; it cannot prove
them circularly. The whole first-f E1/RE guard remains at C_c and cannot
replace D_tail's own phase guarantee. Negative ctrl remains local permission.

For H1 this supplies one retained structural Request/suffix construction;
complete consumed/protected/unmatched/arm/resumed accounting remains open.
For H2 it supplies conditional structural whole-map commutation; every
independent primitive action and foreign provider remains separate. JOINT_DEC
still lacks native demand interpretation, both evidence directions, and
extension laws. F1 and FK1 keep independent quantifiers. H1/H2/JOINT_DEC,
F1/FK1, first-result adequacy, principality, F5 and production remain OPEN.

## 7. Exact missing-definition proposal and compatibility obligations

The owning semantic field is **Lambda in the original
Sigma_choose=(A,B,Lambda)**, specifically its complete declared-result
consumer/pending-phase clause with original Request observation and
response/current-world/future action. The HIR owner
`SourceOperationDeclaration.signature` supplies the finite annotation tree;
it is not a Rust field holding this Lambda. At an independent complete
production root, source-contracts §3.7 additionally requires actual G and
each Z/W declaration. These are separate missing semantic inputs, not
permission to enlarge SourceOperationDeclaration or to choose empty Z/W.

A concrete completion request to the primitive-contract owner is:

| Owning original item | Required value/law at choose | Compatibility falsifier |
| --- | --- | --- |
| Sigma_choose.Lambda and t_choose registration | Original ordered parameter/tuple/evidence telescope, whole-carrier entry/admission, complete result-consumer phase and full alpha+ response; original declaration/use/phase identities | Only Function4/endpoints supplied; hidden binder deleted or reordered; another source root substituted |
| Structural pending clause of Lambda | Typed introduction/elimination for the §4 body; retain original pending witness, same-port Request gluing and lawful response/current-world/completion action | Replays receipt/native return, restores C2, forces latent r, or chooses a new witness at response |
| Original guard G | Whole constraint envelope: descriptor/bound, provider/world/admission, license/scope/profile/K/D; source-base typing into it | G treated as family support or comparison success; changed admission inferred from positivity |
| Independent Z clause, if the original root has one | Its actual whole-tuple predicate, ordered parameter/evidence telescope, fixed/changed fields, original insertion and own license/domain/provider/future actions | Unanchored witness discarded for lacking execution; new provider cast into r's interface; Z assigned false without authority |
| Every independent W clause | Same original predecessor/output/rewrite witness and whole action, including changed-provider admission and dependent futures | Recombines marginals, forgets predecessor, or preserves only row-family identity |
| Complete declaration result/phase guarantee | For every original alternative and lawful response/history, same-port phase development retains genuine Ctrl/full-alpha+ guarantee and guards | Structural k0 equation substituted for universal complete guarantee; first-f E1 used instead |
| Original demand consumer | Effective supported generation/propagation with both evidence directions and coherent later-bound/admission transport | Stores desired formula without interpretation, discharges by an assumed transition test, or reuses a stale completion |

The completion must preserve the original external package when one is
independently fixed. Where meaning is genuinely unspecified, selecting it
returns to Luna's semantic authority path. A source-owned candidate Sigma
could eventually instantiate the earlier theorem parameter, but this packet
does not select one or claim equivalence to an unspecified foreign package.
The structural source equations do not decide whether a non-source tuple is
licensed. No impossibility or source-qualified counterexample follows from
that underdetermination.

**CHOOSE-COMPLETE-2 — Luna / primitive-contract owner.** Supply the preceding
Lambda/G/Z/W fields and actual original clause registration under unchanged
scopes; first missing evidence is the complete pending-consumer telescope
and its domain/guard law. Proposed output is an independently reviewable
source-owned clause definition plus its compatibility proof. It requires
Luna's authority/input selection; it is not another generic IF lookup packet.

**CHOOSE-SOURCE-2 — Luna / sequential source-export owner.** Authenticate the
same original source occurrence through HIR registration and candidate
preflight/root/use. Required input is the actual original source/CST identity;
proposed output is the existing leased export handoff. Fail on substituted
source, preflight bypass, invented SourceNodeKey, root/use mismatch or alias
collapse. This task does not need complete primitive semantics to report an
honest entrypoint refusal or unresolved association.

**CHOOSE-NATIVE-2 — provisional TODO only, no code lease.** After the complete
semantic fields and lowering law are supplied, trace the real
`Action::Operation`/`candidate_operation` output through Catch's separately
resolved operation/binders, same A/B environment and demand consumer.
A minimal future instrument must observe constructor-produced phase/map/
witness retention and its consumption. Fail if it accepts injected transitions,
full-S alone, separated witnesses, lost future actions or a later uncovered
demand. No production structure/API or test is proposed here.

## 8. Source/native evidence, reuse and stopping receipt

Direct inspection of `candidate_source` shows pure operation lookup facts at
slots1/2 and retained declaration/owner/occurrence in Action::Operation;
dispatch reaches `candidate_operation`. That owner uses one value/effect/view
map, builds at level+1 and links slot42. `candidate_signature_value` injects
the operation family only in the outer result-effect construction; inner
alpha+ rows keep their own positions. These are genuine signature constraints,
not complete Lambda or IF-clause witnesses.

`Work::CatchArms` retains the separately resolved declaration and actual
payload/continuation binders/levels. `candidate_catch_operation` pairs A/B
using one environment; slots60/61 handle payload, 62/63 raw continuation,
64 entry effects and 65 whole-scrutinee effects. The latter is explicitly
provisional full-S. No inspected constructor emits the complete §4 semantic
phase expansion or effective §7 demand law. This is a bounded audit of those
owners, not a claim that no conceivable encoding can supply it.

Reused within actual premises: selected complete Call/IF constructors and
remaining-root graph; operation-instance retention; reviewed conditional
operation-source expansion; original current-state Bind/shallow laws; original
full-f theorem only with independent Sigma/world; source-Generalize's scope
and alias discipline. The previous qualification artifact and CLEAN review
supply the precise former missing-input boundary. The operation-source note
records its prior Sol/high producer request and independent bounded reviews;
those are historical provenance, not review of this new specialization.

Rejected as closure: bare Act spelling/arrow, source-only exhaustive alternatives,
empty semantic telescope inferred from nullary family, new R_e as choose's
original root, scalar native slots as IF addresses, full-S as exact suffix,
one local action as FK1, or tests of assumed transitions. Simple-sub generation,
accumulation, propagation, levels, extrusion, qualifying parent/copy intrusion,
generalization and retained hygiene results are unchanged.

Seven substantive stages: contract/pins; declaration/use audit; IF/telescope
specialization; Request/gluing; finite expansion/parent application; concrete
missing-field obligations; freeze. Budget maximum 900 active seconds and eight
stages. Conservative charge 480 seconds, 420 unspent and not transferred.
First successful clock receipt was 2026-10-16T15:03:13Z after initial reads;
final freeze time is in the assignment inbox. Requested
`astra_prover / gpt-6-astra / medium`; observed effective model/effort and
runtime session ID UNKNOWN. Current task identity is
`/root/choose_operation_instantiation`. No effort increase requested.

All 52 direct hashes matched before writing; contract acknowledgement was
sent to Luna. Material missing-field boundary was returned, and Luna explicitly
authorized this bounded conditional specialization and completion proposal,
then freeze/STOP. Final checks: dependency and contract hashes, exact paths,
Markdown fences and whitespace only. Initial `python` was unavailable;
`python3` performed static hashes/writes. Zero tests, builds, executable
research probes, heavy processes, network, Git, nested CLI or descendants.
No third/scratch path. Only this note and the assigned inbox are new files.

Independent review/integration remain pending. Writer stops after the two
outputs are frozen; no background continuation or descendant remains. The
next semantic step requires Luna's supplied/selected complete fields; no
remaining work is claimed to run while waiting.

## Frozen direct dependency manifest

All 52 entries below are byte pins of the unchanged rev1 contract. They are
not blanket proof authority. Only the scoped inputs identified above are used;
transitive unpinned documents linked by those inputs were not added as premises.
Prior authors/reviews remain those recorded in the pinned artifacts.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_effect.rs` | `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/shadow_initialization.rs` | `6ea0914a11a4a05d6dde8d63c413cfd42fb887596b3315d998848d502a91715a` |
| `notes/design/2026-10-02-operation-instance-binding-package.md` | `1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-07-original-call-formation-definition.md` | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md` | `93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-16-goal-driven-sprints.md` | `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e` |
| `notes/design/2026-10-16-source-remaining-root-constructor.md` | `4f9c483b6f3ca7a41ba3af622f91c17446823724269f2f1473b844b9f534cbd5` |
| `notes/progress/2026-10-16-concrete-declaration-export-root-review.md` | `07d27df963812d7ed95cebe4a5643eda59ab7efce8c18f271bae83ce7093d16b` |
| `notes/progress/2026-10-16-residual-public-export-review.md` | `a65090ec2b1fc200d98c951a5a0c85bbebb4a71f3847d91bde4c332ea3341f0f` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/2026-10-08-generalize-export-constructor-bridge.md` | `0a2f966b0ded7f7c5a176aa9966080daf81a58bf7f0a66e5d03d38d289a27734` |
| `notes/theory/2026-10-15-call-native-correspondence-construction.md` | `9a6bf7a37ec1ead4571422e8216e419ba2a377aee321e80d42905623ef42ba02` |
| `notes/theory/2026-10-16-call-suffix-image-demand-construction.md` | `11a058d90ca46c9cb58fdff38d532efe3401f0a0131e8ba8567e91af89d689b4` |
| `notes/theory/2026-10-16-catch-image-later-lower-feasibility.md` | `63ace8b183386737f4b328a2840a4e1585dc6ede22d9df7ec88a37ea92070e67` |
| `notes/theory/2026-10-16-choose-context-and-catch-source-construction.md` | `d03e2d3e61922742a8a62e9049598cbc7009c72492d8f5d6e6718c5e526a9212` |
| `notes/theory/2026-10-16-choose-phase-declaration-qualification.md` | `cd03ed21dbda0be64c928bf0b09803b768e1cf0336315a1534dc44e0148fc478` |
| `notes/theory/2026-10-16-choose-producer-full-source-certificate.md` | `5abbe5f849cbe3f92ba743e0a51c5928350cead62ed8d688766895c2035e1971` |
| `notes/theory/2026-10-16-choose-source-declaration-initial-installation.md` | `b27eed06d5a3eae63b2dfacb62a1f76d01b71f92a478402b452cd8a3b3346471` |
| `notes/theory/2026-10-16-dependent-phase-residual-interpretation.md` | `76484ee88efeee862b0eb8a128dfb44d17f7e8d0c9caafcc0fb92066189b169f` |
| `notes/theory/2026-10-16-first-call-fresh-use-semantic-application.md` | `9d5ec6a410c2b358187c1fcf105ba9efe5b2f5f9f4ede37ea2bb5364801ff46b` |
| `notes/theory/2026-10-16-guarded-catch-image-normalization.md` | `4a92452cf91ee06a5bf55bb07a5f92cce664866c56716b642bf17ad0c92a19d8` |
| `notes/theory/2026-10-16-open-negative-formal-catch-image-design.md` | `639b0282ef08d8e3657dde8ee5654333480f5ce194981dbdfa55c546e25334ff` |
| `notes/theory/2026-10-16-operation-primitive-image-contract-construction.md` | `4fe70b18cad9ded249869b21b84bbf26e2a5f95320f79632a29a5071ddb1c4e9` |
| `notes/theory/2026-10-16-source-remaining-root-contract-construction.md` | `058c6606ece58867587b20fbb7dcf3ed9de1171b7eb4bb1e071489276c72781a` |
| `notes/theory/successor-proof-obligations.md` | `e192f63930adea325f1be5fc92766fc9b58b938217176cb87d4678e4edd68092` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `rules/goal-driven-sprints.md` | `729fed88535671ebd128f0c70fd8618d2a2f7cb7df3a458698799fac9d9f1789` |
| `tasks/agent-loop/inbox/20261016-choose-phase-declaration-qualification.md` | `167cd06664cbbaae2eef135404f02525e10e6c3b5cd7656a9551496590aa79e1` |
| `tasks/agent-loop/inbox/20261016-dependent-phase-residual-interpretation.md` | `c415965efd049fe7ee5255a52c5821b57d371818ba7516548654b9920a1d9bef` |
| `tasks/agent-loop/inbox/20261016-f5-consumer-migration-boundary.md` | `62439df2322cc688eb83abf442261721b4e4b282b4fc81be0deaa0c7967c1981` |
| `tasks/agent-loop/inbox/20261016-source-final-root-export-law.md` | `7cc834e1c3fa627f1738b7638e6f08787c30c0d6766991061fba8f34fba48000` |
| `tasks/agent-loop/inbox/20261016-successor-independent-use-correspondence.md` | `2c8f10bd2530671777783c6a5b9eca96e74c186321c3d509aa981b60954e1af0` |
| `tasks/agent-loop/sprints/residual-and-public-export-correspondence-20261016.json` | `378ee6daeefd817461032ce6b1cb68061302bb27c631033205df85453505e1ab` |
