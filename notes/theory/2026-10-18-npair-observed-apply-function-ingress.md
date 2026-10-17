# Observed-source Apply and Function ingress constructors

Status: candidate constructor-law proof and source/native audit, revision1;
independent review NOT_RUN. No original-parent closure or production authority.
Author/current worker: `/root/npair_actual_argument_ingress`, sole author;
no descendants/coauthors. Assignment `NPAIR-OBSERVED-APPLY-FUNCTION-INGRESS-20261018`.
Sprint `npair-observed-apply-function-ingress-20261018`, contract rev2 SHA-256
`6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8`.
Rev1 was read at launch; rev2 continues the same grant without resetting spent
budget. Its expanded implementation query does not enlarge this proof lease.
Primary-supplied baseline `5c45c1807fc6f4fa495a2f0b85c4bdba1672820d`;
no Git authentication. Requested Sol/prover/high, cap600s; observed model/effort
UNKNOWN/UNKNOWN. New active assignment acknowledged in this session.

## 1. Parent application and actual advance

Original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN,
conditions closed0. This packet establishes the previously uninspected native
Apply constructor and complete Function dispatch from actual source code,
and derives the exact result/effect-child equations those constructors use.
It also establishes the actual local initializer root and native fresh-use
reconstruction law; these are constructor laws, not tests of assumed transitions.

The actual outer call, if successfully constructed from the added source,
compares `f0_use` with receive's actual negative domain `Outer-^r`. It does
not emit an edge `f0_use <: P_f^r` merely because the source formal is named f.
Its nested target is the image `q_D^r` under that actual receive module-use map,
not automatically the original raw q_D. The owning source must transport the
original permission/contribution judgment to that image. N-Transport is an
open obligation, not a proved law supplied by adoption.

Original semantic H0/L2 eta remain unsupplied: a native Support lower and its
source row do not identify the fixed whole original contribution. P3/P6 and
all parent quantifiers remain unchanged. Concrete runtime BoundKeys, emissions,
and original-contribution lift are separately identified below.

## 2. Unchanged original judgment and source inputs

Retain the original actual source/reference composition and its complete
meaning:

```text
P_alpha |- w : Prim_alpha(h,y;xi), xi=(nu,K,D)
OpInst(p,theta)=(p,F(theta(rho)),A_theta,B_theta,Lambda_theta)
s0 = Operation root Function.ResultEffect
s1 = Operation root Function.ResultValue.Function.ResultEffect
D  = receive formal f, Permission path [Result,Result]
```

w is the same original whole witness, with its provider, observation, world,
assignment, source occurrence, actual theta/local binders, call/result slots,
scopes, guards, continuation, interaction and witness lineage. A contribution
c projected from that witness retains that same lineage. No witness is selected
by member/family equality. W/Z alternatives, admission/domain obligations,
independent J1/J2, F1/FK1 and original accepted source domain remain quantified
as before. Local Function actions establish no foreign-continuation case.

The frozen predecessor supplies the baseline `f0(u)=ctrl::choose ()` and
receive body `my g=f(); g()`. This contract proposes only
`my received = receive f0`. No fixture/harness bytes were read or hashed while
the implementation lane owned them. The adopted correction withdraws prior
claims that UnsupportedExpression proved absent LocalSource/collection.
That diagnostic may coexist with the candidate's permitted source fallback:
`CandidateInference::solve_mode` uses a genuine LocalSource, preflights it,
retains its placeholder errors, then collects candidate mode
(`shadow_apply.rs:285–319`). It is incorrect to locate a lowering failure from
the diagnostic alone.

## 3. Actual Apply constructor, including all demand fields

For the actual collected Apply recipe R, `candidate_source.rs:1093–1138`
retains exact HIR callee/argument endpoints, their evaluation effects, actual
result position, application-effect position, level, occurrence and checking
cause. Its initial native=None is completed by the following real producer.

`shadow_apply::admit_candidate_fact:1558–1580` validates the registered recipe,
source-input identity, exact occurrence, both value endpoints and every retained
effect/result position. Any mismatch returns failure. `candidate_endpoint`
(:1540–1557) resolves a Component to its live row or a Parameter to the actual
parameter_live_base+position, preserving the requested polarity.

In graph-effect mode the Apply arm (:1585–1664) creates:

```text
V_c+ = actual callee endpoint
V_a+ = actual argument endpoint
AE_a+ = actual argument evaluation-effect row
R- = actual result-position negative Value projection
J = fresh_effect_at_level(level(actual application-effect row))
D_call = Fun-(V_a+, AE_a+, J-, R-)
```

The fresh allocation happens for this call; J is not borrowed from another
call or inferred from an equal row. Before admission it publishes exactly
these terms and the actual callee/application effects into NativeInterface;
publication rejects a preexisting native record. The constructor then admits
and constrains `V_c+ <: D_call` at this Apply's slot0 (:1667–1684), and slots1/2
admit `callee_evaluation_effect <: B` and `J <: B` (:1696–1717). The call has
all argument/result/effect operands; callee evaluation alone is not complete
Call meaning. Publication preceding the fallible comparison is not by itself
a successful construction or original typing certificate.

`candidate_call::observe:462–553` now serves only as a post-construction check:
it requires native Some, authentic HIR Apply/ownership and exact demand children.
Its existence was not used as the source-emission proof. No executable test
or assumed native interface substitutes for the inspected producer above.

## 4. Lambda domain and complete Function child law

`lib::admit_lambda_fact:11317–11498` chooses the actual argument child from
`formal_domains[parameter_position]` when present; otherwise it uses the
actual parameter's negative row. It resolves the actual body result positively,
keeps all entry/body effects, forms the positive Function, and admits that
Function below its actual root at slot2. It does not insert an actual argument
provider into P_f.

For receive, `candidate_formal_annotation:1294–1369` builds both full polar
pairs, admits slots43/44 and only then publishes Permission and Outer- into
formal_domains. Thus the actual receive Lambda uses Outer- as its argument
child. The shared nested effect row is q_D, with path [Result,Result], not
an injected Support or cap. The native source pair is

```text
Inner+ = Fun+(Unit-, Z-, Q+, Int+)
Inner- = Fun-(Unit+, Z+, Q-, Int-)
Outer+ = Fun+(Unit-, X-, Y+, Inner+)
Outer- = Fun-(Unit+, X+, Y-, Inner-)
Outer+ <: P_f; P_f <: Outer-
```

For every actual positive/negative Function comparison F+ <: G-, the child
array in `lib.rs:12643–12691` is exactly

```text
G.argument+       <: F.argument-
G.argumentEffect+ <: F.argumentEffect-
F.resultEffect+   <: G.resultEffect-
F.result+         <: G.result-
```

This follows by the actual positive_function_children/negative_function_children
reads and explicit construction of each task; no child is omitted.
`candidate_step_function_dispatch:12796–12827` sends every one of those tasks
through candidate_function_port_admit and queues it. The context owner retains
field and Swap/Preserve operation and authentic demand/scope action. The
nonidentity scope laws remain separate semantic obligations.

The actual route equations, retaining every map rather than identifying copies,
are consequently:

| Source producer/comparison | Selected child equation; all other children remain active |
| --- | --- |
| Actual choose() call in f0, with Operation signature O+ | `H_op+ <: R_op-`, where H_op is the actual returned Function and its result-effect child is s1 |
| f0 Lambda F0+ | Its result child is the positive projection of that actual body result R_op |
| Actual module Name uses | Capture/freshen f0 with its own map rho_0 and receive with its own map rho_r; their maps are independent, not interchangeable |
| Outer call `receive f0` | Receive Function's contravariant argument child gives `V_f0_use+ <: rho_r(Outer-)` |
| Actual F0^0 lower exposed at that argument | Result child gives `rho_0(R_op)+ <: rho_r(Inner-)` |
| Actual H_op^0 lower exposed at that returned row | ResultEffect child gives `rho_0(s1)+ <: rho_r(Q-)` |
| receive's independently constructed f() body call | `Y+ <: J1` and `Inner+ <: R1` through Outer+ <: P_f and that actual call demand |
| actual g local-use comparison with its own g() demand | `rho_g(Q+) <: J2` in the definition graph; outer module use subsequently maps this whole equation coherently by rho_r, not Q+ <: J1 |

Rows, copied/extruded Functions and representatives in this table mean their
actual constructor outputs. Where an extrusion changes a structural endpoint,
the actual rewritten Function and actual parent/copy evidence must be used;
the table is not permission to skip that step. The module routes capture the
actual published graph root, restore its actual bounds and route the fresh root
to the exact use component (`candidate_scheme:1089–1111,1495–1548`). These are
actual construction laws. Runtime instantiation still needs the specific
successful collected binding and native event records.

## 5. Both ordered Replay inputs, without invented runtime records

Use `BK_T(x,+,a)` for the actual canonical BoundKey with owner x and lower a,
and `BK_T(x,-,b)` for the same owner's upper b (T=Value or Effect).
Each owner and operand below must be the actual current endpoint, including
its eligible fresh-use/extrusion/canonicalization maps. The first inner-result
Replay's required inputs are

```text
lower_input = BK_Value(r, +, H_op^0)
upper_input = BK_Value(r, -, Inner-^r)
child       = H_op^0 <: Inner-^r
```

Here r is the actual received copy of the f0 body-result row. Its lower input
comes from choose()'s actual result-child comparison, transported through the
actual f0 module use; its upper comes from the actual F0/result-to-Outer-
comparison. Those are different premises. Earlier module-root/Apply bound
Replays must likewise use their actual lower and upper inputs.

For the resulting s1-to-Q comparison, when the actual level-directed storage
owns the upper at the source s, the required concrete-form inputs are

```text
lower_input = BK_Effect(s, +, Support(v_s1^0))
upper_input = BK_Effect(s, -, q_D^r)
child       = Support(v_s1^0) <: q_D^r
```

The Support lower is emitted by candidate_signature_effect's explicit positive
row branch (:1788–1835) and transported by actual module freshening; the upper
is the actual inner ResultEffect child, not permission-generated inflow.
`s0` is absent from both inputs. In the original signature it receives Self
only at pointer-equal root declaration signature; the inner explicit row has
its own written operand, row position, view and port.

The two displays specify exact operands that must meet; they are not a claim
that their raw row/view/relation ids have been observed in this run. In
particular `candidate_apply_value/effect` (:844–899) chooses the owning side
by actual levels. If the target row is younger, storage can instead be a
lower row link at the target. Its subsequent consumers require the actual
row-link Replay chain, not the second displayed source-owner upper by fiat.
If canonical endpoints coincide, the native apply routine may return without
a new Replay; an actual equality/transport derivation is needed instead.
These cases are not excluded to simplify the proof.

The defining implementation law is fully explicit:
`candidate_replay_bound:799–841` orders new-lower `(inserted,existing-upper)`
and new-upper `(existing-lower,inserted)`. `candidate_context_begin_replay:
3401–3470` takes both actual BoundKeys and both relation fibers, retains both
ordered relation ids in Dependency::Replay, unions source evidence and composes
scoped flows. It requires a demand-free lower. Every new fiber meets the
opposite fibers; no first-Origin choice or single-input inference is justified.
A concrete native structural certificate still needs those live admissions,
physical emissions, fibers and endpoint maps. The current constructor proof
supplies their owning rules, not unseen runtime record identities.

## 6. Exact R1 install/use law and missing permission map

`candidate_source::Work::Install` takes the actual g initializer endpoint,
which is the f() result component R1. Staged publication resolves its positive
term and hands that exact exposed term to install_candidate_local_term.
`candidate_scheme:1551–1572` requires a ValueRow, retains that root together
with actual local identity, boundary and capture region. It cannot swap in
an arbitrary Function at the same family point.

`route_candidate_local_run:1590–1620` captures that stored root and prepares
one actual fresh map; `step_candidate_local_use:1739–1779` restores each captured
bound before linking the actual reconstructed graph root to the actual g-use
component. Capture expands all four Function children (:566–623);
reconstruction uses those same four indices (:1308–1359). The eligible row map
shares canonical rows within a use, freshens exactly eligible local rows above
the capture boundary, and leaves nongeneric rows shared (:1198–1213).
Original body/initializer effects are not rerun by this Value freshening.

**Native port-path commutation (successful construction only).** Fix the actual
captured graph and successful FreshUse at receive use r. Capture::expand_node
(:566–623) inspects each authentic positive/negative Function, stores all four
child indices, and validates child kind/polarity (opposite,opposite,p,p).
Capture::row (:386–409) interns its actual canonical `rep(row)` once. The finite
structural reconstruction (:1308–1359) builds the same-polarity Function from
the terms of those exact four indices. Its row branch uses exactly
`fresh.rows[row_index]`. Canonical sharing is fixed by the single map in
prepare_candidate_fresh_use (:1198–1213), including its nongeneric-sharing
branch. Induction on these structural Function nodes therefore gives

```text
PortPath(Fresh_r(captured Outer-), [Result,Result])
  = phi_r(rep(q_D)) = q_D^r.
```

Here PortPath follows the actual outer Result value child, then the actual
inner ResultEffect child; the finite signature DAG and preallocated row
identities justify termination even when other captured bounds cycle.
`phi_r` means this successful graph's actual row-index map; it is not an
injective semantic renaming and is not inferred from a raw-row equality.
If a row is eligible it maps to the corresponding allocated row at use level;
if nongeneric or no longer above the boundary it maps to the actual shared
representative. Both branches preserve the child-index equation. Later
canonicalization composes another actual representative map; no raw ordinal
stability is asserted. A changed reconstruction input, failed polarity check,
unavailable child term, failed restoration/publication or untracked later
rewrite lies outside this successful-path claim and cannot be called a
completed source instance. All four children are premises, even though the
chosen address uses the two result positions.

Apply this lemma only as native P6 support: it constructs the correct image
port address for the actual captured domain. It does not form or interpret
Permission at that image, carry an original contribution or prove source
admission/At. Analogous commutation holds for the actual g graph/map, with
its own captured root and actual eligible/shared branches.

This proves the native same-initializer-root relationship and native port
commutation, not a whole semantic provider/witness map. Capture carries rows, bound evidence, contexts and inert
attachment bundles. FreshUse carries node/row/effect-operand/context/evidence
maps, and begin_candidate_fresh_bound supplies the original source bound,
use origin and mapped relation to actual physical restoration (:1447–1493).
These are useful exact bridge operands. None interprets them as the complete
original `(D,c,delta)` judgment by itself.

For module receive use r, the required permission law is a dependent map
T_rho_r with

```text
port(D_r) = rho_r(port(D)) = q_D^r
T_rho_r(D,c,delta) = (D_r,c_r,delta_r)
```

It must retain D's original annotation occurrence/path and permission operands,
actual remapped receiver/use scope, whole original witness/provider lineage,
constraints, future lowers and eligible binder sharing. The same is required
for the actual g fresh-use map. Neither raw equality q_D^r=q_D nor equality of
families supplies it; raw equality is not even required when the row is
legitimately copied. Intrusion's representative equality also does not merge
permission owners, provider witnesses or residuals.

No current adopted theorem supplies this law. Adopted NPAIR explicitly makes
N-Transport a lifting obligation; adopted construction L3 explicitly stops at
rho_u. Its L4 only preserves distinct allocated native contribution instances
when those captured nodes exist. The pinned candidate_scheme has no
formal_permissions map/reader. Across the eight pinned compiler owners,
formal_permissions references are formation/publication, accounting/checkpoint
and tests. This limited symbol audit is not a claim about uninspected files or
impossibility of a proof-side correspondence. No particular runtime storage
representation is demanded.

## 7. What applies now to H0, eta, P3/P6

The preceding constructor proof discharges the previous packet's uninspected
Apply-demand/full-child owner boundary and the native same-R1 root subtask.
The port-commutation lemma additionally supplies the successful-path native
field-address subpremise `q_D^r=phi_r(rep(q_D))` for P6, at its stated graph
inputs. It supplies no permission or original-witness map.
It directly identifies the correct s1-to-image-Q child. It does not supply
NPAIR-OP-SOURCE-WITNESS/H0 or L2's `eta: c contributes-to L_H` for the same
original whole witness. The native view preserves source owner/position and
Operation provenance, not a complete semantic provider/observation/world/
assignment/alternative witness. A fresh field-native view cannot select c.
The original complete Operation/Call field supplier must provide that lift.

L2's published initial premise `F+ <: P_f` is not established for the actual
outer argument; the real Lambda domain is Outer-. Its final two-result-child
composition is reusable on the actual direct-domain derivation once the
same-c eta and dependent D_r correspondence are supplied. N-Ingress then
accepts that authentic derivation at D_r. This is a parent application locating
the remaining premise, not a newly renamed theorem assuming it.

P3 remains open for same-contribution association and all current/future direct
and annotated routes; P6 remains open for original source/native realization,
actual record coverage and use/scoped correspondence. No At is concluded from
a metadata match or accepted call. No actual residual consumer is established;
receive contains no Catch. P4 N-Transport, P5 residual, universal Operation
compatibility, all W/Z/domain cases, complete Call, generalization, soundness,
principality, termination, F1/FK1 and production keep their independent owners.
Ordinary generation, accumulation, propagation, levels, extrusion, qualifying
intrusion and generalization remain required.

## 8. Minimal mutual TODOs, falsifiers and stop

- `NPAIR-OBSERVED-REPLAY-INPUTS-20261018`: Luna/native evidence owner supplies
  the actual source_call NativeInterface and both live Replay BoundKeys,
  admission/emission/fiber records and actual copy/representative maps for the
  added binding. Use existing `CandidateInference::source_call_count/source_call`
  (:394–399) for native Call operands; source_call's public accessors expose
  the exact native callee/argument/demand/result/effects. Any additional harness
  observation belongs to a separate exact lease; no production edit is needed
  or authorized by this request. Falsifier: no authentic native record, a
  source-owner input absent, stale/canonical-only ids, single-input Replay,
  unsupported level-side assumption, or a fabricated step. Structural-only
  success cannot return At.
- `NPAIR-DEPENDENT-PERMISSION-USE-20261018`: original source-use/Generalize
  proof owner, with candidate_scheme maps as native operands, supplies the
  T_rho_r/T_rho_g law above. Falsifier: changing original provider/theta,
  family/row-based witness recovery, dropping future lowers, wrong scope,
  shared nongeneric coordinate treated as a new owner, or collapsed lineage
  after extrusion/intrusion. Adoption does not discharge this obligation.
- Existing `NPAIR-OP-SOURCE-WITNESS-20261017`: original complete Operation/Call
  supplier provides same-w Written-s1 eta and field correspondence, preserving
  W/Z and original-domain compatibility. Root s0 Self, native Support membership,
  a source trace or new selected witness cannot supply it.

Implementation lane owes the frozen received-binding LocalSource/collection
and run evidence; no moving output is consumed. Luna owns intake, any changed
source-read/implementation authority, fresh independent review and integration.
This author is a producer and cannot independently certify this packet.

## 9. Checks, reuse, resources and authors

Reused: frozen predecessor's exact original parent and authority manifests;
adopted NPAIR definitions/L2/L3 only at actual premises; reviewed s0/s1 field
discriminator; corrected implementation disposition. Rejected: prior absent-
LocalSource claim, diagnostic-based lowering attribution, observer-to-emission
inference, f0-to-P_f invented edge, s0-to-s1 field move, one-input Replay,
row/family-to-w inversion, empty-open-row claim, withdrawn bypass or a narrowed
source/provider/continuation domain.

Checks: actual pinned byte SHA-256, bounded static constructor/call-site reads,
complete Function child calculation and symbol audit over the eight pinned
owners. Truncated combined reads were supplemented by bounded relevant excerpts.
No tests/builds/probes/compiler execution/Cargo/Git/network/contact/nested CLI,
subagents, production edit or shared-state writes. No fixture/harness reads
while their writer was active. Requested model/effort and observed metadata
remain separate; no model switch or enlarged grant.

First sampled clock 2026-10-17 19:53:21 UTC; final timing and writer-stop receipt
are in the exact inbox. Cap600s, Astra0, heavy processes0, descendants0;
CPU/RAM UNKNOWN. Only this artifact and its one assigned inbox are written;
scratch0. Freeze/review has no mathematical or production promotion authority.
Prior artifact authors retain their recorded provenance: adopted proposal
`/root/negative_formal_pair_proposal`, L2/L3 `/root/adopted_npair_construction`,
C1/C2 candidate `/root/npair_operation_contract_candidate`, previous obstruction
this same worker; corrected source report and authority are Luna/primary and
recorded review/user provenance. Source/native file authors and absent prior
runtime metadata UNKNOWN. All direct hashes follow; no mutable implementation
output is a dependency unless separately frozen and identified below.

## Frozen dependencies

| Path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev1.md` | `f1b4610c17189becb92ba9e773c6cd667f265bb2129424ef1f3bf7f5cfae9be3` |
| `tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev2.md` | `6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8` |
| `crates/yu-solver/src/candidate_source.rs` | `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce` |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` |
| `crates/yu-solver/src/candidate_scheme.rs` | `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `crates/yu-solver/src/candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `notes/progress/2026-10-18-npair-actual-argument-source-path-correction.md` | `071b87b2e08acf6845de2b8fd16199fe0c84590abda5fc2f4bb41aae7fa39586` |
| `notes/theory/2026-10-18-npair-actual-argument-ingress.md` | `c5365821565f8043f1d63fe50a209ce24777cf506a26098852f01db33d0d2d09` |
| `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md` | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| `notes/theory/2026-10-17-adopted-negative-pair-construction.md` | `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2` |
| `notes/theory/2026-10-18-npair-operation-self-source-realization.md` | `cc8c96d288ae5fb548acbb8437a504ee0691e86f9f8e2915ded2e67ecbca0b85` |
| `notes/design/2026-10-18-npair-operation-self-effect-contract-candidate.md` | `c8c9854c32cdb3dc5e9fe8e1be15293e3b05bb0b393daff3632f9ba516df1455` |

## Runtime evidence and assignment stop

This revision consumes no new implementation/run receipt. The implementation
query/run is an independently leased live lane, and its unfinished output is
not a mathematical or source/native premise. The exact outer source occurrence,
authenticated native demand and both actual live Replay inputs therefore remain
unobserved in this frozen revision; the relevant constructor laws and required
correlations are explicit above. The prior corrected exit0 receipt cannot fill
those selective-output gaps.

Stop condition: the remaining proof requires original same-w field/contribution
meaning and the dependent Permission/use transport law, not additional reads of
an uninspected constructor already available under this lease. Native runtime
correlation is a separate pending evidence input. No new source owner, compiler
edit, semantic choice or budget expansion is taken. Next work belongs to Luna:
combine a frozen implementation receipt with this candidate, independently
review the exact claims, and route the named original eta/T_rho obligations.
This packet cannot close the original parent from a green observation.

Writer STOPPED after the exact handoff/hash freeze; no descendants, no ongoing
work or unresolved descendant leases. Only the two exact leased research paths
were written. Review/integration remains pending. Full600s reservation is
conservatively charged on return; this is allocation accounting, not a claim
of600s measured active computation. The handoff supplies the sampled clock span.
