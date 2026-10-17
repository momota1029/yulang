# NPAIR source admission: conditional HIR-to-action correspondence and first obstruction

Date: 2026-10-18; revision 1; author `/root/npair_source_correspondence_proof`.
Sprint: `npair-source-admission-correspondence-20261018`; contract SHA-256
`fdbc808bafb8d32df8f86701f41923fbaaf25de91764fdaf65429aa02da6ed25`.
Baseline supplied by Luna: `a5ac0942313e34fac178221a17a1501ed55bc6c2`;
no Git verification. Status: frozen candidate/conditional source evidence,
pending fresh independent review; no production authority.

## Parent application and actual result

Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` retains its original
source/provider/context/assignment/strategy/guard/continuation/future quantifiers
and independent F1/FK1. The adopted slice is a nonempty concrete-only effect
row at a negative nested formal port, with no symbolic member. This packet
supplies the exact current preflight refusal and a conditional dataflow bridge
from an authentic HIR-owned formal annotation to the existing producer call.
It does not establish authentic parse-to-HIR formation or successful normal
source execution. Parent source/native closure remains **0**.

The first missing source premise is owned by the HIR annotation/carrier
constructors delegated to by the leased `module.rs`. Their implementation and
`SourceAnnotation::clone` are outside this read lease. The inspected solver
then has a definite refusal for the adopted negative row. A further uninspected
graph scheduler supplies the definition schedule's actual caller and possible
transaction boundary. These are concrete input/owner gaps, not a replacement
parent theorem. No second equivalent proof attempt was undertaken.

## Frozen dependencies and authors

All following hashes matched the granted pins before reliance. Authority and
contract author: Luna `/root`; reviewed producer theorem author:
`/root/registered_root_proof`. Historical source authors are UNKNOWN; reading
their files supplies no authorship inference. This packet has one author and
zero descendants.

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-18-npair-source-admission-adoption.md` | `fe06a42da82d9bc66da133d0266b0fa1133ffbcfb1128100377c715c0ace0d06` |
| `notes/design/2026-10-18-npair-source-admission-proposal.md` | `398b4f8683503d41e79d4d09b7a0a9591161a5673d48338c224037fae26d3158` |
| `notes/theory/2026-10-18-npair-native-introduction-correspondence.md` | `a26b7cea699597af0b8d56605169a0c2328030e139911573e2112c776039ea40` |
| `notes/progress/2026-10-18-npair-source-owner-handoff.md` | `8d02b0d19617f17ee6ff67a9c0339cd4d24ff71aab8bdc074e4dae21ae4fef11` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_call.rs` | `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `crates/yu-solver/src/term.rs` | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` |
| `crates/yu-solver/src/lib.rs` | `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f` |
| `crates/yu-solver/examples/research_source_registration.rs` | `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c` |
| `crates/yu-hir/src/module.rs` | `60e91c9a51394b04af42b3ec7c284062b34fcd9faa4ea79c35b4ae58aaf460ed` |

The producer proof itself pins the historical `candidate_effect.rs` hash
`11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`.
That differs from this sprint's correct current pin. Its reviewed construction
theorem is reused only under its actual premises; its complete review cannot
silently certify the later file. Current inspected producer clauses below
have the stated structure, but reconciliation of the historical delta belongs
to Luna/fresh review. No historical file, review receipt or unleased path was
opened to manufacture that reconciliation.

## Normal entry and first missing source owner

The leased example calls `parse_file`, rejects structural recovery, calls
`lower_module_with_local_source`, then `CandidateInference::solve`. Its
parser-key and resolved-declaration checks concern its existing receive/choose
fixture. The fixture was neither opened nor executed here, and this example
does not prove the adopted formal annotation is formed.

`module.rs:1029` creates parse identity/source keys and enables local-source
lowering. `lower_module_with_counters` calls
`source_annotation::declarations` at 1055. Definition lowering calls
`local_source::form` at 1984 with the actual definition owner and allocated
parameters; ordinary carriers call `local_source::form_ordinary` at 1179/1192.
The owning child modules are `crates/yu-hir/src/module/local_source.rs` and
`crates/yu-hir/src/module/source_annotation.rs`, named by the module structure;
neither was read or hashed. Parse identity production also delegates to
`crate::source_identity`; its implementation was not read.

The required first evidence is that those constructors retain this concrete
negative formal row, its row-position key, resolved concrete IDs, annotation
owner, parameter identity, lambda occurrence and lexical scope, with no
additional fatal HIR diagnostic. Their clone implementation must preserve the
annotation tree/arena and provenance. The visible `HirModule::local_source_for`
at 875 returns the owned Supported carrier, returns None for Unsupported, or
uses its definition compatibility map; this is lookup, not formation proof.
Its definition/occurrence/parameter source-key APIs provide useful observation
boundaries, not independently established authentic values for this case.

## Exact current refusal and minimal prospective change

`CandidateInference::solve` (`shadow_apply.rs:224`) selects `solve_mode(hir,
false)`. With an available HIR carrier, `solve_mode:292` calls
`candidate_source::preflight` before collecting anything. It then preserves
its existing HIR error filter at 304 and calls
`collect_candidate_mode_scoped(hir,true,true,false)` at 310. No scoped
experiment is needed or substituted.

At `candidate_source.rs:426`, a Lambda's formal checks the root computation
row only for more than one symbolic variable, then calls
`preflight_formal_value(value,false)`. At 457, `preflight_formal` requires for
each negative explicit child row:

```text
row.concrete.is_empty() && row.variables.len() == 1.
```

Function traversal flips variance at Argument and preserves it at Result.
Every targeted nonempty concrete-only negative child therefore fails the
current predicate, and `preflight` returns `CandidateError::Unsupported`.
This is proved for a HIR carrier that actually contains the target; no
unproved textual parser behavior is needed to evaluate this refusal.

The smallest prospective solver change is solely this negative branch:

```text
(row.concrete.is_empty() && row.variables.len() == 1)
|| (!row.concrete.is_empty() && row.variables.is_empty()).
```

The positive `variables.len() <= 1` branch, omitted-row acceptance, root-row
check, ordinary/local annotation preflights and diagnostics must retain their
existing behavior. For a negative explicit row the predicate adds exactly
nonempty concrete-only; it still refuses empty, mixed concrete/symbolic and
multiple-symbolic neighbors. Singleton symbolic-only was already accepted.
This statement concerns the targeted negative port; it makes no false claim
that every positive mixed row was historically refused. No code was changed.
If HIR formation has another refusal, this predicate change alone is
insufficient and no broader deletion follows from this packet.

## Conditional HIR-owned annotation to producer bridge

Assume the HIR formation/clone premises above, unique authentic parameter IDs,
the adopted preflight modification, all unrelated admission checks and
resource operations succeeding, and execution reaching the stored formal
action. Then the following inspected dataflow establishes field preservation:

1. `lib.rs:1160–1182` retrieves the same HIR carrier and calls
   `emit_candidate_source`. At `candidate_source.rs:557`, that collector
   requires pointer equality with `hir.local_source_for(owner)`, checks the
   definition/expression receiver owner, and checks every expression's
   occurrence ownership before recording its source owner. A forged external
   carrier is not the established entry premise.
2. At 596–608, it appends the actual `parameter.id` to `parameter_recipes` and
   records that recipe position, source owner, lambda index and scope in
   `FormalRegistrationInput`. Local binding parameters map to
   `AnnotationScope::Local(binding.id)`; other parameters map through
   `AnnotationScope::for_source(owner)`. The latter maps definitions to
   `Definition(root)` and expression owners to `Source(owner)`. This proves
   preservation of that computed solver scope, conditional on its upstream
   lexical correspondence; it does not equate two distinct scope APIs.
3. At 715–745 it stores the parameter's visit level, clones its annotation
   once into an Arc, and emits `FormalAnnotation(annotation,recipe_position,
   lambda.occurrence,scope)`. The registration and action use the same scope
   formula. The annotation's source owner, all nested type/effect nodes,
   row-position keys and concrete operands are carried through that clone;
   no family-name lookup reconstructs a path or occurrence. Clone semantics
   remains the explicit uninspected representation premise.
4. At 1202–1235, initialization assigns the recorded formal level to its live
   parameter, verifies recipe identity against registration.parameter and
   installs that exact positive parameter endpoint once. Root effects get
   a distinct fresh entry row only for `FormalRole::Computation`.
5. At 1159/1165 collection stores the action vector under the definition root
   or expression schedule. At 1298–1345 the driver selects that vector by
   schedule, clones the next Action, and advances only after successful
   execution. `execute_candidate_action:1351` directly calls
   `candidate_formal_annotation` with the action's annotation, parameter,
   occurrence and scope. No intermediate descriptor reconstruction occurs.

No action carries an independent path field: the producer derives typed
Argument/Result steps by walking this exact annotation tree. In the current
`candidate_effect.rs:1170–1255`, negative variance starts at the formal value,
Argument flips and Result preserves it, and each child effect has its own
path. A concrete-negative row copies annotation.owner, parameter, occurrence,
scope, row.position and the complete concrete vector into one inert Permission.
One fresh effect ordinal supplies both live projections. Full Function outputs
remain `Fun+(an,qan,qrp,rp)` and `Fun-(ap,qap,qrn,rn)`.

At 1294–1364 the current producer uses the original formal level, rejects
duplicate retained formal publication, calls ordinary link43 then link44, and
publishes permissions and the negative root only after both calls. Under the
reviewed theorem's transaction/lifetime and snapshot-transfer premises this
composes with its same-state shared-row/path-recovery result. This packet does
not reprove all allocation/accounting/rollback or downstream link semantics.

Root effects are separate: collection emits `FormalEntry` before the paired
value action only when annotation.ty.effects is Some. At
`candidate_effect.rs:1279`, a singleton symbolic root tail receives equality
links 45/46; a concrete-only root emits neither equality link. Therefore
preserving the root rule does not mean inventing links 45/46 for every formal.
The paired value builder excludes its own root computation row. Nested
Permission contributes no lower, upper/cap, closed-row, emptiness, provider
or subtraction fact. No existing ordinary constraint is deleted here.

`candidate_call::computation_source_plan` at 198–229 additionally checks
registration against the HIR lambda/parameter, source owner and root role for
its observation API. It does not run as an admission check on the above
formal action and cannot supply a missing parser or consumer theorem.

## Actual caller/transaction gap and discriminating evidence

`lib.rs:10413` executes the SCC plan, whose candidate branch at 14793 calls
`InferenceSession::execute_candidate_graph_plan`. Its definition is absent
from every leased source owner inspected; its defining file is **UNKNOWN**
from this lease. A `mod candidate_scheme` declaration is not proof that this
particular method lives there. The root source schedule's actual caller and
its enclosing route transaction remain **UNKNOWN**. Visible
`execute_candidate_source_root -> execute_candidate_source_schedule ->
drive/step -> execute_candidate_action` adds no local route wrapper.
Likewise, the visible loose/expression calls in `lib.rs:10423–10425` add none.
These observations do not prove an absent wrapper at an uninspected caller.
The reviewed producer's rollback theorem must keep this premise; no local
frame action discharges scheduler, transport or foreign-continuation cases.

**Provisional implementation TODO NPAIR-SRC-PREFLIGHT-1 (Luna only):** after
upstream formation, snapshot transfer and actual scheduler premises receive
their owning evidence/review, change the one predicate above under a fresh
code lease. The source-entry falsifier must use `CandidateInference::solve`
after normal parse/HIR lowering, with authentic row keys compared against
retained permissions and complete paired trees. Reuse the existing internal
regression's text as a candidate input, without treating that test as evidence:

```yu
act io
my bridge (consume: ((int -> [io] ()) -> ()) -> (() -> (int -> [io] ()))) = consume
```

The in-file internal regression at `candidate_effect.rs:2333` expects paths
**AAR and RRR**, not AA/RR: parsed Function effects attach to the result child.
That is a useful falsifier specification, not an observed parser result here.
Equal families must retain distinct row keys/paths/fresh ordinals. Change each
targeted negative row separately to empty, mixed or multiple-symbolic and
require its existing refusal. Include previously accepted omitted and
singleton-symbolic negative rows, positive ports, independent parameters,
root-effect separation and unchanged ordinary links. A direct constructor
call or collection that bypasses preflight fails this evidence requirement.
No test was added or executed by this worker.

**Mutual TODO NPAIR-SRC-HIR-1 (Luna -> HIR owner):** supply a separately leased
audit of `local_source::form/form_ordinary`, annotation formation/clone and
the source-identity supplier; first evidence is authentic target retention
with no additional fatal diagnostic. Falsifier: source parse succeeds but
carrier is Unsupported/absent, a row/owner/path operand changes, or a required
diagnostic blocks normal entry.

**Mutual TODO NPAIR-SRC-SCHEDULE-1 (Luna -> scheduler owner):** locate the
actual `execute_candidate_graph_plan` definition and definition action caller,
establish its existing transactional ownership or record an exact mismatch.
Falsifier: the proposed source route invokes the producer outside the reviewed
rollback premise while relying on that theorem for partial-failure recovery.

**Mutual TODO NPAIR-SRC-REVIEW-1 (Luna -> fresh independent review):** reconcile
the historical producer hash with the current pin before transferring reviewed
status; inspect the conditional bridge and required source-entry evidence.
The producer/coauthor cannot independently certify this packet.

## Limits and cessation

The native theorem is reused as a bounded supplier; historical claims that
source admission was refused are replaced by the current exact preflight
evaluation. Historical compile/test receipts and the internal regression are
not reused as successful source evidence. Simple-sub generation, accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization receive
no semantic or implementation change. Provider/witness/residual lineages stay
distinct. F1/FK1, N-Transport, Call, actual contribution/At/consumer/subtraction,
capture/fresh-use/SCC lifetime, source-Generalize, soundness, principality,
termination and production remain OPEN.

Four stages: pins/authority; entry/preflight obstruction; conditional collection/
action/producer correspondence; parent application/falsifiers/freeze. Grant
300 seconds; full grant reserved, no refund of unobserved runtime. First
clock checkpoint `2026-10-17 17:53:39 UTC`; final checkpoint is in the handoff.
Requested model/effort Sol/high; observed effective model/effort UNKNOWN.
Launch-to-first-checkpoint and exact active compute time UNKNOWN. Descendants0,
Astra0, tests0, builds0, probes0, Git0, production writes0, scratch paths0.
Only this artifact and the exact assignment inbox are written. Writer STOP
after frozen handoff; no background work or unresolved descendant leases.
