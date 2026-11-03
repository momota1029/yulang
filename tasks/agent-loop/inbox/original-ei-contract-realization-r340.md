# R340 original EI contract realization — conditional primitive action

Assignment `R340-ORIGINAL-EI-CONTRACT` / handoff revision **1**. Baseline supplied
by Luna: `bcd119715`. Contract:
`tasks/agent-loop/sprints/original-ei-contract-r340.md`, SHA-256
`2ff890a979d08529ba4696bdda5540d544ed437fda514de69a5e00497e3bbab6`.
This receipt also records Luna's in-envelope direction to construct changed
registry/leaf/input evidence from independent primitive actions.

Sole proof author and runtime task: `/root/r340_relation`. Launch receipt is
the parent NEW_TASK in this session; runtime UUID is not exposed. The role
instructions request an Astra core proof lane with normal medium effort;
exact launch model/effort and effective observed model/effort are **UNKNOWN**.
No descendants or coauthors. The checker adapter reuses the prior independent
R339 audit script; that is tooling reuse, not independent review of this proof.

## Result and parent application

**CONDITIONAL mathematics, checked; original EI/R159 parent remains OPEN.**
The unchanged parent is actual original source Union relation → complete
catalogue/licensed child/result fields → unchanged R159 App judgment, preserving
all original worlds, independent arms, scope and shared witnesses.

The new module constructs a Guard syntax action by induction from nine original
atomic predicate laws. It constructs a transformed `PrimitiveLeaf` from the
original declaration lookup equation and a transformed `PrimitiveInput` from
the original resolver equation plus the derived transformed precondition.
No changed-world primitive precondition or finished EI body is an input.
The action fixes the full original source Key/use and declaration/owner/context
prefix; it does not cast the tick callee Key into the Call incidence Key.

Applied at R339's actual R311 calleeRequest consumer, this removes the fresh
changed-world **request/resume PrimitiveInput** assumptions. The whole-record
application uses R339's existing lawful response action and retains the same
record projections and shared witness. Every original response and its lawful
image are quantified; there is no selected native response or eventual Return.

This is not an authenticated original source-contract instance. The independent
`AtomicLaws`, declaration `LookupAction`, and `ResolutionCommutes` equations
remain assumptions. No nonidentity instance is produced from actual source.
The changed prior/resumed **CalleeInputs remain explicit**. The R339 response
schema remains unauthenticated and may be empty; R340 does not label it an
original domain or claim completeness of the target response domain. Thus this
is a conditional algebraic improvement at a named consumer, not an unconditional
parent reduction, Generated instance, licensed R306 child, or R159 closure.

## Exact checked declarations and axioms

Namespace for every new name below:
`YulangClosure.OriginalEIContractRealizationR340`.
Common parameters are the unchanged `s : Sorts`, `View : Type`, `inputs : Inputs s`,
`registry : GuardRegistry inputs`, `resolution : Resolution inputs registry`, and
`a : Action s View`. The six theorem types are fully printed without truncation
in `/tmp/yulang-r340-relation/authored-audit.log`; their source declarations are
in the frozen module. The following type inventory records every premise class:

| Theorem | Type / conclusion | Complete axiom list |
| --- | --- | --- |
| `guard_action` | `AtomicLaws inputs registry a → ∀ guard, guard.Holds inputs registry.original → (a.guard guard).Holds inputs registry.original` | `[]` |
| `goal_keeps_source` | `∀ goal, (a.goal goal).reference = goal.reference ∧ (a.goal goal).use = goal.use` | `[]` |
| `primitive_action` | AtomicLaws + LookupAction + ResolutionCommutes + original `PrimitiveInput ... goal` imply `(primitiveBody ... (a.goal goal)).Holds Z`, for **every** `Z : Family s` | `[]` |
| `goal_operands_action` | `∀ request declarations use operands, a.goal (primitiveGoal request declarations use operands) = primitiveGoal request declarations use (operands.map a.operand)` | `[propext]` |
| `restricted_response_from_primitive_actions` | For every state/request/declarations/schema/head, all original leaf soundness, AtomicLaws, LookupAction, ResolutionCommutes, original request/resume PrimitiveInputs, changed-prior CalleeInputs and changed-resumed CalleeInputs imply every mapped R311 calleeRequest phase body holds in `Meaning inputs` | `[propext, Quot.sound]` |
| `restricted_record_from_primitive_actions` | Same premises plus `LawfulResponseMap inputs schema a.fields`; for every original answer, its actual `restrictResponse` record equals `a.fields.record answer.record`, and its mapped R311 calleeRequest phase body holds | `[propext, Quot.sound]` |

`actLeaf` and `actInput` are checked dependent constructors, not theorem names.
Their types and axiom dependencies are included in the all-constant audit.
All **106 originating constants**, including **50 theorem declarations** generated
or authored in the module, passed type/axiom checking. No `sorryAx`, project axiom,
`Classical.choice`, native-evaluation assumption, or checker bypass occurs in the
new theorem roots. Source scan matches in reused R159/R160 are diagnostic string
literals saying `unapproved axiom`, not axiom declarations.

## Source correspondence and exact unresolved owner equations

Authority inspected: adopted IF §§2–3.3/6; EI §§2–5; source-contracts §§2.1/3.3;
call-semantic-input-realization §§2/4.3. IF expressly supplies independent typed
primitive contracts and lawful actions as inputs. It does not assert that a raw
source occurrence or endpoint predicate supplies those contracts.

1. **Original declaration/source owner → response domain.**
   `OriginalSourceEvents.Response`/`RawResume` retain the full request, actual
   operation, handle, continuation, suffix, response/current and joint data.
   `sourceRecord` establishes source ownership/binder shape, not typing or
   development. `LocalAdmissions.response : Decoded s View → Binder →
   ResponseData s View → Prop` receives only observation/receipt after
   `RawRecord.runtime` erasure. The existing
   `different_operations_same_runtime` theorem exposes this loss. A pre-erasure
   original declaration contract with a sound **and complete** domain/readout
   equation remains absent. The maps must retain the complete current-world
   tuple, scope, witness and every admitted finite/pending development.

2. **Original declaration environment → action instance.**
   `GuardRegistry.law` proves an original registered before/after implication.
   It contains neither changed declaration lookup nor resolver naturality.
   R340 makes their exact missing structural types visible:

   ```lean
   lookup.found : ∀ identifier entry,
     registry.declaration identifier = some entry →
     registry.declaration (lookup.index identifier) = some (a.declaration entry)

   ResolutionCommutes inputs registry resolution a lookup :=
     ∀ goal leaf, resolution goal = some leaf →
       resolution (a.goal goal) = some (actLeaf inputs registry a lookup leaf)
   ```

   These do not assume semantic truth, but **they are not derived from the
   current source declaration implementation**. The consumer proof cannot
   silently count them as supplied. Atomic predicate naturality similarly needs
   the primitive's original contract. Full trace/Meaning naturality is not
   inferred from these Guard-only laws.

3. **Original continuation typing owner → resumed CalleeInputs.**
   EI §5.1 uses the original equation
   `Request(q,C,k) >>= S = Request(q,C,(a,C').k(a,C') >>= S)` and the callee's
   complete original typing. The original Lean `Inputs` exposes opaque
   `observationFields`/`checkedObservation`; `TraceForm` has only `pureReturn`
   and `unfinished`. `PhiT` has no request/continuation constructor or generic
   resumed-trace elimination law. Existing `value_restrict` and
   `carrier_restrict` preserve those specific hereditary objects, not arbitrary
   callee trace membership.

   The exact unproved output needed by R339 is
   `Meaning inputs (.trace ((a.fields.raw answer.raw).atInterface calleeInterface))`,
   together with its actual prefix primitive and dependent CalRet inputs.
   It must follow from the independently typed original saved continuation and
   admitted typed response/development, not be assumed as `CalleeInputs` under a
   new name. A declaration-authenticated equation exposing those response
   obligations in the original callee observation clause is the missing source
   evidence. R340 leaves this hypothesis plainly visible.

4. **Authentic formal route stops at a different interpretation.**
   R336 `sourceRequest` authenticates the complete actual Key/use and physical
   declaration, and `resolved_source_response_domain` gives the exact formal
   typed response domain. `source_bound_request_boundary` applies the formal
   saved-continuation rule without a completed EI body. Its carriers are
   `TypedCall.Value`, `TypedCall.Comp`, and `Control.CallControlStep`; the
   original route uses opaque `s.Observation`, `s.Continuation`, and `Event s`.
   There is no original interpretation equation relating those domains and
   developments in this cone. That missing correspondence cannot be supplied
   by one native run, by choosing an empty schema, or by calling the formal
   domain the original domain.

R311 `Phase.calleeRequest` itself receives only prior/resumed RawObservation;
the actual operation/handle/suffix must therefore be authenticated by an
original encoding/primitive equation. R340's action does not invent that
encoding. R330 static Code registration, R339's conditional receiver packet,
R306 license, and R159 Checking/admission remain separate downstream duties.
No arm was deleted, proved from a source-only route, or replaced by a new W/Z
interpretation.

## Reuse, checks and frozen artifacts

Reused under their actual premises: R339 whole response-record restriction;
R331 PrimitiveInput soundness/callee component construction; R311 unchanged
phaseBody/primitiveGoal; R336 authentic formal response source law. Rejected
as closure evidence: treating R339 schema as original-domain coverage, treating
new changed CalleeInputs as transported evidence, and deriving primitive
typing/lookup from static source registration. Earlier R339 realization gap
receipt is retained; R340 does not claim it has been resolved.

Native code was not changed or executed. This packet produces no new native
correspondence claim. The source/formal owner audit is read-only.

Pinned executable resolved by `elan which lake`:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Observed Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`;
Lean: `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Isolated project: `/tmp/yulang-r340-relation/project`.
Command: `python3 /tmp/yulang-r340-relation/check.py`; actual invocations use
native Lake `--no-cache env lean -j1 -M2048`, explicit `-o` for the selected
module, then complete originating-constant and authored-theorem audits.
All final commands exited 0. One initial multiline record parser error exited
1 and was repaired with the ordinary constructor; attempt-1 logs are retained.

The isolated snapshot authenticated 57 source modules and 3 configs, reused 56
byte-authenticated R339 import artifacts, freshly compiled the new module, and
checked every dependency source hash again after the audit. No shared cache was
written. Measured checker command time across both attempts: **3.824 seconds**.
Finite grant: eight stages/3600 seconds; six substantive stages used (source
contracts, continuation-owner search, atomic action, resolver/input action,
consumer application, check/freeze). Total active wall time was not independently
metered: UNKNOWN; conservatively charge the 3600-second grant, remaining 0.

| Frozen artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalEIContractRealizationR340.lean` | `e4ed751d6c99470ba2df94af250106c786ed86b0e267527aa109cddf09c80019` |
| `/tmp/yulang-r340-relation/dependencies.json` | `261c70d4bb01ab5c9247924ba159829adce18992bf107e93388b98ec294e2d9e` |
| `/tmp/yulang-r340-relation/source-authority-hashes.json` | `a3a790fac49187cb61c2afaa96baebf2d1932d659505d485b7d08079038ac254` |
| `/tmp/yulang-r340-relation/authored-audit.log` | `e92418cd07ec7941be978e964f2e943eeafde1f54783f77de22fa582367fe308` |
| `/tmp/yulang-r340-relation/all-constant-audit.log` | `930805d71058b58885e9deadbd4fd781ba3ac11c168bd9a93217947133c391bf` |
| `/tmp/yulang-r340-relation/summary.json` | `4ad4e257bf35c88fe19f3dcb231839c1756d63bb626ab5073c27d82350d48e73` |

Exact new/write paths are the leased module, this one inbox, and files under
`/tmp/yulang-r340-relation`. The scratch inventory `paths.json` lists every
created/copied file and hash except itself, including the isolated project,
generated oleans, audit sources/logs, source snapshots, manifests and script.
No other file, Git state, compiler, test, expectation, shared record, dependency
pin or configuration was changed.

## Next step and mutual TODOs

`R340-ORIGINAL-DECLARATION-ACTION`: original primitive/source resolver owner
must instantiate AtomicLaws, LookupAction and ResolutionCommutes from its
existing declaration action. Required inputs are the exact original declaration
table and scoped resolver; output is a nonidentity instance for the same source
Key/use. Falsifier: a target registry entry or full-Key resolver disappears while
raw response maps remain lawful. No production edit is authorized by this TODO.

`R340-ORIGINAL-CONTINUATION-CLAUSE`: original observation/continuation owner
must expose the exact independently typed response/current-world domain and
saved-continuation developments in the declaration's original observation
clause, with a two-way domain equation. Derive resumed trace/prefix/CalRet inputs
and apply them at R339. Falsifiers: omitted admitted response, operation/handle
substitution, old-world resumption, replayed receipt, missing divergent prefix,
or a finished CalleeInputs callback posing as the primitive contract.

Luna's next step is independent review of these frozen conditional bytes and
admission of a source-owned instance/continuation bridge if its original owner
can be identified. No claim of complete source Union, R306 license, R159
admission/Checking or production authority follows from this packet.

**SOURCE WRITES STOPPED**, already signaled with source SHA to Luna. Checker slot
released; no subprocess or descendant remains. **ALL WRITES STOPPED after this
handoff's final hash and scratch inventory**. The bounded assignment ends here;
review is PENDING and the worker is STOPPED, not running while waiting.
