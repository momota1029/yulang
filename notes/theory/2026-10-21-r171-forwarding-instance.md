# R171 formal-Name forwarding instance and first native association gap

Date: 2026-10-21 repository session. Status: **UNREVIEWED SOURCE/NATIVE RESULT; parent OPEN**.
Author: `/root/r171_forwarding_proof`; no coauthors or descendants.
Assignment `R171-FORWARDING-INSTANCE`, frozen result revision 1.
Activated contract revision 1: `tasks/agent-loop/sprints/formal-name-forwarding-instance-20261021-r171.md`,
SHA-256 `2491bcdc3dc7b09f8aeb06754ebe635b1dae4b8c1e8cef5f526c7517ea667241`.
Activation is Luna's explicit current-session grant, corroborated by current.json; the frozen
contract's prospective CANDIDATE header does not itself assert activation. Baseline supplied by
Luna: `e27d00039`. This leaf does not perform Git operations.

## 1. Parent application and outcome

Parent: `2026-10-15-computation-forwarding-preservation.md` §§1,6–7. Retain one shared satisfying
assignment `xi=(nu,K,D)`, original resolved declarations/formals, open incoming E, arbitrary finite
forwarding chains without a fixed length bound, repeated calls, simultaneously live receiving
entries and every well-typed finite interaction prefix. Preserve independent A/B, F1/FK1, foreign
continuation, raw reentry, complete Call, soundness and principality obligations.

The frozen source is a member of §1's annotated computation-forwarding fragment under that
section's explicit ordinary base contracts. `terminal` supplies §6's direct formal-Name template;
`terminal t` in `relay` is a genuine forwarding edge. The final call in `answer` is the initial
operation input, not a forwarding edge. Section 2 identifies each occurrence before discussing
native rows. Section 3 separately derives the monomorphic initial-operation typing premise.
Neither statement asserts successful parsing/lowering/inference or execution of this fixture.

Applied immediately: the terminal's original source constraints give the original-template
inequalities; the relay's Name/Apply/body constructors identify the additional joins needed for
one step of §6's finite-chain implication. The supplied frozen inputs do **not** establish the
same-provider source FactId/Terms → captured raw fiber or justified shared anchor → own maps →
actual target consumer q association. `R169-SOURCE-FACT-CAPTURE-INCIDENCE-1` remains OPEN. No source
counterexample is established and no universal native or production gate closes.

## 2. Occurrence-qualified source membership

Frozen fixture: `tools/inference-playground/examples/r171-formal-name-forwarding.yu`, SHA-256
`cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
Byte intervals below are zero-based, half-open UTF-8 coordinates of these exact bytes. They are
source locators, not fabricated numeric SourceNodeKey/HirOccurrenceId/DefId/Term/RelationId values.
Let D_T and D_R denote the actual original definition identities associated with these distinct
`terminal` and `relay` declarations; p_T/p_R mean their own retained HirParameterIds. L_T/L_R mean
their respective source-root Lambda occurrences. Identity is qualified by owner and occurrence,
never by the common spelling `t`. Numeric runtime and HIR identities have not been observed.

| Operand | Exact source occurrence and identity | Membership consequence |
| --- | --- | --- |
| Family S | `signal` family header on line 1, `[0,11)`; unique family in this fixture | Finite resolved concrete set `{signal}` for both annotations. No imported or shadow family is present. |
| L_T / D_T | `my terminal ...` on line 4, `[37,69)` | One original named single-formal Lambda, body N_T. |
| p_T | Formal binder `t` at `[50,51)` in D_T's header | This parameter belongs to L_T/D_T, independently of p_R. |
| a_T / row position | Outer `[signal] int` at `[52,64)`; row `[52,60)` | Explicit outer computation annotation; `Computation(E_T,Int)` with local permission `{signal}` and open incoming E_T. |
| N_T | Entire terminal body Name `t` at `[68,69)` | Resolves to p_T, so L_T is the direct formal-Name subcase in §6. No wrapper, projection or extra effect producer occurs in the body. |
| L_R / D_R | `my relay ...` on line 5, `[70,108)` | Separate one-formal Lambda, body A_F. |
| p_R | Formal binder `t` at `[80,81)` in D_R's header | p_R belongs to L_R/D_R and is distinct from p_T. |
| a_R / row position | Outer `[signal] int` at `[82,94)`; row `[82,90)` | Explicit `Computation(E_Rin,Int)` formal with the same concrete permission family, independently identified annotation and open incoming row. |
| A_F | Entire relay body `terminal t` at `[98,108)` | The forwarding Apply; its actual ML-argument tail owns the retained Apply position. The expression range locates that exact constructor, not an invented identical CST range. |
| A_F.callee | `terminal` at `[98,106)` | Unique module declaration Name resolves to D_T, not to a parameter/local binder. Its provider is terminal's authentic declaration-use instance. |
| N_R = A_F.argument | Entire argument Name `t` at `[107,108)` | Resolves to p_R. This is precisely §1's whole computation formal-Name forwarding argument. |
| A_0 | `relay (signal::ping())` at `[121,143)` in answer | Initial call to D_R; not A_F. Its argument Group contains operation call A_ping. |
| A_ping | `signal::ping()` at `[128,142)` | Separate initial operation call, with Unit actual argument `()` at `[140,142)`. It is not a formal Name or a forwarding edge. |

This table follows the actual source constructors rather than an inference result:

- `yu-hir/module/local_source.rs::form:594–681` starts a separate source owner, preserves each
  original header parameter ID, retains its source annotation, pushes that parameter's lexical
  binding, and constructs its Lambda/body before traversing that body. `HirParameterId` contains
  SourceRootId plus ordinal (`module.rs:410–425`); distinct owners remain distinct even if their
  ordinal/spelling agrees. DefinitionRootId is also branded by the actual immutable HIR artifact.
- `Builder::expression:1057–1090` resolves identifiers through the current owner's lexical map
  first and only then a unique namespace declaration. D_T's only parameter is p_T, so N_T resolves
  to p_T. D_R's only parameter is p_R, so N_R resolves to p_R. No lexical `terminal` shadows D_T;
  the module contains one such declaration. Therefore A_F.callee selects D_T. This is specialization
  of the resolver to these bytes, not an arbitrary desired resolution premise.
- `Builder::expression:905–1023` constructs the actual Apply from its ML/call tail and retains
  its separately allocated callee and argument. Empty call parentheses create Unit; a path tail
  creates Operation using `resolve_operation:1141–1153`. The outer parenthesized argument creates
  Group (`1103–1138`). Group occurs only in A_0, not between A_F and N_R.
- `source_annotation::parse_type_source/parse_row:430–516,532–583` produces Int and a concrete
  unique family ID for each `[signal]` row. Annotation.position and row.position are separate
  original source operands; equal resolved family sets do not merge their identities.
- `candidate_source.rs:870–883` registers each original Lambda/formal and selects Computation
  from the outer effects annotation before body use. `initialize_candidate_source_levels:1585–1620`
  allocates each registration's own entry_effect. A finite local permission set does not impose
  `E_T <= {signal}` or `E_Rin <= {signal}`; no such restriction is introduced here.

Applying the reviewed source RootComp construction to these operands yields separate protection
schemas and local `{signal}` permission schemas for the two original formals. An actual receiving
entry would instantiate its own fresh receiver/boundary; static IDs do not instantiate entries.
For A_F, the exact N_R/one-layer designated consumer/Delay/Argument constructors generate the
root map described in the parent §2 and root source-construction §4. This establishes the source
forwarding shape; native execution of that map remains a separate correspondence obligation.
There are no handlers, Bind nodes, raw resumptions or higher-order fields in this fixture. Their
absence in one finite instance does not remove them from the parent's quantified source domain.

## 3. Separate monomorphic initial-operation premise

There is exactly one original public member declaration `our ping: () -> int` (line 2), in the
one `signal` family. `source_annotation.rs:223–275` constructs that member's SourceOperationId
under its original family, retains visibility/signature, and rejects a non-Function declaration.
Here the signature has no type variables, effect variables or nested callable/result effects:
its parsed input is Unit and response is Int (`parse_group:505–516`, Function/Int branches
`430–497`). `resolve_operation` selects the unique nonprivate family/member declaration.

Under §1's ordinary monomorphic operation and ground-value typing contracts, the explicit
source derivation is:

```text
Gamma contains original signal.ping : Unit -> Int
---------------------------------------------- Unit
Gamma |- () : Unit
Gamma |- () : Unit      declared signal.ping : Unit -> Int
--------------------------------------------------------- Operation invocation
Gamma |- signal::ping() : Comp({signal}, Int)
--------------------------------------------------------- ordinary grouping
Gamma |- (signal::ping()) : Comp({signal}, Int)
```

The family contribution is from invoking that operation; merely naming its operation value is
not execution. There is no unknown polymorphic instantiation needed for this base derivation.
Future responses still satisfy the parent's explicit Int-response hypothesis. This discharges
this fixture's initial monomorphic input/declaration premise **within those existing base
contracts**, not general operation soundness/progress or source acceptance by the current
candidate implementation. The native operation owner `candidate_effect::candidate_operation:
904–927` constructs the actual declaration interface and admits slot 42; source Operation slots
1/2 describe the inert callee occurrence (`candidate_source:1274–1291`). Those code facts do not
substitute for the source derivation or certify a successful run.

## 4. Exact original suppliers and the intended forwarding consumer

Use distinct symbolic endpoints, all owned by their constructors:

- Terminal registration e_tT; direct terminal Name effect e_nT; terminal positive Function RE e_RT;
  terminal original Value row v_T with its Int constraints retained.
- Relay registration e_tR; forwarding argument N_R effect e_nR; A_F output effect e_AF; relay
  positive Function RE e_RR; actual A_F Function-demand RE e_C.

`candidate_source:1294–1305,1736–1740` ties each parameter Name to its own registration.
`candidate_effect::candidate_formal_effect_equal:1439–1448` emits the actual two Name facts at
slots 1/2: e_tT<=e_nT and e_nT<=e_tT for N_T; e_tR<=e_nR and e_nR<=e_tR for N_R.
`lib::admit_lambda_fact:11322–11495` uses that Lambda's registered AE and body endpoints, emits
slot 4 bodyE<=RE and slot 2 `P+<=LambdaRoot`, and omits Value-entry slot 3 for these Computation
formals. Thus terminal's original template has e_tT<=e_nT<=e_RT and e_nT<=e_tT; relay's slot 4
is e_AF<=e_RR. The direct terminal body's result remains the actual formal Value row, not an
Int leaf substituted for it.

Each successful original source admission has its authentic ConstraintOccurrence/CauseId and
exact Term pair. `ConstraintStore::admit_and_record_provenance:3671–3718` returns its FactId and
retains the successful provenance edge. Duplicate Term-pair facts may share FactId while keeping
distinct causes. R169's direct source-drain supplier applies to these original occurrences;
it does not invert an arbitrary later Origin into a unique original constructor.

For A_F specifically, `candidate_source:1390–1431` retains the exact callee, argument, argument
effect, result and application effect in its own ApplySourceInput/recipe. The argument's effect
is N_R's component e_nR. `shadow_apply:1978–2080` checks recipe/source correspondence and records
that Apply's own NativeInterface: its positive callee endpoint and negative Function demand with
AE=e_nR, fresh invocation RE=e_C and exact result port. At A_F slot 0 (`2080–2100`) that callee is
compared with that demand; slots 1/2 admit calleeE<=e_AF and e_C<=e_AF (`2100–2133`). This fixes
the intended consumer by constructor, without selecting a numeric q from an unrelated call.

If ordinary propagation reaches a structural positive terminal provider P compared with this
negative demand D at its actual relation q_F, `lib::dispatch_live_item:12648–12720` decomposes
AE=`D.AE<=P.AE` and RE=`P.RE<=D.RE`. `candidate_function_port_admit:3415–3480` records exactly
that q_F/field/child, swaps AE and preserves RE, uses q_F's post-check context, prefixes the
child-local wrapper in source order, and keeps its source/scoped payload. The ordinary route
needs no omitted-formal FormalConstruction/ScopedDemand handle. No q_F, concrete positive
provider Term, native row ID or successful such dispatch has been observed by this leaf.

For an authentic terminal-use map mu_T whose required mapped bounds are actually admitted,
parent §6 gives e_nR<=mu_T(e_tT)<=mu_T(e_nT)<=mu_T(e_RT)<=e_C<=e_AF. Composing the actual relay
Name equality and relay slot 4 then gives the **original relay body** route e_tR<=e_RR. This
application is conditional precisely on the missing native map/admission/consumer association;
it is not a newly proved native result. The outer A_0 compares its own fresh relay instance,
requiring another authentic mu_R and all corresponding copied A_F/body joins. Distinct calls
and repeated/longer chains each retain their own authentic maps; original and copied endpoints,
provider/witness lineages and runtime receivers are never identified merely by equal row IDs.

## 5. First missing association, alternatives and falsifier

**R169-SOURCE-FACT-CAPTURE-INCIDENCE-1 remains the first unsupported native association.** The
source table removes R170's ignored-body exclusion and names all required Name/body witnesses,
but it does not establish that the particular positive provider at A_F's q_F carries their
surviving lineages. The frozen observer explicitly returns `NotJoinedToContextRecord`
(`shadow_apply.rs:167–174`); it has no borrowed source FactId/Terms-to-context certificate.
`ordinary_provider_observation:339–455` enumerates immediate retained FunctionPort parent rows,
associated incoming dependencies/admissions/emissions/origins, and independently retained
module/local Capture routes. It does not authenticate A_F from those numeric rows, recursively
close every dependency route, or connect a provider row to its source slot-2 receipt.

The actual next stages must retain these alternatives, not choose a matching endpoint:

1. For every justified positive-provider route to **that** q_F, authenticate terminal's exact
   original slot-2 cause/fact/Terms and each required same-construction terminal Name slot 1/2
   and Lambda slot 4. Include relay Name/Apply/body joins when transporting the relay instance.
2. A local captured path must identify `Capture::bound:1020–1065`'s exact pre-interning raw
   `(owner,side,item)` cursor, selected attached relation and EvidenceSnapshot. Structural-node
   deduplication/canonical sharing is insufficient; relation=None from an absent cursor is not
   an authenticated source witness.
3. `Capture::expand_row:1067–1073` skips nonlocal rows. Such a witness may remain at its actual
   unchanged session anchor; this requires the independent same-consumer path, not a fabricated
   captured record. Actual canonical self-pairs can cause no new physical bound: a missing
   emission is neither witness loss nor proof of successful preservation. Return its real
   factorization preserving dependencies, identities and residual/scoped payload. This packet
   establishes neither the self-pair factorization nor an absence counterexample.
4. The provider's **own** `prepare_candidate_fresh_use:1569–1874` supplies one context_use and
   consistent canonical rows/terms/effect operands/context/scoped/bundle/evidence maps.
   `begin_candidate_fresh_bound:1875–1922` maps each captured bound with that use and retains its
   source key/snapshot/use_origin; module restoration completes before returning the root
   (`1530–1568`). A sibling/local/demand-owned map cannot replace this provider's map.
5. Follow every justified Derived/Transport/Replay alternative to q_F, retaining Transport's
   parent/child/use_origin/from/to/reason and Replay's ordered
   `(child,lower,upper,lower_input,upper_input)`. `candidate_context_begin_replay:3807–3895` forms
   new-lower×all-upper and old-lower×new-upper quadrants with exact cutoffs, immutable selected
   parent contexts, source union and ordered scoped composition. Dependency interning may
   merge identical structural certificates; it proves no unique constructor event or operation.
   Replay residuals and FunctionPort post-check contexts are distinct owners whose required
   correspondence stays OPEN. No local frame action settles F1/FK1 or foreign continuations.

All five are required evidence paths, not conclusions silently supplied by the observer.
Concrete native tuple/consumer membership is NOT_OBSERVED. No probe receipt was read or produced
by this assignment. Frozen future observation can supply candidates for these joins, but capped
rows or truncated Debug text at a required link cannot certify completeness.

**Minimal next method at the owner:** after Luna adjudication, borrow the already-retained source
cause/fact/exact Terms and direct source-drain relation together with the provider's own original
and use occurrence, raw Capture/shared-anchor choice and exact route maps. Preserve multiple
source/consumer candidates and return explicit absence if the retained structures lack the
association. The required new evidence is the association at its producer, not another run of
this unchanged observer or a second note assuming the same association. No solver edit is
licensed by this packet; any additional instrumentation needs Luna's exact lease/authority.

**Exact falsifier:** an accepted original history, authentic A_F and its compared provider/use,
required original terminal/relay source witness with its cause/fact/Terms, and actual q_F for
which every justified raw captured fiber, unchanged-anchor path and other retained factorization
fails to carry that required lineage/current residual/scoped payload into q_F. An observational
join is falsified by disagreement with its own source/capture/use/consumer owner records. Equal
IDs, missing optional handles, output truncation, successful solve, or absent physical self-pair
emission alone meet neither criterion. Current evidence proves no such mismatch.

## 6. Frozen inputs, checks, resource and cessation

Reused within actual premises: the reviewed parent source preservation and separate native
original-template/instance-relative implication; reviewed RootComp source construction and source
interface constructors; R169 direct source-fact supplier; R165 restoration only for an identified
captured fiber; R70 only under ENTRY-WF; R71 forward raw-to-canonical transport only. R170's
ignored-input result is comparison evidence, not a direct-Name proof. Historical producer/authorship
locators are retained in that R170 note. This leaf is a new producer, not an independent reviewer.

Rejected: original/copy endpoint identification, count-based witness inference, selecting one
provider from q or Origin alone, shared sibling maps, canonical-to-raw converse, narrowing the
parent to this one edge or to `{signal}`, and inference/compilation success inferred from source
membership. Simple-sub generation, accumulation, propagation, levels, extrusion, Value-SCC-qualified
intrusion and generalization remain unchanged. No withdrawn bypass is introduced.

SHA-256 of read exact dependencies (code owners are repository compiler authors; fixture/harness
and activation/current-state receipts are Luna primary; historical R170 proof is its recorded leaf):

```text
parent            d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
contract          2491bcdc3dc7b09f8aeb06754ebe635b1dae4b8c1e8cef5f526c7517ea667241
fixture           cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f
harness           b8d9afd91154c7b0df1d1192ad1567a0e25fac7ef4ff4b698d989acd1c205e75
candidate_scheme  9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225
shadow_apply      46959cf65e447f4c1dc3db34f1969cfa5746e8d7b86227b1b8b456ac2701ddbb
candidate_source  cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
candidate_effect  c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1
candidate_context d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb
solver lib        c75bf47b3d0d87e99d4365a587e6b90d5d05c335db16880cb2943b8b25985
HIR module        153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
root construction d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0
source interface  278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98
R169 supplier     80e637bb64af9cb6247ff4ccb8d1241ef1d721e2d99fa17c52a121bb21e6bb68
HIR local_source  d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
HIR annotation    b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
R170 source       0a5b9b40ef0df8bbca4c2a1583583fa542dc20b1545af39deebe2b324df8bd25
R170 observation  c8596f6fafbf0aa45cd81de2e7b91037dbd7384910122104692dba797b9636d0
```

Checks: static source/authority reading, explicit occurrence ranges and source typing derivation,
constructor specialization and SHA-256 validation. No tests, compiler/build/probe/Y2/Y3/evaluator,
Git, network, user/external contact or descendants. Some initial combined read output exceeded
the tool cap; relied-on source sections were subsequently read in bounded excerpts. No scratch
files were created. Requested routing: configured prover Sol/high; observed model/effort:
UNKNOWN/UNKNOWN. Grant 900 seconds fully charged, no carryover or extension; exact launch-to-stop
elapsed is UNKNOWN. These resource observations do not reset the grant.

Only this note and `tasks/agent-loop/inbox/20261021-r171-proof.md` are written. Stop condition:
source membership/base premise returned, with exact unsupported same-provider association and
owner/falsifier. Luna owns intake, fresh independent membership/native review, any later frozen
probe consumption, new observation authority and Git. **Writes STOPPED with the frozen handoff;
no descendants, child leases, generated outputs or background processes.**
