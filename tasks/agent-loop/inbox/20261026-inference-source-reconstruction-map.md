# Original source reconstruction: decisive seam assessment

Date: 2026-10-26. Read-only assessment by `/root/execution_frontier`.
This receipt is the only write. No compiler, proof source, cache, Git,
configuration or scheduling record was changed; no children or checks ran.

Revision r2: primary `/root` narrows the source/native distinction after
independent review MINOR-1. The initial frozen r1 SHA256 was
`40df9211b13ff644a2be7e1a53faea3b05661a556ce3b750aa94c37b3150cf17`;
the original finding and input hash remain in the independent review receipt.
No constructor, original judgment, or mathematical component changes.

## Finding and original statement

The new structural backward-soundness and regular-model results do **not** yet
instantiate `SourceProblem.InferenceSoundness` for the full original source.
On the actual native-success path, the missing operation is a concrete producer
of a solution of the original full decorated constraints and its source evidence.
An already supplied solution of original `G_call` contains `TypedCallCert_Dec`:
generation §5, lines 306–315, reconstructs the fixed representation-preserving
decorated Call/Name/Result/Lambda/Bind rule envelope by inversion and structural
induction. That legitimate conditional theorem does not need to construct its
supplied certificate again. Its all-source coverage and the native-success-to-
original-full-solution bridge are distinct remaining obligations.

The unchanged parent is:

```text
forall s xi d a,
  supported(s) -> generates(s,xi,d) -> solves(d,a) ->
  exists e, sourceJudgment(s,xi,e) and sameScoped(s,xi,e,a).
```

For the original Application rule, generation note §5 and the corrected
source-indexed derivation §1 require one shared witness of:

```text
exists_sigma(F_c,e).
  WF_Dec(F_c;xi)
  and VIncl(A_f,F_c;xi,e_value)
  and WholeArgCompatible(J_a,CarrierContract(F_c);xi,e_arg)
  and CIncl(ExecuteCallableImage(J_f,Delay(J_a),F_c,e;xi),
            original Comp(E_c,A_c);xi,e_result)
  and TypedCallCert_Dec(c,F_c,e;xi)
  and Role_0 and canonical Gen-Call-0 records.
```

`J_a` is the actual source code image, not merely its returned value type.
All independently admitted challenges, prefix/pending/response/raw-resume and
future cases, current worlds, provider identities and independent alternatives
remain. `VIncl` covers every decorated value in the callee interface.

No current Lean module defines these original predicates or the selected
ReadInvoke/EvalInvoke descriptor semantics. Searching the actual Lean sources
finds `sourceJudgment` only as the generic Contracts field and its consumers.
This is a representation gap, as well as a native evidence-supplier gap.

## Actual native evidence, by source constructor

Inspected `candidate_source.rs` and `candidate_call.rs`; line numbers below
refer to the inspected current source and may move with the concurrent native
birth-level patch.

| Constructor | Actual producer | What can be reused / what remains |
| --- | --- | --- |
| Literal | `candidate_source.rs:1592–1610` emits positive leaf≤value row≤negative leaf and effect-bottom≤effect row≤empty effect | Exact literal decoding and existing paper literal typing can supply a leaf derivation. An interpretation connecting the scalar row solution to the original decorated result remains necessary. |
| Name | `:1766–1807`; resolved Parameter/Catch/Case identity, Module/import use, active local initializer Link, otherwise Local fresh use | Correct identity is retained; it is not hereditary membership of the actual binding. Computation-role names have separate effect handling and cannot be treated as pure value reads. |
| Lambda | `:2092–2113`; actual formal registration, parameter position, body value/effect, local Lambda effect and defaults | Four-port structural constraints do not construct the original Strict/Computation entry, captures, whole-carrier domain, profiles or all future evidence. |
| Application | `:1808` onward retains `CandidateRelation::Apply` and exact child origins; `ApplySourceInput` retains source/recipe/level/checking IDs | `NativeInterface` contains scalar Terms and rows, not the full formula above or its realization. |
| Record | `:1979–1995` records ordered field labels/endpoints and each child effect | Structural field data exists; source realization must compose actual ordered child computations in the same resulting world and preserve each returned provider/future. |
| Let/block | Work::Initializer/Install plus final Group and statement effect edges | Native publication/freshening needs the selected Source-Generalize package, fixed/shared anchors, actual bound object and independent-use allocation. Ordinary scalar renaming does not identify that package. |

The native API expressly confirms the gap. `candidate_call.rs:1` says its
objects are source-owned inputs to pending complete Call construction, never
certificates. `PendingCallConstruction::suppliers` always reports:

- `OriginalGenCall0`;
- `ArgumentReifyAndWholeCarrier`;
- `ReceiverDispatchAndCompleteResultFutureInterfaces`.

Formal and module routes add their own original registration, introduction,
checking/exposure and module typing/export suppliers. The whole GenCall0
inventory retains B/X/Xi/Delta, declaration, argument interface, registered
root, complete demand, beta, lexical uses, occurrence positions and ElimOrigin;
the existence of those names is not semantic realization.

## Existing results that do and do not remove the premises

Read `docs/yulang-whole-proof-closure-ja.md` §§4.10–4.19 and their relevant
original sources.

- Source-indexed SC1/SC2 construct actual operand-origin and finite-history
  obligation records from the decorated Application inventory. SC3 composes
  realized matching interfaces. They explicitly do not infer realization from
  an obligation address or a scalar row identity.
- SC4's replacement of an old x value/root by a later Record was withdrawn.
  The corrected construction requires actual Return/rebind. For example,
  existing x={a:0}, y=1 cannot become x={a:1} while silently retaining the
  earlier binding event/history.
- VB1 provides actual fresh ValueBind; GC3/HC-RESULT provide the selected
  immutable Name/ReadInvoke result from genuine operand and whole-carrier
  inputs, with the same actual provider and all finite phases.
- The later selected EvalInvoke constructor covers computed callee ordering
  and dependent CalRet; it does not identify every native result row with that
  full descriptor or eliminate target-specific CIncl.
- Native-profile PF1/PF2 construct the selected native licensed local policy
  from actual field provenance and independent local laws. They do not
  manufacture dynamic authority, arbitrary foreign predicates or all unknown
  certificate fields.
- `TypedCall.CallTerm` in `CoreSyntax.lean:442` **already contains**
  `functionTyped`, a Carrier with `typed`, receipt/adapter agreement, and a
  fresh receiver-owner premise. The existing Call prefix/boundary theorems
  consume that object. They cannot produce source inference typing without
  moving the disputed conclusion into these inputs.
- `CallEnvironmentRealization.close_body` genuinely reads captures but still
  needs per-cell typing and a typed body. `SourceGeneratedInteraction` also
  starts with typing and uses typed allocation RHSs. Neither reconstructs
  original source typing from a solved constraint graph.

## Minimal decisive next construction

The strongest concrete original-schema target on that native production path
is the **selected immutable Name-call certificate producer**, starting with
actual `h x` and preserving the original environment, independent challenge
domain and full witness. This is a producer of the original full solution's
components, not reconstruction from a full solution already supplied.

Required theorem, not a new source typing definition:

```text
actual resolved Name h / Name x and their original binding evidence
+ the original independently formed complete H* and its hereditary membership
+ actual NameDelay(x) checking at the already selected Comp(empty,A) inlet
+ the actual IF/GenCall0 field injections for this occurrence
+ the selected native licensed profile/permission constructors
+ independently supplied original primitive / other-arm contracts
  ->
the complete ORIGINAL G_call witness for this occurrence,
including every TypedCallCert field, and for every original finite M_E phase,
DescMem(ReadInvoke(H*,D_h,IF_h)) at the SAME joint witness/current world.
```

The child binding and independently fixed foreign contracts are legitimate
constructor inputs. For this native producer, the desired source typing,
composite CIncl or final Call certificate cannot be assumed from scalar success.
The existing decorated-rule reconstruction may instead consume the certificate
already present in a solution of original `G_call`. Once this producer is established,
literal/Name/Record and actual Lambda introduction can recursively discharge
its local child inputs; actual let publication must use the selected scoped
source-Generalize rules, not simply clone the scalar solution.

**Why the native producer is not already a ready small Lean packet:** GC §4 states that
`TypedCallCert_Dec` in original generation §5 is **not an exhaustive dependent
record declaration**. Its supplied decorated receipt/profile/observation
premises are not all enumerated. PF1/PF2 fill the selected native local-policy
component, but explicitly do not redefine the abstract certificate with all
unknown fields. A new generic `LocalLaws` record or an opaque certificate
parameter would merely rename the missing evidence on this native production
path. This does not invalidate the fixed decorated-rule induction from full
original solutions.

The next bounded constructive assignment should therefore first extract the
complete original certificate telescope from typed-core/source-contracts,
GenCall0, native-signature and the selected ReadInvoke/EvalInvoke authorities,
and give each field an actual constructor. Begin with the original Name route
where GC3 already supplies CIncl/phase evidence. For each field, either:

1. construct it from actual NativeInterface/source-origin data and the named
   authoritative constructor; or
2. expose an exact absent native datum or independent semantic premise.

This is a decisive source-admission/producer task, not a further source-indexed
inventory or source-typing-as-success definition. I do not recommend claiming
the whole source bridge closed by a new finite scalar checker or by a new
small STLC source language.

## Rigorous discriminator and remaining scope

The selected pure-read authority §6 records a separating model: a provider
satisfies its complete Function contract and returns Int while an independently
fixed result descriptor admits Bool. IF incidence and receiver typing alone
do not entail that result descriptor. The selected identity ReadInvoke case
resolves this particular discrepancy by definition; it does not justify
replacing arbitrary fixed targets. The native result-row→selected-descriptor
correspondence is therefore a substantive proof obligation.

Likewise, matching scalar function ports cannot remove WholeArgCompatible or
the original whole joint witness. These are proof-inference obstructions,
not findings that native Yulang accepts an ill-typed source program.

Source-level actual certificate production, native generation correspondence,
complete Call/effect interpretation, source environment realization, recursive
membership and generalization remain OPEN. No original claim, syntax domain,
world/response quantifier or shared witness has been narrowed in this assessment.

**STOP: sole receipt written; all writes stopped.**
