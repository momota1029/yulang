# Original Call output: the single occurrence-introduction clause

Date: 2026-10-07
Baseline: `f3be02da1ba169a88acc154ac29621634f3cc89b`
Status: independently compiler-referee/spec-auditor reviewed; no findings
Claim: candidate-interface premise reduction and explicit minimal unadopted constructor clause
Semantic, implementation and production authority: none

## Result

For the approved `my apply f = { my step x = f x; step }`, O0 is still open.
The new result is a reduction of the previous opaque
`L + G + S + independent complete K -> kappa` interface to **one original
interpretation rule for the already generated `Gen-Call-0` constructor**.
Its inputs are that constructor's dependent source record and the
signature-local immediate call-effect position of an independently
interpreted original Function. The rule specifies a typed constructor and
its projection equations; it does not assume a correspondence as input.

The seed proof `S`, complete invocation typing, actual receipt/execution and
full owner/profile formation are not consumed by this local rule. Their
original dependencies are retained. The signature-local position is a
projection of the granted interpretation, not a fresh interpretation inferred
from successful checking. This is a candidate clause with a precise
introduction responsibility, **not a proof or conditional closure of O0**.

## 1. Exact last-rule boundary

The governing [Function-view Authority](../design/2026-10-05-inferred-function-call-views.md)
§§2,5 fixes source formation, shared roots, typed paths, original scopes and
comparison independence, while leaving the constructing judgments open.
The [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§2 fixes the two formals, lexical capture and inert return of `step`.

The inspected last-rule candidates give these different outputs:

| Rule/source | Output actually available | First missing original step |
| --- | --- | --- |
| [Gen-Call-0](2026-10-06-source-call-generation-construction.md) §§4.2–4.4 | Dependent shared-root, upper-demand and immediate invocation address schema; a conditional decorated port map. | Interpret that constructor as an original typed occurrence. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6,9 | Source body/result skeleton; carrier, entry and consumer links. | Original complete signature formation is not supplied by the skeleton. |
| Typed core §6 `Normalize` | Elimination of the corresponding **known** source computation port. | It cannot introduce the port it consumes. |
| [Typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md) §6 | Signature-local positions and transport using supplied typed correspondences. | No interpretation of this new original source occurrence. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2.2,3.5 | Active independently interpreted `DescMem`; constructor/realization results conditional on local typing and source decorations. | The original descriptor and path introduction clauses remain inputs. |

In particular, the named `TypedOutputCorrespondence` first appears in this
route as an independent premise of [K-Owner](2026-10-07-successor-original-kernel-construction-round2.md)
§3.2. The inspected governing texts do not give a completed inductive
definition of its original-sort judgment. Theorem C's separate
[round-6 inversion](2026-10-07-original-call-theorem-c-output-map-round6.md)
already excludes another supplied-map transport proof and is not repeated.

This is a limitation of the displayed rule inventory. It is not a theorem
that every complete interpretation satisfying Authority lacks an O0 proof.

## 2. Independent inputs after reduction

Write `H_sig` for the independently justified original complete Function
interpretation called `K` in the earlier cut. It is distinct from the shared
predicate ledger `K` in `xi=(nu,K,D)`; typed-boundary §6 explicitly preserves
that ledger's identity and truth conditions.

Fix the original binder tree `B`, source component `X`, whole `xi`, and the
actual dependency context `Delta_c` of this demand at the inner Call. Retain:

```text
e_c : the dependent record produced by this Gen-Call-0 instance

e_c carries:
  c = Apply(u_f,u_x); u_f -> d_f; u_x -> d_x
  captured d_f, endpoint v=A_f and shared contract root R_f
  u = this Call's generated upper-checking occurrence VIncl(v,F_c;xi,...)
  U_c := F_c; beta=(d_f,R_f); p0=(beta,call.effect); p_out(c)
  ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c))
  the original binder positions, upper origin and dependency incidences

q_c := callEffectPosition(H_sig,U_c)
    : EffPosition_sig,orig(U_c; B,X,xi,Delta_c)
```

`e_c` packages existing source records; it is not a new source variable,
runtime carrier or semantic certificate of O0. Its dependent fields retain
the lexical facts `L` and generated facts `G`, so they need not be proved a
second time. A generated `VIncl` obligation is not an assertion that the
inequality succeeds. [The existing bridge audit](2026-10-07-original-call-gen-call0-o0-bridge-audit.md)
already justifies naming its demanded interface `U_c := F_c`.

Only a fragment `H_eff` of `H_sig` is used: the original typed-position
family of this Function, its signature-local `call.effect` projection, and
the original root/provider/scope/dependency indices of that position. Its
meaning is **immediate complete invocation**, including the interface's
entry and designated consumers, rather than body/native return or a latent
result position. The rest of the complete interpretation stays fixed; this
projection does not weaken or redefine its admission/observation relations.

`H_eff` may depend on `c` and other legitimate descriptor indices. Its
independence condition is that its formation/projection proof uses neither
the sought `p0` correspondence nor an original interpretation of `e_c`.
It is not obtained from `Q`, final solved types, `WF_Dec` alone, or the
existence of a successful source execution. This grants signature-local
typing, **not source-occurrence typing in disguise**.

### Binder discipline

`d_f`, `A_f` and `R_f` remain anchored at `sigma_apply`; the lexical `u_f`,
Call `c` and checking occurrence `u` occur in `sigma_step`. These occurrences
and scopes remain distinct. In particular, the entire `U_c` need not live at
`sigma_apply`: it may depend on local `A_x` or other coordinates in
`Delta_c`. Project it in its actual well-scoped context. Do not hoist it to
the outer scope and then claim to recover it by a capture map.

The [joint source judgment](2026-10-06-directional-joint-source-judgment.md)
§§2–3 and source-call §§3,4.4 keep local existentials below every dependency
binder, and keep the captured root as an import of `step`. This clause does
not solve generalization: every later legal substitution must act once on
the whole original tuple and all incident records, as source-contracts §3.4
already requires.

## 3. One unadopted primitive head, with computation equations

The missing operation is **original typed interpretation of this source
Call-effect constructor**. A minimal proposed clause is:

```text
e_c : Gen-Call-0 record at its original dependent indices
q_c : EffPosition_sig,orig(U_c; B,X,xi,Delta_c)
---------------------------------------------------------------- OC-CallEff [UNADOPTED]
ce_orig(e_c,q_c) : original typed Call-effect occurrence
                  incident at (U_c,q_c; beta,u,p0,c)
```

Here `ce_orig` is the proposed primitive introduction, not an operation
already available in Authority. Its computation equations are:

```text
signature_position(ce_orig(e_c,q_c)) := q_c
source_position   (ce_orig(e_c,q_c)) := e_c.p0
source_incidence  (ce_orig(e_c,q_c)) := e_c's original (beta,u,c)
origin_and_scope  (ce_orig(e_c,q_c)) := e_c's original dependent indices
```

**Typing this constructor in the original occurrence family is the entire
unadopted clause.** The projection equations alone, or an untyped pair with
the same fields, do not prove that typing. No generic `Reindex`, injection,
original-port-formation predicate or assumed commuting square hides the
introduction above the line. The already generated `ElimOrigin` retains its
separate leg to `p_out(c)`, designating complete invocation; interpreting this
clause must retain that leg without manufacturing runtime `Flow` or receipt.

If this clause is independently established, its incidence evidence is
exactly the requested one-port `kappa`. Forgetting the evidence shows the
graph `{(q_c,p0)}`, but that graph does not supply the evidence. This explains
how the proposed rule would discharge O0 without asserting a new conditional
theorem whose premise already is O0.

The equations concern typed occurrence interpretation. They assert no
equality of effect rows, `E_call` with a body row, actual observation sets,
provider values, or numeric IDs. They do not replace the original path,
slot, contribution or license domains by a constructor image.

## 4. Why this is the remaining atomic clause

First project `q_c` from the independently granted original signature. Its
sort and selected complete-invocation position then require no additional
source rule. Next use `e_c` for the source address and all linked indices;
their construction is already reviewed. What remains is one head: **the
original typed incidence of those two constructor projections**.

Splitting that head into untyped endpoint projections loses the required
incidence. Introducing another predicate saying that their interpretations
agree merely renames this same rule. Adding owner, admission or execution
premises makes it stronger without explaining this introduction. Thus the
displayed head is the atomic source clause on this fixed-constructor route,
relative to `H_eff`. It is not a claim of a representation-independent
minimum axiom basis for every possible completion of the language.

The following premise reductions are exact for this proposed local head:

| Removed from the consumed O0 premises | Reason; evidence that remains retained |
| --- | --- |
| A separate `L` proof | Its resolved incidences are fields of the existing dependent `e_c`; they are not discarded. |
| `S` / seed-at-exposure truth | Protection acts on the upper output occurrence. It does not give that occurrence its type. The original seed, upper/lower provenance and scopes remain available unchanged. |
| Whole `H_sig` as an opaque proof port | Only its independently formed `H_eff` projection is read. The complete original semantics stays fixed and is not inferred from this projection. |
| Complete `CALL_TYPE`, actual receipt, entry or world execution | The constructor introduces a static position; it proves no observation or carrier membership. Complete-invocation meaning comes from the signature projection. |
| O1/C1/J0, `Q` success or final solved type | None constructs this original typed incidence. No downstream theorem is invoked. |

The [directional rule](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
§§2–4 is preserved: retain the original upper occurrence `u` and its seed;
do not use a lower/provider output as `q_c`, propagate the new seed backwards,
or remove independently present provider protection. This reduction consumes
no seed truth and certifies no event protection or ownership.

### What is still not supplied by granting `H_eff`

The current theory has not constructed this signature-local original family
and projection for the fixed source. The reduction does not claim otherwise.
For an unconditional O0 result, a producer must independently discharge
`H_eff` as well as justify `OC-CallEff` in the original interpretation.
Writing a definition of `H_sig` that includes `ce_orig`'s desired typing would
be circular. No existence of a satisfying assignment, descriptor, admitted
source or full `SEM_JOINT` model follows from the rule interface.

## 5. Classification and decision boundary

This is an A/B **source-elaboration introduction obligation**. The selected
source direction and immediate port are already fixed. The missing item is
the original typed interpretation at the owning construction, not a choice
between immediate and latent effects.

If an independent original occurrence interpretation already fixes this
constructor's meaning, `OC-CallEff` must be proved against it as a coherence
lemma. If it does not, the clause specifies the missing case of that
interpretation and remains an unadopted formalization. The inspected texts
do not establish that it is merely a definitional equality already present,
nor prove a new observable language choice unavoidable.

Retention alone is insufficient now: no inspected current compiler phase
constructs this original typed occurrence and then drops it. After a justified
introduction, retaining its canonical derivation is implementation debt;
reconstructing it from current shadow IDs would still be invalid.

No complete pair of Authority-consistent semantics differing on the same
admitted source, and no genuine admitted-source countermodel, was constructed.
Withholding an unspecified judgment or deleting its required typing premise
is not such a countermodel. Therefore no user-decision blocker is established.

## 6. Review, verification and repository handoff

Two independent producer methods examined direct constructor inversion and
adversarial premise independence. They converged on this clause; no third
transport/model variant was launched. The primary repaired a scope hazard:
projection of a locally dependent `U_c` cannot be transported from an
unjustified outer-scope formation. Fresh compiler-referee and spec-auditor
reviews both passed the frozen submission with no findings. They certify the
bounded candidate-interface reduction and authority/scope boundaries, not
existence of `H_eff`, validity of `OC-CallEff`, a derivability equivalence or O0
closure. The primary accepted both reports; no mathematical repair followed.

Mode M3: one compiler-referee for typing, independence and scope; one
spec-auditor for authority and claim boundaries. Convergence requires no
accepted blocking/major finding. Verification is limited to the canonical
DAG generator/checker, reference integrity, exact diff and dependency
stability. No compiler/runtime behavior, test contract or performance path
changes; no build, Oracle run, execution probe or performance sample is needed.

Final deterministic checks: `python tools/research_successor_obligation_dag.py
--write` and its check-only invocation passed at 90 nodes / 196 edges.
Comparison with the baseline JSON found changes only to ORIGINAL_ASSOC's
remaining-clause text and reference list; all statuses and prerequisites are
identical. All 15 newly added relative file links resolve, and
`git diff --check` passes. The GitHub branch check still returned the pinned
`f3be02da` baseline before integration; governing dependency files are unchanged.
These checks verify records and navigation, not the proposed semantic rule.

```yaml
CLOSED:
  - No new O0 or successor gate; existing closed scopes remain unchanged.
REMAINING GENUINE THEOREMS:
  - "O0: independently form H_eff and justify the one OC-CallEff original introduction."
  - "After O0 only: O1 original Slots/Own introduction at the retained upper occurrence."
  - "Then C0: actual-provider whole-carrier checking elimination with retained CalRet evidence."
DESIGN/IMPLEMENTATION DEBT:
  - Original Call-effect interpretation case remains unadopted.
  - Retain its canonical evidence only after its introduction is justified.
USER DECISION NEEDED:
  - None demonstrated; no competing complete semantics or new source restriction selected.
```

`ORIGINAL_ASSOC` stays OPEN-SEMANTIC. All statuses and dependency edges remain
unchanged; its O0 leaf is refined only. O1/C0 and C1/J0/ATTACH/licensing/PROFILE
were not expanded. This note authorizes no production cutover.
