# Successor frontier attack from current remote

Date: 2026-10-07
Baseline: `182cfebad42bd77e98dd96022f96c71bb4933759`
Scope: bounded current-HEAD attacks on the existing canonical DAG; no semantic or production authority added
Implementation: captured-source shadow retention already present; no code change

## Status accounting

The canonical validator at the pinned remote reports 90 nodes / 196 edges:

| Status | Start | After these attacks |
|---|---:|---:|
| CLOSED | 7 | 7 |
| CONDITIONAL-CLOSED | 20 | 20 |
| IMPLEMENTATION-ONLY | 1 | 1 |
| OPEN-PROOF | 43 | 43 |
| OPEN-SEMANTIC | 19 | 19 |

These attacks closed no node and produced no admitted-source counterexample.
The status count is deliberately unchanged. `REC_INIT_SELF` remains closed
only for the exact approved singleton `my f = f`; no other initializer inherits
that result. CALL_TYPE and PRINCIPAL retain their existing conditional
closures. No status was promoted from a conditional construction or a
syntactic/source identity.

| Attack | Before | Result | After |
|---|---|---|---|
| CALL_TYPE input construction | CONDITIONAL-CLOSED | Exact Name/Name CI-Operands and CI-ArgFrame instances still need independent semantic construction | CONDITIONAL-CLOSED |
| ORIGINAL_ASSOC P2 | OPEN-SEMANTIC | Existing original slot/typed-position/complete-contribution/joint-incidence introduction still lacks a source constructor | OPEN-SEMANTIC |
| INIT_WORLD W0 | OPEN-SEMANTIC | Guarded step-index route lacks zero-step open-root introduction at import incidence | OPEN-SEMANTIC |
| REC_DESC | OPEN-PROOF | FH failure inversion and simultaneous two-closure route each retain their exact independent semantic input | OPEN-PROOF |
| REC_INIT | OPEN-SEMANTIC; `REC_INIT_SELF` CLOSED | Exact singleton rule unchanged; other initializer classes remain unspecified | OPEN-SEMANTIC; `REC_INIT_SELF` CLOSED |
| ALL_VIEW / PRINCIPAL | ALL_VIEW OPEN-PROOF; PRINCIPAL CONDITIONAL-CLOSED | No actual designated export Direct certificate; restricted Function rule requires the matching interface premise | ALL_VIEW OPEN-PROOF; PRINCIPAL CONDITIONAL-CLOSED |
| SOURCE_ADEQUACY | OPEN-PROOF | Lambda head reduces to raw-vs-emitted completed Call body correspondence | OPEN-PROOF |

## Priority A: ordinary Call and original association

The fixed approved source cut remains
`my apply f = { my step x = f x; step }`, with the inner
`call(result(name f),result(name x))`, one original `X`, scope tree and
`xi=(nu,K,D)`.

**CALL_TYPE** was already CONDITIONAL-CLOSED by the reviewed full composition.
The attacks did not instantiate its source-generated premise family. Even on
the exact Name/Name cut, lexical lookup and `Result(Value(A))` do not type the
returned descriptors. The first local constructor heads are the independent
operand/environment introduction and its Name/Return consequence:

```text
admitted original (C0,w0)
  -> jointly adequate Env_X/Gamma/provider/world at one scope and xi
  -> Typed_X(R_f, Return(lookup f), C0; w_a)
     Typed_X(R_arg, Return(lookup x), C0; w_a)
```

At an actual returned callee world `C1`, the complete carrier branch additionally
needs one evidence-preserving compatible extension which jointly establishes
`Typed_X(R_arg, Return(lookup x), C1; w1)` and
`ArgCompatible_X(R_arg, CarrierContract(U); w1)`. For this particular inert
Name callee, adequate lookup can specialize `C1=C0`; it does not prove either
semantic predicate. Receiver receipt, phase, designated consumer, ordered
Bind and pending/future-use laws remain independent CALL_TYPE inputs. No
Authority rule inspected derives these heads. No fake CALL_TYPE
counterexample was obtained by deleting one of its conditional hypotheses.

**ORIGINAL_ASSOC P2** remains OPEN-SEMANTIC. Granting the complete typed Call
does not introduce an inhabitant of the existing original kernel. FVIEW §2
leaves source generation of `beta`, `Slots(beta)`, typed `p0`, owner and paths
open; source-contracts §2.1 takes independently interpreted primitive and
owner/view kernels as input, and §3.5 preserves those inputs. The minimum
missing source rule must jointly introduce an original slot/owner, a typed
position, the complete source-owned contribution and their incidence at the
same original `X`, scope and `xi`, with no `Q` premise. A typed Call image,
locator, endpoint, equality or successful comparison cannot stand in for that
introduction. This remains a clause gap, not a nonderivability theorem or a
selection of new semantics.

The minimum target is kept at the existing sort boundary:

```text
OriginalAssocType_X(
    beta, p0, j_call;
    slot, contribution, owner/view,
    xi=(nu,K,D), original_scope)
```

Its independent constructor inputs must each expose their actual evidence:
`slot ∈ Slots(beta)` together with its source declaration/root ownership;
the original typed output-position correspondence for `p0`; a contribution
typing certificate for the **complete** callee + whole-argument + actual
receiver/entry + body + designated consumer + return + pending/future suffix;
and a joint owner/view incidence tying that slot, position, contribution and
source occurrence to the same `X`, original scope and `xi`. Their original
licensed witness domain remains complete. This is the input/output contract
needed to construct the existing judgment, not a selection or definition of
those semantic predicates; the inspected Authority supplies none of these
constructor inputs from source identities alone.

P3's uniform complete-family assembly and preservation of every licensed
witness, then P4/ATTACH and both licensing directions, remain open downstream.
Pointwise coverage does not provide one original witness for the whole family.

## Priority B: initial world and recursive descriptor

**INIT_WORLD** remains OPEN-SEMANTIC. The guarded step-index candidate only
admits a hole assumption at a smaller index after a concrete source
transition. Initial Name/capture/Delay and descriptor construction are
inert, so they supply no such step. The zero-step introduction still missing
is an independently licensed open semantic root for the punctured callable
and whole-argument interfaces, at the actual import incidence and one
`(rho,C0,xi,w)`, preserving shared provider/state/reference identities and
existing activity. Its conclusion must remain filling-independent. Putting
installation into the source transition would add an unselected event;
closed-program reachability and a supplied `Imp_Delta` do not introduce this
root. This narrows the indexed proof route only and selects no world rule.

**REC_DESC** remains OPEN-PROOF. For captured `g`, name synthesis and K can
retain the actual provider `v_g` and actual returned world, but do not prove
`DescMem(R_g,v_g;xi,w)` there. FH gives
`forall h. exists e. LocalCheck(h,e)`; a failure proof needs the correctly
scoped `exists h. forall e. not LocalCheck(h,e)`, not one failed extension.
The direct route instead needs independently grounded simultaneous ordinary
constructor acceptance for both closures, their own-root/world validity,
CompleteMem and nonrecursive guards; assuming a world which already entails
the target member is circular. These are two distinct candidate proof methods,
not two proofs of the missing clause. No finite reflection or recursive
acceptance theorem was established.

The reviewed exact `REC_INIT_SELF` source rule already rejects only singleton
`my f = f` before initialization or RHS self-read and preserves F4 `Never`.
This attack does not reopen it. Aggregate REC_INIT and actual enforcement
remain separate.

## Priority C: actual export and principality

**PRINCIPAL** remains CONDITIONAL-CLOSED; **ALL_VIEW** remains OPEN-PROOF. The
actual-export attack found no designated `Direct(B_common,R_V)` certificate
for a nonidentity widened value view. Within source-contracts §5.3's displayed
certificate calculus, a changed Function result interface cannot use its
Direct Function rule because that rule requires a matching non-coverage
interface; paired Option 2 extras only propagate supplied base/envelope
proofs. Even an independently supplied finite leaf `VIncl` does not satisfy
that parent rule. The separate decorated `MemValue(Int,z) -> MemValue(Top,z)`
leaf is still not constructed. This is a restricted calculus obstruction,
not a counterexample to every resolver or an admitted source.

## SOURCE_ADEQUACY and shadow lane

**SOURCE_ADEQUACY** remains OPEN-PROOF. Approved inert Bind/Lambda formation
reduces the first latent body square to the original raw `f x` Call versus its
emitted complete Call at the same environment, current world and original
scope/witness. The operational correspondence must include the actual
provider entry, receipt, body, declaration-designated result consumer,
return delimiters and the full pending suffix in both directions. Dropping
the post-native-return consumer gives a discriminator, but violates the
already-required completed Call; it is not an admitted-source counterexample.

The proposed captured-source shadow-retention implementation slice is already
present at the baseline in `yu-hir`, Core and `shadow-f5`: it retains the
approved Bind/capture/Apply identities through solver finish while preserving
all seven pending premises, production `UnsupportedExpression`, empty
semantic facts and no Call acceptance. The existing
`shadow_captured_source_retention` integration target passed all 4 tests with
`RUSTC_WRAPPER=` and one Cargo build job. The initial wrapper-default run
stopped in sccache before compilation; the explicit empty wrapper rerun passed.
No code edit or new semantic carrier was warranted. This is structural
retention/refusal differential, not old/new inference parity.

## Review, integration and next attack

These are bounded constructive/falsification/source-artifact reports. The
compiler-referee and spec-auditor independently reviewed this synthesis;
their only finding was the corrected §5.3 owner citation, closed by delta
review. Both accepted all status limits and the qualified semantic clauses.
No tests beyond the already existing focused shadow target were run; no broad
suite, build matrix or performance measurement was run. No Git mutation has
been made in this attack slice.

The highest-leverage source chain remains `CALL_TYPE -> ORIGINAL_ASSOC P2`:
construct and review the independent `Env/Name/Return` and whole-carrier input
clauses first, then the original owner/contribution introduction at the
existing kernel sorts. Until such source rules are Authority-grounded and
their premises discharged, downstream licensing, profile, rows and admission
cannot be claimed closed. Preserve every original `xi`, provider and
licensed witness. Production cutover remains blocked by all open semantic and
source-adequacy prerequisites.
