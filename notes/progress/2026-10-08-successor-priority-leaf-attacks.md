# Successor priority leaf attacks: O0, P2, and returned-provider CALL_TYPE

Date: 2026-10-08
Baseline: `61651a312ba7e92839b899a92d2aac9b5b6c16ee`
Status: bounded constructive and adversarial attacks; independent compiler-referee review passed; no gate closed
Authority: current Authoritative Function-view charter and approved question receipts; Draft/conditional constructions remain conditional

## Starting and ending DAG counts

Both before and after these attacks, the canonical 90-node / 196-edge DAG has:

```text
CLOSED: 7
CONDITIONAL-CLOSED: 20
OPEN-PROOF: 43
OPEN-SEMANTIC: 19
IMPLEMENTATION-ONLY: 1
```

The attacks sharpened exact leaves but established no new inference rule or semantic judgment. Status promotion would overstate the evidence.

## O0: original complete-invocation position

The reviewed minimal-clause result already isolates an original typed Call-effect occurrence introduction (`OC-CallEff`) after signature-local position formation. This attack found that the earlier candidate full judgment

```text
B; X; xi; Delta_c ⊢ U_c=F_c : CompleteFunctionSignature_orig
```

is a sufficient possible interface, but minimality of all fields in that judgment has not been shown. The smallest current leaf is the independent formation and projection of the original signature-local immediate complete-invocation effect-position family for dependent `U_c` in its actual `Delta_c`, retaining original indices and whole `xi`. Only after this projection is justified can a separate constructor introduce `ce_orig` with typed incidence. Generated `WF_Dec` is an obligation, and eliminating a generated decorated witness does not change it into original signature kinding. The relevant typed-boundary route assumes supplied descriptors; typed-core's complete-invocation account is a Draft construction under premises.

The compiler-referee review passed this refined boundary and confirmed it remains separate from `OC-CallEff`. No source occurrence, signature position, or typed incidence was produced. `SIG_RULES` and `ORIGINAL_ASSOC` remain OPEN-SEMANTIC; O0 remains open.

## P2: source-owned original slot and owner introduction

Provisionally granting O0 only to isolate P2 leaves the first stop at original static slot membership and owner incidence. The reviewed candidate head is:

```text
e_c : Gen-Call-0 record at fixed original B,X,xi,Delta_c
kappa_c : O0 typed Call-effect occurrence for that same record [granted only]
S_c : reviewed S1 protection at the Call-generated checking occurrence u
       (distinct from the lexical callee occurrence u_f), same seed/root/scopes
-----------------------------------------------------------------------
exists s,o. s ∈ Slots_orig(beta) ∧ Own_orig(beta,s,u_f,p0,o;X)
```

Here the captured root stays anchored at `sigma_apply`; locally dependent `U_c` and its Call check stay at `sigma_step`. Existing K-Leaf/K-Image materializes contribution forms, while K-Incidence consumes an already supplied owner. The previous K-Owner shorthand is unadopted and does not itself provide an Authority-backed introduction. The reviewed `source-contracts` package is conditional/Draft in this area. The refined candidate does not add a cardinality/uniqueness claim, set `s=p0`, or establish P3 uniform family coverage.

Compiler-referee review passed the bounded candidate signature and found no circularity provided the original `Slots`/`Own` judgments retain independent fixed meanings. This is a minimum interface proposal, not a derived owner. `SIG_RULES` / `ORIGINAL_ASSOC` stay OPEN-SEMANTIC.

## CALL_TYPE: actual returned-provider argument compatibility

The source check against `F_c` and the `CalRet` witness's actual provider `U` still require a same-witness bridge. The inclusion direction for a sufficient route is:

```text
Acc(CarrierContract(F_c);C1,w) ⊆ Acc(CarrierContract(U);C1,w)
```

But it cannot be called the first remaining premise without an earlier retained-membership link: `CalRet` supplies membership at `U`, while the source check produces `VIncl(A_f,F_c)` and still needs to establish that the same returned `f` inhabits `F_c` at the same `w`. The corrected dependency order is: (1) derive this checked membership link from `VIncl` and independently justified returned-value membership, preserving exact `CalRet(d_f,f,U,C1;w)`; (2) establish whole decorated carrier inclusion to actual `U`; (3) type the argument at that same witness and compose to actual-`U` compatibility; then apply the already reviewed `DelayIntro` law. Checking only `J_x` cannot establish universal carrier inclusion.

The compiler-referee found the conditional composition sound after the membership-link predecessor is explicit. The carrier inclusion is not proven minimal; argument-specific compatibility could be weaker. `CALL_TYPE` remains CONDITIONAL-CLOSED with its existing `SEM_JOINT` dependencies and no status/count change.

## Review, checks, and next leaf

Each attack was bounded to the selected source and governing rule paths, used no Frozen Oracle semantics, made no repository edits, and ran no build, test or executable probe. The independent compiler-referee review covered O0, P2 and the corrected CALL_TYPE implication. No complete same-source pair of Authority-consistent semantics with different observable outcomes was constructed, so no user-decision blocker is warranted.

Next dependency order: first independently form O0's original signature-local immediate complete-invocation position family; prove `OC-CallEff`; then return to P2 original slot/owner birth. In parallel, keep CALL_TYPE's returned-provider `F_c` membership link and actual-carrier inclusion as separate same-witness premises. These are smaller leaves within existing nodes, not new DAG nodes.
