# Successor dependency attack, round 4

Date: 2026-10-07
Baseline: `1001c274cbf8bc867a03e72edbbfb08b3618e950`
Status: bounded cross-gate attack; no DAG status promotion
Claim class: conditional sublemma and exact remaining-clause localization
Semantic and implementation authority: none

## Goal and starting point

This pass continued from the latest remote `research/simple-sub-intrusion`
HEAD. It did not regenerate the obligation DAG. The canonical DAG checker
reported 90 nodes / 196 edges: 7 CLOSED, 20 CONDITIONAL-CLOSED,
43 OPEN-PROOF, 19 OPEN-SEMANTIC and 1 IMPLEMENTATION-ONLY.

The attack prioritized the existing dependency order around
`CALL_TYPE → ORIGINAL_ASSOC`, while running separate checks on INIT_WORLD,
REC_INIT and ALL_VIEW. The preceding bounded Frozen Oracle archaeology is
retained as historical constructor evidence only: parser/header, formal and
reference construction, application lowering and frame selection identify
structural producers; they supply no original typed output map, original
slot/owner witness, or authoritative source rule. This pass did not query or
execute the Oracle.

## Gate-by-gate result

### ORIGINAL_ASSOC P2 after S1

Before: `ORIGINAL_ASSOC` OPEN-SEMANTIC, with the reviewed S1 seed/exposure
derivation already removed from the independent premise list. After: same
status and counts.

S1 supplies, for the selected captured `f x`, the outer seed at
`sigma_apply`, same-root capture and protection at `sigma_step`, while keeping
the formal binder, lexical Name use, Call checking occurrence, endpoint and
scope indices distinct. `Gen-Call-0` supplies the dependent source root,
complete Function variable, initial effect address and static elimination
schema. Neither result has an original-sort typed output correspondence or
introduces original `Slots_orig`/`Own_orig`.

The first exact residual for this source remains the composition:

```text
OriginalCallOutputIntro:
  resolved source Call and one original scope/xi
  + independently typed callee/whole argument and complete invocation
  + shared U = F_c and source elimination port correspondence
  ---------------------------------------------------------------
  TypedOutputCorrespondence(U, outEff(U), p0; original scope, xi)

K-Owner:
  Resolve(u_f,d_f), Capture(step,d_f,R), SharedContract(d_f,R,sigma_apply)
  UnannotatedFormal(d_f), SeedOrigin(k,d_f,sigma_apply)
  ProtectedVarAt(k,d_f,sigma_step,u_f)
  SourceUpperUse(u_f,d_f,U,sigma_step)
  TypedOutputCorrespondence(U,outEff(U),p0; original scope,xi)
  ----------------------------------------------------------------------
  exists s,o. s in Slots_orig((d_f,R))
             and Own_orig((d_f,R),s,u_f,p0,o;X)
```

`OriginalCallOutputIntro` is a missing original-sort constructor, not a
consequence of `ElimOrigin`, a solved Function shape, endpoint equality or
successful comparison. K-Owner is a candidate rule head, not an adopted rule.
No complete source semantics pair or admitted-source counterexample was
constructed.

### CALL_TYPE immediate returned-world subcase

Before: `CALL_TYPE` CONDITIONAL-CLOSED with CI-Operands and the full
CI-ArgFrame/whole-carrier inputs still uninstantiated. After: same status and
counts.

For the exact inert Value-tagged Name callee, grant one original CI-Operands
witness at `C0` containing captured-argument adequacy and `Typed(J_x,C0)`, and
grant retention of those facts along each retained `CalRet` witness. The
callee's inert `Return(lookup f)` gives `C1=C0`; equality and evidence
retention therefore prove the immediate argument-typing/frame projection at
`C1` using the same retained witness. This removes no canonical premise:
CI-Operands and its independently justified Name/Return facts were granted,
not derived.

The exact remaining immediate compatibility implication is an independently
sound whole-carrier argument-check certificate, linked to the actual returned
`U`, whose satisfaction jointly extends each retained `CalRet` witness to
`ArgCompatible_X(R_arg,CarrierContract(U);w1)` while preserving the original
argument evidence. Later demand worlds, raw resumptions and latent-provider
uses remain outside the immediate `C1=C0` projection.

### INIT_WORLD W0

Before: INIT_WORLD OPEN-SEMANTIC with the independently imported open-root and
zero-step extension clause retained. After: same status and counts.

For a source closure wrapping an independently imported root `p`, Name and
Lambda construction propagate `p`'s retained provider/reference dependencies;
inert construction introduces no transition that discharges them. The exact
missing rule must independently interpret the import at its original
importer incidence, preserve old external incidences, and jointly extend the
open root over the same original `X,xi` and binder positions while leaving
callable/argument holes open. The clause must not assume checked-hole
membership or validity of the extended world. Legal open-import substitution
also needs identification with the fixed semantic import interpretation, not
just generic relation-image transport. This conditional dependency lemma is
not an admitted-source counterexample.

### REC_INIT

Before and after: `REC_INIT_SELF` CLOSED; aggregate REC_INIT OPEN-SEMANTIC;
counts unchanged. The approved exact singleton `my f = f` proof already
establishes pre-execution rejection, preserved F4 inference, no RHS read and
the conditional production ordering obligation. This pass found no new source
class. The next semantic leaf remains another-member direct-Name initialization
with independent inclusion/start, actual target availability and incoming
world; exact q1 does not decide that case. Compiler enforcement remains in
HIR_WIRING.

### ALL_VIEW

Before: ALL_VIEW OPEN-PROOF; PRINCIPAL CONDITIONAL-CLOSED. After: unchanged.

Even after granting independent validity and complete checking at the same
original witness, the nonidentity changed-result case requires both:

1. a finite decorated result-check inclusion certificate preserving original
   operands, scope, incidence and shared witness; and
2. an applicable whole-Function evidence introduction consuming that
   certificate at the actual `B_common` root.

Widened allowance and paired Option 2 extras do not discharge either
obligation. The conditional composition preserves the complete admission,
original strategy and all unmatched extras; it does not establish that such a
certificate or actual resolver case exists. No universal-resolver
counterexample was constructed.

## Integration and verification

The DAG status vector is unchanged because none of these attacks derived an
unconditional node conclusion or a reviewed, authorized semantic rule. The
attacks reduce no status count; they retain the exact next independent clauses
above rather than renaming the same blockers. There are no newly proven
semantic clauses. The Call immediate-return projection is a conditional
sublemma only.

No code, test contract, source semantics or production path changed in these
proof lanes. Producer reports were read against the pinned baseline; the
primary verified that `HEAD` and `origin/research/simple-sub-intrusion` both
equal the pinned SHA before integration. The independent compiler-referee and
spec-auditor reviews passed the bounded claims; the spec auditor's minor
baseline-trace finding was closed by that live ref check. Neither review
promotes a semantic gate. No test, build, runtime probe, Frozen Oracle
execution, performance sample or Git mutation was part of the proof attacks.

Next highest-leverage semantic attack: derive the original typed Call-output
introduction at the actual `f x` occurrence, without consuming the target
association or pending comparison as a premise; then feed that exact map into
K-Owner. In parallel, the default-off implementation lane may add structural
identity joins only while keeping successor export and transport explicitly
unresolved.
