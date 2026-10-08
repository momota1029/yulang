# Scalar import: exact PhiW premise substitution

Date: 2026-10-10
Baseline: `00bc2351bee96dbb705a680408e3ff436d70c313`
Branch: `research/simple-sub-intrusion`
Status: compiler-referee-reviewed conditional derivation and constructor-signature characterization
Authority: research only; `INIT_WORLD` remains OPEN-SEMANTIC
Exclusive lease: this file

## Objective and fixed interpretation

Determine whether the selected immutable constructors construct an
importer-owned scalar binding at the same original `(C0,xi)` and restrict
back to the prior tuple. This is a premise-substitution calculation for one
binding, not another search for missing definitions.

Governing sources are contextual Function membership definition §3,
simultaneous immutable introduction §§2–5, semantic input realization §4.1,
and the zero-step extension attempt. Keep the exact selected positive
operator, independent domains and immediate guards. Knu still covers its
exact two-closure source graph; Step still covers its actual captured closure;
Lemma W Import still restricts an existing same-reference certificate. No
source constructor, semantic import rule or foreign embedding is added.

## One scalar instance and its hypotheses

Use the earlier scalar example `pub seed = 0`. Treat its independently typed
scalar descriptor `A_s` as supplied: this note does not derive the original
literal typing or choose the meaning of `Int`. Assume it has no latent
Function/carrier demands. Fix a *single original fiber* `xi=(nu,K,D)` and
original binder/witness scopes containing the exporter root `rho_s` and a
licensed importer incidence `i`. Exporter and importer may have different
configurations even in this common fiber. Different-fiber linking requires
an additional map and is outside this instance.

Let `b : W*(C0,w_B,e0)` be the supplied valid importer base, with
`e0` retaining actual configuration `C0`. Incidence `i` is absent from its
installed environment. Form the non-overwriting record

```text
w+ = w_B plus {i -> (A_s,0,rho_s)}.
```

Copy every old coordinate and dependent witness at its original scope. Add
no provider, activation, receipt, grant or State identity. Distinguish:

```text
g_s : Ground(A_s,0,rho_s,e_s; exporter incidence)
g_i : Ground(A_s,0,rho_s,e0; importer incidence i)
j+  : JointRegistryScopeCurrentAuthorityIncidence(C0,w+,e0;xi)
a+  : AliasCaptureAndSharedWitnessAgreement(w+,e0;xi).
```

`Ground` abbreviates the selected PhiV ground clause's *entire independently
specified relation*, including original registration/incidence and hereditary
restrictions. `g_i`, `j+` and `a+` are independent premises, not conclusions
from exporter validity. Existing guards at old coordinates and overlap
agreement must remain at the original joint assignment. For a foreign
EnvStore, the exhaustive evidence-preserving clause embedding is another
premise.

## Conditional derivation: membership adds no recursive obstacle

Write `Z*=(V*,W*,T*,Car*)=nu Z.Phi(Z)` in the selected interpretation.
Given `b,g_i,j+,a+`, construct `W*(C0,w+,e0)` as follows.

1. Unfold `b` once. Its PhiW readout supplies each old binding's same-root
   `V*` or designated `Car*` certificate at `e0`, together with the old joint
   fields and agreement. The proposed record copies these exact binding
   tuples; it does not transport their certificates to a different event.
2. Apply PhiV's ground clause to `g_i`. It has no recursive kernel premise,
   so it gives `Phi(Z*).V(A_s,0,rho_s,e0;i)`. Fixed-point equality gives the
   same tuple in `V*`.
3. Supply `j+` and `a+` directly to PhiW. Its binding obligations are precisely
   the unchanged old certificates plus the scalar certificate from step 2.
   Thus `Phi(Z*).W(C0,w+,e0)` holds.
4. Fixed-point equality yields `W*(C0,w+,e0)`.

This is an operator-level conditional theorem. It assumes neither completed
extended-world validity nor scalar membership recursively. No new coalgebra,
declared hole, challenge-domain restriction or operational install step is
needed. It does **not** generalize Knu's source constructor theorem.

## Exact restriction and its semantic limit

The construction has the structural equation

```text
pi_B(w+) = w_B.
```

On binding coordinates, projection returns the exact old tuples and their
certificates from step 1. No witness is hoisted above its original binder;
the retained certificate is still `b` at `(C0,xi,e0)`. Consequently the
construction can carry a checked record retraction and the supplied base
proof together. This is preservation of an input certificate, not a generic
restriction theorem for arbitrary extended-world evidence.

To obtain an importer-owned semantic restriction action from the *extended*
certificate alone, its original guard interpretation must additionally prove

```text
pi_B(j+,a+) = the base guard/agreement evidence at (C0,w_B,e0;xi),
```

with all required independent atoms and dependent scopes preserved. Phi's
monotonicity is in `Z`, not in the registry, environment or independent
context domain. It therefore supplies no deletion/puncture law for those
fields. Hereditary restriction is to independently compatible **events**;
deleting a binding at the same event is a different action. The displayed
record retraction must not be promoted to that missing semantic law.

## Which selected signature supplies the premises?

| Selected case | Exact input/output at this scalar instance |
|---|---|
| PhiV ground leaf | Consumes `g_i` at the importer tuple. World-independent scalar payload facts from `g_s` are reusable; original registration/import incidence facts still require importer evidence. |
| PhiW | Consumes `j+`, all old binding certificates, the new same-root certificate and `a+`. It proves the world after those inputs; it cannot generate its immediate guards. |
| Inert registration | Consumes original source formation/license and joint registry/scope/cross-root incidence guards. Even if `i` has a license, that license supplies no demonstrated configuration-agreement proof at `C0`. |
| Lemma W Import | Follows a resolved reference to the same existing binding certificate and restricts it. The new importer incidence is not an existing base projection. ResultBind needs an actual typed Return and rebind; neither is a zero-step scalar import premise. |
| Knu / Step | Retain their exact source/capture cases and independently supplied registration/context guards. Their constructor inputs cannot be replaced by `g_s` at a different configuration. |

The narrowed owner obligation is therefore an importer introduction of
`g_i,j+,a+` with a clause-preserving `pi_B` at the original tuple. Even the
common-fiber, inert, one-binding instance lacks that selected premise action.
The scalar payload and fixed-point membership machinery are not the remaining
construction problem. This is a signature mismatch, not a rejected Yulang
program or a source counterexample.

## Evidence, coverage and stop condition

Method: documentary unfolding, exact premise substitution and structural
projection. The independent oracle is the selected clause presentation, not
an executable checker or an independently established importer rule. The
derivation shares its Phi definition and ground/guard parameter meanings with
the selected theorem. It supplies no independent source-rule validation.

Coverage: one non-overwriting, inert scalar incidence in one original fiber
and one actual importer event. Omitted: source literal introduction,
cross-fiber linking, hole-dependent imports, source-open aliases, negative or
world-dependent descriptor fields, State, future-event compatibility,
foreign embedding and arbitrary world restriction. No seeds, enumeration
ranges, mutations, builds, tests or probes apply. Failure occurs if the new
ground/incidence proof or any joint immediate guard is unavailable, shared
witnesses conflict, an old coordinate is overwritten, or restriction loses
an independent atom/scope.

Read-only commands: pinned `git show` section reads; baseline/branch/status
inspection; SHA-256 dependency inspection. No Git mutation or question file
read occurred. CPU/process budget consumed: zero build/test/probe processes;
only short serial/paired documentary shell reads. Peak RSS and total wall
time were not measured. An independent compiler-referee review passed with no
findings in the conditional derivation, scope-preservation, and structural-
restriction claims; foreign embeddings and Rust correspondence were outside
its scope.

Recommended next action: obtain or authorize for research one exact
importer-owned ground-incidence/joint-guard clause with its `pi_B` evidence;
review that clause before using the conditional PhiW derivation. Another
fixed-point toy probe would leave this same premise untouched.

## Frozen commit packet

- Exact leased path: `notes/progress/2026-10-10-initworld-phiw-import-construct.md`.
- Baseline: `00bc2351bee96dbb705a680408e3ff436d70c313`.
- Dependency changes: none used; all source reads were pinned to baseline.
- Review status: independent compiler-referee PASS; conditional derivation only.
- Checks run: exact selected section reads and baseline dependency SHA-256;
  artifact scope/whitespace inspection. No builds/tests/probes.
- Proposed commit message: `research: isolate scalar importer premises for PhiW introduction`.
- Shared-record deltas left to primary/curator: retain INIT_WORLD OPEN-SEMANTIC;
  distinguish conditional PhiW membership from the unresolved importer guard
  introduction and semantic old-tuple restriction. No authority/DAG closure.

Pinned semantic dependency SHA-256:

```text
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
607ca1783075274b21ac617369b9298b1c48ccb255c3a51e142a02ca91a733b3  notes/progress/2026-10-09-init-world-zero-step-extension-attempt.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
```
