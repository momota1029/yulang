# Adopted pre-Call construction for `my invoke f = f 1`

Date: 2026-10-11
Status: Conditional derivation; actual declaration correspondence OPEN
Scope: formal/Name/Int source-owned pre-Call schemas in the adopted interpretation
Baseline: `18049fc9af145ebf558fa189503df07d5c2b9191`
Candidate dependency: `fdda52fd8ec9eb1b3a691825a7b895b3a40fc753`, SHA-256
  `9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`
Authority: [bounded API adoption](../design/2026-10-10-original-registry-constructor-adoption-proposal.md)
Proof review: independent compiler-referee delta accepted for the conditional construction
Supersedes: none

## Claim and assumptions

Fix the actual source occurrences in `my invoke f = f 1`: the lambda `L`,
formal `d_f`, resolved body Name `u_f`, Apply `c`, literal `a` with payload
`1`, the actual `Resolve(u_f,d_f)` edge, lexical/scope maps, and the argument
incidence from `c` to `a`.

Assume the **complete finite declaration graph required by the adopted
candidate's recipe and import closure** is supplied. For every reached
declaration, assume its entire ordered telescope, every arm and catalogue,
scope/reference/world maps, and static constructor operations are well-formed
at the candidate's displayed operand contexts. In particular, the complete
Value-entry, carrier, receipt, designated Force, rebind, Int, Return, Prefix,
Name, and scope/reference declarations must each have an applicable whole
substitution. This assumption is stronger than merely having one declaration
or a collection that happens to contain the Int declaration.

Under these assumptions, in the adopted source-owned interpretation, the
source recursion constructs one immutable raw registry `P` and, at that same
`P`, a dependent schema family containing:

```text
WellFormed(P), reg_f, T_c,
q_f  : Data_src(P,T_c,name u_f,Value(A_f)),
q_cf : Code_src(P,T_c,result(name u_f),Comp(empty,A_f)),
q_a  : Data_src(P,T_c,literal(a,1),Value(Int)),
q_ca : Code_src(P,T_c,result(literal(a,1)),Comp(empty,Int)),
ChildCode(a,q_ca), J_f, J_a.
```

The family retains each original scoped local proof choice and predecessor;
it does not choose a successful runtime witness. `J_f` and `J_a` contain the
whole declared Return and Prefix image alternatives and their complete local
catalogues.

This is a conditional pre-Call construction theorem. Its declaration-graph
assumption has **not** been shown to follow from the selected actual source
declarations. It does not identify the adopted constructor family with a
separately fixed original kernel, and it proves no primitive membership,
inhabited guard, returned provider, successful Call, solving, public
generalization, principality, or F5 behavior.

## Construction

1. From the actual source occurrences, emit the nominal Formal, DataName,
   ResultName, DataLiteral, ResultLiteral, and Image recipes. Traverse the
   complete finite local declaration/import graph and retain each reached
   declaration token once. Seal this source, context, recipe, and schema syntax
   as `P` before forming any registry-indexed source object.

2. Substitute this same `P` into the original ordered context `Gamma_0(P)`.
   The assumption supplies each complete local declaration application at its
   original binder order. Check every field type at its preceding binders,
   including fields under guards and opaque alternatives.

3. At the unannotated formal, Source Generalize supplies the ordinary Value
   role and the pre-challenge descriptor
   `Desc(C,d_f,value,sigma_f,Delta_f)`. Allocate its ordinary flexible
   descriptor `A_f` from that source introduction. No invocation result,
   received argument, or successful Call is used to choose the role or Desc.

4. Apply the adopted `Header-Parameter`, `Declare-Owned-Port`, and
   `FormalOwner-Ports` constructors. These form the candidate header, intrinsic
   root, `ParameterOrigin`, and the complete carrier/receipt/Force/rebind port
   declarations and scope maps. This is the adopted candidate origin; no
   equality with another fixed kernel judgment is inferred.

5. Apply `Assemble-Value-Entry` to those complete ports. In original order it
   forms Receive, Receipt, designated one-layer Force, and Rebind, yielding
   `T_c = ValueBind(Empty,d_f,r_f,A_f,entry/rebind origin)`. These are schemas;
   event receipts, providers, worlds, body values, and future witnesses remain
   dependent fields and are not inhabited by this construction.

6. `Register-Parameter` packages the header, Desc, owned declarations,
   licenses, entry schema, and `T_c` into `reg_f`. `OShared` then forms the
   shared invocation anchor from this registration. The anchor is a static
   address schema, not Function realization or slot membership.

7. The actual lexical `Resolve(u_f,d_f)` edge and the same Formal bundle form
   `q_f`. Its whole Return port then forms `q_cf` by Code-Result at the same
   `P`, `T_c`, root and `A_f`. Reuse preserves the same scoped Formal proof
   choices; Name does not re-register or re-instantiate the formal.

8. The complete Int declaration at the actual literal occurrence forms
   `q_a` with the same `T_c` and original scope. Its complete Result header and
   Return port form `q_ca` and `ChildCode(a,q_ca)`. The literal token supplies
   no primitive membership or guard witness.

9. From each whole Data and Result bundle, apply every declared Return and
   Prefix constructor-image alternative with its original field maps and
   catalogue provenance. Their tagged union forms `J_f` and `J_a`. The image
   roots are source-generated under the adopted interpretation and remain
   distinct from `Comp(empty,A_f)`, `Comp(empty,Int)`, q2's `J_lit`, and any
   separately fixed image relation.

The dependency ranks are Law `0`, Formal `1`, Data `2`, Result `3`, and Image
`4`. Every source formation reads only raw `P`, a genuine complete local
declaration, an original preceding binder, or a strictly earlier source
bundle. Induction on these ranks therefore constructs the decoder and all
listed same-`P` projections without a circular `P = table(Code(P))` premise.
Candidate inversion and reflection results apply only to their stated
already-well-typed consumer applications receiving this complete same `P`.

## Exact remaining source and Call premise

The actual declaration correspondence has not established the first
`Declare-Owned-Port` application. Its missing judgment is the complete
ordered application for each carrier/receipt/Force/rebind family:

```text
Gamma_available(P, I, h_f, endpoint, incidence)
  |- mu_delta : Delta_in(delta)

Fam_delta[mu_delta]
```

`Delta_in(delta)` here denotes the actual full local telescope, including the
domains of all binder arguments, not a newly proposed signature. The argument
maps must retain the actual source/scope maps, each whole field and static
license, and check every field type at its original predecessors. The
read-only source audit found no complete elaboration of these applications in
the selected Generalize/Call-input/source declarations. It found a missing
supplier, not a late-decoder dependency, incompatible declaration, or source
counterexample. `Gamma_0(P)` formation and complete primitive/operator
catalogue maps must also be shown for the actual declaration graph.

After this pre-Call gate, the original normal-inference theorem still needs an
actual complete Application/Gen-Call constructor, whole-argument compatibility
at the same returned provider, independent admission/C0, complete Call
discharge, and the downstream soundness/principality argument. The source
candidate's scalar four-port demand does not supply those judgments.

## Evidence and review

The constructive producer was the configured `prover` role, requested at
Sol/high; effective runtime model/effort metadata was unavailable. A
source-correspondence researcher independently located the
`Fam_delta` application gap. An independent compiler-referee first found the
claim's declaration quantifier too broad, then accepted this repaired complete
declaration-graph premise and the conditional rank construction on delta
review. The reviewer confirmed that actual `Fam_delta[mu_delta]`,
`Gamma_0(P)`, static-license evidence and complete catalogue maps remain absent
from source correspondence. No compiler files, tests, builds, Oracle runs, or
measurements changed this theorem's scope.
