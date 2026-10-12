# f y: bounded native domain-map attempt

Date: 2026-10-12
Status: frozen, unreviewed research; conditional partial derivation only
Baseline supplied by primary: `28f0f7fd1ae667997d1ecdf1b4c482909c7722c8`
Branch supplied by primary: `research/simple-sub-intrusion`
Producer: leaf `/root/fy_domain_map_astra`; no delegation
Lease: this file only; static proof budget at most 25 minutes
Requested runtime: `gpt-6-astra` / `low`; observed model/effort: unknown

## 1. Frozen claim and dependencies

Use the exact 116-byte source and original binder graph of
[two-use source bridge](2026-10-12-two-use-exact-source-bridge.md) §§1,3–5:

```yulang
my answer = {
  my f x = {
    my g y = { my drop z = y; drop (f y) };
    my first: int = g 0;
    g ()
  };
  f
}
```

Application c is Apply 13, callee Name 14 referring to the active recursive
f, argument Name 15 referring to g's y, at E(7), level 3. f's initializer
is expression 2 at level 2. Keep Group 12 and the enclosing drop call,
all unused binders, both later g uses, and every event-indexed g/drop allocation.
The source bridge establishes reachability of this private candidate route,
not original semantic admission.

Freeze the original source and scopes, `xi=(nu,K,D)`, initialization event,
whole scoped assignment and strategy, original A_f, independently formed
complete demand F_c, actual entry I_x and every retained
`Act(v_f,U_f,r_f)`. At each actual compatible event e the required finite
original local check has conclusions

```text
D: every d in D_F_c(e) belongs, as the same whole challenge, to D_A_f(e).
P: every o in P_A_f[S](d) belongs, as the same decorated tuple, to P_F_c[S](d).
```

D is independent of S. Its required entry consequence is
`Acc(I_x;d.wholeCarrier,C_e,w_e,eta0,xi)`, plus the actual receipt/path/context
preconditions and original A_f challenge formation. P retains all complete,
pending, administrative and zero-step observations, every compatible future
and finite history. Neither domain is restricted to Delay(Name y), returning
carriers, source-generated alternatives or one convenient provider.

A_x remains before f's challenge. A_y remains before g's challenge and below
its actual enclosing f-body dependencies; A_z remains below drop's original
g-body dependencies. EventProof/ViewLogic witnesses stay at their existing
licensed scopes. Shared worlds, evidence, residual lineage and aliases are
never independently reselected. No f membership, H_f, D, local Call admission,
solver success, complete replay or actual intrusion equality is a premise.

The selected [Source Generalize construction](2026-10-08-source-generalize-definition-and-proof.md)
§2 L3/L4 and §§3.1–3.3 govern the finite rule tree. The
[semantic input realization](2026-10-08-call-semantic-input-realization.md)
§§2–3,4.2–4.3 governs complete challenge, ActualAdm, Return and carrier meaning.
[Call input construction](2026-10-07-call-input-construction-proof.md)
§§3.2–3.4 owns Entry-Value, Lambda and Code-Call.
[Original Call formation](../design/2026-10-07-original-call-formation-definition.md)
§§2–4 constructs the invocation root of an already emitted complete scoped
demand; it does not identify a native four-port term with that demand.
[Top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 prohibit replacing native accumulation by eager checking or weakening
ordinary inference. The supplied [finite-check reduction](2026-10-12-application-c-finite-check-proof.md)
§§1–6, [native tree trace](2026-10-12-fy-constraint-to-check-tree-construction.md)
§§1–6 and [native source audit](2026-10-12-fy-native-constraint-check-source-audit.md)
§§1–5 are prior evidence, not missing semantic laws.

## 2. Native derivation: follow levels before interpreting carriers

Let X,Y be the original native parameter rows, O f's initializer, N its
callee facade, B the f-body value row, E_x the entry-effect row, Q_f the
Lambda invocation-effect row, E_y the Name-y effect and Q_c/R the Call
invocation-effect/result rows. These names are native operands, not A_x,
A_y, I_x or complete F_c.

The actual producers give

```text
L = Fn+(X-, E_x-, Q_f+, B+) <: O <: N
N <: U = Fn-(Y+, E_y+, Q_c-, R-).
```

The source Link is emitted while f remains monomorphic. Lambda adds
`E_x <: Q_f` and `E_body <: Q_f`. Apply adds its separate callee-prefix
and invocation-effect edges to its application effect. Those facts follow
from `candidate_source.rs` Name/Apply/Lambda arms, `shadow_apply.rs:1300–1404`
and `lib.rs:11233–11365`; the Lambda's native entry effect is not omitted
because x is unused.

Accumulation in `candidate_extrusion.rs:763–837` stores the actual bound and
replays opposite bounds with both input incidences. It does not need an
already typed recursive f. Negative extrusion of U toward O's older level
flips the argument ports. For a copied argument Y_u it retains
`Y <: Y_u`; for a copied entry-effect operand E_yu it retains
`E_y <: E_yu`. Positive extrusion of L, if present on the actual path,
flips its argument ports the other way and retains `X_l <: X` and
`E_xl <: E_x`. Uncopied endpoints use identity. See extrusion row creation
at `candidate_extrusion.rs:76–126` and Function traversal at 210–250.

When the corresponding transported Functions actually meet, Function dispatch
at `lib.rs:12490–12535` submits `Y_u <: X_l` and `E_yu <: E_xl`.
Therefore the native constraint calculus has these finite path compositions:

```text
Y   <: Y_u  <: X_l  <: X
E_y <: E_yu <: E_xl <: E_x.
```

This is a constructive native inequality derivation conditional on that actual
dispatch and its actual retained copy links. It neither asserts that an
unexecuted dispatch happened nor interprets native inequality as original
whole-carrier inclusion. No global semantic extrusion theorem for arbitrary
cyclic graphs is assumed: the displayed calculation composes only these
explicit argument-row links. The analogous result directions are covariant,
but they do not discharge original P.

The reference `Typer.scala:48–56,64–72,106–127,133–184` confirms the underlying
native operations: open monomorphic recursive root; Function constraint;
opposite-bound replay; polarity-indexed copies with one-sided links; freshening
above a level while retaining shared copies and their bounds. Generalization
does not turn the inequalities into equality or assign their original carrier
meaning. Nor may unused x be silently replaced by Top: X is the original
flexible scoped declaration, and the claim ranges over its lawful assignments.
Qualifying parent/copy intrusion can add only the actually justified equality;
assuming its preservation here would import another open parent gate.

## 3. Construct the carrier map by its original clauses

Take arbitrary `d in D_F_c(e)` before using any source membership. Challenge
inversion supplies its actual carrier t, checked carrier admission, independent
context and all shared indices. It supplies no admission by U_f.

Unfold the original carrier criterion from semantic input realization §4.3.
To turn this evidence into `Acc(I_x;t,e)` one must construct **both**:

1. inert formation at the original registered view/root, retaining license,
   references, scope, authority, incidence and shared dependencies;
2. every designated one-layer execution observation and admitted development
   at I_x, including all pending prefixes and dependent future interfaces.

Here is the direct attempted construction using the native paths of §2.
If their semantic interpretation supplies same-decorated-value inclusion
`ValueMem_A_y(a,r,e') -> ValueMem_A_x(a,r,e')`, then the original Return clause
of §4.2 gives a real local child:

```text
ReturnMem_A_y(Return(a,r,C,w))
  -> JointWF(C,w) and ValueMem_A_x(a,r,e') and the unchanged incidences
  -> ReturnMem_A_x(Return(a,r,C,w)).
```

This preserves the witness and live world and assumes no f membership. It is
conditional because native Y <: X has not independently been interpreted as
that full value inclusion; A_y can itself denote a latent callable. It is not
an atomic-ground shortcut for the original source.

For an original provider bound, a genuine `Allow(E_y) -> Allow(E_x)` implication
would permit the fixed-domain coverage step in
[source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§4 Lemma 1: retain the same provider, N_j, all challenges and non-coverage
predicates; compose the coverage implication. This is an actual available
semantic lemma. Its own boundary explicitly excludes monotonicity when the
admitted input domain changes. A native effect edge is not independently a
proof of the complete Allow interpretation, and this coverage calculation
cannot alter receipt authority, carrier license or continuation admission.

Attempting to pair these two children stops **before** a carrier admission
proof. The inert-formation conjunct concerns t's actual registered view/root;
Return inclusion and coverage weakening do not transport its full formation
certificate to I_x. Even with that transport, the execution conjunct requires
the same full pending/response/raw-handle/future equations, including every
independent alternative's nonpositive premises. Neither subcalculation proves
those equations. The original Name Delay lemma proves its one authentic
source carrier from its code/environment; using it on arbitrary t would
change the quantified domain.

The additional domain step has not disappeared: original A_f challenge
formation must preserve the actual receipt/path/context guards. The selected
Strict constructor (captured-closure construction §3.1) supplies such a domain
when its **original complete** I and IF operands are given. Its formation law
does not identify this original A_f or F_c with an arbitrary Strict interface
chosen from X/Y after the fact. Entry-Value specifies actual receive/Force/
rebind order but leaves its original designated entry view as an operand.
Thus it cannot fill the missing formation transport merely because both
entries have Value role.

This is a partial clause-by-clause construction, not a new carrier relation,
a toy model, or a claim that the genuine carrier transport is false.

## 4. Exact remaining premises and source owners

| Required premise | Source owner and current evidence |
| --- | --- |
| Full native Y/X and E_y/E_x interpretation at the original scoped interfaces | Native Parameter, Apply and Lambda retain operands and real bounds. Selected source rules introduce flexible complete endpoints and require genuine local checks; no inspected constructor proves this interpretation. |
| Same-carrier inert-formation transport into I_x | Original Entry-Value designated view and Call checked carrier-interface formation. Their authentic formation/license fields must justify transport without a new root or license. The native four ports do not supply the law. |
| Complete execution/future transport for that same carrier | Original carrier/computation constructors and each independent alternative. Return and fixed-domain coverage children above are only partial; pending/nonpositive/future children remain. |
| Original A_f challenge formation with actual guards | Original complete Lambda/entry/IF and Call context constructors. ActualAdm projection is available only after the carrier and guard evidence is supplied. |
| P at S | Original finite checking constructors, genuine equation pairing and nonpositive child proofs. Ordinary V* implication cannot act on unproved S membership. |

The implementation boundary corroborates, but does not prove impossibility of,
this gap. `candidate_call.rs:215–250` still requests OriginalGenCall0,
ArgumentReifyAndWholeCarrier and ReceiverDispatchAndCompleteResultFutureInterfaces.
`shadow_apply.rs` retains the native terms before propagation, rather than
constructing those semantic records. Native provenance/FunctionPort/backlinks
can authenticate construction incidence; retaining a new tag cannot prove
any of the five interpretations above.

No lawful source-qualified falsifier was obtained. Assigning an arbitrary
extra carrier or rejecting receipt merely while preserving native projected
rows would not suffice: it would also have to satisfy the original complete
source residual, scoped licenses and challenge constructors. That verification
is precisely unavailable, so no such assignment is presented as a falsifier.
The exact source is not rejected, and the parent theorem is not refuted.

## 5. Economy adjudication and next action

D/P remain required A/B. Lost native incidence is reconstruction debt D, but
this attempt reaches a semantic formation/execution cut even after granting
all genuine native incidence. Levels, bound replay and generalization cannot
supply a missing original complete-interface law by themselves. This bounded
Astra attempt supplies no closure and no claimed progress on the original
D/P conclusions; the useful partial calculation is the explicit separation
of Return transport, fixed-domain coverage weakening, carrier formation and
complete challenge guards.

One next action for the primary: adjudicate the original Entry/Call complete
interface construction at this exact formation cut, with a source-qualified
carrier transport rule and all of its independent premises, before dispatching
another D-tree attempt or proof-dependent implementation. An omitted source
constructor must be constructed; an actually undefined semantic choice must
follow existing design authority. This note selects neither interpretation
nor source restriction. Return to normal Sol work after this bounded result.

## 6. Checks, resources and commit packet

Performed bounded static rule/skill/source reads, direct substitutions and
manual clause derivations; dependency SHA-256 snapshots and leased-file
whitespace/fence/link checks. No Git command, compiler run, build, test,
executable probe, external communication, child agent or model change.
One reasoning lane and sequential lightweight read/hash processes; zero heavy
processes, measurement samples or search cases. CPU/RSS and exact elapsed
reasoning time were not instrumented. The 25-minute bound was not extended.

Actual worker identity is `/root/fy_domain_map_astra`. The packet requests
Astra/low and the inspected prover role has no model/effort pins. No effective
runtime metadata is exposed to this worker; actual model/effort remain unknown.
The role configuration and packet prose do not establish that an override ran.

Unverified: original D/P, source admission, full semantic extrusion and
qualifying intrusion preservation, actual complete replay, generalization,
L4, soundness, required principality, effect hygiene and production cutover.
Independent review remains primary-owned. Shared records were not edited.

Direct dependency snapshot (no leaf edits; primary owns baseline comparison):

```text
d2689d6e0ee7581926916454481be9b384b54e04c3e73c874b9bd43a0cc3902f notes/theory/2026-10-12-two-use-exact-source-bridge.md
2f84356158426711bf81f099ca99748fa320d2bbc52876a08a73fcdaabc25d2c notes/theory/2026-10-12-application-c-finite-check-proof.md
79a3106769caf353ec70a20ff4c8c4069cda8d285f900d01929b32bef239b13e notes/theory/2026-10-12-fy-constraint-to-check-tree-construction.md
7f58c7ea77b1d58f8a5a6e92bc9e09c9804d935b9996efe4de998a5fe4582038 notes/theory/2026-10-12-fy-native-constraint-check-source-audit.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240 notes/theory/2026-10-08-source-generalize-definition-and-proof.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a notes/theory/2026-10-08-call-semantic-input-realization.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6 notes/theory/2026-10-07-call-input-construction-proof.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94 crates/yu-solver/src/lib.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0 crates/yu-solver/src/candidate_extrusion.rs
79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35 crates/yu-solver/src/candidate_call.rs
cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411 crates/yu-solver/src/shadow_apply.rs
f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9 /home/momota1029/rust/simple-sub-reference/shared/src/main/scala/simplesub/Typer.scala
```

Commit packet:

- Exact leased path: `notes/theory/2026-10-12-fy-domain-map-astra-attempt.md`.
- Baseline SHA: `28f0f7fd1ae667997d1ecdf1b4c482909c7722c8`.
- Changed dependency hashes: none observed between snapshots; baseline equality
  remains primary-owned, not inferred from the supplied SHA.
- Claim/review: frozen unreviewed conditional partial derivation; no theorem
  promotion, lawful counterexample or independent certification.
- Checks already run: static source/semantic clause derivation, hashes and
  leased-note integrity only; no executable compiler verification.
- Proposed checkpoint message: `research: record bounded native carrier domain-map attempt`.
- Shared-record deltas for primary/curator: preserve D/P, L3/L4 and parent
  inference gates OPEN; record the unsuccessful bounded escalation and exact
  carrier formation/execution/guard cut. No automatic third equivalent packet.

Writes stop at handoff.
