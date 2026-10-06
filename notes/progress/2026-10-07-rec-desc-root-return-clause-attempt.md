# Root and inert Return clauses: bounded REC-DESC attempt

Date: 2026-10-07
Baseline: `1870b1330160e83b71756f60300900f3e2ff4545`
Branch assigned: `research/simple-sub-intrusion`
Status: unreviewed conditional derivation and bounded authority characterization
Gates: DESC_CLAUSES / REC-DESC; neither gate closed
Implementation and semantic authority: none added
Exclusive lease: this file only

## 1. Objective and outcome

Determine what can already be derived for an ordinary descriptor root, the
zero-interaction case, and `Return` of the actual latent recursive handle.
The method is source-rule inversion followed by a case-specific quantifier
derivation. This does not repeat the general finite-observation translation
schema or the earlier effectful/quiet provider discriminator.

Two useful conclusions follow. First, the reviewed FH base case proves `W`
and has **no interaction check**. It does not automatically check a newly
attached zero-step descriptor condition. A root condition proved separately
in `S` instead makes its failure case impossible under `S`; that is not a
new admitted failure history. Second, at an actually reached inert Return,
failure of a condition fixed by the old tuple contradicts every compatible
event-local extension if the full local judgment independently reads that
condition. The source rules fix the returned handle needed for this argument;
they do not supply the independent descriptor/readout rule.

No actual failed `DescMem` instance or Authority-consistent countermodel is
constructed. The strongest proved statement below is conditional on an
independent immediate-condition/readout instance, not complete reflection.

## 2. Baseline and authority

All research reads use `git show 1870b1330:<path>`, not unfinished working-tree
edits. Governing sources and exact scopes are:

- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.2, 3.1–3.7, 10: independent `DescMem`, separate admission, conditional
  constructor typing, and Option 2's unselected exhaustive production rules.
- [Source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
  §§2–4: same original tuple, inert source constructors, reference root rule,
  whole-observation projection and query-independent future use.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§4, 9: conditional core simulation, latent results, actual entry and
  current-state invocation/suffix laws.
- [Ordinary computation package](../design/2026-10-02-ordinary-computation-semantics-package.md)
  §§2–5: state-threaded Return/Bind, inert closure/delay data, current
  configurations and active authority. This remains a candidate package;
  it does not become exhaustive descriptor authority through citation.
- Approved Function-denotation answer `production-function-denotation-answer/d1`,
  decisions 1–5, and bound-membership answer
  `production-function-bound-membership-answer/d1`, decisions 1–4. Their
  committed receipts record consumption. Option A selects independently
  constrained complete typed observations; Option 2 permits licensed extras
  without source-constructor witnesses. Neither selects concrete clauses.
- [Obligation DAG](../theory/successor-proof-obligations.md): DESC_CLAUSES,
  ADMISSION_CLAUSES, SEM_JOINT, REC-DESC and FH; and the REC-DESC proof cut in
  `tasks/current.md` (lines 158–172 at the baseline).
- Reviewed [reflection localization](2026-10-07-rec-desc-finite-reflection-localization.md)
  and [finite history bridge](2026-10-07-rec-desc-observation-finite-bridge.md).
  [Recursive synthesis](2026-10-07-successor-recursive-synthesis.md) §4 is
  needed for FH's exact base and local premises. The already reviewed
  [provider derivation](2026-10-06-descmem-provider-derivation.md) is prior
  evidence, not a new result here.

Rules read in full: `rules/research-lab.md`, `rules/design-authority.md`,
`rules/git-concurrency.md`, and `rules/question-board.md`. No pending answer
or alternative language meaning is used. No Oracle is used as evidence or
authority.

## 3. Fixed judgments and witness positions

Fix the actual provider knot, the ordinary descriptor `R`, original binder
tree, and original scoped `(xi,w)`, with `xi=(nu,K,D)`. In particular the
preexisting handles `v_f,v_g`, descriptor incidences and captured-root
identities are fixed. Let `Ext(h;xi,w)` be the authorized compatible
event-local extensions for one admitted decorated history `h`; each agrees
with all old coordinates and any shared event coordinates. This is notation
for the supplied extension domain, not its definition.

For clarity, consider the existential local-check form

```text
Local(h;xi,w) = exists e in Ext(h;xi,w). Check(h,e;xi,w).
```

Nothing here selects that form as the complete production judgment. If an
active rule has additional universal witnesses, those binders remain at
their original positions. For this displayed form, a reflected failure must
be `forall e in Ext(h;xi,w). not Check(h,e;xi,w)`. FH's actual pointwise
premises remain stronger than independently picking a fresh old `w` per
transition; they are not weakened to that practice.

The outer reflection target fixes the old coordinates before selecting its
history:

```text
for each original scoped (xi,w):
  S(xi,w) and not DescMem(R,v;xi,w)
    => exists h. Adm(h;xi,w) and not Local(h;xi,w).
```

This does not move an existential across a rigid operation binder. The
analysis is pointwise at each original fiber, before any original-scope
hiding and before the single final `Pi_xi`. Concrete handle identity is used
internally to select the retained provider; it is not added to public typed
observations erased by `Pi_xi`.

## 4. Root and zero-interaction cases

### 4.1 Independently discharged static root condition

Take an actually specified root conjunct `B(R,v;xi,w)` whose truth is fixed
by old coordinates. If the independently proved static judgment has the
readout `S(xi,w) => B(R,v;xi,w)`, then

```text
S(xi,w) and not B(R,v;xi,w)
```

is inconsistent. Thus a failure of this conjunct cannot be the residual
descriptor failure under `S`. No inhabited admission domain, zero-step
certificate, or new FH premise is needed for this exclusion. This is a
conditional logical derivation with a named static readout premise, not a
proof that `S` supplies all ordinary root conjuncts.

### 4.2 Root condition left to an explicit zero-step check

The exact FH proof in recursive synthesis §4 says that at size zero the
initial certificate supplies `W` and **there is no interaction check**.
The admitted initial certificate and its compatible extension therefore do
not by themselves give `B` or `Check_0`.

There are two precise sufficient interfaces to investigate, without choosing
either as a new rule here:

1. Independently derive `W => B` at initialization, and use case 4.1 with
   that independently established root fact.
2. Supply a legitimate zero-step certificate `h_0` and independently prove
   `Check_0(h_0,e) => B` for every authorized extension, **and** establish
   that the invariant's base validates this `Check_0` judgment.

Under the second interface, `not B` implies `not Local_0(h_0)` for every
extension because `B` is fixed. It is a valid zero-interaction witness only
when `Adm(h_0)` is independently established. FH presently supplies neither
the new readout nor its base validation. Writing `Check_0 = W and B` and
then citing the old FH theorem would silently strengthen its base premise.

Admission is also not automatic for a bad root: an independently interpreted
initial-domain clause may require a root condition. If that makes `h_0`
inadmissible, it cannot be used as a reflection witness. Static discharge is
then the applicable route. Empty admission alone never proves the root.

## 5. Actual inert Return: the exact case derivation

### 5.1 Facts supplied by the retained source rules

Use the already derived recursive body occurrence `result(name g)` in
`f`, with its original lexical lookup `eta_f(g)=v_g`. Assume a separately
certified finite admitted prefix reaches its result binding with current
configuration `C_ret`. The constructor inventory and reference membership
clauses then give

```text
name g reads the original root v_g;
result(name g) gives Return(v_g,C_ret);
Return(v_g,C_ret) >>= Suffix = Suffix(v_g,C_ret).
```

This source instance fixes the result handle and passes that same current
configuration to the suffix. It invokes neither `v_g` nor its latent
descendants. A surrounding invocation return may subsequently pop its
current frame; that is a suffix operation, not a reason to replace `C_ret`
with an old state at the Return incidence.

If argument Force earlier suspended, its original resumption runs this
pending suffix using the current resumed state. The Return rule does not
replay the earlier receipt, choose a new operation witness, revive exited
authority or create a capture grant. A later new call to `v_g` performs its
own actual entry in the later compatible context. A delay's later Force
instead opens its designated computation port; inert Return supplies
neither operation.

These are conditional source/reference facts under the decorated-source
premises. They are not a production `DescMem` introduction rule. In
particular source contracts §3.5 still **assumes** the local descriptor
typing lemma for this emitted observation.

### 5.2 Immediate old-coordinate failure

Let `h_ret` be the independently admitted finite prefix through this Return.
For an immediate ordinary condition `B_ret(R_ret,v_g,C_ret;xi,w)`, suppose:

- **Admission:** this very decorated prefix, including its actual inlet and
  handle, belongs to `Adm`; admission does not require the `DescMem` result
  under proof or pending comparison success.
- **Invariance:** every compatible event-local extension evaluates
  `B_ret` identically. In particular its inspected coordinates are already
  fixed at the Return incidence. A permission depending on new event/live
  coordinates does not satisfy this premise merely because an old endpoint
  spelling is fixed.
- **Local readout:** independently interpreted complete local checking at
  this Return satisfies
  `Check(h_ret,e;xi,w) => B_ret(R_ret,v_g,C_ret;xi,w)` for every authorized
  `e`.
- **Actual failure:** `not B_ret(R_ret,v_g,C_ret;xi,w)`.

Choose an arbitrary authorized `e`. Local readout would imply `B_ret` if
`Check` held. Invariance identifies it with the fixed false condition.
Therefore `not Check(h_ret,e)`. Since `e` was arbitrary,

```text
forall e in Ext(h_ret;xi,w). not Check(h_ret,e;xi,w)
therefore not Local(h_ret;xi,w).
```

Together with Admission this is the required finite failure of the **whole**
existential local judgment at the same old assignment. An empty `Ext` also
falsifies that existential, but cannot establish Admission; the proof does
not manufacture an inlet from that emptiness. The smallest conditional
witness suffix is one `Return(v_g,C_ret)` after its certified prefix, with
zero future eliminations of `v_g`. No globally minimal prefix length is
claimed; the original Value-entry Force and any earlier requests remain in
the actual prefix.

The proof needs no existential descriptor witness reselected per segment.
Its named readout must hold for every extension; one failed typing proof or
one incompatible extension is insufficient. This gives a concrete
conditional reflection case for immediate conditions, not an instance of
complete `not DescMem` reflection until the descriptor inversion identifies
such a failed conjunct and the independent readout is proved.

### 5.3 Immediate checks pass, but the latent descriptor fails

Neither the inert Return equation nor the reference root rule eliminates
this case. The reference root derives `P_ref` from a source derivation;
source contracts §2.2 separately conjoins `DescMem` before the production
projection. Removing that conjunct or using the source derivation to define
it would change the selected basis.

The future-use inventory identifies necessary operands: the actually
returned `v_g`, its original typed port, the retained joint history and the
current compatible context. It does not independently prove that a failed
latent `DescMem` has a finite admitted call/force exposing a failed complete
local judgment. The missing production clauses are exactly:

1. returned-Function/delay descriptor inversion identifying all latent
   obligations after immediate conditions pass, with their original binders;
2. independent admission coverage for a failing obligation at this actual
   handle, without assuming the recursive member validity being proved;
3. full-local-check readout/reflection, negating all allowed existential
   extensions, with any infinite-observation finite-prefix premise proved;
4. their common SEM_JOINT interpretation with descriptor, carrier and world
   predicates, rather than a per-case chosen interpretation.

Option 2 additionally prevents making the source constructor inventory
exhaustive for production. This attempt supplies no rules for its licensed
extras. It establishes no equivalence between `DescMem` and finite-history
validity, and does not assume a greatest fixed point.

## 6. Coverage, falsifiers and evidence independence

The documentary coverage is exactly: one discharged static-root case; one
conditional zero-interaction readout; one actual `result(name g)` Return
instance; its conditional immediate-check failure; and the residual latent
failure case. The sibling `g` returning `v_f` follows by exchanging the fixed
source occurrences, not by choosing new witnesses. No Request, Bind, Call,
carrier, world or abstraction membership clause is characterized exhaustively.

The strongest falsifier of the immediate-case theorem's intended application
would be an authorized compatible `e_good` for this same `h_ret,(xi,w)` with
`Check(h_ret,e_good)` while the claimed fixed `B_ret` is false. It disproves
the readout or invariance premise, not FH. Lack of an independent inlet or
future-use certificate instead blocks Admission. A latent descriptor failure
that passes every finite admitted local check would defeat complete reflection
unless independently excluded; no such semantic instance is asserted here.

Named shortcut mutations, evaluated by logical inspection only: attaching
`B` to the old zero-step FH conclusion without a new premise; replacing
`v_g` by an endpoint-compatible provider; using one bad extension to refute
an existential; using `DescMem(v_g)` to admit its future failure witness;
and using §3.7's guard `G` to prove the source typing `R subset G` it assumes.
No mutation was executed and no pass count is reported.

There is no executable checker or external oracle. The documentary
derivation shares the retained source equations and supplied primitive,
typed-path, owner/world and independent-admission premises with earlier
research. This is not independent validation of those source rules. Reviewed
inputs do not make this producer's new note independently reviewed.

No seeds or enumerated ranges apply. No tests, builds, formatting, compiler
edits, child processes for experiments, or Git mutations were authorized or
performed. Commands were bounded sequential `git show` section reads,
`rg`/`sed` locators, `git ls-tree` dependency inventory and an exact-path
`git diff --name-only 1870b1330 -- <dependencies>`; that comparison was empty
for the listed semantic/proof dependencies. The task record was read only
from the pin because it is a primary-owned moving coordination path. Peak
RSS/CPU and total reasoning wall time were not instrumented; each reported
read command completed in about 0.1 seconds or less. No compute search ran.

Unverified: actual root/Return readout lemmas; exhaustive DESC_CLAUSES and
ADMISSION_CLAUSES; SEM_JOINT; complete REC-DESC; actual initial-world
inhabitance; separate `M_E`, CarrierMem, WorldMem and simultaneous CompleteMem;
FH's local premise suppliers; arbitrary raw-source adequacy, soundness,
principality and production conformance. No gate is promoted or weakened.

Recommended next action: obtain one independently specified immediate
Return condition and prove its full-local readout on the retained
`result(name g)` incidence, while establishing roots independently of FH's
zero-interaction base. Another toy execution of Return would leave this
same missing premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-rec-desc-root-return-clause-attempt.md`.
- Baseline SHA: `1870b1330160e83b71756f60300900f3e2ff4545`.
- Claim/review status: conditional immediate-failure derivation and bounded
  source-authority characterization; unreviewed, research-only; no theorem
  closure, semantic adoption or implementation authority. Freeze on handoff;
  producer writes stop before independent review.
- Checks already run: pinned governing/source/FH reads; exact Return/Name
  inversion and arbitrary-extension contradiction above; narrow dependency
  difference check and Git blob inventory. No executable/test/build check.
- Dependency hashes changed: none among the narrow semantic/proof dependency
  comparison at write time. Frozen baseline Git blob identities follow:

  | Dependency | Baseline Git blob |
  | --- | --- |
  | Source contracts | `1c2b1a579a9cc7a51d98a4fda755838decb96d07` |
  | Source-indexed realization | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
  | Typed core | `d0948191bbc2d1eb10a7e6e360dc8852a185db1d` |
  | Ordinary computation package | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
  | Reflection localization | `b6f1321d29cb369ee3fdacf0ab017132aaf3e185` |
  | Finite history bridge | `0668f38b125bf1e18f216e349198ce3109c22e9d` |
  | Recursive synthesis / FH | `2fddbc4e7df95e45830f6bb61d42805cd08cf488` |
  | Prior provider derivation | `effb4f1dffedc8ca934988e9c06f4c9e52ad169a` |
  | Obligation DAG | `e6d9ed6eff36ca42215f8abaf29cf088bdd02af9` |
  | Option A approved answer | `a3aa2e5c1b37547e2c6272b97849a0a5b5fcb365` |
  | Option 2 approved answer | `fb4a169a2d748422490cc74c026338587290e90c` |
  | Pinned `tasks/current.md` read | `01a5ea9b16ead58444d08ad44c4ce9561f821367` |

- Proposed one-line research-checkpoint commit message:
  `research: isolate root and inert Return descriptor readouts`.
- Shared-record deltas intentionally left for primary/curator: add this
  locator if accepted; record that FH's size-zero conclusion is `W`, with no
  newly supplied root check, and that old-coordinate Return conditions admit
  an all-compatible-extension failure proof only under an independent
  immediate-condition/readout/admission instance. Keep DESC_CLAUSES,
  ADMISSION_CLAUSES, SEM_JOINT and REC-DESC open. No shared task, index,
  theory, authority or question-board file was edited.
