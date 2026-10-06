# Formal-profile formation: source rule shape and exact conditional cut

Date: 2026-10-06
Status: Compiler-referee and spec-auditor reviewed conditional research; no findings within scope; no semantic or implementation authority
Baseline: `f19fb4f473344e8f4478ae145d0915e04d250b09`
Lease: this file only
Method: manual constructive factorization and finite proof-tree inversion; no executable model

## 1. Objective and result

Express the general source formal-profile formation judgment that could prove
completeness of original applicable positions, then specialize it to
`my apply f = { my step x = f x; step }`. The result is an interface with a
proved positive source seed and explicit unknown introduction rules. It does
not determine the exact original singleton from current authority.

The useful reduction is to two local negative obligations: what the implicit
formal contract may introduce before grouping its uses, and what an original
Call may introduce beyond its immediate complete-invocation effect position.
Typed transport cannot answer either. An exhaustive introduction grammar could
answer them; supplying an inventory already equal to the wanted answer cannot.

## 2. Governing inputs and retained decisions

The exact approved direction is [function-call-view q1/a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md),
validated by its [integration receipt](../../questions/2026-10-05-function-call-view-formation/receipt.md).
[Inferred call views §§2–5](../design/2026-10-05-inferred-function-call-views.md#2-source-formation-direction)
requires a shared contract from relevant declarations, definitions, uses and
recursive components; source position/scope preservation; one original joint
`xi=(nu,K,D)`; and admission independent of `Q`. It expressly leaves exact
formation and protection judgments open.

Unannotated `f` has provisional fully protected Handler treatment; ordinary
value evidence refines the inferred formal/use relationship on the same root.
This is not a generic Value-entry-implies-non-Handler rule and does not change
an actual supplied callable's role. No annotation means full protection at
applicable positions and no annotation removal grant. The specified `[io]`
annotation permits removal of its governed contribution; its source mapping
and realization remain separate open rules. Callback-literal B is retained.

[Source contracts §§2–3/10](../design/2026-10-05-source-contracts-and-common-allowance.md#2-an-independently-interpreted-constrained-presentation)
provides conditional relation/emission and generalization contracts over
decorated inputs. It does not derive their original profiles.
[Typed-boundary §6](../design/2026-10-02-typed-boundary-realization-draft.md#6-common-typed-view-transport)
receives source profiles and proves tagged transport, no authority creation
and depth preservation under supplied typed correspondences.
[Call construction §§3–4/7](2026-10-06-source-call-generation-construction.md#3-exact-input-roots-and-whole-argument-distinction)
already generates the exact source's positive initial position.
[P/A review §4](2026-10-06-source-generation-pa-review.md#4-smallest-remaining-source-introduction-clause)
records the missing original converse. These research results are dependencies,
not new language authority.

The [nested addendum §2](../design/2026-10-06-nested-block-function-source-realization-addendum.md#2-selected-source-meaning)
fixes the exact source to the following tree, retaining the same captured `f`:

```text
lambda(f,
  bind(step,
    result(lambda(x, call(result(name f), result(name x)))),
    result(name step)))
```

The final `step` returns a function without invoking it. This interpretation
does not assert current compiler acceptance.

## 3. Formation interface before choosing missing rules

Fix a resolved source component `C`, its original scope tree `sigma`, and one
symbolic joint fiber `xi`. The input includes resolved declaration, definition,
use, annotation and recursive-component identities and the independently
interpreted declaration/descriptor basis. It does **not** include an original
applicability inventory, a solved Function shape, or success of `Q`.

A minimal interface shape is:

```text
Resolve(C; sigma, Decl, Def, Use, Ann, Rec)
IndependentBasis(B; original declarations and scopes)
---------------------------------------------------------------- Form-profile [candidate interface]
C; B; sigma; xi |- d : R =>
  (F, beta, E_intro, E_policy, E_flow, E_role, E_joint)
```

The outputs are a source constrained presentation and dependent schemas, not
a new runtime object. `E_intro` presents source introduction witnesses;
`E_policy` relates their original contributions to protection/permission;
`E_flow` keeps matching typed paths and source provenance; `E_role` retains the
same inferred root through provisional/refined states; `E_joint` retains all
constraints in the one original binder environment. Interpretation at `xi`
yields generated positions and policy. Effectively finite presentation,
existence, uniqueness and principality are not asserted by writing this rule.

One may write a *generated* witness as

```text
Intro(C,n,d,R,p,kappa;xi)
```

where `n` is a resolved source occurrence and `kappa` supplies its independent
source constructor, contribution and typed-origin certificate. This name does
not define original applicability: an eventual constructor table must supply
the actual rules producing these witnesses. In particular, it cannot have a
rule whose premise is simply `Applicable_original(C,d,R,p;xi)`.

The known exact-instance rule is:

```text
Call(c,u_f,u_x); resolve(u_f)=d_f; ordinary Value evidence at u_x
original shared R_f,F_c,sigma; NoAnnotation(d_f)
---------------------------------------------------------------- Intro-Call-0 [existing construction]
beta=(d_f,R_f); p0=(beta,call.effect)
Intro(C,c,d_f,R_f,p0,ElimOrigin(c,u_f,d_f,R_f,p0,p_out(c));xi)
Policy(p0)=FullProtection; AnnotationRemovalGrant(p0)=None
```

`p_out(c)` is the complete invocation position, including entry/body/consumer,
not a bare body row or outward-support test. This introduction is static and
can be emitted before any satisfying Function description exists. It is not
an executed receipt, observation, activation or grant.

The general interface has the following **unknown rule leaves**:

| Leaf | Required source input/output; not a supplied inventory |
| --- | --- |
| `I-formal` | Resolved formal declaration/definition component to its implicit original contract introductions; determine whether it has origins independent of use-generated demands. |
| `I-call-rest` | Resolved Call and shared contract to any independently justified additional original positions/contributions; classify callee-result origins without scanning latent type shape. |
| `I-annotation` | Original annotation occurrence and boundary evidence to the particular governed contribution/path; distinguish permission from realization. |
| `I-declaration` | An independently interpreted primitive/import declaration to its scoped original profile origins, preserving joint parameters. |
| `I-component` | Multi-use/recursive source relationships to one shared inferred interface and valid role refinement; no independent per-port choices. |
| `I-exhaust` | Local inversion identifying every original first introduction with one of the actual constructor clauses, including independently introduced callee-result profiles. |

This table is a list of obligations, not an adopted exhaustive language rule
set. The producer has supplied only `Intro-Call-0` for the exact instance.
Treating the unknown leaves as arbitrary independent relations would yield an
envelope of candidate decorations, not the original source relation.

## 4. Conditional completeness theorem and its premise

Here is a conditional theorem that an eventual constructor table could support.
It assumes a separately defined original source derivation relation rather
than defining that relation by this candidate checker.

Hypotheses:

1. **Local introduction soundness.** Every emitted introduction clause has a
   source-typing proof for the same original occurrence/contribution at `xi`.
2. **Local introduction inversion (`I-exhaust`).** Every first introduction in
   an independently derived original source profile inverts to a specified
   source constructor clause with the same original scope and witness. This
   is an unproved source theorem; currently no complete table is supplied.
3. **Transport matching.** Remaining steps are the supplied typed-boundary §6
   indexed relational images. They preserve origin tags and the common ledger;
   new result-profile sources must themselves pass hypothesis 2.
4. **Whole scope transport.** Relevant generalization/use steps have the
   source-contract §3.4 whole-coordinate certificates. No per-segment hiding,
   freshening or independently selected `xi` is permitted.

**Conclusion.** At a fixed original fiber and scope, generated and original
applicable-position witnesses correspond, with their contribution origins.

**Derivation.** Induct on each finite original derivation. At its first
introduction apply hypothesis 2 and emit the matching source witness. At a
transport step use the same indexed path witness; at a certified scheme step
use the same whole scope action. This constructs a generated witness.
Conversely induct on a generated witness: hypothesis 1 supplies the original
introduction; hypotheses 3–4 reconstruct its transport and scheme steps.
Taking positions after this witness correspondence proves coverage in both
directions. Unfolding finite recursive derivations uses the same induction;
infinite/coinductive original introductions are outside this argument.

This proves a conditional composition result. It does **not** prove hypothesis
2 by checking the candidate's own transition rules. The source-contract
C-realization induction already has the same kind of decorated-input boundary;
using it to supply `I-exhaust` would be circular.

## 5. Exact candidate: what reaches singleton and what does not

The approved resolved tree has one use of `f` as the callee at `c=f x`, no
written annotation for `f`, and the original root `R_f`. The known constructor
therefore gives:

```text
Generated_Call(C,beta;xi)={p0}
p0 is an original applicable position, by the positive Call construction.
```

The first equality concerns the Call constructor's output, not complete
`Slots_original(beta;xi)`. For this exact source, full singleton would follow
conditionally from all three additional local premises:

- **`N-formal`:** the implicit outer formal contract only groups introduction
  witnesses justified by this component's resolved declaration/use rules; it
  contributes no extra position at the formal binder without such an origin.
- **`N-call`:** inversion of this exact original unannotated Call yields its
  immediate `p0` introduction; any independent callee-result introduction needs
  an additional source-contract witness, and this source has none.
- **`N-other`:** the remaining Name/Result/Bind/capture/Lambda steps preserve
  this formal's original introductions. Any separate local closure/public
  contract or external inherited packet retains its own source tag; it cannot
  become a new original `beta` introduction merely by transport or type/root
  equality.

Then take any original position witness for this `beta`. Follow its provenance
back through the transport steps. `N-other` prevents a new formal origin there;
`N-formal` places the origin in an independently justified component witness;
`N-call` inverts that witness to the sole `c`, hence `p=p0`. Together with the
positive rule, this yields the exact singleton. These negative premises are
**not established** by the approved formation direction. §6 supports the
transport part after profiles/maps are supplied, not complete raw-source
inversion of the formal or Call introductions.

The single outer boundary identity does not prove `N-formal` or `N-call`: its
profile could have several applicable positions if independently introduced.
Conversely, writing `result.latent.effect` does not produce an independent
source origin and gives no authority-consistent alternative completion.
No alternative complete source rule, accepted-source counterexample or
observable separation is claimed here. The exact absence of annotations fixes
policy at applicable positions; it does not by itself prove the inventory.

Even the conditional singleton does not complete contribution interpretation,
same-root seed/refined-view normalization or preservation of every original
solution. Those are separate `E_policy/E_role/E_joint` obligations. It also
does not erase inherited actual-provider/result packets. Profile expiry and
current receiver activity remain different objects.

## 6. Evidence boundary, coverage and failure conditions

This is a manual derivation over the exact finite resolved tree and the stated
rule interfaces. It uses no Oracle execution, frozen Oracle semantics,
transition checker, random seeds, enumeration range, mutation campaign,
compiler build or test. Oracle independence here means that no legacy
transition rule supplies a current-language premise; it does not mean an
independent oracle has validated the proposal. Shared assumptions are the
approved source meaning, the existing decorated relation basis and typed
transport contracts.

Failure of `I-exhaust`, an independently justified extra formal/Call-result
origin, or a non-preserving raw-source constructor invalidates singleton.
Incorrect policy attribution or a role normalization that restricts original
solutions invalidates full profile formation even if singleton holds.
Admission that filters by pending `Q`, independently hidden joint witnesses,
or inherited packets relabeled as newly introduced formal origins invalidates
the intended downstream use. Infinite introduction rules would invalidate the
finite-derivation induction without an additional argument.

Omitted: general multi-use/recursive formation, annotation mapping, actual
receiver activation, source-valid import/world interpretation, all-context
admission, principality, effective finite solver construction, production
Option A/2 alternatives and conformance. No `FVIEW -> SRC` edge is promoted.
No attempt to enlarge a toy probe addresses these missing source leaves.

Independent review found no findings within this conditional artifact scope.
The compiler-referee specifically requires hypothesis 1 to be genuine source-
introduction soundness, not merely descriptor well-typedness; hypothesis 2
(`I-exhaust`) remains unproved. The spec auditor confirmed that no exhaustive
rule, annotation prerequisite, Q-derived position, role rewrite or production
authority was introduced. Neither review certifies source completeness or the
full inference replacement.

Recommended next action: supply a proposed **local original first-introduction
table** for the implicit formal binder and Call-result cases, with independent
source justification, then review its negative inversion on this exact tree.
If that table selects a new meaning, the primary must route that concrete
clause through design review and approval before treating it as a rule.

## 7. Dependency snapshot and checks

All direct dependencies below matched their pinned baseline bytes when read.
SHA-256 values:

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-source-generation-pa-review.md` | `9f51c91fbaa9976022fed10d4b3fd9ab7eb1ae2027192bb9d5823f5a2d0fef2a` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |

Checks: read-only `git rev-parse HEAD`; targeted `rg`/`sed`/`cat`; SHA-256 and
byte equality against `git show <baseline>:<path>`; final leased-path whitespace,
relative-link existence and dependency-byte recheck. No tests/builds were
authorized or run. One lightweight shell/Python process at a time; no search
jobs or generated side outputs. CPU/RAM/elapsed time were not instrumented.

## Commit packet

- Exact leased paths: `notes/progress/2026-10-06-formal-profile-formation-rule-attempt.md`.
- Baseline SHA: `f19fb4f473344e8f4478ae145d0915e04d250b09`.
- Changed dependency hashes: none; snapshot above must be revalidated by the primary before integration.
- Claim/review status: compiler-referee and spec-auditor reviewed conditional derivation, no findings within scope; original-profile completeness, gate closure and implementation authority remain absent.
- Checks already run: narrow reads, baseline equality/hash checks, leased-note whitespace/link checks and final dependency recheck; no tests/builds/Oracle/search.
- Proposed checkpoint message: `research: factor formal-profile formation into explicit introduction obligations`.
- Shared-record deltas left to primary/curator: link this conditional attempt if useful; record the local `I-formal/I-call-rest/I-exhaust` cut without promoting P, admission, principality, source adequacy or production conformance.
