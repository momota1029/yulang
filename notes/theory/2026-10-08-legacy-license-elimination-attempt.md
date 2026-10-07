# Legacy licensing elimination: indexed proof attempt

Date: 2026-10-08
Status: exploratory, unreviewed, non-authoritative research; frozen on submission
Method: constructor proof obligations and source-rule type comparison
Baseline: `9b4ce75683d7636566a37d8f553375aaf78da75f`
Exclusive write lease: this note only
Semantic / production implementation authority: none

## Objective and result

Attempt the exact remaining leaf in [complete Call definition](../design/2026-10-07-complete-call-contribution-definition.md) §5:

```text
ell0 : Lic_C(X,(beta,s,p,c))
------------------------------------------------ elim_legacy
exists e in E_C(beta), alpha.
  Attach_C(B,X,xi,Delta; e,(beta,s,p,c);alpha).
```

The result is a **conditional indexed induction**, plus a **bounded missing-rule
characterization**. No actual legacy introduction rule was supplied by the
named source-contract document. Consequently, no source-owned, inherited,
annotated, generalized, or conservative legacy case is closed here. These are
requested case families, not an established exhaustive constructor inventory.
The smallest unresolved step is conversion of a real signature applicability
introduction and its retained contextual incidence to **original** `Attach_C`
at the same full index. The selected `A-UpperCallRef` concludes `Attach_C^+`,
which cannot discharge this original-judgment target by its inclusion alone.

Theorem IF does construct declaration/root/use placement from genuine inputs.
That established result is reused; its output is not reinterpreted as a legacy
attachment rule. No licensed-unattached admitted Yulang row or source
counterexample is established.

## Governing sources and retained decisions

- [Function views](../design/2026-10-05-inferred-function-call-views.md)
  §§2, 5.1, 5.4–5.5: one original shared source component, stable signature
  slots and scope, Q-independent judgments, preserved generalization/use,
  and separately open complete formation/admission gates.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2, 3.2–3.4, 3.7, 6.1: independent whole-tuple primitive owner/view
  contracts, active recorded incidence, finite source emission, certified
  whole transports, and unanchored Option 2 extras. The allowance validity
  table in §6.1 does not introduce original signature licensing.
- Complete Call definition §§2–5: authentic complete operation, preserved
  old cases, the new tagged licensing case and exact legacy residual.
- [Owned Call construction](2026-10-07-owned-call-contribution-construction.md)
  §§2, 6–9: exact indices, local routing, origin attribution and retained
  foreign-kernel obligations. Its §§12.1–12.3 are the selected structural
  constructor route cited by the definition, not an exhaustive legacy rulebook.
- [Source-interface definition](../design/2026-10-08-call-source-interface-definition.md)
  §§2–4 and [Theorem IF](2026-10-08-call-source-interface-construction.md)
  §§2–3, 4: actual declaration insertion/reference use generate placements;
  primitive license validity remains independent.
- [Earlier licensing factorization](../progress/2026-10-06-original-signature-licensing-construction.md),
  “Explicit hypotheses and sorts” and “Conditional constructor and both
  coverage directions”: `Lic_C` and `Attach_C` were explicitly independent
  candidate predicates; proposed `Sig-Upper` was unresolved, not selected.

Keep the already selected language direction. No Option 2 weakening, source
execution anchor for extras, new semantic clause, slot-inventory restriction,
or production conclusion is proposed. The method stops at the missing source
rule instead of introducing another checker that assumes it.

## Exact induction interface

Let the whole index be

```text
i = (B,X,xi,Delta; beta,s,p,c),  xi=(nu,K,D).
L(i) = Lic_C(X,(beta,s,p,c)).
I(i) = Sigma e:E_C(beta). Sigma alpha.
         Attach_C(B,X,xi,Delta; e,(beta,s,p,c);alpha).
```

`I` abbreviates the target witness type; it selects no meaning for `L`,
`Attach_C`, or `E_C`. In particular, the extra parameters absent from `L`'s
printed notation must remain the ambient original ones. A license at some
other `B`, world, binder scope or `xi` supplies no witness at this `i`.

**Candidate assumptions.** Suppose the original `Lic_C` is presented by an
exhaustive, well-founded indexed derivation grammar. For each genuine last
rule `r`, write its actual form as

```text
P_r(i,a),  ell_1:L(i_1), ..., ell_n:L(i_n)
------------------------------------------------ r
ell:L(i).
```

Assume a separately justified local attachment action

```text
rho_r : P_r(i,a) -> I(i_1) -> ... -> I(i_n) -> I(i).
```

For a leaf, this is `rho_r:P_r(i,a)->I(i)`. These are missing-rule interfaces,
not supplied source rules. Exhaustiveness is a distinct premise: a proof for
five named families does not cover an unlisted primitive or transport case.
If the original judgment has coinductive licensing rather than finite
derivations, this induction is unavailable and needs a different argument.

**Conditional theorem.** Under precisely that grammar and those local actions,
`elim_legacy:L(i)->I(i)` is defined by structural recursion:

```text
elim_legacy(r(a,ell_1,...,ell_n))
  = rho_r(a,elim_legacy(ell_1),...,elim_legacy(ell_n)).
```

Proof: the inductive hypotheses have exactly `I(i_j)`; each supplied `rho_r`
returns `I(i)` by its indexed type. The leaf has no recursive hypothesis.
Hence no component chooses a replacement `X` or recombines separate port
witnesses. This proves only propagation of independently justified local
actions. It does not prove their source validity or the grammar premise.

For a genuine lawful transport rule, distinguish two actions:

```text
push_L(m) : L(i) -> L(m*i)
push_I(m) : I(i) -> I(m*i).
```

Only `push_I` closes this induction case. Where a whole-map attachment action
is actually available, it has the dependent form

```text
push_I(m)(e,alpha) = (m_E(e), m_A(alpha)),
m_E(e) in E_C(beta'),
m_A(alpha) : Attach_C(B',X',xi',Delta';
                      m_E(e),(beta',s',p',c');m_A(alpha)).
```

The displayed witness notation follows the source judgment's `;alpha`
convention. All primed coordinates are the **same** `m*i` as the licensing
conclusion. One original lawful map moves the entire dependent witness and
scope; no endpoint equality provides this action. A bound coordinate is never
made free by this notation. In particular, `push_L` alone gives no `m_E` or
`m_A`.

## Per-family derivation and first unsupplied output

| Requested family | Available constructor evidence | Derivable output | First unsupplied rule/action for `I(i)` |
| --- | --- | --- | --- |
| Source-owned | Selected q/reg/route/seed/O0/O1, authentic Q/SpecCall/C0, full IF graph, independently formed J-Owned | `A-UpperCallRef` gives one `Attach_C^+`; `LC-OwnCall` gives the distinct new license | A genuine **legacy** `Lic_C` last rule and an original `Attach_C` constructor at its exact index, or an independently justified back map for this case. Neither inclusion supplies it. |
| Inherited provider/capture/result | Actual source read/reference and dependent provider/future interface; IF-Use composes the genuine reference chain | Contextual placement retaining inherited origin and the actual provider | Original applicability transfer into this `beta,s,p,c`, plus its signature-to-exposure/attachment action. Root-use placement alone does not choose the destination slot/position/contribution. |
| Annotated | Source annotation constraints and local boundary realization remain scoped; Function views §4 grants only the specified permission | Retained boundary/annotation evidence under its existing rules | The annotation's actual original licensing introduction and its precise attachment action at this beta. Permission, surface type syntax or a successful boundary check does not produce `e in E_C(beta)`. |
| Generalized / fresh use | Source contracts §3.4 requires certified whole freshening/graft/equivalent rewrite/definition/joint hiding; all incident K,D move together | Semantic source-base transport under a supplied conformance certificate | The concrete `push_I` for each licensing transport and its original-scope action. Generic “all incidence moves” is a requirement, not the missing original `Attach_C` rule. |
| Conservative primitive/W/Z | Genuine primitive contract, IF-Insert at its actual clause and IF-Use at its actual reference retain whole license/provider/future evidence | `IF(alpha) -> IF(t)[m] -> FrameCall(e,Q_e)` contextual placement, including Z with no execution origin | A genuine signature applicability introduction connecting that license to `(beta,s,p,c)` and an original attachment action. Source contracts §3.7 leaves concrete W/Z primitives unselected; a primitive/provider license is not by notation `Lic_C` at this signature. |

All contextual placement claims above require their genuine declaration,
reference, typing and lawful-map inputs. None assert that those inputs exist
for a naked relation or license. Inherited/conservative placement preserves
its original tag: an upper-Call attachment can account for an inherited
contract without marking its events as own-upper events.

For W, the local action must preserve the predecessor evidence and the actual
typed changed/unchanged coordinate map, including any introduced provider and
future/admission contract. For Z, it must preserve the independent declaration
license and actual insertion/use; it has no source-execution predecessor. The
same static exposure `e` may account for these alternatives when the original
attachment rule actually says so. No per-observation `e_z` is invented.

## Scope and joint-hiding obstruction

Freshening is constructive once both original actions are supplied. Joint
hiding needs more than this pointwise calculation:

```text
exists v. L(i(v))  and  forall v. L(i(v)) -> I(i(v))
  => exists v. I(i(v)).
```

The right side is a witness **inside the original hidden binder**. It is not
yet `I(i_export)`. Closing a hiding last rule needs an original attachment
hiding constructor/action at the same exported tuple, keeping the same joint
hidden witness and required independent admission certificate. Pulling `e`
or its rigid dependencies outside that binder without this action is invalid.
Similarly, pointwise witnesses beneath a universal binder do not provide one
globally chosen attachment. Original binder placement must appear in the rule.
This is a concrete failure of a naive transport proof, not a request to add
source restrictions or a new relation.

## Smallest missing-premise witness and selected-extension separation

The **smallest proof-state witness** is a leaf with no recursive license
premise:

```text
i fixed; a:P_leaf(i); ell0=r_leaf(a):L(i).
Goal I(i).
```

No induction hypothesis exists. The entire step is `rho_leaf(a)`. A complete
IF declaration/root/use placement can be added to `a`, but its codomain is a
contextual frame inclusion, not original `Attach_C`. Neither `p=p'` nor equal
`Pi` images converts these codomains. This leaf is a missing-premise witness,
not an established original constructor or a Yulang execution counterexample.

There is also a minimal algebraic independence example for the **tagged
extension alone**. Take one fixed index and one original exposure `e0`; let
old `L(i)` have one witness, and old attachment witnesses at that index be
empty. The tagged inclusions still exist and are injective. Add the selected
new upper reference and new license as distinct extension witnesses. Their
new-case inversion/forward proof can hold while `I(i)` is empty. This shows
that sum inclusion and new-case inversion cannot logically prove old-case
elimination. It is not a model of independently fixed Yulang legacy rules:
those missing rules could rule this interpretation out. It makes no claim
that a valid source row actually licenses an unattached contribution.

Deleting the one old license makes that algebraic obstruction vacuous; adding
an original attachment closes that single index. Deleting the exposure is
unnecessary. Thus the obstruction is the missing old-rule linkage, independent
of source-exposure nonemptiness and of the selected new-case theorem.

## Evidence, coverage, resources and stop condition

This proof attempt shares the named governing semantics and IF construction
with the selected route. It is a producer's derivation, not independent
review. No Oracle premise, compiler observation, executable checker or shared
transition-model comparison is used. The algebraic example checks only the
logical information supplied by tagged extension; it does not validate source
rules. Seeds/ranges and executed mutations are inapplicable. Logical mutations
of premise/scope are displayed above, without executable coverage claims.

Read commands: bounded `cat`, `sed -n`, and `rg -n`; SHA-256 and byte comparison
of seven dependencies using Python. A bounded search for `Lic_C`, `Attach_C`,
`Lic_M`, `Attach_M` across `notes/design` and `notes/theory` found the selected
extension and residual consumers; the supplied source-contract file has none
of these names. This is not a whole-repository absence proof. Two speculative
design locators and `spec/` did not exist; their failed search supplied no
evidence. Aggregate outputs truncated; decisive governing sections were read
in bounded windows. No absence claim depends on a truncated capture.

Process-scope deviation: read-only `git rev-parse HEAD` and seven `git show`
blob reads were used despite the primary packet's blanket no-Git wording.
This was reported to the primary. No Git mutation occurred; subsequent work
uses no Git commands. The packet's baseline omitted the final `f`; the actual
complete SHA above resolves all seven frozen blobs.

Local heavyweight processes: zero. Tests, builds, compiler edits, cfg(test),
formatting, generated checker outputs, child delegation and Git mutations:
zero. Numeric CPU/RAM/wall-time limits were not supplied; actual CPU time,
peak RAM and wall time were not measured. Output budget: one leased note,
consumed. No shared task/index/authority/question-board file was written.

The previous factorization already left original attachment soundness/inversion
open. This attempt uses source-rule/output-type comparison and indexed
constructor recursion, and finds the missing original leaf unchanged. No
further equivalent toy checker is warranted. Recommended next action:
recover or construct the actual source-owned **signature applicability**
introduction at beta formation, retaining its exact `(s,p,c)` incidence and
scope; then test its original attachment action against inherited, annotated,
conservative and whole-transport last rules before adopting any constructor.
Theorem IF already owns declaration/use contextual placement and need not be
reproved.

Unverified scope: exhaustive actual `Lic_C` grammar, every original local
attachment action, foreign interpretation/back maps, Generalize eligibility,
joint-hiding admission, complete Slots/profile/row existence, all-source
generation, operational admission/permissions and production conformance.
No aggregate gate or DAG status closes. Writing stops before submission for
frozen review.

## Frozen dependencies

All seven files match the baseline bytes; hashes are SHA-256.

| Path | Hash |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-07-owned-call-contribution-construction.md` | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/progress/2026-10-06-original-signature-licensing-construction.md` | `f5032a91781706551dcd01474f6024eb34fcb0cb110fa6157f7ec577ccfc5cff` |

## Commit packet

- Exact leased path: `notes/theory/2026-10-08-legacy-license-elimination-attempt.md`.
- Baseline SHA: `9b4ce75683d7636566a37d8f553375aaf78da75f`.
- Dependency changes: none; all seven baseline byte comparisons matched.
- Claim/review status: exploratory conditional indexed derivation and bounded
  missing-rule characterization; unreviewed, non-authoritative, no gate closure.
- Checks already run: governing-source/output-type comparison, indexed
  base/transport/hiding proof audit, bounded locator search, dependency SHA-256
  and byte comparisons, output-path absence check. No tests/builds/checker.
- Proposed research-checkpoint commit message:
  `research: isolate legacy licensing elimination constructor obligations`.
- Shared-record deltas intentionally left for primary/curator: record the
  original leaf and exhaustive last-rule inventory as unresolved; distinguish
  IF contextual placements and new `Attach_C^+` cases from original attachment;
  keep ATTACH/LIC_FORWARD/LIC_INVERT and all production/profile/row gates open.
