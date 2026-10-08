# `id` / `pick`: ordinary Parameter ownership at internal Generalize

Date: 2026-10-08
Status: Reviewed bounded source-rule audit and conditional derivation
Baseline: `51714826c2a832471329d04600592476cbfa70b4`
Lease: this note only; frozen on submission
Reviewed-by: compiler_referee (Parameter ownership/scope seam), spec_auditor (q1/public boundary)
Review result: no blocking, major, or minor findings within those scopes
Authority / adoption / gate closure / implementation: none

## 1. Objective and result

Inspect whether the selected ordinary Parameter rule actually introduces an
ordinary `Desc` record for nonrecursive `id` and resolved monomorphic `pick`,
including its owner, type scope and dependency telescope. The method is exact
source-rule inversion and correspondence inspection. The primary narrowed the
initial retained-root assignment to this ownership seam; this note does not
repeat the existing GS/GC internal-retention theorem as a new result.

**Bounded result:** the selected native source definition explicitly makes
Parameter the constructor of `Desc(C,q,sort,sigma,Delta)` and `Build` retains
that constructor output. Its source subsystem does not assume an eligible
binder list or infer classification from generalization success. However,
`T`, the original type scope and dependency telescope are supplied by its
independent typed source context/local rules. The cited proof does not derive
those semantic operands from current parser/HIR/F5 artifacts. A fresh F5 row
and its generalization origin supply identities, not that correspondence.

The committed native definition/proof has selection/review headers. Per the
assignment it was inspected as questioned historical input; its clauses are
reported precisely, without invoking GS/GC as evidence for a stronger source
or production claim, withdrawing its status, or adopting a new rule here.
If the remaining INTRO item asks only for classification *within those selected
source rules*, Parameter supplies it definitionally. If it asks for independent
construction of original scope/telescope or compiler correspondence, this
bounded inspection does not close it. Those are different claims.

The accepted `successor-generalize-root-policy/q1/a1`, decision items 1–5,
requires a transformed/displayable scheme plus necessary use-time information
as the actual public target. A retained Lambda is internal evidence. The
primary explicitly confirmed this boundary. Neither a source-rule `Desc`
record nor complete internal retention supplies the actual public export.

## 2. Baseline and exact governing sections

All semantic reads used committed `git show BASE:path`. `tasks/current.md` and
`notes/design/INDEX.md` were locators only; dirty coordination was excluded.

- `inferred-function-call-views` §§1.1–2, 5: distinct written/public/internal
  layers, source-derived incidences and one original `xi=(nu,K,D)`; Q cannot
  manufacture identity, scope, paths or admission. §§3–4 supply no `apply`
  inference rule for these projections.
- SCC-intrusion charter §§1–3, Gates B–E, §§18, 21–24: replace F5; fresh ordinary
  Value endpoint; same-activation Force/rebind; actual Pure ordinary literal;
  every derived comparison re-enters the guard; levels belong to variables.
- `source-result-synthesis-choice` §§2–4 and typed-computation core §§2–3, 6, 9:
  selected source roles, Name/Result synthesis and conditional typed context,
  body and complete invocation construction.
- PG-1 eligibility attack §§3–4.1 and PG-1 whole-root falsification: repeated
  identity endpoint and fixed projection capture; syntactic endpoints do not
  establish complete publication admission or designated-root Direct.
- Historical native source definition §§1–4; its proof §§2–5, 6 Parameter case,
  §§7.1–7.2: exact definition versus genuine local laws and actual resolver.
- `source-contracts-and-common-allowance` §§2.1–2.2, 3.1–3.3, 3.7, 5.3 and
  `id-descriptor-source-bridge` §§3–6: independent active descriptor/admission,
  production extras and actual-root query suppliers remain distinct.
- Root-policy approved answer items 1–5 and committed receipt: transformed
  public target; no renamed complete source relation and no sufficiency claim.

## 3. The exact ordinary Parameter derivation

Envelope: resolved `my id x = x` and `my pick y = z`, one unannotated ordinary
formal, no recursion, callback position, annotation, conversion or common
formation. At `pick`, `z` denotes an independently installed immutable
monomorphic Value certificate. Polymorphic captured Name instantiation and
local brace realization are outside this inspection, not rejected programs.

Fix the actual validating component `C`, Lambda occurrence `L`, formal
occurrence `u`, declaration key `q_u`, independent original binder tree `T`,
type scope `sigma_u` and its legal dependency telescope `Delta_u`. Under the
selected source subsystem, the bounded rule instance is

```text
SourceParameter(L,u) is ordinary unannotated
C is its actual validating source component
sigma_u, Delta_u are supplied by its original typed source context in T
fresh ordinary flexible value endpoint a at q_u
------------------------------------------------------ Parameter [selected subsystem]
P_L = Value(a)
Desc(C,q_u,ValueEndpoint,sigma_u,Delta_u)
body binding after actual entry rebind: u : Value(a).
```

`ValueEndpoint` here spells out the sort, not a proposed compiler enum or new
language constructor. The record key is the actual introduction `q_u`; `a` is
its endpoint. Writing `Desc(C,a,...)` alone can obscure this distinction.

The exact documentary chain, with baseline line locators:

| Committed source | What it supplies; what it does not supply |
| --- | --- |
| Charter lines 577–590 (§21) | Unannotated parameter gets a fresh inferred Value endpoint; Force/rebind precedes body even if unused, effectful or divergent. It selects source entry, not a generalized binder classification algorithm. |
| Typed core lines 339, 349–379 (§6) | Constructs one finite parameter binding/receipt/entry skeleton before body synthesis; one skeleton up to fresh naming; lawful substitution retains the tag/entry. Original admitted annotation/typed-flow premises are retained. |
| Historical proof line 140 (§3.1) | Ordinary unannotated Parameter receives an ordinary flexible endpoint at its source typing scope, distinct from existential inference/request opening. |
| Historical proof lines 207–217 (§3.3) | Explicitly declares `Desc(C,q,sort,sigma,Delta)` at the owning introduction. Parameter type scope precedes challenges; an endpoint cannot depend on an argument witness selected after entry. |
| Historical proof lines 219–228 (§3.3) | Calls the typed records outputs of the owning rule and assigns Parameter the `Desc`/`Description` constructors. This is definitional construction in that subsystem, not an opaque assumed Generalize conclusion. |
| Historical proof lines 364–387 (§4) | `Build(S,T)` allocates one symbolic declaration per actual introduction, shares repeated references, and retains owning-rule/dependency records. It takes original T and local rules as inputs. |
| Historical proof lines 473–480 (§5.1) | Uses ordinary retained `Desc` records outside fixed closure as eligible declarations at their original scopes. It consumes Parameter classification; it does not independently derive it from solver row shape. |
| Historical proof lines 658–659 and 712–717 (§6) | SRC retains the Parameter source tag/declaration and inversely records the independent derivation's endpoint at that declaration. It preserves the given telescope; it does not reconstruct T/Delta from untyped syntax. |

Thus ordinary classification is produced by the selected Parameter definition,
then retained by `Build`. The theorem is relative to independently meaningful
local source constructors L1–L5, not a proof that an unrelated historical
`Intro22` predicate or current F5 row already denotes this declaration.
Ordinary classification also does not exempt later comparisons from guards.

## 4. Endpoint, scope and capture consequences

After entry rebind, source Name/Result inversion gives

```text
id:   Gamma_body(x)=Value(a)
      Synth(name x)=Value(a); Result=Comp(empty,a)
      same q_u at formal and body/result references.

pick: Gamma_body(y)=Value(a); Gamma_outer(z)=Value(b_z)
      Synth(name z)=Value(b_z); Result=Comp(empty,b_z)
      q_u introduced here; b_z belongs to the installed outer certificate.
```

There is no separate result declaration in either case. At `id`, the body
returns the actual rebound provider. At `pick`, it returns the fixed installed
provider of `z`. Pure receiver, Value entry and result forwarding follow the
selected source decisions; the body empty effect does not erase full argument
entry, pending resumptions, divergence or invocation consumer obligations.

The whole internal Lambda root retains those exact occurrences and the
original dependent scopes. For `pick`, installed provider, world/lifetime,
prior realization evidence and every free latent/admission/future contract
operand are fixed. Repeated type spelling does not establish those identities.
If that fixed closure reaches `a`, it fixes the corresponding `Desc`; otherwise
`a` is the bounded candidate template. An equation `a=b_z` remains active even
if it eliminates effective freedom. This is the existing selected placement
rule instantiated, not a new maximal-generalization theorem.

The scope/telescope conclusions have an exact limit:

1. `sigma_u` is before the Lambda invocation challenge. Result Name forwards
   `q_u`; it cannot introduce a later challenge-dependent endpoint.
2. `Delta_u` is the original allowed dependency telescope at `sigma_u`. No
   challenge, response, rebind value or future history introduced later can
   be added to it. Captured operational witnesses keep their original binders.
3. Neither the source Parameter table nor the historical proof enumerates a
   concrete complete `Delta_u` from raw syntax. This note does not guess
   `Delta_u=empty`, bind every free Function port, or equate lexical scope with
   the semantic telescope. Nested enclosing type/rigid dependencies may exist.

**Conditional derivation:** given the independent original type scope and
legal telescope, Parameter introduces exactly one ordinary declaration;
Name/Result retain its incidence for `id`, and retain the outer certificate
for `pick`. `Build` preserves that record by its defining constructor clause.
Proof is direct inversion of the cited Parameter, Name and Result cases.
It assumes neither a scheme-instance success nor eligible-list success.
The whole source-retention/soundness/completeness theorem under L1–L5 is
already in the historical selected subsystem; no second GS/GC proof is claimed.

The remaining source-to-artifact supplier, if demanded, is the owning typed
elaboration output mapping actual `(C,L,u,q_u)` to the original `sigma_u,
Delta_u`, ordinary introduction class and complete dependent incidence set.
Its soundness must follow from genuine local formation/transport laws. A
record that merely asserts those values without its owning construction is
not that proof. No repository-wide absence claim is made.

## 5. Narrow compiler correspondence and actual public root

Current HIR inspection shows `HirParameterId` created from the definition root
and ordinal in `crates/yu-hir/src/module.rs:1293`; exact source identity is
recorded at line 1300; lexical parameter scope is pushed at line 1312; Lambda
retains that parameter at line 1339. Name resolution at line 1997 chooses an
actual parameter before module resolution at line 2002. These are authentic
lexical identity suppliers. Their inspected fields are not the semantic
`Desc` sort, `sigma_u` or complete `Delta_u` certificate above.

The existing `shadow_parameter_row_identity` test lines 30–73 constructs
`my id x = x`, captures its solve-branded F5 parameter row, and checks exactly
one matching current generalization origin. This is code-inspection evidence,
not an executed test. That identity assertion does not prove source scope,
telescope legality, complete admission or successor public generalization.
No test, parser run or compiler acceptance was measured.

q1/a1 still requires a separate actual public publication relation

```text
internal whole Lambda evidence I_b
  -- independently justified abstraction/formation E_pub -->
P_b=(displayable Sigma_b, necessary alpha_b), actual designated root r_pub.
```

No such `E_pub` is constructed here. The use-side decoder must obtain its
actual complete descriptor/admission/membership from `P_b` without traversing
the source definition or retaining the whole source relation as alpha.
Descriptor bridge S1–S6 remain the exact named suppliers.

The real use obligation is

```text
C_V(v) => exists original-scope z.
  Instance(P_b,i;v,z) and Direct(r_pub^i(v,z),R_V(v)).
```

For source-contracts §5.3's sufficient rule, this requires finite complete
`Eq(D_pub^i,D_V)` and `Le(M_pub^i,M_V)`, including `DescMem`, original residuals,
all Option 2 production alternatives and original scoped operands; matching
actual role/entry/consumer; every derived comparison's guard; and actual
resolver acceptance of that whole-root certificate. Retained-root identity
or separate successful concrete comparisons do not supply `Direct` at r_pub.
Current F5 Q/R, extrusion and closed-scheme alpha-equivalence are not the
successor semantic target under charter §§1–3.

## 6. Discriminators and stopping condition

These are hand-inspected failure conditions, not executed mutations:

| Shortcut | Exact premise it would violate |
| --- | --- |
| Reconstruct ordinary `Desc` from a successful exporter or a row shape | Parameter's actual owning introduction and source tag are missing. |
| Allow `a=T(response)` with response introduced after entry | `sigma_u` precedes the challenge; Delta cannot acquire that later dependency. |
| Introduce a second `id` result description | Name/Result forward the same q_u and actual rebound value. |
| Generalize `b_z` at `pick` because it appears in the Function | It is installed outer Mono evidence, with its full fixed dependency closure. |
| Ignore entry when `pick` ignores y | Admitted divergent/effectful carriers are still forced before the body. |
| Treat the HIR lexical stack as the complete semantic telescope | The inspected HIR fields provide identity/resolution, without the required typed dependent operands. |
| Query the retained Lambda instead of the transformed published descriptor | It proves a different query from the required designated-root Direct. |

Oracle independence: no executable oracle, reference interpreter or checker.
Source inversion is independent of Generalize success, but shares the selected
Parameter/Name/Result laws and supplied original context. It does not validate
those local semantic laws by implementing their transitions twice. PG-1 and
the descriptor bridge already leave public interpretation/query untouched;
this audit isolates the owning Parameter record rather than proposing another
equivalent toy probe.

No seeds, ranges or exhaustive enumeration; no executed mutations. No missing
ordinary classification premise remains *inside the selected rule definition*.
The exact possible blocker is construction/correspondence of its original
scope/telescope and local laws if the INTRO consumer requires more than that
relative definition. Actual transformed export/Direct is separately unresolved.

Unverified: raw-source complete type-scope/telescope reconstruction; production
Desc correspondence; independent primitive/world/descriptor laws; complete
Option 2 inventory; transformed public sufficiency/Direct and principality;
recursive, State, method/adapter, callback, annotation and local-brace cases;
solving, lifecycle and resource bounds. This inspection adds no source
restriction or mandatory annotation.

Recommended next action: identify the exact INTRO consumer and require its
owning typed Parameter output to expose `(q_u,ordinary,sigma_u,Delta_u)` at
construction. Reuse the selected source-rule classification if that is the
consumer's full premise; otherwise prove the particular scope/telescope
correspondence without reconstructing it from F5 success. Keep public export
and Direct outside this discharge.

## 7. Checks, resources and pinned inputs

Only read-only Git inspection and bounded document/code reads plus final
static lease/whitespace/hash inspection. No tests, builds, formatting, child,
Git mutation or shared-record write. One lightweight local process at a time;
no heavyweight process. No numeric budget was supplied. CPU time, peak RAM
and total wall time were not instrumented; captured commands were subsecond.

One broad literal/constructor locator capture was truncated; subsequent
specific sections were read in full. A guessed solver-path grep had no
matches; neither result is an absence proof or exhaustive source search.
All dependency hashes below identify committed baseline bytes. Dirty task,
index and theory coordination is not a premise.

| Path | Baseline SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6` |
| `rules/design-authority.md` | `925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `rules/question-board.md` | `8c617ceb978dfa26ce12f4f71ecc8ece22ffd8f1cf1982125b33142f645ae1c0` |
| `tasks/current.md` | `b02bac0bc54381275ee1c170c71cda914e8b725b1cb9c5f37569f8888087e73a` |
| `notes/design/INDEX.md` | `eb6299147fccf0352b3aceea589208eeb3f4368a7c11f8fa714da1cce1f4b609` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/progress/2026-10-06-source-generalization-eligibility-attack.md` | `2445a67ab8ce3372e7acd62fd90d598ca1ea3bc92872ff9b8588f176fc077d3e` |
| `notes/theory/2026-10-08-pg1-generalize-direct-falsification.md` | `0ee458def47c3c99c022dab46840a18d0c528bd012a4053d49d8c7a4bb9c40ae` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-08-id-descriptor-source-bridge.md` | `dcc91b8cb958f68208b61f490b68cbc3d42318b65f14604b0ad80742b1798a10` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/tests/shadow_parameter_row_identity.rs` | `7210a616a7ef49791d97aa94c4314336de2f898de62597f680978c58107a0583` |

Final baseline check: current HEAD `51714826c2a832471329d04600592476cbfa70b4`; changed committed direct dependency hashes: none.
Live paths differing from baseline (excluded from input): `tasks/current.md`, `notes/design/INDEX.md`.


## 8. Commit packet

- Exact leased/changed path: `notes/theory/2026-10-08-id-pick-retained-root-generalize-candidate.md`.
- Baseline SHA: `51714826c2a832471329d04600592476cbfa70b4`.
- Claim/review status: independently reviewed bounded ownership audit and
  conditional source-rule derivation; no adoption,
  gate closure, public sufficiency or implementation authority.
- Checks already run: exact committed sections/code reads, SHA-256 dependency
  inspection and final static leased-note checks. No semantic execution,
  tests, builds or formatting.
- Proposed checkpoint message: `research: audit id and pick parameter Desc ownership`.
- Shared-record deltas intentionally left for the primary/curator: distinguish
  ordinary classification constructed by the selected Parameter rule from
  source scope/telescope and compiler correspondence demanded by INTRO's
  actual consumer; retain transformed public export/Direct and all other
  gates. No task/index/DAG/design/question or compiler changes are made or
  status promotion proposed under this lease.

Writing stops on submission; the note is frozen for independent review.
