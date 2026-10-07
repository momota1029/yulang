# Generic Bind initial certificate and the Call initial incidence

Date: 2026-10-08
Status: Reviewed, non-authoritative research proposal
Reviewed-by: compiler_referee, spec_auditor
Claim class: conditional native constructor derivation and bounded contract extraction
Baseline: `ecf18d9d8f19579ba027ee4aa3b851375ec9fe61`
Exclusive write lease: this file only
Scope: generic Bind initial certificate applied to `P.CallInitial`; no adoption, compiler change, admission change or gate closure

## 1. Objective, method and result

Test the proposed factorization into one generic Bind initial certificate and
a Call-specific static incidence embedding. This is a forward dependent-record
construction, not another descriptor argument or executable probe.

The factorization can define a **new native initial presentation**, conditional
on an independently typed initial package and its lawful whole action. Its
constructor and incidence map are explicit below. It cannot supply the
already fixed original `C_c` from the inspected documents. Those documents
neither type the initial package completely nor provide an original initial
observation coordinate and evidence embedding. These two missing contracts
remain necessary; the generic certificate does not manufacture them.

The useful difference from the previous retained-field proposal is a precise
two-rule derivation, a single shared anchor for validity and formation, and
an explicit map requiring no Call-to-Bind admission conversion. The native
coordinate is defined here as a candidate, so this is not a theorem that its
coordinate was already present in the original kernel.

## 2. Governing sources and baseline

| Dependency | Exact governing scope used |
| --- | --- |
| `rules/research-lab.md` | Explicit lease, frozen inputs, distinct methods, conditional claims and stopping after an untouched premise. |
| `rules/design-authority.md` | Scope-sensitive authority, proof-obligation economy and Draft/adoption boundary. |
| `rules/git-concurrency.md` | Disjoint artifact ownership; primary alone integrates. |
| Source contracts §§2–3.5 | Joint original interpretation, finite source grammar, Bind equations and independent admission inventory. Their concrete operator/formation hypotheses remain conditional. |
| Source scheduling A §§1–5 | Callee first; whole-argument inert introduction after actual callee return; explicit entry demand. |
| Source result synthesis A §§1–5 | Preserve known result interface; inert lookup/synthesis; no extra result layer or recursive force. |
| Source Call interface definition §§1–4 | Selected full static Call frame and declaration/use inclusions; original operator, hole/world and witness contracts remain independent. |
| Source-interface construction §§3–5, 7 | Complete dependent Bind/Call interfaces, genuine formation origins, suspended suffix and actual-provider incidence. |
| Pure-read result constructor §§2–5 | Initial prefixes before carrier/challenge; `DescMem` remains separate from source-base derivation. |
| Call-initial prefix proposal §§3–6 | Reviewed starting Draft supplied by the packet; exact retained-input and missing-telescope boundary. Its own displayed review header is not promoted here. |
| Original-rule schema proposal §§3–6 | B-initial/C-initial and original decorated P/A/G residuals. |

Accepted meanings stay fixed: captured `f` is the same outer formal; `x` is
the actual local formal after entry rebind; the enclosing block returns its
closure inertly. Actual role and entry belong to the actual provider. Value
entry forces once in the same activation; Retained entry preserves the
carrier at entry. No implicit latent force, Q-dependent admission, narrowed
challenge domain or source anchor for every W/Z alternative is introduced.

`tasks/current.md`, `tasks/research-lab.md` and `notes/design/INDEX.md` were
read only for orientation. They are not theorem premises. The initial
proposal is an explicitly supplied frozen working-file dependency not yet
present at the pinned commit; its exact hash is in §8. The other direct
dependencies are pinned by their current hashes, matching the incoming
proposal manifests; a complete committed-file comparison is left to the
primary. No concurrent compiler or
shared-record edits are consumed as proof inputs.

## 3. Static decomposition, with one anchor

Fix a genuine original source formation package `F : Formation(j_F)` at

```text
j_F = (B,X,xi,Delta_c; original callee/argument/receiver/result/future incidences)
xi = (nu,K,D)
n_f = name b_f;  q_f = result(n_f)
n_x = name b_x;  q_x = result(n_x)
c = call(q_f,q_x).
```

`F` includes the actual formation derivations and the selected `IF_c`, its
Resolve/Capture/Application/reify/Return origins and original scopes. Repeated
fields are projections from this one package, not newly chosen witnesses.
The selected interface construction exposes the following static Bind shape:

```text
shape(F) = (q_1, form_1, M_F, S_F, form_S, kappa_F)
q_1      = q_f
M_F      = the original dependent ResultBind telescope at q_f's result port
S_F      = suffix code under M_F
kappa_F  = the actual static Bind/callee/suffix-to-Call incidence inclusions.
```

`M_F` retains the same returned value/provider/root, current `C_1`, dependent
rebind environment and whole witness that the original result port exposes.
Its actual types remain those of that original operator contract. The source
law determines the suspended code, under that telescope:

```text
S_F(m) = inertly form Delay(whole q_x, original capture references) at m;
         ExecuteCallable(actual provider projected from m, that carrier,
                         current C_1 projected from m).
```

This equation describes **code under a binder**, not a total function
returning invocation evidence for every `m`. `form_S` is code/interface
formation with the original dependent schemas. It neither supplies `m:M_F`
nor proves that any suffix invocation succeeds. All whole `q_x` is retained,
including its latent nonreturning or effectful developments. No actual
`v_f`, `U_f`, runtime `t_x`, `d:D_c`, receiver, receipt or Return occurs at
this stage. Future result/provider fields occur only under their original
dependent schema positions.

The generic construction below is indexed by the **full F**, including the
original Call source identity. It is a generic certificate for an initial
Bind shape, not an assertion that a separately formed source `bind` and this
Call have the same initial admission. Forgetting F down to `(q_f,S_F)` would
lose precisely the ownership and initial-validity evidence at issue.

## 4. Required initial telescope and candidate native coordinates

The following is a formal **parameter interface**, not a claim that all its
types have been defined by the inspected original documents. An owner must
supply it independently of Q, descriptor membership and execution:

```text
InitialOwner(F):
  Assign_F                              : Type
  History_F(eta0)                       : Type
  Current_F(eta0,h)                     : Type
  Environment_F(eta0,h,C)               : Type
  Witness_F(j_F,eta0,h,C,Gamma)          : Type
  Valid0_F(eta0,h,C,Gamma,w)             : Type

  A0(F) := Sigma eta0 : Assign_F.
           Sigma h : History_F(eta0).
           Sigma C : Current_F(eta0,h).
           Sigma Gamma : Environment_F(eta0,h,C).
           Sigma w : Witness_F(j_F,eta0,h,C,Gamma).
                     Valid0_F(eta0,h,C,Gamma,w).
```

Here `Valid0_F` must be the complete original initial event/environment
judgment, with its original source-typed punctured context, other-environment,
slot/hole and joint-dependency evidence at the stages where those fields are
available. All such fields must be exposed within these dependent telescopes;
the display does not authorize omission of an original hidden coordinate.
At zero local steps it cannot demand that the source has already formed its
argument Delay, assembled a checked challenge or obtained receiver acceptance.
Its history `h` may already be nonempty. `C` is its live state, never inferred
to be the assignment's initial state. `Gamma` and `w` have the same F, event,
world, scope and xi; they cannot be picked independently per operand.

The inventories and IF construction do not supply these six actual type
families, their complete guards, or the initial validity rule. Giving the
missing families names in this interface does not discharge that omission.
The conditional derivation assumes a genuine owner implementation, without
assuming that `A0(F)` is inhabited for any raw source program.

Given that interface, define a candidate native observation grammar for
**this initial slice only**:

```text
NativeB0(F) has constructor
  InitBind(a : A0(F))
with retained fields
  anchor       = F
  first        = (q_1, form_1) projected from shape(F)
  middle       = the uninstantiated M_F
  suffix       = (S_F, form_S) projected from shape(F)
  live         = (a.eta0, a.h, a.C, a.Gamma, a.w, a.valid)
  local_steps  = 0
  stage        = poised-first / suspended-whole-suffix.

NativeC0(F) has constructor
  InitCall(b : NativeB0(F))
with retained fields
  bind_initial = b
  call_origin  = F's actual Call formation
  incidence    = kappa_F projected from shape(F).
```

These constructors are dependent records with the displayed fields fixed
by their parameters. They contain no independent replacement F, witness,
history, environment, first child or suffix. The native observation has a
whole retained coordinate, not merely the projected empty trace. A projected
empty prefix alone cannot recover the source origins or live witness.

The concrete candidate incidence embedding is

```text
iota_F : NativeB0(F) -> NativeC0(F)
iota_F(InitBind(a)) := InitCall(InitBind(a)).
```

This domain is the generic certificate at the **same anchored F**. There is
no map from arbitrary `NativeB0(F')` or a Bind observation with matching
endpoints. Static `kappa_F` is retained as incidence only; it is not used as
a proof of an original semantic predicate.

## 5. Conditional finite derivation and whole map

Define candidate evidence families for the native slice by exactly two rules:

```text
F genuinely formed; shape(F) has genuine child/suffix code formation;
a : A0(F) independently supplied
---------------------------------------------------------------- [B0-native]
B0Evidence(F, InitBind(a), a.w)

b : NativeB0(F); beta : B0Evidence(F,b,w)
---------------------------------------------------------------- [Call0-native]
Call0Evidence(F, iota_F(b), w).
```

Neither rule asks for a child execution, `C_qf`, `C_qx`, callee Return, actual
carrier, challenge, receipt, entry, receiver invocation or `DescMem`. Thus for
the Name/Name formation in §3 and any independently supplied `a:A0(F)`, the
smallest derivation is one `B0-native` followed by one `Call0-native`. Its
local source-step count is zero; its evidence height is two. Formation and
initial-validity proofs are opaque supplied premises, whose heights are not
claimed to be two. No initial-validity inhabitant is constructed here.

**Conditional native theorem.** For any genuine F with the displayed Bind
decomposition, and any implemented `InitialOwner(F)`, every supplied `a:A0(F)`
has that two-rule derivation at the unchanged witness. This follows directly
by the two constructors. It establishes the proposed native grammar's
initial case only, not its full source adequacy or fixed-original membership.

Now let `g` be an independently legal original whole action with supplied
dependent maps on formation, all scopes and indices, the uninstantiated
ResultBind/suffix interface, and the **complete** initial package:

```text
g_form : Formation(j_F) -> Formation(g(j_F))
gF := g_form(F)                   g_A : A0(F) -> A0(gF)
g_shape(shape(F)) = shape(gF)      g_kappa(kappa_F) = kappa_gF.
```

The supplied original `g_form` transports the one fixed F at its original
formation judgment. `g_A(a)` jointly transports
`eta0,h,C,Gamma,w,valid` and every original hidden dependent field. Its
validity component must be supplied by the owner; IF proves only static
incidence transport. Rigid binder positions stay fixed as required by g.

Define the actual candidate maps by constructor recursion:

```text
g_B(InitBind(a)) := InitBind(g_A(a))
g_C(InitCall(b)) := InitCall(g_B(b))
g_beta(B0-native(F,a)) := B0-native(gF,g_A(a))
g_gamma(Call0-native(F,b,beta))
  := Call0-native(gF,g_B(b),g_beta(beta)).
```

Then, definitionally on every native constructor,

```text
g_C(iota_F(b)) = iota_gF(g_B(b));
witness(g_C(iota_F(InitBind(a)))) = (g_A(a)).w.
```

The same action is applied to q_f, whole q_x and S under its transported
ResultBind telescope; no returned middle tuple is chosen. Identity and
composition for observations **and evidence** follow by constructor
elimination from identity/composition of the supplied owner/formation actions.
This proof does not use an inverse for g, or pretend that a graft is invertible.

The theorem covers only legal actions with the displayed typed package maps
and laws. A joint-hiding or other relational certificate that selects an
output witness can be lifted pointwise through these constructors at that
single jointly supplied output package. A total `g_A`, functor laws or
admission preservation for such a certificate do not follow merely from its
existence. No per-child hiding, reselected provider or newly legal action is
created by the native map.

## 6. Fixed-original bridge and exact blockers

For an already fixed original source kernel, `NativeC0(F)` is not its
observation type and `Call0Evidence` is not `C_c`. To interpret this candidate
one still needs actual original families and maps with this signature:

```text
Obs_orig(F,a)                            : Type
Evidence_orig(F,a,O)                     := C_c(O,a.w; j_F, eta0=a.eta0,
                                               h=a.h, live C=a.C,
                                               environment=a.Gamma)

K0_F    : Pi a:A0(F). Obs_orig(F,a)
P0_F    : Pi a:A0(F). Evidence_orig(F,a,K0_F(a))
K0-law  : K0_gF(g_A(a)) = g_O(K0_F(a))
P0-law  : P0_gF(g_A(a)) = g_E(P0_F(a))  [at the transported dependent head].
```

The notation for `Evidence_orig` requests the original complete decorated
head, including its own actual scope and fields; it does not define a new
meaning for `C_c`. `g_O` and `g_E` must be genuine original lawful actions.
Once this independent signature is supplied, the interpretation is explicit:

```text
embed_O(InitCall(InitBind(a))) := K0_F(a)
embed_E(Call0-native(B0-native(F,a))) := P0_F(a).
```

Its whole-map law follows from K0-law/P0-law. This is conditional use of an
original source rule supplier, not a proof of that supplier: `P0_F` is exactly
the original `P.CallInitial` obligation in this scope.

An independently supplied original `B_initial` plus a genuine original Call
image theorem could factor K0/P0 further. That route also needs either initial
validity indexed by this full F, or an explicitly proved validity transfer
to the Bind owner's frame. The Return/Request equations specify reached
cases; they neither create `B_initial` nor that transfer. A static IF arrow
supplies neither. Calling this transfer an embedding would leave its main
premise untouched.

The precise blockers after this attempt are:

1. **I0 owner telescope:** actual definitions of the §4 initial families,
   complete dependent fields and independently valid initial judgment/action.
   The selected documents provide an inventory, not those typing clauses.
2. **O0 original coordinate:** actual `Obs_orig`, K0/P0 and whole-evidence
   laws, or the genuine original B-initial/Call-image factorization. The
   selected laws specify the stage, not this representation or its original
   head constructor.

For a new native presentation, O0 is a proposed explicit definition in §§4–5;
I0 remains required and its full independently justified validity cannot be
selected from the inventory. Full native observation/source correspondence
also remains unproved. For fixed `C_c`, both I0 and O0 are required original
contracts. Research permission authorizes neither their adoption nor compiler
implementation. A global absence claim about other original kernel suppliers
is not made; only the assigned documentary dependencies were inspected.

## 7. Evidence, limits and next action

Established inputs reused: selected timing/result meaning and static IF
constructors in their declared scopes. Bounded characterization: the supplied
documents expose a suspended Bind shape and leave I0/O0 abstract. Candidate
assumptions: the owner interface and new tagged native initial coordinate.
Conditional theorem: the two-rule native derivation and its whole action
commute once the owner package/maps are actually supplied. No established
original-source, all-context or production theorem is claimed.

The smallest missing-contract witness remains the genuine five-node
Name/Result–Name/Result Call at a valid independent initial event, before
either Name completes. The new generic factorization gives it an explicit
native coordinate conditionally; there is still no original K0/P0 derived
from the supplied source laws. This is an unresolved-rule witness, not a
source counterexample or proposed rejection.

There is no independent executable oracle. The supplied source contracts,
original formation and actual initial validity are shared assumptions. A
checker implementing B0-native/Call0-native would establish consistency of
this candidate grammar, not its source validity or presence in fixed `C_c`.
Seeds/ranges, mutations, samples and search failure counts do not apply.
No tests, builds, probes, Git mutations, child agents, questions or formatting
were run. Broad initial orientation output was truncated; exact relevant
sections were reread in bounded chunks. No exhaustive repository search ran.

Failure conditions: a partial initial telescope; validity derived from Q or
successful execution; forgetting F before validating incidence; live C reset
to eta0; separate operand witnesses; treating code formation as suffix
membership; an early actual carrier/challenge/Return/receipt/receiver;
claiming original membership from the new tag; missing original action laws;
or changed frozen dependencies. None licenses a new source rejection.

Unverified scope: initial validity inhabitation and complete admission domain;
fixed-original correspondence; other initial/prefix constructors; actual
receiver V and response/resume/future A; remaining G maps; emission/fixed-E
attachment; W/Z validation; raw-source typing; full C0; inference,
principality, F5 replacement, production and cutover. No semantic alternative,
aggregate status or canonical gate has changed.

Resource budget: one leased note, documentary reasoning and short read/hash
commands; zero builds/probes/heavyweight processes. No numerical CPU, memory
or wall-time cap was supplied. Peak CPU/RAM and total reasoning wall time were
not instrumented. No search or performance budget was consumed.

Recommended next action: extract the complete I0 initial event/environment
telescope and legal action from its owning kernel. If it cannot be supplied,
return its exact missing guard/field contract to the primary rather than
produce another equivalent initial-prefix model. Only after I0 is typed can
the primary review/select this native initial coordinate; a fixed-original
claim separately requires O0. The two attempts have left I0/O0 unchanged, so
another tag or toy checker is not a useful next method.

## 8. Frozen dependency manifest

SHA-256, capture and recheck; no dependency is edited by this lease:

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
181e95a9d87d90c265f28ad87e0176f10dd11c3c84bd308e1b802c571ae8d568  notes/design/2026-10-02-source-call-scheduling-choice.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
8f4cffa76a375e42abccb14709fd51c5cef7a99a1336b5653346a1e4f41febd9  notes/theory/2026-10-08-call-initial-prefix-constructor-proposal.md
9ead9f9f373967c7748a05dac1ff3d5de23b0cbd2a777fb0b4438d42f4d0a00d  notes/theory/2026-10-08-readinvoke-original-rule-schema-proposal.md
```

The final artifact hash and final dependency comparison are in the frozen
handoff packet; a file cannot contain its own complete SHA-256 hash. No
dependency changed during this lease. The initial-prefix proposal's frozen
working-file hash is additional to the baseline, not falsely claimed to be
present at that revision.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-08-call-bind-initial-bridge-proposal.md`.
- Baseline SHA: `ecf18d9d8f19579ba027ee4aa3b851375ec9fe61`.
- Dependency hashes changed by this lease: none. Additional frozen input:
  initial-prefix proposal SHA-256 `1018a642debff8d2d49458c444c33137255f243632b7536fc1363670a9dc837c`, absent at baseline.
- Review status: Reviewed Draft, non-authoritative; compiler-referee and spec-auditor reviews found no defect within the bounded native factorization.
- Checks already run: exact governing-section extraction, narrow baseline/existence check, dependency SHA-256 capture/recheck and leased-file inspection. No tests/builds/probes, compiler edits or Git mutations.
- Proposed one-line research-checkpoint commit message: `research: factor Call initial evidence through an anchored Bind certificate`.
- Shared-record deltas intentionally left for primary/curator: record this conditional native factorization and exact I0/O0 supplier residuals; preserve original P.CallInitial, H_rules, attachment, F5 and aggregate gate statuses. No task/index/authority/theory-map/question-board edit included.

Writes stop at frozen handoff; review repair requires a renewed explicit lease.
