# Captured `f`: constructive registration attempt at the first source judgment

Date: 2026-10-06
Status: Frozen compiler-referee-reviewed research; bounded rule-interface characterization and conditional derivation
Baseline: `9e29dcb409db8e173959716a4abacbce40dcf0d5`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: forward derivation followed by last-rule analysis; static work only
Implementation authority: none

## Objective and result

For the exact approved candidate

```text
my apply f = { my step x = f x; step }
```

construct a comparison-independent source judgment linking the original
formal/contract/profile of `f` to the provider retained by the returned `step`
closure. The attempt stops before return transport or later receiver
activation: the inspected rules do not introduce the original registered
provider/contract relationship from the resolved formal and its call use.

The reduced missing output is a **registered symbolic relation root**, with
its original contract/profile and provider incidence. It need not be a
solved or uniquely determined complete Function type. Requiring a solved
interface in `Gamma` would assume a stronger conclusion and conceal this
earlier missing step. Even an unsolved root must relate its source position,
contract, capture operand and joint scope; a fresh endpoint alone does not.

This is a bounded characterization of the named interfaces, not a theorem
that no possible source inference system can construct the root. The
conditional derivation below establishes an ordinary skeleton. It proves
neither source acceptance nor registration, admission, soundness,
principality, source adequacy or production conformance. No accepted-source
counterexample is claimed.

## Baseline, governing premises and dependency snapshot

Read and apply `rules/research-lab.md`, `rules/design-authority.md` and
`rules/git-concurrency.md`. The authoritative locators are
`notes/design/INDEX.md`; `tasks/current.md` was status context only. Neither
is a proof premise. Unrelated live HIR/test/task edits were observed and left
untouched. No live compiler edits or other workers' unfinished artifacts
were consumed.

Exact governing sources:

- Nested-block source-interpretation addendum §2 fixes sequential local
  binding, final-expression function return, lexical resolution and retained
  outer capture, only for this candidate. Its §§3–4 preserve the open gates.
- Inferred Function call views §§2–5, with §1.1's distinction among annotation,
  public scheme and internal view, require source-generated contract/slot,
  original scope and joint `nu,K,D`, independent of pending comparison `Q`.
  Integrated `function-call-view-formation/q1 a2` and its receipt are the
  accepted decision; no differently numbered answer is assumed.
- Callback-context delivery §§2–4 starts with the instantiated callback
  contract/profile. B remains normative: deliver its boundary before body
  generation, synthesize endpoints independently, check one completed
  `F_lit <: F_cb`. Existing callable values retain actual role and entry.
- Typed computation core §§2–3/6/9 supplies the conditional ordinary
  parameter/name/call skeleton, descriptors and complete invocation. It is
  Draft; its conditional constructions are not new source inference authority.
- Source contracts §§2–3/5.3 supplies the conditional decorated-input,
  emission/admission and complete-query certificate requirements.
- Typed-boundary §6 supplies transport of already typed view packets,
  receiving ownership, event observation and activity filtering.
- The prior nested-block registration attempt is the reviewed dependency
  locating this seam; its reviewer status does not certify this new artifact.

All direct dependencies matched their pinned baseline bytes at inspection.
SHA-256 snapshot:

| Path under repository root | SHA-256 |
| --- | --- |
| `notes/progress/2026-10-06-nested-block-callview-registration-attempt.md` | `31b45bbb95c06dbbe91430fac2107af112b239fac413fac944b3e08623a9b97b` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |

## 1. Forward derivation without a completed interface in `Gamma`

Use proof labels `b_f` for the outer formal, `b_x` for the inner formal,
`l_step` for the inner closure origin, `u_f,u_x` for the names in its body,
and `c` for `f x`. The selected source meaning establishes

```text
resolve(u_f)=b_f; resolve(u_x)=b_x;
c is in l_step's body; l_step retains that enclosing b_f capture.
```

Explicit hypotheses for the following conditional construction:

H1. The approved structure is represented by a finite ordinary core
derivation to which §6's parameter/name rules apply. This is not production
acceptance or a full decorated source certificate.

H2. Ordinary parameter generation supplies fresh value endpoints `A_f,A_x`;
the inner lexical environment retains the outer `b_f` binding under its
resolved identity. This is ordinary endpoint reuse within this skeleton,
not a theorem about local generalization or arbitrary scheme instantiation.

H3. The application row generates its callee, whole-argument and complete
invocation constraints as obligations. They are not solved interfaces,
typed-profile certificates or admission proofs.

Then the §6 table constructs:

```text
P_apply_f = Value(A_f)       P_step_x = Value(A_x)
Gamma_inner(b_f)=Value(A_f)  Gamma_inner(b_x)=Value(A_x)
n_f=result(name b_f)         n_x=result(name b_x)
Result(I_x)=Comp(empty,A_x)
n_c=call(n_f,n_x)            Result(I_c)=Comp(E_c,A_c)
d_step=lambda(P_step_x,n_c)
I_step=Value(Fun(P_step_x,Comp(E_c,A_c)))
```

The displayed `Fun` is §6's body/result skeleton. `E_c,A_c` remain constrained
complete-call endpoints. In particular §9 forbids replacing complete call
behavior with the inner body's pure name lookup or an unconditional row
union. The ordinary `Value` tag on `b_f` describes the binding of the supplied
value, not the actual role or entry of the callable it denotes.
The display abbreviates §6's administrative `eliminate(reify(call(...)))`
by `call(...)`, conditionally using that section's same-context law. This
abbreviation neither constructs a profile/path certificate nor moves the
call across a receipt or return delimiter.

The final `step` name and ordinary `bind` return this function descriptor
conditionally through the approved structural correspondence. Neither
executes `c`. Sections 2–3 describe that closure as retaining lexical
references **and typed evidence** when those exist. H1–H3 have supplied the
references and endpoint obligations; they have not supplied the latter
contract/provider evidence. No completed `F_f` was installed in `Gamma`.

## 2. Exact missing source judgment

Let `C` be this resolved declaration/use component, including annotation
absence. The following is notation for the required output, not a selected
inference rule, compiler record, or proposed surface type:

```text
SourceRegisterCapture(C,b_f,u_f,c,l_step)
    produces a jointly constrained relationship J_f such that
      J_f registers the original provider root R_f of b_f;
      its role-indexed contract and original position form beta,Slots(beta);
      its typed capture operand belongs to l_step's retained b_f binding;
      u_f/c refer to that relationship at their admitted typed positions;
      all dependent endpoints, predicates and incidences use one original
        binder tree and one jointly scoped nu,K,D.
```

`J_f` may be symbolic and retain unsolved obligations. Its source origin,
annotation absence and scope must be identifiable. No equation sets
`beta=b_f`, `beta=c` or `beta=source-range`; the contract is essential.
This target does not choose which uses enter the component, a seed-discharge
rule, a principal solution, a logical binder tree from lexical nesting, or
the representation of a provider root. Those are still separate obligations.

The phrase “original provider root” has two levels. Statically it is the
root registered for the formal/use relationship. At a later invocation of
a particular returned closure `s`, its capture operand must refer to the
provider actually retained by that `s`. A common lexical binder label does
not equate providers across distinct outer activations. The required
capture correspondence relates these levels; it cannot be reconstructed
from underlying pointer equality or from the public view of `s`.

### Supplied decorated input changes the proof frontier

There are two different premise sets; the failed derivation must not conflate
them. Source contracts §3.1 expressly takes a finite **decorated** graph. Its
captures and aliases retain original provider roots, and its source supplies
actual roles, entry, declared operations, typed paths, owners, receipts,
raw resumptions, consumers and the original shared tuple. H1–H3 above do not
assert that full envelope. The approved resolved candidate alone also does
not assert it.

| Premise | H1–H3 ordinary skeleton | Full decorated source contract |
| --- | --- | --- |
| Resolved formal/capture identity and ordinary endpoints | Supplied/generated as displayed | Supplied with typed decoration |
| Original provider roots and retained dependent capture operands | Required registration output | Supplied source data to §3.2 |
| Actual role, entry, typed paths/owners/receipts/consumer and original tuple | Only ordinary entry skeleton and open obligations | Explicit §3.1 inputs |
| Original contract/profile linked to typed provider incidence | Missing `J_f` | Must be supplied in the full certificate under call-view §§2–5, source contracts §2.2 and typed-boundary §6; §3.1 alone does not name a `beta,Slots(beta)` construction |
| Name/Lambda emitted relation clauses, local descriptor typing, finite conformance | Not constructed | Additional obligations, not implied merely by the decorated graph being supplied |

If a full decorated source certificate containing that contract/profile link
is an explicit hypothesis, the first registration anchor is already present.
Then the narrower outstanding construction is emission of Name's original
resolved root with dependent providers, and Lambda's captured-root clause,
with their original typed operands/scopes. Section 3.2 is an emission
inventory that requires those clauses. Section 3.5 additionally assumes
local descriptor typing lemmas and a finite conformance certificate for
§§3.1–3.4 before proving source-base correspondence. Thus supplying the
decorated input removes the earlier cut but does not itself supply those
emission/conformance lemmas.

This narrower cut is preserved as a conditional alternative, not rejected.
It does not solve the assigned construction from the exact resolved source:
that construction still must derive or explicitly assume the full decorated
input. Conversely, claiming no registration anchor can follow from an input
that already supplies it would be false. The next section's restricted claim
uses H1–H3 only.

## 3. Last-rule analysis at the registration cut

Claim class: conditional non-generation statement about the inspected
proof interfaces. Define a registration anchor as a supplied or produced
certificate connecting an original source contract/profile to its typed
provider operand. Assume leaves contain H1–H3 and resolved syntax only,
and all rules used are the named ordinary skeleton, descriptor, transport,
emission or local comparison rules, with their stated side conditions.
Then those rules cannot derive `J_f` without an additional registration
anchor or a new source-generation premise.

Proof: inspect the possible last step that could first introduce the anchor.

| Inspected rule | Why it cannot be the first registration introduction |
| --- | --- |
| §6 ordinary parameter/name | Generates/reuses `Value(A_f)` and binding/entry skeleton; receipt paths explicitly retain admitted annotation/typed-flow premises. It does not construct the nested role-indexed contract/profile. |
| §6 application | Generates a callable constraint and whole-carrier path/contract obligations. Treating an obligation as its certificate assumes the needed source interpretation. |
| §§2–3 lambda/descriptor | Translates the supplied derivation and captures its lexical references and typed evidence. It does not supply missing typed evidence merely by capturing a reference. |
| Source contracts §3.2 Name/Lambda | Requires original resolved provider roots and captured roots in an already decorated source envelope (§3.1). The inventory requires their emitted clauses; the local typing and finite conformance certificate is an additional §3.5 premise. None derives that envelope from raw resolved syntax. |
| Callback delivery §2 | Its first premise is an already instantiated `F_cb,beta,Slots(beta)`; B cannot initialize an unknown captured contract by copying those nonexistent inputs. |
| Typed-boundary §6 introduction | Introduces a dynamic instance at a source-certified callback boundary with a supplied signature profile. Its own source-elaboration premise is the missing anchor, and dynamic introduction is distinct from static registration. |
| Typed-boundary §6 transport/receipt | Every output profile incidence has an input profile witness. `Receive` adds use ownership to an existing typed view and creates no contract or boundary. |
| Source contracts §5.3 certificate | Provider leaves require the same whole provider operand and fixed envelope; congruence requires matching original provider/path/scope operands; recursive pairing requires already registered roots and original source/interaction/guard/binder labels. The query proves consequences of those inputs. |

For ordinary composition the induction is direct: copying, relational image,
conjunction or certified uniform renaming can retain an anchor already in a
premise, but cannot be its first introduction. Endpoint freshness creates
an endpoint, not a source-contract anchor. Typed-boundary introduction and
emission rules consume the anchor in their side conditions, so they do not
break this induction. The §5.3 parent Function rule explicitly requires the
actual emitted roots and finite domain/membership certificates; a successful
pending `Q` is not an introduction rule. This proves the restricted claim.

This is not a repository-wide rule-absence proof. The authoritative formation
direction requires a source producer, and this last-rule analysis establishes
only that the particular candidate core/transport/contract clauses inspected
here do not implement it. A future explicit generation rule can cross the
cut, subject to the existing approval and proof gates.

## 4. What transport would prove after that cut

Conditionally supply `J_f`, a typed capture correspondence `M_cap` into
`s`'s environment, and admitted subsequent name-use correspondence `M_use`
for that same retained provider. Then typed-boundary §6 gives

```text
chi_use = (M_use composed M_cap)_* chi_f
D_use   = (M_use composed M_cap)_* D_f
K_use   = K_f under the same nu
```

with each tagged source witness retained. This is a preservation consequence,
not construction of `chi_f`, `M_cap` or `M_use`. Returning `s` transports its
public result view at matching result paths; it does not paste that public
profile over all private captured bindings. Original logical scopes and
dependent provider incidences must move together through any certified
generalization/use; independently freshened capture and call witnesses do
not satisfy the premise.

Later active receiver/profile binding, event-specific `Observe`, matching
receipt, actual owner identity and current activity remain additional
premises. Retained lexical capture does not keep the outer activation live.
No receipt is replayed or ended receiver revived by transport. Any registered
recursion certificate must retain its original source/interaction/guard and
binder labels with complete alternatives and positive child uses; no such
certificate is built here. Origin and guard conditions are not weakened.

If the source producer and these admitted transports depend only on `C` and
its original joint constraints, changing pending `Q` with those inputs fixed
does not change their outputs, up to permitted joint renaming. That is a
conditional dependency argument; it does not prove that a source producer
exists merely because `Q` is absent from its proposed signature.

## Evidence, failure conditions and scope limits

There is no executable oracle. Approved sources independently fix this
candidate's meaning and formation requirements; the typed/core transport
conclusions share the displayed source-typing/registration premises. This
At freeze, this note was the producer's output. A checker assuming the missing
registration/transport transitions would verify their consequences, not prove
those source rules.

Coverage: one exact source candidate and its named rule interfaces. No
seed/range, execution enumeration, mutation, runtime trace, build, test or
formatting was run. This uses a different method from an activation-prefix
falsifier: it locates the first possible proof introduction. It stops at the
same registration premise identified by earlier attempts and supplies no
third equivalent toy probe.

Failure conditions for a proposed closure of this gate: install a completed
interface in `Gamma`; equate a source label with a complete slot/profile;
claim that ordinary endpoint freshness creates a registered provider;
interpret a generated callable/path obligation as solved source evidence;
use `Q` to choose that evidence; conflate different closure-instance providers;
copy a public closure view to private bindings; infer live authority from
capture retention; discard original origins/guards or jointly scoped
dependencies; or use §5.3 relation congruence to invent its operand roots.

Unverified seams remain: the actual registration/role seed and annotation
profile rules; typed capture/call/adaptation sufficiency; original logical
scope and local generalization; receiver activation and lifetime; initial
and future-use admission; production Option 2 extras and whole-domain
containment; raw production acceptance; soundness, principality and source
adequacy. Actual callable roles, B, annotation boundaries, and Option A/2
are preserved rather than derived from this skeleton. No annotated variant
or F5-based source-rule reconstruction was attempted.

Commands: read-only `git rev-parse`, `git branch --show-current`, `git status
--short`, `rg`, `cat`, bounded `sed` section reads, `sha256sum`, and
`git diff --name-only <baseline> -- <direct dependencies>`. Dependency diff
was empty. Initial combined captures were truncated; decisive original
sections and approval texts were reread in bounded captures. The note was
created with `apply_patch`; no Git mutation or other path write occurred.
Final baseline/dependency recheck and `git diff --no-index --check /dev/null
<leased path>`
are the artifact checks, not tests. Independent review is recorded below.

Resources: static-work packet only; no numeric CPU/RAM/wall-time budget was
specified. At most three lightweight read subprocesses overlapped; no build,
test or executable research process ran. CPU time, peak RSS and total wall
time were not measured. No children were spawned.

Recommended next action: primary/architect should specify the minimal
source-registration rule that introduces this symbolic contract/provider
anchor for the resolved `b_f,u_f,c,l_step` component, including its original
logical scope and typed capture operand, then seek review against the fixed
call-view decisions. Transport, activation and admission work cannot supply
that introduction retroactively.

## Independent review

`compiler_referee` reviewed this note together with the complementary
premise-inversion audit and found no blocking, major, or minor issue within the
declared scope. The review confirms that the ordinary derivation stops before
contract/profile registration; the supplied decorated-input case has a
narrower Name/Lambda emission and local-typing/conformance obligation; and
transport is applied only after `J_f`, `M_cap`, and `M_use` are premises. This
is reviewed bounded evidence, not source registration, theorem closure, or
production authority. The reviewer did not inspect compiler behavior, tests,
runtime acceptance, or exhaustive source-rule absence.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-captured-provider-registration-constructive-attempt.md`.
- Baseline SHA: `9e29dcb409db8e173959716a4abacbce40dcf0d5`.
- Changed dependency hashes: none; snapshot above. Recheck before integration.
- Review status: compiler-referee-reviewed bounded research; no theorem/gate closure or production authority.
- Checks already run: exact dependency/path reads and hashes; baseline/current dependency equality; final HEAD/dependency recheck and leased-path whitespace check. No tests/builds.
- Proposed commit message: `research: isolate captured-provider registration introduction`.
- Shared-record deltas left for primary/curator: record the registered-symbolic-root introduction as the earliest remaining producer, link this note as reviewed bounded evidence, and retain transport/activation/admission, origin/guard, soundness/principality/adequacy and production gates. No shared records were edited.
