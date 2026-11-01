# R178 proof handoff — original App admission and finite Checking

Status: FROZEN revision 1, **BLOCKED_ORIGINAL_APP_ADMISSION**, unreviewed. No theorem was constructed;
no Lean module was written and no Lean command was run. This is an exact
source-qualified missing-premise report, not a soundness counterexample.

Owner/session: `/root/app_demand_original_checking_r178_proof`, registered
`lean_prover`, current assignment session. Baseline: `yulang3` at `8fbcfcd6d`.
Sole output leases: this file and
`notes/theory/lean/YulangClosure/AppDemandOriginalCheckingR178.lean` (absent).
The existing pinned `.lake` was exclusively reserved to this lane and was not
read or modified by a build/check. No cache/environment/scratch was created.

## Fixed claim, authority and source scope

The parent remains `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:127–130`:

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The same `e` must prove the original source judgment and relate to the same
solution `a`. No quantifier or source constructor was removed. The current
packet selects only the original App value premise, leaving computation,
complete Call, full Build, and the shared witness downstream.

The governing inference principles (2026-10-11, Authoritative) retain actual
constraint inference and independent correctness obligations. The selected
source-Generalize definition/proof, §§2–3.3, requires independent local source
rules and finite checking. In §3.2(4), Function checking concludes
`D_checked ⊆ D_source` and whole-tuple observation inclusion for each checked
challenge on the same actual callable. L3/L4/L5 are genuine local obligations,
not solver-success assumptions. The source safety manuscript's opening
correction/status notice and the semantics integration guide are research
evidence, not blanket authority for candidate policies.

The exact source rule is `YulangClosure.OriginalSource.sourceRules`,
`OriginalSourceGeneration.lean:111–123`, for
`Source.app ⟨site,none⟩ callee argument` in original `Γ`. It introduces
`b := ⟨site,.viewLogic,0⟩`, then checks

```text
g := ⟨.value,site,Γ,⟨callee.site,.returnedValue⟩,⟨site,.descriptor⟩⟩
∃ v, original.admitted ρ b v ∧ Checking original (ρ.extend b v) g
```

This is the unchanged R177 target. Callee returned value is its subject;
the application's result endpoint is not substituted for it.

## Exact retained native operands and attempted construction

`shadow_apply.rs:4302–4388` constructs, for the retained source-owned Apply
owner and occurrence, `D− = NegativeFunction(U+,Eu+,J−,R−)` and admits
`F+ ≤ D−`. Here `F+` is the actual callee endpoint, `U+` the argument value
endpoint, `Eu+` its argument-effect endpoint, `J−` the fresh invocation-effect
endpoint, and `R−` this application's result. It retains the native tuple
before admission, together with the source-call indices/checking occurrence
and cause. Those source identities must remain fixed in any interpretation.

For an actual positive Function `L` against this negative demand `U`,
`lib.rs:14905–14936` generates exactly:

```text
U.argument+     ≤ L.argument−
U.argumentEff+  ≤ L.argumentEff−
L.resultEff+   ≤ U.resultEff−
L.result+      ≤ U.result−
```

`candidate_context.rs:3924–3987` retains the parent source set and scoped flow,
uses Swap/Swap/Preserve/Preserve, and installs argument-effect stamping or
result-effect protection from the authenticated demand. These operations
supply native endpoint/context relations. They do not construct an original
`Logical` packet or a finite original `Checking` tree.

Attempting the existential first requires constructing an actual
`OriginalSourceEnvironment.Logical s View` (`:249–254`): descriptor and
interface entries, full view interpretation, assignment, and joint witness,
interpreting that same demand and whole argument in the original scope.
`scopeCandidate ρ occurrence (.logical .viewLogic data)` supplies the original
parent path mechanically, but `admitted_scoped_iff` (`:648–653`) then leaves
this exact local goal:

```text
admissions.logical state b .viewLogic data
```

`LocalAdmissions.logical` is declared at `OriginalSourceEnvironment.lean:
599–600`; the logical case of `DataAdmitted` at `:611` requires that predicate,
and `Admitted` at `:638–642` additionally requires the actual environment
readout. No audited native Apply operation supplies this original App-local
admission or its descriptor/whole-interface interpretation. Selecting arbitrary
fields or assuming this predicate would supply the missing conclusion as a
premise; it would not construct the required original admission.

`OriginalFormalAdmission.localAdmissions` (`:122–132`) does provide a concrete
local constructor for an actual Lambda/formal `Introduction`. Its `ViewPacket`
(`:55–66`) references the selected formal declaration and writes no descriptor
or interface entries. It delegates other source binders to `base.logical`.
The actual App occurrence is not a Lambda-formal Introduction; equating those
owners or repurposing that constructor is unsupported. This is the first
missing supplier, before a native comparison-to-finite-proof induction can
start. `candidate_call.rs:397–438` independently retains OriginalGenCall0 and
whole-carrier/complete-result suppliers as pending; those labels are not a
proof of untypability.

## Finite checking obligations retained after admission

Even if an authentic App admission were supplied, the native four comparisons
must be justified as the original finite recursive children.
`OriginalSource.Checking.function`, `OriginalSourceGeneration.lean:705–713`,
requires an original `functionShape`, a finite `.domain` child, and a finite
`.observation` child for **every** original `checkingAdmitted` invocation in
its extended environment. No visited-native-pair rule is a Checking constructor.
A genuine recursive equation pairing needs its original finite derivation
or a separately justified cycle interpretation; this lane asserts no cycle
counterexample or automatic finite unfolding.

`OriginalSourceChecking.FunctionShape` (`:823–839`) keeps reversed domain
endpoints, preserved observation endpoints, original contexts, and an actual
`Proof` for every probe. Its `Proof.functionStep` (`:231–250`) separately needs
same-provider guard and capture transports, checked-domain inclusion for every
challenge, and observation transport for all raw observations on the whole
joint tuple. Endpoint shape or scalar port inclusions do not discharge those.

`OriginalCheckingAdmission.goal_function_checking_constructor` (`:330–365`)
constructs a finite Function node **from** the supplied finite domain and
universally admitted observation Checking children and its stated original
shape/readback/guard/capture premises. It does not derive those from solver
ports. `OriginalFunctionFuture.function_observation_child_at_actual_event`
(`:156–180`) uses an already checked child at the actual incoming event and
preserves the raw input/prefix. It avoids identifying future events with the
creation event, but does not generate the missing child or the App admission.
The current-event `.domain` reading at `OriginalSourceChecking.lean:1085–1087`
also cannot silently replace the all-event value obligation (`:1075–1081`).

Consequently no existing law inspected here closes the selected existential.
The exact next construction belongs jointly to the App original-rule admission
owner and the candidate comparison-preservation owner: interpret this retained
source-owned demand as its independently admitted original complete descriptor,
then prove the original finite domain and all-invocation observation children
with the required guard/capture/event and recursive justification. Full Call,
other App atoms, computation Checking, all language cases, and one shared
same-solution `sameScoped` witness remain OPEN. No production authority follows.

## Input authentication and material process evidence

- Rev1 contract SHA was
  `92b981b295dfa70de5c90a20ec952a254d0e3f2bb9bd1cb62ab6313f21bb79f6`.
  The initial verifier matched only full 64-hex rows, reported 30 matches, and
  silently omitted the malformed 63-hex candidate_scheme row. That ACK was
  incomplete. No candidate_scheme content was read. On primary notice the
  lane paused and disclosed its already completed pinned/operating-source
  reads; no writes/checks/builds had occurred.
- Rev2 contract SHA was
  `255bf8ed15a0a87c9171ac8f54a06e74e9930741b66e2b87be4678966b9c04f8`.
  Strict enumeration verified all 32 direct rows, every full SHA-256, before
  resumption. Rev2 content inspection stopped at the unpinned environment and
  syntax owners; neither was read before admission.
- Current rev3 contract SHA is
  `a1c9ae675762370ae56f27015a122f5f07a10466742333f8f7dcb3c111152b10`.
  Strict enumeration verified all 37 direct path rows, every full SHA-256,
  zero malformed rows or mismatches, before newly admitted content reads.
  Dependency hashes are the exact immutable rev3 contract values; none changed.
- One search mistakenly used the broad glob `OriginalSource*.lean`. Its output
  contained only pinned OriginalSourceGeneration/OriginalSourceChecking hits,
  but rg may have scanned additional matching files. This was disclosed to
  primary immediately; no unpinned content was output or used. Later commands
  use explicit paths. This scope mistake is retained rather than erased.

Commands were read-only `rg`, `sed`, `nl`, `cat`, Python SHA-256/enumeration,
and one write of this sole handoff. Short commands exited 0. No theorem was
constructed, so contractually **zero Lean/Lake/version/build commands** ran.
Lean 4.35.0 is the contract pin, not a newly measured version receipt.
Delivered theorem types and axiom audits: none; no claimed kernel acceptance.
No tests, Cargo, runtime, environment/cache/scratch or compiler edits occurred.
CPU/RAM peaks were not measured; only short source/hash processes ran within
the finite 1200-second assignment budget, excluding primary-directed pauses.

Coverage is the exact App existential and the potential finite Function case;
no constructor is claimed proved or removed. This author cannot provide
independent review. The only changed path is this handoff; the leased `.lean`
path remains absent. Shared task records and Git belong to primary.

STOPPED: reads and writes are finished; no build/check/cache process is running.
