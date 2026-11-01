# R178 source handoff — Function comparison and original App admission

Revision 1; FROZEN. Author/session: `/root/app_demand_original_checking_r178_source`.
Baseline: `yulang3` at `8fbcfcd6d`. Claim class: bounded static source
correspondence; outcome **BLOCKED_ORIGINAL_APP_ADMISSION**. This handoff
constructs neither an original Checking proof nor an accepted-source
counterexample. The unchanged `SourceProblem.InferenceSoundness` parent and
one shared same-solution `sameScoped` witness remain OPEN.

## Dependency receipt and method

R178 rev1 contract SHA was
`92b981b295dfa70de5c90a20ec952a254d0e3f2bb9bd1cb62ab6313f21bb79f6`.
Strict pre-content verification found 31 listed paths: 30 valid SHA-256 rows
matched, while `candidate_scheme.rs` had a malformed 63-hex digest. The actual
file hash was `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`.
The lane reported this and STOPPED before source-content reads. No claim of
successful verification of that malformed row is made.

Sequential rev2 SHA
`255bf8ed15a0a87c9171ac8f54a06e74e9930741b66e2b87be4678966b9c04f8`
had 32 listed direct paths. Every row was parsed, required to contain exactly
64 lowercase hexadecimal digits, and recomputed successfully before content
reads. The lane paused at the newly named `candidate_scope.rs` owner.

Sequential rev3 SHA
`a1c9ae675762370ae56f27015a122f5f07a10466742333f8f7dcb3c111152b10`
had 37 listed direct paths. The same strict parser verified all 37 with zero
malformed rows or mismatches before resumption. The sole output lease remained
this handoff. Revision admission changes the dependency set, not the parent
meaning or outcome. The prior R177 verification overclaim is governed by the
primary's pinned correction records, not silently repaired here.

Method: inspect only pinned Rust producers, continuation/dispatch and pure
comparison/replay representation, comparing their actual premises with the
independent original finite Checking constructors. Existing original source
rules supply the semantic reference; this lane did not create an oracle that
assumes the solver transitions. No executable experiment, enumerative range,
seed, mutation, Rust execution or semantic counterexample was used.

## Exact retained Apply operands

Preserve the R177 source-owned Apply occurrence, exact callee/argument source
indices, checking occurrence/cause and the same candidate session. In
`shadow_apply.rs:4302–4388`, the producer constructs

```text
D− = NegativeFunction(Vargument+, Eargument+, Jinvocation−, Rapplication−)
Vcallee+ <: D−
```

Its native record retains that exact callee, argument, callee evaluation effect,
argument evaluation effect, result, demand, invocation effect/row and application
effect before constraint admission. Source occurrence must match the recipe and
no prior native interface may already be installed. This is source incidence
and native construction evidence. The nearby comment explicitly gives that
retained registration no semantic consumer.

`shadow_apply.rs:4424–4444` separately admits `Ecallee+ <: Eapplication−` and
`Jinvocation+ <: Eapplication−`. The argument effect is already a demand port;
absence of an additional direct edge is not a demonstrated counterexample.
No strict/eager argument interpretation is introduced.

## Function children and continuation

For positive Function `L = (A_L−, E_L−, J_L+, R_L+)` and negative demand
`U = (A_U+, E_U+, J_U−, R_U−)`, actual dispatch in
`lib.rs:14905–14936` constructs exactly:

| Field | Child comparison |
| --- | --- |
| Argument | `A_U+ <: A_L−` |
| ArgumentEffect | `E_U+ <: E_L−` |
| ResultEffect | `J_L+ <: J_U−` |
| Result | `R_L+ <: R_U−` |

These are two contravariant and two covariant polarized comparisons. They are
not by themselves the original same-callable checked-domain and whole joint
observation theorem.

The parent typed pair is admitted with pending diagnostic completion and actual
value-child diagnostic edges before dispatch continuation is installed
(`lib.rs:14937–14955`). `candidate_context.rs:59–103` retains the stage,
current work item/relation, source occurrence/cause, previous processing,
consumed flag, transition count, replay acknowledgements and four Function
children with `next` and `pending`. `candidate_step_function_dispatch`
(`lib.rs:15060–15087`) first admits a child's relation, retaining the pending
work item, then enqueues that item before advancing the cursor. Children are
selected in reverse array order and pushed to the front, preserving the array
processing order. Child admission is not synonymous with completion or a
finite semantic proof.

`candidate_function_port_admit` (`candidate_context.rs:3924–3987`) records
FunctionPort operations `Swap, Swap, Preserve, Preserve`; it propagates the
parent's exact source set and scoped flow. Argument fields swap inherited
nonidentity context; child-local prefix authority precedes inherited context.
An active demand must authenticate against that exact parent's negative
Function root, and the inherited scoped transformer must be identity. The
active demand is consumed for the child: argument effect receives
`stamp_input(demand.input)`, result effect receives
`protect_body(demand.output_scope,demand.input)`, value ports receive identity.
These are actual context/provenance guards, not original registered semantic
function guards or capture implications.

In `candidate_scope.rs:1–4,102–119,179–210`, a transformer changes finite input
route tags and protection scopes only. Stamp unions its input into route tags.
Protect retains existing protection and adds its scope when the initial input
tag is absent. Effect members and capture grants are explicitly outside this
state. This trace cannot treat those operations as a supplier of the original
capturedFields or complete raw-observation premises.

## Original finite constructor obligations and first missing supplier

`OriginalSourceGeneration.lean:690–713` has finite `Checking.identity`,
`primitive`, `compose`, `structural`, and `function` constructors. Actual native
operations above supply none of these constructors as a registered original
proof artifact:

- Native endpoint equality/canonicalization is not equality of the original
  source endpoints required by `identity`.
- Pair admission and conflict diagnostics do not register the original
  declaration/primitive proof required by `primitive`.
- Bound propagation/replay does not supply two original derivations with an
  independently interpreted common original endpoint for `compose`.
- Four native Function ports do not supply an original structural-shape proof
  and recursively checked original child list for `structural`.
- `function` additionally needs original `.domain` and `.observation` goals,
  an invocation binder, original `functionShape`, a finite domain derivation,
  and an observation derivation for every original admitted invocation.

The original `FunctionShape` (`OriginalSourceChecking.lean:823–837`) reverses
the same goal's endpoints for domain, preserves them for observation, preserves
context, and requires finite proof syntax for every probe.
`Proof.functionStep` (`OriginalSourceChecking.lean:231–247`) explicitly requires
same-provider function guard and capture proofs, checked-domain transport for
every checked challenge, and observation transport for every raw observation
of that same challenge. `function_value_check:578–602` retains these obligations
at every original event. Neither scalar result/effect comparison nor endpoint
shape proves the universal observation implication.

The earliest missing supplier is already the original admitted App logical
packet: the retained native tuple has not been interpreted into the independent
original descriptor/interface and admitted ViewLogic in the original source
context/event scope. The proof lane located its concrete admission owner at
`OriginalSourceEnvironment.lean` (`LocalAdmissions.logical:599–600`,
`DataAdmitted:611`, `Admitted:638–642`); this source lane reports that location
as the proof lane's finding, not an independently inspected derivation.
`OriginalFormalAdmission.localAdmissions:122–132` is Lambda-formal admission,
not a supplier for this App. The primary froze R178 on this first missing
supplier, before any downstream cycle conclusion.

Thus the unchanged exact R177 goal is still unconstructed:

```text
same source-owned Apply/callee/argument and actual Function comparison
  ⊢ ∃ v, original.admitted ρ ⟨site,.viewLogic,0⟩ v ∧
       Checking original (ρ.extend ⟨site,.viewLogic,0⟩ v)
         ⟨.value,site,Γ,⟨callee.site,.returnedValue⟩,⟨site,.descriptor⟩⟩
```

This is a missing construction/preservation proof, not a false original typing
judgment or a concrete accepted ill-typed program.

## Recursive behavior and bounded comparison representation

`lib.rs:13593–13602` shows candidate duplicate suppression requires both an
existing raw typed pair and the actual processing relation completed in the
current intrusion generation. `dispatch_live_item:14540–14570` executes this
check before re-decomposition. Context processing occurs earlier in the drain
(`lib.rs:14430–14472`), so this is not merely an endpoint-only cache.
`record_typed_pair_admission:15400–15475` calls `mark_candidate_pair` and retains
pending diagnostic state; it does not construct finite original Checking.

The exact generation-marking/cycle owner is the unpinned
`crates/yu-solver/src/candidate_intrusion.rs` (module declared at `lib.rs:225`).
The lane STOPPED at this owner and did not read it. Completion/invalidation and
cycle-cut semantic justification are **UNVERIFIED**. No claim that its suppression
is unsound, acyclic, well founded, or an original finite derivation is made.

The inspected pure comparison/replay representation is narrower than the
complete source Function semantics. `f5c_generalization.rs:450–502` represents
Function value argument/result with pure `Empty`/`Bottom` effect variants.
The Function walker (`:7778–7848`) checks both effect ports with
`pure_function_effect`, taints invalid drafts, reverses argument polarity and
retains result polarity; `ExitFunction` rebuilds the two value children.
`f5c_replay.rs:913–965` reconstructs positive/negative Function with those pure
effect constants and retained argument/result polarity. These are representation
constructors, not a proof of arbitrary complete Call observations/captures.
Recursive variables are copied by the inspected replay cases (:793–794,
837–838); no finite original recursive Checking derivation follows from copying
a recursive ordinal. Full generalization cycle semantics was not audited.

## Checks, resources and disposition

Commands: Python strict SHA-256 validation, bounded `rg`/`sed`/`cat` reads and
one leased Markdown write; successful commands exited 0. A bounded `rg` search
for original function guard/capture registry names in the five inspected Rust
owners returned no matches (exit 1), which is only lexical absence evidence.
No Rust/Lean execution, tests, Cargo/build, cache/environment/scratch creation,
compiler edit, manifest change, Git mutation or shared-record write occurred.
CPU/RAM peaks were not measured; only short read/hash/write processes ran.
The assignment used the 900-second source lane and primary-directed pauses;
this handoff does not assert an independently measured wall-time receipt.

Recommended next action: construct the source-directed original App logical
packet/admission from the exact native producer, then prove the original finite
domain and universally admitted same-callable observation children. The first
packet must retain original meaning; an assumed admission-to-Checking relation
would leave the blocker untouched.

STOPPED: this exact leased handoff is frozen. No further source reads, writes,
checks or builds are running. Independent review remains pending.

Commit packet:

- Exact leased path: `tasks/agent-loop/inbox/app-demand-original-checking-r178-source.md`.
- Baseline: `8fbcfcd6d` (`yulang3`, primary-pinned).
- Dependency changes: sequential rev1 → rev2 → rev3 contracts as recorded;
  no source dependency was modified by this lane.
- Review status: unreviewed bounded static source evidence; R178 BLOCKED and
  original parent OPEN.
- Checks already run: strict rev1 incident detection, rev2 all 32 and rev3 all
  37 direct hashes; static source inspection only.
- Proposed commit message: `Record R178 original App admission blocker`.
- Shared deltas left to primary: STOPPED observation; exact frozen artifact
  hash/review intake; original App admission blocker; downstream Function
  checking, cycle semantics, complete Call/effects and shared sameScoped OPEN.
