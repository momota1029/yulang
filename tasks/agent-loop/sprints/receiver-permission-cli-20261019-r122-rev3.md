# Sprint R122 rev3 — nested receiver permission with a runnable surface

Revision 3; preserves [rev1](receiver-permission-cli-20261019-r122-rev1.md), SHA-256 `719147cba10a42485a1bd20e596d5ed95f8dd3e153ef44effed97b47fdd08180`, and [rev2](receiver-permission-cli-20261019-r122-rev2.md), SHA-256 `2017134e79146ffc08a991a883c970a7f683dd7397617d515eee18d4346a617f`.
Status: CANDIDATE pending CLEAN pre-spec review and Luna grant. Contract bytes
are frozen for that review; any repair creates a sequential revision.
Branch / baseline: `research/simple-sub-intrusion` at `a1d04100f6b6d175f4ca0ec20831ccba3f5d7e0e`.

## Goal and bounded outcome

Advance the proof-backed inference/evaluator goal with breadth and depth. This
sprint rotates to the wrong/sibling receiver-permission front and exercises the
public source runner early. It also advances §21 Computation-parameter role
correspondence for the exact nested source below: authentic annotated formals
must become the respective invocation receivers and retain their distinct
received views through nested entry. It does not prove a general effect or
role theorem.

The six effect fronts remain distinct and OPEN: ordered handler priority;
§21 Value/Computation entry; wrong/sibling permission; unmatched outward
request plus suffix; continuation capture/resumption; static-to-runtime
projection. R120/R121 supply finite CLI observations on fronts five/four;
R117 supplies a conditional binder bridge on six. R122 advances three with a
public CLI pair and applies same-HIR caller evidence to `R117-JOIN-1`. Method
syntax/role remains a parallel goal; R119's conditional M/T/A refinement is
kept intact and any syntax requiring the still-unadopted R85 design remains
behind its explicit semantic decision. Method/role is the next planned proof
slice after this receiver packet; effect-front rotation continues afterward.

For the exact positive/negative sources below:

1. Derive the source-owned identities, two annotated `[io] int` Computation
   formals, nested lexical resolutions, HIR retention, candidate actions,
   RuntimeProgram roles and two distinct invocation/view/receipt paths.
2. Establish why the positive helper's own received view has a local grant and
   why the negative's captured outer view does not, accounting for every
   `local_grant` eligibility alternative and the authentic receipt that the
   negative still has. Preserve the exact runtime outcome class.
3. Add one paired test-only observation at direct Machine and public stdin CLI
   layers. Positive must complete with integer 7 and CLI `7\n`; negative must
   reach `RuntimeUnavailable::HandlerEvidence` (not fail preparation), with no
   completed result, and CLI failure/empty stdout/existing runtime-unavailable
   diagnostic.
4. Prove the bounded `lib.rs::prepare/execute` caller handoff relevant to
   `R117-JOIN-1`: one immutable `Arc<HirModule>` is cloned into candidate
   solving and that same HIR is moved into `RuntimeProgram::from_hir`. Apply
   only this identity-preserving caller fact; source formation, successful
   candidate admission, execution and the wider R117 parent remain separate.

Falsifiers include changed formal/name ownership, conflated receiver views,
missing eligibility alternatives, negative preparation failure, positive
unavailability, either different public result, a second lowering or substituted
HIR in the caller route, or an unlisted owner/dependency needed for the proof.

## Exact sources and predicted outcomes

Positive P, UTF-8, 210 bytes, no final LF, SHA-256
`765a89c4cee89ceaf4213663b1be8e3110d0f81f4026d2112ddf4ee2f9a23780`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)
```

Negative N changes only `catch pending` to `catch thunk`, 208 bytes, no final
LF, SHA-256
`e1b42dbbbd1141c35857a552123e78f4bb8fe69d55bdd2429aaa6614f135705c`.

Expected direct Machine outcomes: P completes with integer `7`; N returns
`RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))`, with no
value. Expected public stdin CLI: P succeeds with stdout exactly `7\n` and
empty stderr; N fails with empty stdout and the existing
`runtime unavailable: HandlerEvidence(...)` error. Assert the error variant
and stable diagnostic prefix; do not pin Debug internals beyond the reviewed
source contract. Both CLI processes use `--run main --steps 30000 -`.

## Authority, frozen dependencies and exclusions

Authority: charter §21 for annotated computation receivers and §§14–15 only
for the exact handler selection/forwarding consumer. The approved top-level
inference principles govern source/solver separation. Reuse R96 only for its
actual exact nested source owners and conditional construction; the new
caller-to-same-HIR fact is checked against the current `prepare/execute` owner.
No language refusal, general permission/protection theorem, semantic adoption,
production change, or parent closure follows.

Frozen direct dependencies (SHA-256):

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
notes/theory/2026-10-19-r96-sibling-receiver-permission.md 2e6026e77d04fa6385e82ecf62cf9f0e63448bcd7619fb6500f11ca2789fe9a9
tasks/agent-loop/sprints/sibling-receiver-permission-20261019-r96.md 195468ceef7c5fe29aee157260e9f0c218a5dd3e95ed759c40f1f86b348d4892
tasks/agent-loop/inbox/20261019-r96-proof.md 84b3302c61e4a20e882552c960c95dadb5e9cb14bae80a5e9e810815f18de583
tasks/agent-loop/inbox/20261019-r96-implementation.md fb99947f978ab905bc65e5f7291ff38f18a74c062b2bc1fe2c5f85113f69b2d6
notes/theory/2026-10-19-r117-catch-payload-projection.md efd4a06e222e5de2bb546e3eb2cde1db1eba8710e7b42bda65b8139b1aea708a
tasks/agent-loop/inbox/20261019-r117-proof.md 36dda08e16d90bab40f87c92b969e8f4c7a4fcc0683c0658f0c7a7f05ec44f6a
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
tools/inference-playground/tests/runtime_receiving.rs 6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
tools/inference-playground/tests/cli_local_resume.rs c315daccfd28279192b0052f55c5558fa11133509291855129f744037633e747
tools/inference-playground/tests/cli_outward_root_suffix.rs c56e1a2a58900728e87069f3e467ceabaa4e91886dc6befd8e79268d8b630f06
```

No production code, expected-output fixture, diagnostic, language semantics,
method implementation, A/B claim, all-front theorem, source-domain narrowing,
R85 adoption or test retry is authorized. Existing tests remain unchanged; the
new CLI test is the only implementation output.

## Lanes, review, and one bounded command

After CLEAN pre-spec review and Luna's explicit grant:

- Proof lane `/root/r118_proof_lane`, Sol/high, cap 600 seconds. Writes only
  `notes/theory/2026-10-19-r122-receiver-permission.md` and
  `tasks/agent-loop/inbox/20261019-r122-proof.md`. Derive the two authentic
  source-to-candidate/runtime view paths, account for every positive and
  negative `local_grant` branch, prove the §21 annotated-formal role route
  conditionally, and trace same-HIR prepare/execute into R117-JOIN-1. State
  exact unmet admission/semantic premises. No commands.
- Implementation lane `/root/r118_implementation_lane`, Luna/high, cap 360
  seconds. Writes only `tools/inference-playground/tests/cli_receiver_permission.rs`
  and `tasks/agent-loop/inbox/20261019-r122-implementation.md`. Add one
  serial paired direct-Machine and public stdin CLI test. No production edits,
  existing-test edits, check, test, build, CLI, formatter or Git command.
- Once both producers stop, fresh compiler/source, spec/authority and
  regression reviewers inspect frozen outputs and all pins; no author reviews
  their own artifacts. Repair blocking/major findings only as Luna in a
  sequential revision, then obtain exact delta reviews.
- After all three required reviews are CLEAN, Luna runs exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_receiver_permission -- --nocapture
```

No alternate command, standalone build, probe, retry or fixture repair. A
failed command or outcome consumes the attempt and stays an open result.

Total cap: 1,800 seconds (inventory 180, pre-spec 120, proof 600,
implementation 360, post-review 300, command 120, closeout 120); Astra 0.
Preserve all three inherited UNKNOWN identities, the quarantined board lease,
and every other FROZEN lease. No capacity or unrelated path is reclaimed.

## Parent application and next breadth step

If the packet succeeds, it supplies (a) a finite, source-qualified wrong-view
runtime contrast and §21 role-correspondence witness, (b) direct/public surface
behavior, and (c) caller-to-same-HIR identity evidence applicable to R117's
join premise. It closes none of their quantified parents. Candidate solve,
source admission, HIR formation, terminal runtime assumptions and public CLI
outputs remain individually reported.

After R122, return to the method/role path with a source-owned proof objective
that does not silently assume R85 adoption; present the exact R85 decision only
when a concrete reviewed implementation gate is ready. Then rotate again among
the remaining effect fronts. Next selector boundary: sprint end, source or
authority counterexample, dependency drift, cross-lane seam, resource change,
or semantic adoption event.
