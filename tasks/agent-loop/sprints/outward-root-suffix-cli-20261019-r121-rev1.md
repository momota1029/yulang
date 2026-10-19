# Sprint R121 — outward forwarding with a live root suffix and runnable control

Status: CANDIDATE pending fresh pre-spec review and Luna's grant. This revision
is frozen for review; any repair creates rev2 and preserves rev1.
Branch / baseline: `research/simple-sub-intrusion` at `0d33b715b9f311674ec7ebf125b9d2f73d70f037`.

## Goal and bounded outcome

Advance the original proof-backed inference/evaluator goal while keeping effect
hygiene broad and source execution visible. The six distinct effect fronts stay
separate: ordered handler priority; §21 Value/Computation entry; wrong/sibling
permission; unmatched outward request plus suffix; continuation capture and
resumption; static-to-runtime projection. R121 advances only the fourth front,
uses ordered matching as a control, and checks an effectful public execution.
It does not extend storage/fiber analysis or claim progress on the other five.

R119's reviewed conditional method/role source refinement remains part of the
same overall goal. Method execution is a separate in-scope future vertical path;
its M/T/A producer and admission premises remain open, and R85 remains an
unadopted Draft requiring an explicit user decision before dependent code.
Ordinary/effectful CLI cells already run; R121 strengthens the effectful surface
with two actual source roots and a positive/negative pair. Original Simple-sub
and evaluator A/B claims and quantifiers remain unchanged and open.

For the two exact sources below, provide (1) a finite source-to-machine trace
that distinguishes matching from unmatched forwarding and identifies the
actual still-live second expression root in the saved return cursor, and (2) a
test-only pair of direct-Machine and public stdin CLI observations. The trace
must establish that an unmatched first root stops with the original `tick`
request before the real second root and selected `main` fallback execute. It
must not describe the continuation as carrying a copied root schedule.

## Exact inputs and predicted public outcomes

Both sources are UTF-8, contain no final LF, and are distinct from R113's
fixed recipe. Each has two source expression roots followed by a separate
selected-definition fallback. The positive control changes only the first
handler's operation pattern.

Negative, 159 bytes, SHA-256
`685aa2465d5a5b47d18447762637107b4cb0da5971d384fad7bc1ad56937448f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
catch io::tick 7 { io::other(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7
```

Positive control, 158 bytes, SHA-256
`11f811ba795dfc8420aadd0706221fe14f1efa9a192b902bda5b7816d627924f`:

```yu
act io:
    our tick: int -> int
    our other: int -> int
catch io::tick 7 { io::tick(p), _ -> 99 }; catch io::other 23 { io::other(q), _ -> q }; my main = 7
```

The positive public CLI prediction is success, stdout exactly `7\n`, stderr
empty: the first handler matches `tick`, the second root handles `other`, and
only after both roots finish does selected `main` produce 7. The negative
prediction is failure, empty stdout, and the existing unhandled-request
diagnostic: the first handler does not match, so original `tick` escapes and
the retained suffix does not run. The static identity of the later root and
original HIR operation occurrence must be established separately from CLI
depth or text order.

## Proof/source obligation

Starting at the authentic HIR item sequence and LocalSource constructors,
establish the two `ExecutionRoot::Expression` entries and their order, then
follow RuntimeProgram schedule formation and Machine root entry. In the
negative source, trace `tick` resolution and payload 7 through ordered handler
selection and the exhausted shallow handler. Show from the actual saved frame
and cursor that the pending root completion points to the already-existing
second expression root in the machine's live schedule. Establish terminal
request publication preserves the original operation identity, payload and
source occurrence; the second root and `main` fallback have not executed.

For the positive control, trace the first handler's `tick` match and the second
root's `other` match to normal completion, followed by selection of `main` and
public value projection. This is finite evidence for the exact candidate route,
not a general effect-hygiene or evaluator theorem.

Falsifiers: either source fails authentic preparation; expression roots are
missing or reordered; the saved cursor does not designate the actual second
root; the negative case changes request identity/payload/source, executes its
suffix or reaches `main`; or either public CLI outcome differs.

## Authority, exact frozen dependencies and exclusions

Apply charter §§14–15 to shallow selection, outside-arm execution and
forwarding; use §§21–24 only where the exact source path requires them. Source
root order follows the approved module-expression owner and initialization
order. Pin all inputs before assigning either writer; any hash mismatch or
needed unlisted owner returns to Luna.

```text
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-16-initialization-order-global-effects.md e2f70f535319522261cc6f52592d62b491d9d0e9d32e14310ac5d9fb81ee1bb6
notes/design/2026-10-16-module-expression-source-owner.md ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5
notes/design/2026-10-16-source-remaining-root-constructor.md 4f9c483b6f3ca7a41ba3af622f91c17446823724269f2f1473b844b9f534cbd5
notes/theory/2026-10-16-runtime-module-expression-roots.md 915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694
notes/theory/2026-10-16-source-remaining-root-contract-construction.md 058c6606ece58867587b20fbb7dcf3ed9de1171b7eb4bb1e071489276c72781a
notes/progress/2026-10-19-r113-module-request-suffix.md a3dc4937b41bda6fe8570cc329987b584bfb704ded5012bb4fab0d0ac7078e49
tools/inference-playground/tests/runtime_primitive.rs 2b6a99690e43442c9553786c420c7108bcc8d8d9974391b4f677b73572bac3db
tools/inference-playground/tests/runtime_module_expressions.rs 8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/tests/cli_entry_publication.rs ac2ba1cb201f35c79dbc67d140012b2c5db4b43c2395efe804be7e9a11f9535e
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
```

No production runtime/source changes, inference changes, semantic adoption,
diagnostic or expected-output edits, R113 retry, test repair, nested proofs,
whole-program theorem, all-six-front closure, method implementation, or A/B
closure. R113's prior partial result remains intact. The runtime proof may use
only the listed inputs. The implementation may inspect these plus its new test
file; a new dependency is a Luna decision before writing.

## Leases, parallel lanes, and gates

After CLEAN pre-spec review and Luna's grant, retain the actual existing worker
identities and issue these exact disjoint leases:

- Proof lane `/root/r118_proof_lane`, Sol/high, cap 600 seconds; writes only
  `notes/theory/2026-10-19-r121-outward-root-suffix.md` and
  `tasks/agent-loop/inbox/20261019-r121-proof.md`. No commands. Construct the
  finite source/native trace, apply it to both exact cases, state the earliest
  source/admission/runtime premise not established, and preserve all remaining
  parent gates.
- Implementation lane `/root/r118_implementation_lane`, Luna/high, cap 360
  seconds; writes only `tools/inference-playground/tests/cli_outward_root_suffix.rs`
  and `tasks/agent-loop/inbox/20261019-r121-implementation.md`. Add one
  serial test covering both positive and negative inputs. The direct-Machine
  cells authenticate two ordered expression roots and check completed positive
  value versus the negative original operation, integer payload 7 and actual
  HIR source provenance. The public stdin CLI cells use `--run main --steps
  30000 -`; assert positive success, stdout exactly `7\n`, empty stderr, and
  negative failure, empty stdout, existing unhandled-request diagnostic with
  range grounded in the HIR occurrence, and no completed receipt. Do not run
  the test or any command.
- After both writers stop, assign fresh independent compiler/source,
  spec/authority and regression reviews, sequentially within 300 seconds total.
  Review proof/source correspondence, both CLI outcomes, root and request
  identities, diagnostic provenance, untouched fixtures/expectations, and all
  pins. No author/coauthor can review its artifact.
- Luna runs exactly one command only after all three reviews are CLEAN:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_outward_root_suffix -- --nocapture
```

No standalone build, formatter, direct CLI, probes, alternate command or retry.
A failure/timeout consumes the sole attempt and leaves the observation open.

Total cap 1,800 seconds: inventory 180; pre-spec 120; proof 600;
implementation 360; post-output reviews 300; command 120; closeout 120.
Astra 0. Preserve three inherited UNKNOWN reservations and the quarantined
board lease. The two producers may run concurrently; reviews start only after
both stop. Stop on missing owner, dependency/authority drift, blocking review,
falsifier, or exhausted cap.

## Parent application and stop conditions

Before/after evidence is the exact finite link from two authentic source roots
to (a) successful handled execution of both roots and later `main`, and (b) an
unmatched original request whose continuation still points at the live
unexecuted second root. A pass reduces only this source-qualified outward
suffix premise. Green tests alone prove no mathematical parent.

All six effect parents remain open, including the other five unadvanced fronts;
all original Simple-sub/evaluator A/B, method/role M/T/A and R85 adoption stay
open. No method semantic decision follows from this sprint. The next material
selector boundary is counterexample, missing authority/dependency, resource
change, user adoption of R85, cross-lane integration, or sprint end.
