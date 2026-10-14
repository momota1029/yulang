# H1-B: callback profile and partial-operation source discriminators

Status: frozen, independently reviewed research characterization; no executed source counterexample.
Baseline: `242bf06f5f10c3fcbf2492491621c7f550b0308b`, branch `research/simple-sub-intrusion`.
Lease: this note only; complementary static leaf, not the H1-A constructive proof.
Budget: at most 15 minutes, no Cargo, builds, semantic probes, benchmarks, children or Git commands.

## Objective, authority and evidence class

Attack shortcuts that reconstruct callback eligibility from a direct formal-use
hint, empty native words, or nominal effect-family membership. Trace authentic
source constructors for omitted callbacks, aliases/captures/returned callbacks,
and two operations with one matching arm. Governing sections: top-level
principles §1.1; annotation hygiene §§1,3–5; contextual admission §§2–4; charter
§§13–20,24; boundary construction §§3,6; native residual P §§1,5.

The accepted meaning is fixed: callback protection follows the corresponding
typed value path while its receiver remains live; a local arm supplies no
contract for that callback. Selected arms and raw resumption run outside the
shallow handler. No constant evaluation, family-wide operation coverage,
zero-word unguardedness, universal handler classification or explicit-negative
formal map is inferred here. Ordinary unannotated local lambdas remain pure
under charter §24; the outer invocation remains live in the capture/return
controls below. Post-expiry protection is not asserted.

Established here means directly visible source construction at the hashed
snapshot. Program acceptance, graph readout and source/runtime behavior are
**unverified predictions** because no program was executed. The note neither
supplies a callback profile nor proves the native/source bridge U. Complete
Call, hygiene, soundness, principality, rigid generic opening and F5 remain OPEN.

## Minimal source controls

Use this shared declaration; `next` and `later` have identical ground signatures
and different declaration identities in the same family:

```yulang
act tick:
    our next: () -> int
    our later: () -> int
```

Each body below is a separate source input. For callback cases append
`my answer:[tick] int = relay tick::next`. Mutating only the output allowance to
`[]` checks whether tick still reaches the output. The explicit positive
allowance is a check at the result, not authority granted to cb inside relay.

| ID | Body | Distinction tested |
| --- | --- | --- |
| D | `my answer = catch tick::next() { tick::next(), _ -> 0, v -> v }` | Direct ground operation matching its own arm. |
| O | `my relay cb = catch cb() { tick::next(), _ -> 0, v -> v }` | Omitted callback invoked under an operation Catch. |
| A | `my relay cb = { my alias = cb; catch alias() { tick::next(), _ -> 0, v -> v } }` | Same callback through a local binding/fresh use. |
| C | `my relay cb = { my invoke ignored = cb(); catch invoke() { tick::next(), _ -> 0, v -> v } }` | Callback captured by a local lambda, invoked during the outer live receiver. |
| R | `my relay cb = { my forward ignored = cb; catch (forward())() { tick::next(), _ -> 0, v -> v } }` | Callback returned by a nested lambda and invoked before relay exits. |
| P | `my answer = catch tick::later() { tick::next(), _ -> 0, v -> v }` | Only next has an arm; later must remain unmatched despite family equality. |
| X | `my answer = catch tick::next() { tick::next(), _ -> tick::later(), v -> v }` | Same-family request in the outside arm. |
| K | `my answer = catch { my ignored = tick::next(); tick::later() } { tick::next(), k -> k 1, v -> v }` | Raw suffix contains later; k must not reinstall H. |

These are finite, ground, identifier/wildcard source shapes supported by the
inspected constructors and current preflight. No input uses generic operation
arms, guards, labels, tuple patterns or negative concrete formals. Exact parsing
of these newly assembled strings has not been run. Existing fixtures establish
that their constituent syntax and paths are present; they are executable
candidate-inference controls, not executable VM/native-runtime claims. The
playground README describes this exact parser → LocalSource → candidate route
and its graph/check output; it does not run program effects.

## Authentic source trace table

Locators below are relative to the repository. L =
`crates/yu-hir/src/module/local_source.rs`; S =
`crates/yu-solver/src/candidate_source.rs`; E =
`crates/yu-solver/src/candidate_effect.rs`; Apply =
`crates/yu-solver/src/shadow_apply.rs`.

| Path | Owning source/binder construction | Actual native consumer/effect contribution | Established distinction and remaining premise |
| --- | --- | --- | --- |
| Declaration / D,P | `source_annotation.rs:32–61,265`: resolved family ID and separate operation declaration ID; L:798 resolves `(family,member)` to declaration. L:827–912 retains the actual operation pattern and arm source. | S:538–555 → E:786 `candidate_operation`; E:1494 selects `declaration.id.family` for the outer invocation result-effect port; E:1528–1535 inserts family Support. Apply:1463–1501 creates the Function4 demand and invocation row; Apply:1545–1563 routes callee/invocation effects into application effect. | HIR knows next versus later. Equal signatures/family do not imply equal operation IDs. Ground preflight S:119–131 accepts either declaration, without requiring exhaustive family coverage. |
| O formal/invocation | L:386–412 makes the unannotated cb parameter and Lambda; S:260–272 registers its formal, S:284–287 gives Parameter endpoint, S:313–320 retains direct formal Name. S:582–599 retains actual Apply and direct `formal_name`. | `lib.rs:11254–11308` consumes parameter/body endpoints and creates entry/return effects with entry/body ≤ return. Apply creates ordinary later Function demand against the initially variable formal. | The constructor needs no prior known Function shape. Neither bare-formal construction nor an inert inferred-entry origin is an executable callback profile. |
| A local alias | L:960–1059 retains the local binder/initializer/final expression; initializer Name cb uses the original Parameter endpoint. S:470 installs initializer at local boundary; S:575,879 uses the local scheme route. | S:838–841 stages publication from the actual initializer; subsequent Apply uses the alias Component endpoint and normal native demand. | `formal_names` is populated only for Parameter Names, with wrapper propagation at S:604,630,655. A Local Name does not get that hint (S:568–578). Guard construction based solely on `ApplySourceInput.formal_name` misses this admitted route. This refutes that proposed shortcut, not current hygiene. |
| C captured callback | L:430–461 retains local lambda parameters while outer cb remains lexically bound; S:638–652 retains its LambdaRecipe with original body endpoint. cb inside invoke resolves to the original outer Parameter. | Same direct cb Apply route as O, now enclosed in the local lambda; entry/body effects flow to its returned effect. Local install/fresh use then carries invoke's Function to the Catch scrutinee. | Capture is a real lexical path, not a fabricated new formal. The direct cb hint may still exist inside invoke, so absence of the hint is not asserted for this path. Preservation through local capture/freshening and the exact active owner still need H1/H2 evidence. |
| R returned callback | forward's body is Name cb; S:638–648 stores `body_value_endpoint=Parameter(cb)`. `lib.rs:11269–11282` reads that original parameter as the lambda result. Block/Group and both Apply nodes remain actual source occurrences. | First Apply constrains its result to the returned callback; the second Apply places a Function demand on that result. Its callee is an Apply result, with no direct formal Name hint. | Ordinary result constraints retain the Value route. Neither the inner invocation's completion nor an anonymous result endpoint proves expiry of the still-live relay receiver; actual profile transport is missing. |
| All Catch arms | L:811–910 creates arm-local binder IDs; S:399–440 aliases value binders to scrutinee and retains ground operation payload/k actions only when referenced. | S:495–513 unconditionally routes the full scrutinee effect S to Catch output, and each arm's effect separately to that output. E:806–865 constructs packet fields/raw k; no Catch subtraction is installed. | Current forwarding preserves support conservatively and cannot demonstrate eligible removal. X stays an independent arm projection. No matching arm is implied by a value arm or equal-family support. |
| K raw suffix | Ground B=Int and original V come from the actual declaration/scrutinee; S:435 passes the original effect coordinate to E:806. | E:832–860 gives raw k response B, original V, fresh entry E/return R with E ≤ R and S ≤ R. k invocation contributes its return effect via ordinary Apply; response argument effects enter through E. | Whole S is a provisional upper bound, not exact suffix equality. It preserves an allowance for later outside H; neither handler reinstallation nor removal of later is supplied. |

The candidate Call artifact consumer confirms the hint's narrow meaning:
`candidate_call.rs:379–404` authenticates only a direct formal Name and the
Group/Ascription/Block routing spine. This authenticates that particular use;
it is not a certificate that other aliases/results lack inherited protection.

## Concrete identity discriminator and control predictions

P's membership is **family-wide**, established from the concrete code:
`SourceEffectId` derives Eq over module and family declaration
(`source_annotation.rs:31–35`); `SourceOperationId` additionally retains its
operation declaration (`:45–49`). E:1494 passes only the former into the outer
operation effect Support. `Contribution` retains effect/origin/instance and
View retains operation provenance, but E:995–1006 obtains only `effect` and
executes `allowed.contains(effect)`. It neither compares operation IDs nor
consults the arm coverage/profile/origin at this membership branch. Its tail
branch E:1008–1013 forwards only effects not in that allowed family set.

Thus a hypothetical P input containing contributions from both next and later,
with J={tick} chosen from a next arm alone, drops both at this branch. This is a
source-qualified obstruction to the proposed whole-scrutinee nominal filter.
There is no current wrong-subtraction counterexample: S:499 presently forwards
the full S. P remains valid under its original plain-input/U hypotheses; this
trace attacks supplying those hypotheses from family equality.

| Control | Current candidate prediction, NOT EXECUTED | Selected eventual distinction / targeted mutation |
| --- | --- | --- |
| D | `[tick] int` check accepts, `[] int` check conflicts because full S is forwarded. | With actual eligibility and consumption established, matched direct contribution may enter P. D alone cannot validate U. |
| O,A,C,R | `[tick] int` accepts and `[] int` conflicts. | Callback-derived contribution remains protected under the corresponding live typed path. Seed-only-at-direct-formal or empty-word shortcuts would risk erasing it after a future cut. |
| P | `[tick] int` accepts and `[] int` conflicts. | Later must survive a next-only handler. Add/delete a next arm without adding a later arm must not remove later. A J={tick} whole-S cut predicts a false pass for the empty check. |
| X | `[tick] int` accepts and `[] int` conflicts. | Even after direct next removal, outside later survives. Filtering the final output, rather than the eligible scrutinee projection, loses it. |
| K | `[tick] int` accepts and `[] int` conflicts. | Outside raw suffix later survives; conservative S can also retain next without claiming exactness. Filtering k's return or implicitly reinstalling H would be an invalid shortcut. |

These predictions rely on successful native admission/processing and actual
LocalSource formation. A structural recovery, Unsupported result, resource
deferral or unrelated type conflict invalidates the corresponding executable
discriminator; it must be reported instead of counted as a hygiene observation.
Current identical pass/conflict predictions across D/O/P are intentionally
insufficient to establish the eventual local distinction.

The zero-word objection is separate: `candidate_context.rs:116–135` stores
zero-sized left/right words; `:2581` seeds identity or a closed-check prefix;
`:2660–2705` transports inherited contexts through real Function ports;
`:2840–2905` executes zero-word checks. These facts do not turn omitted callback
source contributions into unprotected ones. No profile is assumed here, and no
detached PUSH is treated as live eligibility.

## Smallest discriminating code evidence and limitations

The primary's smallest useful observation seam is the existing source Apply /
Function-port relation and Catch scrutinee-to-output edge: record the original
formal owner/typed position, relation context and both native port parents for
O versus A/R, then verify the same active protection reaches the cb invocation.
For P record the two resolved operation declaration IDs before eligibility and
the exact contribution passed to P versus bypass; inspecting only the exported
family row cannot discriminate next from later. No new per-call token or
alternate solver is justified by this audit. Compiler instrumentation/tests
require the primary's separate exact-file authorization.

Oracle independence: no Oracle implementation or program ran. Source-rule
expectations come from the fixed governing decisions; implementation facts
come from the real source, not a checker whose transitions encode those
decisions. Agreement with these predictions would establish only this bounded
constructor/consumer evidence, not full semantics. Eight hand-selected controls;
no randomized seeds, enumeration ranges, runtime mutations, or omitted-search
claims. Generic arms, non-ground matching, runtime selection, activation expiry,
late-bound lifecycle transport and exact suffix precision are not covered.

## Frozen dependency snapshot, checks and commit packet

Read baseline checked by reading `.git/HEAD` and its named ref directly; no Git
command ran. Four packet-pinned source hashes and five governing hashes matched
dispatch. Auxiliary source/test/README hashes below freeze the additional live
reads; their equality to committed content was not independently inspected with
Git. All 17 listed hashes and the branch ref were rechecked unchanged before
freeze. Primary integration must validate the auxiliary committed-content seam
if concurrent source edits are present. No dependency was changed by this worker.

```text
a5fe26b4c5423468826842a618c8647af1d94a9ef135d18607999262977ead1a crates/yu-solver/src/candidate_source.rs
f4a8cb624204ae8afd4f2ab599048e71efc5022724130161d390058a09997d9d crates/yu-solver/src/candidate_effect.rs
ed2981e436e94353411b4a976c09872edd345e381a5847941a7908ffe04005e0 crates/yu-solver/src/candidate_context.rs
91938447f78b6ca6b252a67641f30c2e20f05193d112aa7f0019a87caf6f93e3 crates/yu-solver/src/lib.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074 crates/yu-hir/src/module/local_source.rs
f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38 crates/yu-hir/src/module/source_annotation.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831 crates/yu-solver/src/shadow_apply.rs
664999082a17e59457f0de7cca21a0cf6be6a968285f95c5e074f320ac576015 crates/yu-solver/src/candidate_call.rs
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484 crates/yu-solver/tests/candidate_operation_catch.rs
7e438b91ed03dbb52b644f78bc082232efd5164fd8d095d10373d826d2d7d0cb crates/yu-solver/tests/candidate_operation_source.rs
abde1ce8cd34cd52ba6143b7896555eeda112e4545fc5938f79c7a1c0a20e4d3 tools/inference-playground/README.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
81eed00aefed2948768290c6066d95463bac0fd2340b7e33d56227d7368ec59f notes/theory/2026-10-14-handler-boundary-construction.md
469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b notes/theory/2026-10-14-native-handler-residual-cut.md
503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a notes/design/2026-10-10-annotation-effect-hygiene-integration.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc notes/design/2026-10-10-contextual-attachment-admission-design.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
```

Checks: bounded `rg`, `sed`, `cat` source/rule reads; 17 unchanged SHA-256
dependency rechecks; no trailing whitespace, four balanced fences and final
newline (`0a`). No Cargo/test/build or
semantic-executable process, benchmark sample, Oracle run, child or Git command.
CPU/peak RAM not measured; only lightweight shell inspection processes. Requested
runtime: researcher leaf, no model/effort override specified in this packet;
observed effective settings unavailable. Applying yulang-proofs does not make
this worker the constructive prover or an independent reviewer.

Recommended next action: authorize one minimal H1 constructor/consumer observation
for O/A/R, with P as the compulsory partial-coverage control, before enabling H3.

Commit packet: exact leased path
`notes/progress/2026-10-14-callback-profile-source-falsifier.md`; baseline
`242bf06f5f10c3fcbf2492491621c7f550b0308b`; changed dependency hashes: none by
this worker, rechecked snapshot required before integration; one fresh
independent compiler-referee found no blocking or major issue. This remains a
research characterization, not an executed source counterexample or U/H1 proof.
Checks already run are listed above; no source execution. Proposed message:
`research: trace callback alias protection and partial-operation residual controls`.
Shared-record deltas intentionally left to primary/curator: record family-wide
P membership and direct-formal-hint insufficiency as bounded source findings,
retain U/H1–H4 and all parent theorem/cutover gates OPEN, and assign the actual
profile/port and operation-coverage evidence to their owning constructors.
