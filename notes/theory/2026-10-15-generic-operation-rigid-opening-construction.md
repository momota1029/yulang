# Generic operation opening: selected source rule and current construction gap

Date: 2026-10-15
Status: Frozen research checkpoint; unreviewed bounded source characterization
Claim class: source-rule calculation and minimized implementation obstruction;
no new established theorem, executable probe, or implementation authority
Baseline: `research/simple-sub-intrusion`,
`871d2ecb559f064dc034501b8bfe8c9bd6659876`
Lease: this file only

The original packet's SHA was malformed. The primary explicitly confirmed the
SHA above after the leaf reported the discrepancy. All substantive compiler
reads below use committed baseline bytes (`git show HEAD:<path>`), not the
concurrent structural-certificate changes in the working tree.

## 1. Frozen objective, scopes and exclusions

For one operation declaration
`Delta |- p : forall rho_family,beta_local. Sigma(rho,beta)`, fix a known
admitted family instance `rho`, a source arm body `h`, its annotations and
captured environment `Gamma`, and one joint assignment `nu` to captured/shared
endpoints. `Delta` contains the rigid imports and already-shared endpoints.
`beta_local` is the declaration-owned tuple absent from the family parameters;
it includes local callback-effect binders wherever they occur. Coincidence of
assigned values does not change ownership.

For every actual selected request `q`, let `theta_q` be its retained declaration
instantiation, fixing `Delta` and this family instance, and let
`s_q = theta_q(beta_local)`. Its complete packet contains payload
`A(rho,s_q)`, response interface `B(rho,s_q)`, raw continuation
`B(rho,s_q) => J_q(rho,s_q)`, profiles/evidence, symbolic `K,D` and latent
dependencies. Dependent `J_q` is inside the package. The operation use chooses
`theta_q` once; lookup of that already-instantiated value, aliasing, emission of
another dynamic event and raw resumption do not independently freshen it.
Different separately typed declaration uses may retain different maps.

Required conclusion: the arm's one source checking derivation opens the complete
package under one fresh rigid tuple `kappa`, with every dependent field mapped
jointly; checking assumptions are the declared interface/bounds and fixed
captured environment. Caller-private `s_q = Int` must not become the assumption
`kappa = Int`. A successful uniform derivation may specialize jointly at each
retained `theta_q`, preserving aliases, raw resumption and all dependent roots.
No request may be discarded to make this conclusion true.

The original checking order is retained:

```text
exists Z_shared.
  forall kappa_local.
    DeclBounds(rho,kappa) implies
      exists Z_body. BodyConstraints(Gamma,rho,kappa,Z_shared,Z_body).
```

Here a single finite source body/consumer derivation is required; separate
pointwise elaborations at concrete witnesses do not satisfy it. `Z_shared`
stays outside the universal. Body-local witnesses retain their inner scopes;
nested declaration binders retain their original scopes. The fixed captured
assignment is never solved again per event.

The requested derivation's existing hypotheses are declaration well-formedness
and bounds, a substitution-stable checked body template, the actual primitive
typing laws, typed Flow along actual paths, and well-formed store/raw-suffix
interfaces under the current resumed state. Their truth for arbitrary source
arms is not inferred from this formula or from stored constraints.

Excluded conclusions: complete inference/checking or completeness, lifecycle
preservation and arbitrary effectful generalization, principality, full Call,
full handler/effect hygiene, global soundness, F5 cutover and any compiler change.
No value restriction, source escape ban, annotation requirement or restriction
on ordinary inference is introduced.

## 2. Exact authority and reuse boundary

The governing decisions are [charter §§19–20](../design/2026-09-29-scc-intrusion-redesign-charter.md#19-user-correction-a-generic-operation-arm-cannot-narrow-its-local-type-binder-2026-10-02),
baseline lines 500–570. §19 explicitly rejects the `sink::put` arm containing
`my checked: int = x`, including when every selected caller supplies Int. §20
selects existential opening as source typing and requires the joint dependent
packet. These user-selected decisions govern this scope despite the charter's
broader research status.

[Operation-instance package](../design/2026-10-02-operation-instance-binding-package.md)
§2, lines 37–112, fixes declaration ownership, single instantiation and the
checking-access/retained-ledger distinction; §3, lines 114–167, fixes selected
instance compatibility; §4, lines 169–216, gives conditional local transport
and constructive signature substitution. §7, lines 305–388, already supplies
the conditional uniform-instantiation/cut argument. §8, lines 390–859, is a
limited equality/level treatment, not full checking. §9, lines 862–883, supplies
the schematic `echo` discriminator and leaves the invocation image open
(through line 885).
The source index's locator is `notes/design/INDEX.md:1516,1527`.

This packet does **not** add another proof of §7. Its additional question is
whether the actual HIR-to-candidate owners construct a generic rigid opening
and supply that checked derivation before ordinary body consumers run. The
answer is the obstruction in §4 below. Reusing §7 with an assumed new opening
constructor would leave exactly the existing unsupported premise untouched.

The top-level inference principles, §§1–4, require native constraint
generation/accumulation/propagation, levels, extrusion, qualifying intrusion
and generalization. The package's logical quantifiers select no new solver or
rigid IR representation. This note proposes neither.

## 3. Selected source-rule calculation, with explicit remaining premises

Write `P_q(rho,beta)` for the complete dependent packet telescope, including
dependent `J_q` and all profile/ledger/path references. The selected source
rule gives `Pack_s(P_q[s/beta]) : exists beta. P_q(rho,beta)`. This records the
existing use witness, with no runtime box or fresh instantiation.

To check the fixed arm, alpha-rename bound proof names away from `Gamma`,
`Delta` and retained endpoint names. Allocate one name `kappa_i` per original
local binder `beta_i`, and apply the *single* map `beta_i -> kappa_i` to the
entire packet telescope. Every occurrence of a binder therefore has the same
image, including occurrences in both A and B, nested callback effects, J,
K,D and latent views. This is the simultaneous signature-transport
construction of package §4 applied to the selected opening rule.

The arm context receives that declared interface and `DeclBounds(rho,kappa)`.
It does not receive arbitrary caller equations just because K,D retain their
joint correspondence. Adding `kappa = Int` from the private ledger would
violate charter §20's checking rule. This is a rule boundary; it is not a
proof that the present solver enforces the boundary during propagation.

Given an actual uniform derivation `D_h(kappa)` satisfying §7's primitive,
Flow, store and raw-suffix premises, pack/unpack cut uses one simultaneous
substitution `[s_q/kappa]` throughout `D_h`, its body witnesses and its incident
packet references. The assignment to captured/shared endpoints is fixed.
Signature transport preserves occurrence correspondence, so this cut cannot
pick a separate marginal witness for payload, continuation or effect view.
An alias denotes the same retained object; another raw resume accepts that
same `B(rho,s_q)` and enters its original suffix at the current state. It
does not reinstall the shallow handler or replace J with the arm's result.
These are applications of §§4 and 7 within their existing hypotheses, not
new source/compiler preservation theorems.

Returned/stored dependent roots must keep this simultaneous correspondence
with every incident field. The calculation does not prove that later
generalization, storage or re-entry preserves it; package §7:379–383 and
charter §20:565–568 explicitly leave that lifecycle theorem open. It also
does not assert a conventional non-dependent existential escape restriction.

For `echo : 'a -> 'a`, opening gives `x:kappa` and raw `k:kappa => J`;
supplying x as the response has the same endpoint on both sides. This is the
uniform-positive payload/response discriminator only. The actual Call/Value
entry and suffix/store premises still apply. For `sink::put : 'a -> ()`, the
annotation `checked:int = x` asks the arm to narrow its unconstrained rigid
input; actual Int callers supply no checking assumption to justify this.
The explicit source rejection remains unchanged. Neither example was executed.

## 4. Actual owner trace and first unsupported transition

All locators in this table are at the pinned commit.

| Owner | Actual construction/consumer | Evidence and limit |
|---|---|---|
| `yu-hir/src/module/source_annotation.rs:31–95,127–287` | Act/operation declaration lowering retains resolved family/declaration identities and the complete supported annotation tree. `parse_type:430–491` retains local sigil variable occurrences. | Current carrier is for nullary source family headers (`164–165`); it is not a representation proof for the original arbitrary fixed family-instance scope or declared bounds. |
| `yu-hir/src/module/local_source.rs:798–807,827–888` | Resolves the operation, builds payload/continuation binders with distinct owner/arm/ordinal identities, and places the body in its CatchArm lexical scope. | These are value binder identities and source annotations. They do not themselves construct a retained existential request or rigid type checking context. |
| `yu-solver/src/shadow_apply.rs:191–224` | `CandidateInference::solve` calls source preflight at line 204 before candidate collection/session construction at 222–223. | A rejected source carrier does not reach normal candidate action execution. |
| `yu-solver/src/candidate_source.rs:119–128,177–183` | Operation Catch preflight requires `monomorphic_signature`. It rejects every `SourceAnnotationValue::Variable` and every symbolic effect-row variable recursively. | **First unsupported transition:** a generic operation arm is rejected as `CandidateError::Unsupported` before any generic opening/body constraint construction. This is not proof of source rejection of a valid generic arm. |
| `candidate_source.rs:399–440,880` | For admitted operation arms, binds referenced payload/continuation components, queues one `Action::CatchOperation`, then visits the fixed arm body; execution calls `candidate_catch_operation`. | Sharing a syntactic arm action is not a generic request opening theorem. |
| `candidate_effect.rs:806–869` | Uses one values/effects/views map across positive and negative A/B materialization. Payload slots 60–61 are paired links. Continuation slots 62–63 pair Functions using the response and original scrutinee value. Slots 64–65 are stored **and** passed to live effect processing. | The supported monomorphic construction has actual admission consumers, not merely retained constraints. Raw suffix effect is explicitly provisional full-S at 856–858; no exact J theorem follows. |
| `candidate_effect.rs:1422–1514,1574–1592` | Signature recursion reuses one map entry per local variable spelling within this declaration materialization. New value entries use ordinary `fresh_value_at_level` at 1461; effect entries use ordinary fresh effect rows. | If one merely bypassed preflight, these sites would still not supply evidence of the required rigid checking boundary. This observation is not an executed bypass or a solver unsoundness counterexample. |
| `candidate_effect.rs:786–804` | An operation expression uses its own shared declaration-materialization maps at `level+1`, then admits a value link at slot 42. | It is not the retained typed-request pack/open bridge. OperationOrigin at 146–163 records declaration/occurrence provenance, not by itself an instance witness/rigid-opening proof. |

Thus the exact missing premise is:

> The real source operation-Catch construction produces, before checking its
> body consumers, one uniform checking context over the declaration's rigid
> local tuple and complete dependent packet, keeps caller-private equations
> outside its assumptions while retaining their joint correspondence, and
> supplies the corresponding checked derivation/transport at actual retained
> request maps.

This premise has no constructor evidence on the inspected candidate route:
generic preflight prevents that route. The downstream shared maps establish
neither rigidity nor request-instance retention. Removing the preflight alone
would not establish the premise. The leaf stops here instead of assuming a
transition that the source constructors do not emit.

This does not refute the selected source rule, certify the current compiler,
or claim global absence across uninspected legacy/production routes. It locates
one exact source-to-candidate obligation. General all-path enforcement of the
level discipline is also unproved: package §8:461–496 already identifies direct
extrusion bound-copy mutations missed by a wrapper around `constrain`. That
existing gap is not discharged by this arm-local map observation.

## 5. Proof-obligation economy and one next action

The source checking boundary is A (correctness); supporting intended uniform
generic arms is B (natural inference). Recovering an already-chosen request
map later from family identity would be D (reconstruction debt), and family
projection is non-injective by package §2. Keeping the construction's original
correspondence is preferable to such recovery. This does not promote a status
or choose a compiler representation.

No two new proof attempts were run. The first source audit found a concrete
absent transition; a second cut proof assuming that transition would duplicate
the existing conditional §7 result. The audit therefore stops at the owner
rather than adding an equivalent conditional theorem.

Next action for the primary: assign the bounded proof-first construction
invariant at `candidate_source::CatchOperation` / `candidate_catch_operation`:
derive how native generation, bound accumulation, propagation and extrusion
enforce the selected rigid checking boundary for one joint A/B/J/local-effect
tuple, including the existing direct-extrusion gap. Keep implementation and
lifecycle gates open until source constructor/consumer evidence exists. This
is a proposed handoff, not an implementation design or running job.

## 6. Frozen dependencies, checks and commit packet

SHA-256 of committed direct semantic/code dependencies:

```text
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9  notes/design/2026-10-02-operation-instance-binding-package.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38  crates/yu-hir/src/module/source_annotation.rs
afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074  crates/yu-hir/src/module/local_source.rs
a5fe26b4c5423468826842a618c8647af1d94a9ef135d18607999262977ead1a  crates/yu-solver/src/candidate_source.rs
f4a8cb624204ae8afd4f2ab599048e71efc5022724130161d390058a09997d9d  crates/yu-solver/src/candidate_effect.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  crates/yu-solver/src/shadow_apply.rs
```

Dependency recheck: the authority and listed HIR/shadow_apply files equaled
HEAD; live candidate_source and candidate_effect differed from HEAD. Those
live bytes were excluded. The primary must revalidate their delta before
applying this baseline correspondence to a later integrated snapshot.

Observed live dependency hashes at the final static recheck (excluded from the
proof inputs; concurrent writers may subsequently change them):

```text
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  crates/yu-solver/src/candidate_source.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  crates/yu-solver/src/candidate_effect.rs
```

Checks already run: read-only `git rev-parse HEAD`, branch inspection,
`git show HEAD:<path>` with bounded line reads, `rg -n` for owners, and
Python SHA-256/current-byte comparison for the direct dependencies. Commands
completed successfully; the note has zero trailing-whitespace lines and its
exact lease is an untracked new file. No build, test, probe or measurement ran. One static
leaf within its 20-minute budget; no delegation, Git mutation or shared-file
write. CPU/RAM were not measured; no compute experiment process was launched.

Routing evidence: configured normal prover defaults are GPT-6.1 Sol/high in
`.codex/config.toml`; `.codex/agents/prover.toml` has no model/effort pins.
Requested launch settings and observed runtime model/effort are unavailable
to this leaf and recorded as **unknown**; role-file defaults do not prove
effective runtime routing. No Astra request or execution occurred.

Commit packet:

- Exact changed lease: `notes/theory/2026-10-15-generic-operation-rigid-opening-construction.md`.
- Baseline SHA: `871d2ecb559f064dc034501b8bfe8c9bd6659876`.
- Changed proof dependencies: none in the committed baseline; concurrent live
  changes to the two solver dependencies are excluded and require primary
  delta revalidation. Their baseline hashes are above.
- Review: producer output only; independent review pending. No theorem,
  implementation or parent-gate closure is claimed.
- Proposed checkpoint message: `research: pin generic operation opening construction gap`.
- Proposed shared-record delta, for primary/curator only: generic rigid opening
  remains OPEN; add this exact preflight-to-opening constructor obstruction and
  its owner, reuse package §7 under its existing hypotheses, and keep lifecycle,
  full Call, hygiene, soundness, principality and F5 gates separate. No shared
  record was edited.
