# Generic operation opening: native rigid-boundary falsifier

Date: 2026-10-15
Status: frozen research-only producer artifact; independent review pending
Method: bounded static adversarial trace of the existing native owners
Baseline: `research/simple-sub-intrusion`, `427d1ff5daab866fa7d89cb513a077063cc6454d`
Lease: this file only; no compiler, test, shared-record or Git mutations

## Objective and result class

Attack the proposed shortcut of admitting generic Catch arms through the
existing ordinary signature materialization, without changing the selected
rigid checking boundary. The selected source rule is charter §§19–20:
operation-local binders open rigidly, checking uses declared interfaces/bounds
and one fixed captured/shared assignment, and caller-private `s=Int` is not an
assumption about the opening. `sink::put` with `checked:int=x` stays rejected
even for Int-only callers. `echo` with `k x` is only the positive discriminator.
Operation-instance package §§2–4,7–9 and top-level inference principles §§1–4
govern the dependencies; the package remains Draft, without implementation
authority. Neither a concrete rigid IR node nor a new constructor rule is
selected here.

**Result:** one fresh native value row plus one Int demand is a minimized
candidate-internal witness that ordinary row allocation/levels do not implement
rigid checking. This is a derivation from actual committed methods, not an
executed experiment, an admitted source counterexample, a new conditional
generic-arm theorem, or a compiler unsoundness report. The authentic generic
source route still stops at preflight. The narrower conclusion is that removing
`monomorphic_signature` alone supplies no rigid boundary, and its existing
downstream consumer can record a narrowing demand as an ordinary bound.

## Exact witness and native derivation

Hypotheses: a healthy private candidate session with available resources; a
fresh row `X` at any representable level `l`; no other bounds on `X`; a new
ordinary value comparison with no effect filter. This row is the kind actually
allocated for an operation signature Variable. No hypothesis asserts an
existing generic opening or a retained request witness that the source does
not construct.

The minimized input is:

```text
X = fresh_value_at_level(l)
ValueRow(X) <: IntNegative
```

Its static transition is:

1. `lib.rs:10177–10201` initializes empty VariableBounds, stores `l`, and sets
   origin `Fresh`, `non_generic=false`. The allocation does not distinguish an
   operation-local checking name from an inference variable.
2. The actual operation signature Variable case uses exactly this allocator
   at `candidate_effect.rs:1452–1465`, reusing one spelling map. Catch's paired
   payload construction at `823–828` would therefore use an ordinary row for
   an unconstrained local variable if reached. Sharing the map preserves an
   endpoint identity; it does not change how its bounds are admitted.
3. `candidate_scheme.rs:1369–1375` admits an ordinary value link to the live
   consumer. Its direct value context is identity: `candidate_context.rs:
   2683–2694,2696–2716` adds a closed allowance context only to effect pairs;
   `2953–2976` returns ordinary dispatch for identity/no-filter relations.
4. In `lib.rs:12436–12450`, a ValueRow has no fixed primitive shape, so
   `incompatible_value_shapes` returns None (`14105–14125`). The row/atom
   route at `12486–12497` negatively extrudes Int to the row's level.
   `candidate_extrusion.rs:211–258` has neither a row nor Function child for
   this atom; it returns Int unchanged. Constructors carry no stored levels.
5. Dispatch reaches `apply_value_task`, which selects the actual candidate
   implementation at `lib.rs:13804–13810`; the separate non-candidate bound
   transition below that locator is not this witness's consumer.
6. `candidate_apply_value` at `candidate_extrusion.rs:811–834` chooses
   owner X, Negative, IntNegative and calls `candidate_insert_bound`. The
   latter canonicalizes endpoints, records provenance, and physically pushes
   the atom to X's exact upper bounds (`435–456,497–504`). It has no opening
   classification or rigid-boundary guard. Resource/journal/evidence handling
   can fail for resources; it does not impose rigid universal checking.
7. Replay sees zero opposite bounds (`573–585,766–808`). Therefore this
   isolated demand adds the Int upper bound without generating an incompatible
   primitive pair. Its row/atom processing does not depend on the numeric
   choice of `l`.

This does not assert `X=Int`: an upper bound is the actual mutation. It is
already enough to distinguish flexible inference from proving the source
consumer uniformly for an unconstrained rigid input. If X is reused as that
opening without an additional established invariant, this consumer has no
evidence for the required uniform judgment. A caller-private lower bound
Int would merely replay Int <: Int and supply no uniform checking proof.
No caller ledger connection or full source acceptance is inferred here.

Minimality is relative to this row/atom consumer: one row and one nonidentity
demand suffice. With no demand there is no narrowing transition; with no row
there is no local binder to attack. No callback, alias, Function, caller,
continuation or extrusion copy is required for this witness.

## Source seam and direct extrusion consequence

The source-to-native seam remains excluded: `CandidateInference::solve` calls
preflight at `shadow_apply.rs:204`, before collection/session construction at
`222–223`. `candidate_source.rs:119–128,191–197` recursively rejects signature
Variables and symbolic effect variables for every operation arm. On this
baseline that applies even to unused/wildcard binders; usage controls the
separate port-support check, not monomorphism. The reviewed earlier audit
already establishes this bounded owner fact; this lane does not repeat its
fixture search or preflight coverage investigation.

Below that boundary the existing schedule would pair the signature ports
before visiting the arm body (`candidate_source.rs:430–461`), and the local
annotation consumer would emit initializer <: Int at
`candidate_effect.rs:1217–1231`. Thus the witness targets the actual
signature/consumer seam of a preflight-only bypass. The bypass was neither
implemented nor executed; no assertion is made that all remaining source
constraints, raw-suffix effects or publication would succeed. The consumer
emission above is a locator correspondence, not a proof of a newly admitted
source route.

The inspected native extrusion also exposes the exact owner of the previously
identified reference coverage concern. For a deep row X, positive extrusion
to l allocates R at l, remembers the copy, directly inserts X.upper += R
(`candidate_extrusion.rs:92–125`), and traverses its snapshotted lower bounds.
An existing shallow row P at l is returned unchanged (`93–95`); Work::Bound
directly inserts it into R.lower (`310–325`). Both insertions call the same
one-sided bound owner, rather than the ordinary comparison dispatcher.
This trace uses existing ordinary rows and mutations; it is not a source
counterexample with P secretly assumed to be a constructed rigid name.
It establishes the concrete native routing that a complete opening invariant
must account for. Effect-row copies use the same loop; their general semantics
and scope enforcement were not audited here. Provenance retention and dirty
intrusion marking (`563–570`) do not themselves establish opening guard checks.

## Independence, limits and next action

The semantic discriminator comes from the selected charter; the transition
evidence comes from committed code. No checker assumes transition rules, no
executable oracle is used, and no independent review of the constructive lane
or this artifact is claimed. The shared premises are the selected source
meaning, fixed captured/shared assignment and pinned baseline. There are no
seeds/ranges, actual mutations, executable probes or measurements. The
preflight-only bypass is a named unexecuted shortcut, not adopted semantics.

Inspected scope: native Catch signature/payload materialization, concrete local
annotation demand emission, fresh row metadata, value pair dispatch, direct
bound mutation/replay, identity value context and row extrusion. Omitted:
parser/HIR execution, legacy/production routes, whole-native ownership,
generalization/alias/resumption lifecycle, request K,D retention, dependent J,
callbacks, nonidentity contextual cases, complete scope invalidation/replay,
soundness, principality, full Call/hygiene and F5. No authentic admitted source
counterexample was found or claimed. No global all-path negative search ran.

Stop condition: the minimized native discriminator is reached; repeating a
fresh-row toy model would leave the absent source opening premise untouched.
Recommended next action: the primary should give the constructive lane the
actual `fresh_value_at_level` / `candidate_apply_value` /
`candidate_insert_bound` / `candidate_extrude` owner trace and require the
uniform-opening invariant to explain why this narrowing demand cannot become
a successful generic arm derivation while `echo` retains its shared endpoint.
Keep generic implementation and parent proof gates OPEN. This handoff chooses
no representation or new language restriction.

## Dependencies and checks

Initial HEAD was the assigned baseline. During the lane it advanced to
`b2c10cfe3413661759a4a7d18e57504a73e2e508`. At the dependency check all listed
compiler/authority working bytes still matched the pinned baseline. The two
prior notes changed only review metadata and added review descriptions; their
baseline substantive content was used, and the read-only delta was inspected.
These changes do not independently certify this artifact.

SHA-256 of direct pinned dependencies:

```text
a261db48f0986ed2f03a26a6506e5179793bc992708f8e26c90a2aa383c6e492 notes/progress/2026-10-15-generic-opening-source-audit.md
55d4e68cb9f144c42c07a33cb7d9ea3c9278a674bb8ae1c47c39864ec1745967 notes/theory/2026-10-15-generic-operation-rigid-opening-construction.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed notes/design/2026-09-29-scc-intrusion-redesign-charter.md
1eb2cbdb49368b0839d839d6a5e72698bb06252813b00200098e70371645c7c9 notes/design/2026-10-02-operation-instance-binding-package.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81 notes/design/2026-10-11-yulang-inference-top-level-principles.md
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831 crates/yu-solver/src/shadow_apply.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4 crates/yu-solver/src/candidate_source.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91 crates/yu-solver/src/candidate_effect.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1 crates/yu-solver/src/candidate_extrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd crates/yu-solver/src/candidate_scheme.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461 crates/yu-solver/src/candidate_context.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5 crates/yu-solver/src/lib.rs
```

Observed newer note hashes (editorial dependencies only):

```text
773e4166f202e38e8f131201425257202db363548b98cac8be704c8594546e1d notes/progress/2026-10-15-generic-opening-source-audit.md
dcf9b7d6d75fea8527683cbb6f7fae3aa922d9fca99167491099c02bd17762f0 notes/theory/2026-10-15-generic-operation-rigid-opening-construction.md
```

Checks: read-only `git rev-parse`, branch/status inspection, `git show
427d1ff5d:<path>` with narrow `nl/sed`, `git grep` owner searches, Python
SHA-256/byte comparison, and a narrow read-only diff of the two notes.
One initial rg locator included a nonexistent candidate_value.rs; that search
was incomplete and was replaced by pinned git grep on the actual owners.
No claim relies on its failed coverage. Artifact fence/whitespace/final-newline
integrity and dependency stability were checked before freezing.
Budget: one static lane within 15 minutes; zero Cargo/build/test/probe/
measurement processes and samples. Read/hash shell processes only; CPU/RAM
and exact elapsed wall time were not measured. No delegation or Git mutation.

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-generic-opening-rigid-falsifier.md`.
- Baseline SHA: `427d1ff5daab866fa7d89cb513a077063cc6454d`.
- Dependency changes: none by this leaf; two editorial note hashes changed as
  listed above, with compiler and semantic dependencies unchanged at recheck.
- Claim/review: frozen candidate-internal static falsifier; unreviewed producer
  artifact; no admitted source counterexample, theorem closure, semantic
  adoption or implementation authority.
- Checks already run: pinned owner reads/searches, 12 dependency hashes/live
  comparisons, editorial delta inspection and note integrity; zero execution.
- Proposed checkpoint message: `research: pin native generic-opening rigid-boundary falsifier`.
- Shared-record deltas left to primary/curator: link the exact row/Int consumer
  and direct native extrusion owners in `tasks/current.md`,
  `tasks/research-lab.md` and the applicable theory map; keep generic opening,
  implementation, lifecycle and original parent gates OPEN. No shared file was
  edited, and no new selected semantics or representation is proposed.
