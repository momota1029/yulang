# R209 outcome — model incomplete at source specification

Status: **CLOSED_INCOMPLETE / BLOCKED_AT_SOURCE_SPECIFICATION**

## Work and evidence

R209 followed the user's root-first instruction and performed a targeted
inventory of the Lean modules directly needed by the unchanged roots in
`notes/theory/lean/YulangClosure/Contracts.lean:128–154`. The primary pinned
all direct dependencies in the frozen handoff. One read-only explorer performed
an independent Lean-source inventory. No Rust path was read or changed; no
question bundle was changed; no Lean compilation, build, test, cache mutation,
or worktree/environment creation occurred. `lake --version` and
`lake env lean --version` both reported Lean 4.35.0.

The audit confirms that concrete pieces exist—full raw syntax and symbolic
`Build`, structural Simple-sub terms and subtyping, conditional propagation /
extrusion / intrusion preservation, generalization fragments, scope machinery,
and partial principality/termination results. They are not one concrete
independent source/type/effect model plus the actual combined algorithm.
`Kernel` still supplies source atom, admission, primitive, shape, boundary and
conversion meanings. Existing `SimpleSubConstraintSoundness.Step` permits
arbitrary inserted bounds and takes references, birth levels and names as
inputs. Generalization is a conditional fragment, and no concrete original
principal order or full `inferInitial` / `inferStep` pair was found.

## First exact source specification inputs

1. **Original Literal L1:** independently specified declaration and local
   typing at the same original source/root/event/scope, together with the
   actual Return and contextual-effect obligations. The symbolic
   `literalDeclaration` equation and the eight-kind base `PaperTypes` mapping
   do not supply this original source rule.
2. **Typed Union:** selected branch-to-result relation and dependent governed
   field transport equations, with both branch schemas, the original result
   telescope and shared coordinates retained. The existing pending question
   `questions/2026-11-02-original-typed-union-rule/question.md` revision `q1`
   asks for this exact decision; it remains untouched and unstaged.

Beyond those source laws, soundness needs a noncircular generated-constraint
satisfaction relation that derives every original local premise at the same
source scope, endpoint, world and shared witness. Termination separately needs
one endogenous transition relation connecting generation, accumulation,
propagation, extrusion, intrusion and generalization. Arbitrary histories of
local `ConstraintStep` do not provide it.

No Lean candidate was written from the audited routes: assuming these source
meanings, placing them in an arbitrary model parameter, or renaming the existing
`Build` / `Satisfies` interface would violate R209's acceptance gate and fail to
advance the original root. The selected Source-Generalize authority still
allows legitimate missing definitions to be drafted for independent review;
such drafting would not adopt the semantics.

## Accounting and next input

Parent delta: **0/4 roots; 0/5 packages**. No theorem, theorem premise, or
implementation gate was closed. R208's annotation candidate remains preserved,
unintegrated and unverified; it is not a substitute for the whole model.

The next step is to authenticate the original Literal L1 rule and resolve the
existing typed-Union source question through the established authority process.
If an existing rule determines them, record its exact source and equations. If
the specification authorizes drafting missing definitions, prepare the full
concrete equations for independent design review; drafting is not adoption.
Then resume the same complete model packet, including Call/effects wherever
they are core. Do not dispatch another isolated constructor theorem or use Rust
internals to fill the mathematical semantics.

The active goal remains soundness, principality, termination and Rust
correspondence, with effect hygiene in scope. This outcome is a current
specification blocker, not a counterexample, proof of semantic
underdetermination, goal pause, or cancellation.
