# Parent-obligation reconstruction for Yulang inference

Date: 2026-11-01  
Status: research-plan revision; not a theorem, semantic adoption, or closure
receipt.

## Why the previous plan is insufficient

The five-package plan in `2026-11-01-parent-backward-inference-plan.md` names
the four roots, but R194–R198 kept trying to construct their shared source
model one missing local meaning at a time. Each result moved the same missing
edge—from primitive/literal meanings, to admission/readout, then to annotation
IDs—without discharging a premise in an original root. R198's artifact is an
honest stop, but it does **not** meet its contract's accepted blocked outcome:
the contract required the first missing equation and its owner to be pinned,
while the frozen handoff says the owner remains unidentified. Its review found
zero mathematical delta and one contract-level blocker.

The correction is to reconstruct the proof composition from each root before
assigning another local proof. A source table, signature wrapper, passing Lean
module, or conditional lemma does not count as a removed dependency by itself.

## The unchanged parent roots

The statements are the definitions in `Contracts.lean:128–154`; all quantifiers,
supported source forms, scopes, effects, and witnesses remain unchanged.

| Root | Backward proof obligation | First unclosed edge in current evidence |
| --- | --- | --- |
| `InferenceSoundness` | Independently interpret generated constraints and every solution; prove each source-generation case yields its original typing premises under that same assignment; compose with original source reconstruction to obtain one `e` and `sameScoped`. | No concrete original `SourceProblem`/independent solution interpretation connects the existing generator and reconstruction. `OriginalSourceGeneration.source_reconstruction` applies only after complete `Build` satisfaction under supplied `Kernel` meanings. |
| `SourceScopedCoverage` | Invert each original source rule into the *same* generated problem, construct one assignment satisfying it, and preserve the original scope/witness. | No reverse generation/solution construction over the original constructors. Forward soundness does not establish this direction or existence of a satisfying assignment. |
| `PrincipalCoverage` | Fix the original principal predicate and `instanceOf`; construct a solving principal assignment and prove that every original derivation factors through it at the same scope. | Both the ordering's source meaning and the all-derivations factorization are open. `OriginalPrincipality` gives a finite-use algebraic descent criterion under premises; it does not instantiate those source premises or select the original order. |
| `InferenceTermination` | Show accessibility for every actual `inferInitial` state and every `inferStep` transition. | Existing scan/parser descent is local. No single well-founded argument covers the original transition system across propagation, allocation, extrusion, intrusion, Replay/callbacks, and generalization. |

The shared prerequisite is a fixed mathematical model of the original source
rules and Simple-sub operations. Soundness is forward constraint-to-typing;
principality adds the original order and a universal factorization; termination
reasons about the actual inference transitions. `PrincipalCoverage` logically
implies `SourceScopedCoverage` for the same model: choose the principal result
using the given derivation as nonemptiness evidence, then specialize its
all-derivations clause to that derivation. This is a direct corollary, not a
second principal-order proof. The two definitions remain separately tracked
roots; a reviewed proof of that corollary closes the coverage root only when
the principal root is proved. Soundness and termination are not corollaries of
principality.

## Soundness composition to prove

For the unchanged `InferenceSoundness` statement, the intended composition is:

1. `p.generates s x d` gives the actual formula/store generated for the
   original `(s,x)`.
2. `p.solves d a` means independently that assignment `a` satisfies those
   generated constraints. It must not be defined by restating source typing,
   admission, reconstruction, or the target conclusion.
3. Structural induction over the actual generation/source rule derives each
   original constructor premise from the generated constraints under the same
   assignment. Pattern and body hypotheses may be used only for their actual
   subterms. Lambda-local declaration, Call, and effect obligations must come
   from their own emitted constraints/interpretation.
4. Apply the original reconstruction theorem only after its full satisfaction
   hypotheses have been derived; return the same source, scope, assignment,
   and one shared witness required by the parent.

Existing evidence occupies only parts of this path. `SimpleSubLatticeInference`
proves structural store satisfaction under explicit decoding/history/acceptance
hypotheses. `SimpleSubGeneralizationSoundness` transports structural solutions
under boundedness/anchor hypotheses. `OriginalSourceGeneration` reconstructs
source judgment from a supplied kernel and complete satisfaction. R184's first
App obligation still contains original admission, descriptor formation,
whole-argument compatibility, Call, incidence, and callable-image atoms.
These results are reusable only after their exact premises are independently
derived and applied; their existence does not fill those premises.

## Model gate before another proof packet

The primary must prepare one constructor-by-constructor mathematical candidate
against the existing authorities before delegating a new theorem attempt. It
must state:

- original syntax and every source judgment rule, including declarations,
  annotations, literals, primitives, patterns, statements, Call and effects;
- the exact Simple-sub type/effect domains and satisfaction relation;
- generation, accumulation, propagation, extrusion, intrusion, generalization,
  and the actual inference transitions;
- the assignment/readout and scope relation used by the original parent;
- the principal relation and instance ordering as a separate definition;
- the precise existing theorem attached at each edge, with its still-open
  hypotheses.

Every original constructor needs a rule equation. A parameterized table is
acceptable only if its entries have independently specified meanings and the
same table is consumed by generation, satisfaction, and source typing. It
cannot contain the typing/admission fact being proved. Do not infer declaration
meanings from Rust IDs, receipts, owners, or registration traces. For every
equation, distinguish a derivation from an already approved rule from a new
semantic or architecture choice. A new choice requires its normal authority
review and recorded user approval before it can be adopted or used to activate
proofs; an asserted conservative intent is not evidence of approval. If the
existing authority does not determine an equation, record the exact open
decision and keep dependent proof work unactivated. The pending typed-Union
question remains open and unstaged; preserve that constructor and stop at its
actual equation if the candidate depends on it.

Independent conformance review of this complete model is the activation gate.
If the model has an unresolved equation, the result is `MODEL-INCOMPLETE`, not
a successful package or proof milestone. No new owner-search or wrapper packet
is admitted as a substitute.

## Ordered proof plan

1. **Freeze the abstract Simple-sub/source model.** Use original Yulang source
   rules and the approved deterministic algorithm. Prove the basic semantic
   operations and constructor equations. Include Call/effects in this stage
   wherever the original rules make them core; keep every form and quantifier.
2. **Close forward soundness.** Prove solution satisfaction implies each
   original typing rule, then compose into the unchanged parent with the same
   assignment and single witness. Do not count a constructor lemma until the
   parent derivation consumes it.
3. **Close principality and termination as separate roots.** Principality
   proves its own solution existence/order/factorization obligations;
   termination proves well-foundedness of the actual inference transitions.
   Shared model definitions may be reused, but neither result is inferred from
   soundness. Derive and independently review the direct `PrincipalCoverage →
   SourceScopedCoverage` corollary; consume it to close the separately tracked
   coverage root when the principal theorem closes. If principality is pursued
   in a narrower stage, prove coverage directly instead of assuming it.
4. **Finish remaining Call/contextual-effect obligations** where these are
   genuinely outside the fixed Simple-sub core, without narrowing the original
   theorem's domain or weakening the earlier roots.
5. **Prove Rust correspondence.** Relate the implemented solver's states and
   transitions to the already fixed abstract algorithm, then establish its
   output/readout path. Rust correspondence cannot be a premise of the
   abstract theorems or a substitute for them.

## Progress and stop accounting

Current baseline: **5/5 dependency packages open; 0/4 roots closed**. R198
changes neither count. For every future report, record:

- the exact original root and premise edge before work;
- the independently owned equation/theorem that discharges that edge;
- the application site in the parent derivation;
- the remaining premise and its true semantic/proof owner;
- the exact before/after package and root counts. If a parent theorem entails
  another root by a direct corollary, record and apply that corollary rather
  than counting the two as unrelated proof burdens.

Conditional lemmas and local theorems are listed as evidence, but count as zero
parent reduction until applied. If a new premise appears, attach it to the
original owner instead of treating it as a solved prerequisite. After two
materially different methods leave the same premise unchanged, audit the
owning definition/model before authorizing another proof variant. Lean theorem
counts, sprint numbers, test counts, and implementation traces are not progress
metrics for these roots.

This plan changes research ordering and accounting only. It adopts no new
language rule, does not claim semantic underdetermination or global absence,
and grants no Rust production or cutover authority.
