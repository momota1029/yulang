# Simple-sub reassessment: restore the application inference path

Date: 2026-10-10
Baseline: `b2894cb6b`
Authority: current explicit user correction; existing source/inference contracts
Claim class: pinned algorithm and current-code audit; corrected work ordering
Mode: M0 records from bounded architect/explorer evidence; no semantic adoption

## Correction

The user explicitly corrected the repeated questions:

> 明らかにsimple-subの解法を無視した質問が続いています．考え直してください

The previous planning treated detailed source/runtime registry certification as
a prerequisite for the basic application constraint-generation step. It also
offered a literal-only versus ordinary-value inference choice although that
step is uniform in Simple-sub and existing source parameter/result synthesis.
Those dependencies were not established by the actual algorithm.

The questioner's new original-formal rule assignment was interrupted; no output
from that assignment was present in the worktree. No further rule/adoption
question was created.

## Actual reference algorithm

The pinned [Typer.scala](https://raw.githubusercontent.com/LPTK/simple-sub/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala)
at commit `9bae772624c23b52a93c1b226157e16898b4d9db` was read directly,
including typeTerm, constrain, extrusion, freshenAbove and scheme definitions.
The existing [paper/source audit](2026-09-30-simple-sub-paper-mlsub-audit.md)
provides the broader provenance and Yulang-specific boundaries.

At the definition's raised level:

```text
invoke f = f 1:
  f : fresh monomorphic alpha
  1 : Int
  result : fresh beta
  constrain(alpha, Function(Int,beta))

apply f x = f x:
  f : fresh monomorphic alpha
  x : fresh monomorphic gamma
  result : fresh beta
  constrain(alpha, Function(gamma,beta))
```

At equal levels the demand enters alpha's upper bounds. Every existing lower
bound is compared against it. A Function(P,R) lower bound requires Int <: P
(or gamma <: P) and R <: beta by argument contravariance/result covariance.
Alpha is not replaced by an exact Function type; no concrete provider is
required merely to collect this demand.

Lambda-bound references reuse their monomorphic variable. Let use freshens
above the binding boundary with one memo per use, copying the complete bound
graph and preserving within-use sharing. Cross-level extrusion uses separate
variable/polarity representatives and reverses polarity under Function arguments.
These are algorithmic consequences, not new language choices.

This is the value constraint spine, not a complete Yulang scheme/soundness
claim. Existing source result synthesis selects ordinary Value-entry and fresh
unannotated value endpoints. The already selected shared-formal role/protection
direction needs its evidence connection; it does not create a choice to exclude
noninteger ordinary arguments from application constraint generation.

## Actual compiler gaps

The bounded explorer mapped the following code against the reference:

- `shadow_apply.rs` already allocates an Apply result row and constrains the
  callee against a negative Function using the argument endpoint (`:854–919`).
  Literal/formal arguments differ by their endpoint, not the Apply rule.
- Ordinary collection rejects Apply/Group (`yu-solver/src/lib.rs:995–1026`),
  and `emit_lambda` (`:1717`) only handles leaf bodies. The shadow collector's
  one-formal lookup (`shadow_apply.rs:826`) and special captured-local cases
  need a general lexical parameter-to-recipe map and recursive collection.
- Live value/effect rows, bound worklists and four-port Function variance
  already exist (`lib.rs:3866`, `:9819`, `:11310–11416`, `:12323`). Their reuse
  does not require a literal-specific Function constructor.
- The candidate constrains Apply/Group evaluation effects to empty, drops child
  effect endpoints, and uses fixed bottom/empty callable effect ports
  (`shadow_apply.rs:661–689`, `:843`, `:857–860`, `:916–918`). A pure argument's
  evaluation does not imply an empty invocation effect.
- Current F5 closed effects/generalization/freshening encode only bottom/empty
  effects (`f5c_generalization.rs:470–479`, `:6440`, `:7662–7668`). Allocate and
  retain effect variables/bounds in the successor scheme and fresh-use path;
  merely inserting variables into the current pure exporter is insufficient.
- Current `extrude` (`lib.rs:10921–11090`) lowers existing reachable row levels
  in place. It does not implement the reference's polarity-keyed copied
  approximants. The test-only intrusion transport is not wired to the session
  and does not determine source local/anchor partitions. No reference
  extrusion equivalence is claimed for either path.

The completed source/runtime Call certificate remains a later correctness
requirement. Source collection retains resolved binder, operand, annotation and
scope/incidence facts; inference constructs fresh endpoints/demands; complete
Call solving/elaboration establishes correlated effects, images, actual
provider/entry, protection, admission, licensing and future behavior. No full
registry-before-bound-collection dependency has been exhibited. Missing compiler
constructors cannot be exported as semantic residuals; genuine constraints may
remain residual only with defined meaning and an ordinary consumer.

## Disposition and next implementation work

Withdraw ordinary-value q1's offered scope choice; preserve its unapproved
draft/history. Suspend registry q4 as an inference prerequisite; its six-choice
interpretation remains unadopted research. Retain q2's adopted Reify choices,
q3's design/review scope and the reviewed registry candidate's actual theorem
limits. No canonical proof-DAG gate is promoted or silently closed.

Proceed from the compositional source collector and live constraint graph:
lexical formal lookup, recursive Apply/Group recipes, fresh results, retained
callee/argument/invocation effects, lower/upper propagation and scope/polarity
handling. Follow with successor generalization and per-use freshening that keep
effect identities and bounds. Full Call obligations stay attached to their
owning source/solve/elaboration phases. Do not promote the current fixed-empty
shadow scheme as the completed replacement.

No new user decision was demonstrated for the basic application constraint
spine. A genuinely different semantic rule or public residual meaning must be
identified concretely before it becomes another decision question.

## Checks and limits

The architect checked both pending questions against the pinned algorithm,
source result synthesis, Function-view direction and selected Call sources.
The explorer independently mapped current collection, live solving, F5
publication/freshening and intrusion transport. These are evidence-producing
read-only audits, not a new full soundness review. No compiler edits, tests,
builds, execution probes or measurements ran. Full effect/role/protection
inference, actual source-to-solver correspondence and F5 cutover remain open.
