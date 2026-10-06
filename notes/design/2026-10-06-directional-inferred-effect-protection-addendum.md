# Directional protection from an inferred variable to a Function upper view

Date: 2026-10-06
Status: Draft formalization; current explicit user decision recorded in section 1
Selected-by: user, directly in the continuing source-generation conversation
Review: not independently reviewed in this runtime
Scope: the displayed protected-variable/Function-upper inference step and the
       exclusion of reverse protection of an existing Function lower bound
Supersedes: the pending E/R adoption framing in
`2026-10-06-source-generation-introduction-decision.md`, not its historical
algebraic calculations; narrows the open producer in inferred call views
Implementation authority: none; production cutover remains gated

## 1. Direct source of the correction

The user first distinguished an unannotated higher-order formal from a known
externally supplied callable:

> ちょっと待ってね．fが引数で何の型注釈もされていないならそこから出るeffectも保護されるべきです．しかし，fがすでにわかっていて外部から注入されるものであれば保護されません．Eはこれを無視していませんか？

The user then made the direction explicit:

> もっと言うなら`'f`が`'f`の段階で保護されていた場合，`'f <: 'a ['b] -> ['c] d`と推論するときに`'c`を保護するという意味です．なんとなく伝わりますか？　再帰関数とかで下から`'e -> ['g] 'h`とかで抑えられてた場合は`'g`が保護されない感じになりますが．

Finally, the user requested continuation and repository integration:

> というわけでこれでまた考えてください．pushもお願いします

These are direct current user instructions, not approval of either former
E/R draft. No stable conversation URL or message ID is available. No
`approved-answer.md` is synthesized. Under
[design authority](../../rules/design-authority.md), the current explicit
instruction governs its stated scope; the Draft status here applies to its
mathematical elaboration and proposed representation, not an invitation to
ask the user to choose E/R again. The question-board rules explicitly permit
ordinary conversational clarification without a new question.

## 2. Selected direction, without an accidental strengthening

The positive instance is:

```text
'f is protected while it is still an inferred variable
'f <: 'a ['b] -> ['c] 'd       [an original source upper-use constraint]
---------------------------------------------------------------------
protect the covariant/output-effect occurrence 'c of this upper view
```

The negative instance is:

```text
'e -> ['g] 'h <: 'f           [existing provider/recursive lower bound]
'f is protected
---------------------------------------------------------------------
this fact does NOT propagate that protection backwards to 'g
```

When both constraints exist, retain both and their shared original assignment.
The upper occurrence `'c` receives protection from the protected-variable
step; the lower occurrence `'g` does not acquire it from that step. This does
not delete any independently present protection on a provider's `'g`.

The distinguishing input is inference/source provenance, not whether a
normalized type happens to contain an effect position. Nor is it whether the
position is called immediate or latent. A known external callable does not
receive a new unannotated-formal seed merely because its local Name use has
no annotation. If a protected formal receives that callable, retain the
formal's upper-use provenance separately from the provider's lower provenance;
do not paint the latter with the former's protection.

The statement concerns construction of an inference view. It does not yet
assert that every concrete event produced by a provider becomes protected
when it passes through that view. Such an event-to-profile statement needs
its source contribution, typed incidence, receipt and live receiver evidence.
The previous assistant explanation made that blanket event-level claim too
readily; it is not adopted here.

## 3. Proposed minimal inference-rule notation

Let `k` identify the already justified source protection seed at the original
shared variable `v` and scope `sigma`. Let `u` identify an original source
upper-use demand with complete Function view `U` and its designated
covariant/output-effect occurrence `outEff(U)`. Record the premise that the
variable is protected at this exposure, rather than reconstructing it from
its solved value.

```text
ProtectedVarAt(k,v,sigma,u)
SourceUpperUse(u,v,U,sigma)     U = 'a ['b] -> ['c] 'd
---------------------------------------------------------------- Dir-Protect
NewProtection(k,u,outEff(U))
```

For the unannotated formal case, the existing selected source treatment
supplies the seed from that formal's actual annotation absence, before its
use exposes `U`. For a known external Name, there is no such seed generated
by Name lookup. `SourceUpperUse` is a constraint produced from source usage,
not successful Function membership and not the answer to pending `Q`.
Constructing its symbolic Function demand does not wait for a solution.

This rule has one conclusion at `'c`. It is not a new rule recursively
marking `'b`, `'d`, or all effect positions inside a solved result. Existing
marks at those coordinates survive. A subsequent latent exposure can use a
corresponding directional rule only when its own protected-variable and
source-exposure premises are established; this note does not fabricate them.

`ProtectedVarAt` expresses proof-stage provenance. No new global wall-clock
ordering, seed aggregation across arbitrary recursive SCCs, or late-seed
replay policy is selected. The executable research model retains the explicit
set of seed-origin witnesses present at each exposure for this fact. It does not claim to derive that
fact for all source graphs.

## 4. Evidence identity and preservation requirements

One possible proof record is `(k,beta,u,sigma,outEff(U))`, with
`beta=(original formal, shared contract root)` retained from the existing
source context. This is a logical index using the existing source/evidence
vocabulary, not approval of a new runtime or solver carrier.

Keep original upper and lower occurrence identity even when endpoint values
or printed types coincide. A global bit keyed only by a solved effect value
cannot express the required distinction. Distinct upper uses can share a
slot while retaining different introduction witnesses; the number of uses
is not a theorem about the number of static `Slots(beta)`.

Protection is not an empty-row claim, an effect-membership assertion, a
concrete removal grant, an actual Handler-role rewrite, or a receipt. The
existing no-annotation policy, actual provider entry/role, callback-literal
B, original scope and whole `xi=(nu,K,D)` remain intact. Existing profile
transport follows independently justified typed correspondences and retains
inherited evidence. Upper protection is not permission to reverse such a
correspondence or erase lower/provider predicates.

## 5. Retirement of the wrong decision boundary

The previous proposals asked for an exhaustive choice between only an
immediate Call origin (E) and an automatic result-default schema (R).
Neither was adopted. Treating the user's clarification as approval of R's
whole-result traversal would repeat the error; treating it as E because one
example has a single output-effect occurrence would also lose the direction.

The earlier assistant suggestion to mark every effect position of the
complete inferred contract is withdrawn. So is the request to answer E/R as
an outstanding prerequisite. The current local target is the directed rule
above, including its explicit no-backflow case.

This does not falsify the older mathematical facts about arbitrary supplied
profiles, substitution, or local visibility. Their interpretation as an
unresolved E/R choice for this task is superseded. Existing full P/A,
contribution/receiving, source adequacy, principality and production proofs
are not thereby certified.

## 6. Next proof target, not another semantic vote

[The companion derivation](../progress/2026-10-06-directional-protection-source-generation.md)
constructs the local incidence output and proves its exact rule-relative
coverage, no-backflow, and information-retention properties. The old
`Applicable_original -> p0` theorem is no longer the right unconditional
source-generation target. The new completeness obligation is to enumerate
all source-justified directional exposures with their original seed witnesses,
then compose their effects with the already supplied/derived typed evidence.

The present document records the decision and a bounded formalization. It
neither requests a repeated decision about its two displayed instances nor
claims independent review, full inference soundness, or implementation readiness.
