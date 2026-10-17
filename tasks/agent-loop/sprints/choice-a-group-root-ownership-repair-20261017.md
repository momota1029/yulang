# Sprint choice-a-group-root-ownership-repair-20261017

Status: ACTIVE, Luna-admitted at baseline `a640dd909132b2be1d1bbbe35a4249e16642b84b`.
Branch: `research/simple-sub-intrusion`; revision 1.

## Parent and fixed outcome

Parent remains the original Yulang inference/execution goal with original A/B
claims, quantifiers, source/native correspondence and all F1/FK1, N-Transport,
Call, soundness, principality, termination and production gates OPEN. The
predecessor sprint `choice-a-root-source-key-contract-repair-20261017` closes
REVIEWED-PARTIAL after CLEAN spec review and one compiler MAJOR on root Group
identity ownership. No original theorem condition closes.

Outcome: define one root-occurrence/source-key rule for every retained
constructor in the direction-A grammar (`Atom`, `Apply`, `Group`), establish
the authentic Group key source statically, and obtain a short sequential delta
review. This is proposal-only; no compiler/test authority or final adoption.
Reuse the exact source audit and code pins; do not broaden the parser audit.

## Baseline and exact inputs

Baseline: `a640dd909132b2be1d1bbbe35a4249e16642b84b`.
Successor rev3 SHA-256:
`ae572403ec4e36c56f034135f9e223e93dc9f0bad5c01fbed1d368048713eb2a`.
Handoff rev3 SHA-256:
`f2eff28c5087f406332e284290f0c651527caf2d607dc310ee89c3da3ff1e4c5`.
These frozen bytes remain in Git commit `a640dd909`; do not rewrite their
history. Frozen source audit SHA-256:
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.
Current direct pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
```

## Required constructor rule and evidence

For every accepted binding body, the existing body-root occurrence is assigned
to the outermost **retained canonical HIR node**, regardless of constructor:

| Retained root constructor | Preserved body-root occurrence maps to |
|---|---|
| `Atom` | Exact `IdentifierExpression` or `IntegerLiteral` key |
| `Apply_ml` / `Apply_call` | Exact outer `MlArgument` / `CallTail` key |
| `Group(E)` | Exact `ParenthesizedExpression` key |

Do not collapse a retained `Group` to expose an inner Apply as root. Proper
retained descendants receive distinct canonical-HIR IDs after existing carrier
formation, in source preorder, with each exact constructor/source key. For
`my z = (f x)`, Group keeps the body-root ID and parenthesized key; inner Apply,
callee and argument get appended IDs and their own exact keys. Parentheses elided
by the existing association adapter around an atom remain elided only where
that adapter actually elides them; the root ID follows the retained Atom's exact
key in that case.

Static feasibility: trace the pinned ordinary Group key owner. Establish that
`source_keys(parsed)` contains every parse-owned syntax node; the LocalSource
`ParenthesizedExpression` branch obtains the key through the checked `self.key`
lookup and retains Group as a node. This supports key availability/mapping only;
it does not expand the fixed-literal parser audit or establish arbitrary parser
acceptance. If ordinary association cannot provide an authentic unique
ParenthesizedExpression key for a proposed retained Group, preserve the exact
residual and stop rather than reconstructing a key or eliding Group.

Keep the rev3 root collision rule: same existing key is retained without
insertion; a conflicting root key fails `InconsistentIdentity`; descendants and
root mapping are staged and published atomically via checked `append_stage`
after carrier passes. Carrier outcomes, IDs and ordinals remain unchanged.

Update design sections on root mapping, finalization, supersessions and
regressions consistently. Required regressions: root Atom, root Apply, Group
around Atom, Group around Apply (`my z = (f x)`), nested retained Groups, exact
root/descendant keys, no Group elision, unchanged carrier identities.

## Exact leases and bounded sequence

Luna/high author <=90s; exact writes only to:

- `notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`
- `tasks/agent-loop/inbox/20261017-ordinary-hir-application-admission-successor.md`

Prior revisions stay immutable in Git. No parser/source audit rewrite.
After STOP/freeze, run sequential fresh review: spec <=60s, compiler <=90s,
architect <=90s, of the same artifact, handoff, source audit and pins. Spec
checks all three constructor rows and supersessions; compiler checks Group key
availability, source audit boundary and post-carrier feasibility; architect
checks preserved root allocation and carrier noninterference. Reviewers are
read-only and write no files. No overlap. If a major finding exceeds the 90s
author cap, stop REVIEWED-PARTIAL and record the exact residual.

Cap: 480s total: Luna90, reviews240, coordination60, reserve90. Predecessor
220s is retired with no carryover. Three inherited UNKNOWN leases stay
quarantined.

## Non-goals and stop

No code or test edits/runs, builds, Cargo, runtime probes, new source census,
Call typing, solver acceptance, source T, theorem closure, production promotion
or final adoption. After CLEAN review, exact final user approval is still
required. Closeout states original theorem gates closed (0), implementation /
test behavior (none), and next open gate.
