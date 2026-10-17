# Frozen handoff: ordinary-hir-application-admission-successor

Sprint: `choice-a-group-root-ownership-repair-20261017`, revision 1.
Sprint SHA-256: `21f4e33adebb4e92894bfe5fbc96eb96dac49135bbb06f65c18d0211991c332e`.
Assignment: `ordinary-hir-application-admission-successor`, handoff revision 4.
Successor artifact revision 4:
`notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`,
SHA-256 `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
Revision 3 is preserved at baseline commit `a640dd909132b2be1d1bbbe35a4249e16642b84b`.

Parent: original Yulang inference/execution goal; original A/B claims,
quantifiers and source/native obligations unchanged. Original theorem conditions
closed: 0. HIR-APP-CST-1 remains candidate pending fresh compiler review.
HIR-APP-ADMISSION-1 remains OPEN pending sequential reviews and explicit final
user approval.

Baseline `a640dd909132b2be1d1bbbe35a4249e16642b84b`. Frozen source audit SHA:
`e8a320be0e78ecc2c5ee5210338476740c03a1fae61fb2747ec39636286ad501`.
Direct pins:

```text
crates/yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
crates/yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
crates/yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
```

The spec review of rev3 was CLEAN on prior mapping fixes. Compiler review found
a MAJOR because retained root `Group(E)` had no occurrence-owner rule. Revision
4 generalizes the root ID rule across retained `Atom`, `Apply` and `Group`:
Atom maps to its exact identifier/integer node, Apply to its exact outer tail,
and Group to its exact `ParenthesizedExpression`. For `my z = (f x)`, Group
retains the old body-root ID; inner Apply and its operands receive distinct
post-carrier IDs and keys. Group is not elided. Parentheses elided by the actual
association adapter around atoms remain distinguished from a retained Group.

Static key-availability trace against pinned owners (not parser/runtime evidence):
`source_keys(parsed)` visits every node of the parse-owned source root and stores
its exact `SourceNodeKey`; `LocalSource`'s `ParenthesizedExpression` branch
calls the checked `self.key(&node)` then retains `LocalSourceForm::Group`. This
establishes a source-key lookup for an actual retained Group node, but does not
prove arbitrary parser acceptance or expand the fixed-literal source audit.
Atomic same-key/conflict checks, `append_stage`, and post-carrier canonical
finalization remain implementation obligations. No identity representation or
Group-elision policy was added beyond the explicit constructor table.

Outcome class: successor proposal revision 4; not adopted. Author Luna `/root`,
requested/effective model UNKNOWN; 90s fully conservatively charged, STOPPED.
Exact author leases: design and handoff. No code or tests. `python3
tools/agent_sprint.py check` and `git diff --check` are required before commit;
no tests, builds, Cargo, parser/runtime probes or compiler execution ran. Three
inherited UNKNOWN leases remain quarantined. Next: sequential spec <=60s,
compiler <=90s and architect <=90s review of these exact bytes, source audit and
pins.
