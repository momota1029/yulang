# R317 — scoped relational result investigation

Baseline `94459236d`; contract
`tasks/agent-loop/sprints/scoped-relational-result-r317.md` SHA-256
`6cc775be1acbe5aa58792d20c91d241a4576d4e42a2b7381a55f70a0e2a852aa`.
No new source-owned registration or theorem was produced: the existing
source exports lack the authentic complete scoped arm/IF declarations and
the complete EI phase interpretation. The proof lane stopped at that boundary
rather than assume the desired readback or invent source arms.

An independent parent-edge review found a precise distinction in R293. Its
added `TaggedAlternative` preserves the selected packet at the same tuple,
while `relations` also retains the independently supplied original relation;
R293 does not replace all old relations by identity. An identity-shaped
injection alone cannot construct an arbitrary original child-to-result map.
For example, a Boolean relation from `false` to `true` is not a value-preserving
injection. This is an abstract relation example, not a source counterexample.
R310 also retains per-arm scope/binders that R293's endpoint list alone cannot
reconstruct. These remain correspondence obligations, not refutations of
R293's conditional theorem.

The existing `choose` source declaration, candidate construction and runtime
operation path were inspected; they expose actual syntax, types and runtime
events, not the full independent whole-Call arm declaration. Inferring an
empty arm inventory or interpreting source condition branches as those arms
would be unsupported.

The proof worker independently checked five existing declarations in an
isolated pinned Lean 4.35.0 dependency cone: all theorem type and complete axiom
audits passed, with no new theorem claim. Commands, full types and axiom lists
are in `tasks/agent-loop/inbox/source-computed-result-registration-r317.md`;
the audit log SHA-256 is
`6cc126b9c27566ec8d392549b4406394285ac42cb72c84305378fd55e86ad6ad`.
R293's original computation Checking and callable-image membership remain
conditional, and no R159 premise was removed.
