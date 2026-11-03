# R308 — actual source/native Call and original Union clauses

Baseline `cde58b51e`. Preserve the unchanged R159 App quantifiers, both child
judgments, common extension, original relational Union and independent arm
laws. R307 authenticates finite source Apply/child roots; R306 computes a
conditional Union-node lookup. Neither establishes EI q_c registration or
logical admission. No semantic or production compiler changes are authorized.

Implementation lane: use a single actual `Arc<HirModule>` for source Apply
incidence and candidate inference, following `CandidateInference::source_call`
and actual generation/admission. Authenticate same owner, occurrence and raw
children, retain Group path, checking cause and all value/effect ports; verify
slot-0 fact lower/upper against native callee/demand, since source_call's shape
checks alone do not rule out a foreign Call's native bundle. Follow actual
result and propagation where existing public evidence supports it; report exact
missing consumer when it does not. Handle conflicts, truncation and foreign
HIR explicitly. Check nested, Group and empty-call cases, use complete stable
term identities rather than raw ordinal equality. Emit proof-readable finite
evidence only when authenticated, and do not identify finite Function ports
with EI-All. Exclusive outputs:
`tools/native-signature-observer/src/bin/source_apply_native_r308.rs`,
`tasks/agent-loop/inbox/source-apply-native-r308.md`, `/tmp/yulang-r308-native`.
Offline locked checks; 1800s; no Git or children.

Proof lane: construct the actual R293 tagged Union consumer from existing
original full trace clauses, retaining world, each branch's own guards, form,
observation fields, all Fin arms and dependent indices. If useful, factor the
common world with proof/evidence conversions and apply the result back to
R293's existing introduction and branch consumers. Investigate the real q_c
registration and apply only if original Inputs and their actual equations
justify it: the original trace clause has an outer `both` while R293's
unionBody has outer `either`, so an unproved literal equation is unsound.
Integrate source/native evidence only if a genuine Lean artifact can be joined
without re-parsing or assuming desired correspondence. State exact remaining
R159 premises and never claim semantic parent closure from local conversions.
Exclusive outputs:
`notes/theory/lean/YulangClosure/ComputedCallUnionClausesR308.lean`,
`tasks/agent-loop/inbox/computed-call-union-clauses-r308.md`,
`/tmp/yulang-r308-proof`; pinned Lean 4.35, per-theorem type/axiom audits,
2400s; no Git/children.

Independent reviewers must inspect actual frozen source and model inputs,
cross-call swap, omitted/double Group, same-position occurrence conflation,
lost/reordered arms, different guards/worlds and hidden desired-equation
assumptions. One heavy checker at a time. Primary integrates and handles Git;
unknown prior leases remain quarantined.

Direct input SHA-256: R307
`c3f63a454831d4193ee708f754d4d1194ececfa5a21d777624556eacb0898a07`;
R293 `50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543`;
candidate_call `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`;
candidate_source `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`;
shadow_apply `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`;
solver lib `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`.
