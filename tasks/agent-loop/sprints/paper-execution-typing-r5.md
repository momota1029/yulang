# Paper execution typing substitution — r5

Status: primary-only continuation issued at the R4 resource boundary.

Branch / baseline: `research/simple-sub-intrusion` at
`e9735cc2640d73114fd52b55bcda7105c739595e`.
Authority: `docs/yulang-operational-type-safety-ja.tex`, §types and the
simultaneous substitution claim at lines 953–977, item 2; downstream safety
theorem at line 1140. Preserve the full paper judgment, constructors,
quantifiers and source scope. No generic preservation premise, assumed target
substitution theorem, `Bad` typing, or reduced language is admissible.

Frozen direct dependencies at admission:

- `PaperExecutionSyntax.lean`: `2c2f7efac389488cdebee22fb2c5c666b183f7c200fd3ffec73c9c2fb41ae81d`
- `PaperExecutionTypingSubstitution.lean`: `f5800430ac04028ef8b7b6f1faf5004aa0cab48cc472e608d1c0ca255c51f3b4`
- `PaperTypeFormation.lean`: `e090a4674fcdac27dc73b50b8a0f32c65618c81d1ccd350648319ecfb4a1f454`
- `PaperTypeSubstitution.lean`: `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`

## Original outcome and proof stages

The unchanged parent outcome is the paper's simultaneous type-substitution
theorem for every execution typing judgment, including declarations,
operation instances, contexts, plans, payload/response pairs, continuations,
patterns, primitive/template cases, and the exact shared `Xi`. Retain the full
constructor inventory in `tasks/agent-loop/inbox/paper-typing-subst.md`.

Use the generated mutual recursors for the four current judgments, supplying
all four motives explicitly. First establish correct environment-index
transport and constructor normalization under `mapPaperValue`,
`mapPaperComputation`, declaration mapping and `subst`; then apply the resulting
induction structure to every paper judgment and binder. Reuse the checked
operation-instance substitution results where their hypotheses match. Replace
`ValueGraph.guarded : Prop` with the paper guard before claiming graph coverage.
Apply each checked result to the original parent; a partial judgment or helper
alone does not close it.

Success evidence is either a checked full theorem with exact type and complete
axiom audit, a source-qualified counterexample to the original claim, or a
specific checked result that strictly reduces the parent proof to a named,
smaller premise and owner. Record omitted constructors and the first remaining
premise without relabeling the parent as closed. Full type inference,
executor safety, source/native correspondence and A/B obligations remain
separate gates.

## Lanes, resources and review

Proof owner/checker/cache owner: primary `/root`, serial construction only.
`collaboration.list_agents` at admission showed only `/root`; the configured
dispatcher and eight historical/foreign worker reservations have no cessation
receipts, so keep them quarantined and admit no worker, reviewer, Astra, Rust or
native process. This is degraded serial work; no live agent/model execution is
claimed. There is no independent implementation lane in this Lean-only packet;
do not change compiler semantics. Independent review remains NOT_RUN and is
required before promotion.

Fresh R5 allocation: at most 900 primary active seconds, 8 serial Lean/Lake
invocations, and 120 cumulative checker seconds. Prior R1–R4 charges remain
recorded; this is a new bounded continuation, not a refund or rewrite of prior
usage. One owner controls `.lake`; build only after coherent edits. Stop at the
first exhausted limit, a counterexample, dependency/authority change, or user
STOP. Preserve exact diagnostics and do not use nested CLIs.

Exact primary leases: this contract, `PaperExecutionTypingSubstitution.lean`,
`tasks/agent-loop/inbox/paper-typing-subst.md`, and
`tasks/agent-loop/current.json`. `PaperExecutionSyntax.lean` remains held by
the primary but requires a coherent edit before modification. No root imports,
manifests, Rust sources, or unrelated task records are leased.

Dispatcher selection was unavailable because the live inventory had no
dispatcher and no safe slot for a new assignment. The previously recorded
within-contract next step is retained; no new semantic or source-domain choice
is made. Run `python3 tools/agent_sprint.py check` for state consistency. At a
substantial verified milestone or the next resource boundary, freeze the
outcome, update compact state, and consult the dispatcher if capacity permits.
