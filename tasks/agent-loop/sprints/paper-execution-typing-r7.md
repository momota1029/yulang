# Sprint FULL-PAPER-TYPE-SUBSTITUTION-20261025/r7 — explicit mutual transport

Status: issued by the primary after R6's failed proof-lane boundary.
Branch / baseline: `research/simple-sub-intrusion` at
`ee689474d4c77b176ce445483736753e4f58ace2`.
Authority: `docs/yulang-operational-type-safety-ja.tex:953-977` item 2, with
record rules `:217-231` and record code lemma `:724-749`. Preserve the original
full paper claim and all source cases. Downstream safety and inference/executor
A/B gates remain OPEN.

## Original result and R6 evidence

R5's checked partial substitution theorem remains valid only for 13 value
constructors, five computation constructors and list rules. R6 added an
unverified candidate record shape, field membership and payload judgments, but
four focused builds failed within 6/6 proof-lane Lake calls (22.47 build
seconds). The exact failures and artifact hashes are frozen in
`tasks/agent-loop/inbox/paper-typing-subst-r6.md` (SHA-256
`a724bf16688d4af4801a26cf84a6a954c1227479dfd6dc4b221c82aa31e7985b`). R6's
candidate is not in the main checkout and is not accepted as proof.

R7 targets the same record/field/lookup substitution slice using one explicit
mutual recursor with all five motives (`ValuesTyped`, `ValuesAllTyped`,
`RecordPayloadsTyped`, `PaperValueTyped`, `PaperComputationTyped`). Before
construction, inspect the actual generated recursor types from pinned Lean
4.35.0. Make environment and record-type indices explicit in motives and
transport every shared index together. Prove the raw record list map equality
using the pinned `List.attach_map_val` lemma (Init/Data/List/Attach.lean:149),
after confirming its exact declaration. Do not retry R6's same mutual theorem
block with cosmetic `simp` changes.

No `Formed`/`RecordFormed` substitution premise may be added: the original
paper theorem gives arbitrary simultaneous σ and no such hypothesis. Keep
record row labels, required labels, raw Presence tags, declarations, and payload
types distinct. Paper requires required labels ⊆ actual domain ⊆ declared
labels, typing each present payload, optional absence, required-only `field`,
and `lookup` for any declared label returning `1 ∨ A`. The raw Presence tag's
meaning is not stated in paper runtime-value syntax and remains an explicit
source-correspondence question. Rust's inspected playground has record
construction and parameter/default lookup but no established direct paper
field/union-lookup correspondence. No compiler change is authorized.

## Exact primary lease and resources

Primary `/root` owns and may edit only these R7 paths:

- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`
- `tasks/agent-loop/inbox/paper-typing-subst-r7.md`
- `tasks/agent-loop/current.json`
- this contract
- `tasks/agent-loop/history/archived-resolved-outcomes-r1.json` (compact-state archive)
- this project's `.lake` generated Lean/cache outputs, exclusively for this
  single verification owner

Read-only inputs: the R6 handoff, frozen paper and existing formation/type
substitution dependencies. The R6 candidate in `/tmp/yulang-r6-paper-record-proof`
is unverified input; inspect it before applying any parts. No workers, Astra,
Rust/native build, implementation changes, tests, or other source paths are
assigned. The eight prior UNKNOWN leases remain quarantined and unchanged; no
slot is reclaimed. The currently live root session is the only proof writer.

Budget: <=900 active seconds, <=8 serial Lean/Lake invocations and <=120
cumulative checker seconds; one Lake/Lean process at a time, `-j1 -M1024`.
R1-R6 charges remain recorded and are not refunded. Inspect the proof tree
before the first edit. Stop after a coherent successful build plus exact type
and axiom audit, the first genuine obstruction after at most two distinct
proof methods, any counterexample, dependency/authority change, budget limit,
or user STOP. Keep failure logs; never use `sorry`, `admit`, generated failed
declarations, project axioms, or stronger hypotheses as a result.

## Verification, parent application, and review seam

Success requires focused module build exit 0; exact types and complete axiom
audits for all five mutual transports and record support lemmas; no `sorryAx`,
failed declaration dependency (including `_f`), or project axiom; and a
source-to-paper case map that distinguishes represented and omitted rules.
Falsifiers: missing required field accepted, undeclared field accepted, payload
type mismatch accepted, absent optional field rejected, list order imposed,
raw Presence equated to row presence without paper evidence, or σ changing
labels/presence/declaration identity. An earlier proof failure was preserved;
R7 must demonstrate that the selected recursor/mapping method changes that
failure, not merely rename it.

Even a fully checked R7 slice leaves variants, nominal tables, binders,
polymorphism, recursive graph guarding, operations/handlers/mappers,
primitives/templates, patterns, continuations and administrative forms open.
It does not close the original substitution theorem, type inference, executor
safety, source/native correspondence or A/B. Fresh independent review is
NOT_RUN until the artifact is frozen and the primary has a safe reviewer slot.
At the boundary, update compact state and consult the selector; only the primary
adjudicates, integrates, commits, inspects the outbound range and pushes.
