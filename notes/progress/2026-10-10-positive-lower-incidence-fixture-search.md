# Positive lower before shared incoming-Allowance restoration: fixture search

Date: 2026-10-10
Status: frozen, independently reviewed bounded source characterization; no runtime witness or R closure
Assigned baseline: `ddbb588d27de14bd31702ad4a3b18c5309e76bcd`
Producer: `/root/positive_lower_incidence_fixture_search`, researcher-contract leaf
Exclusive lease: this note only

## Objective, authority, and result

Search existing authored solver fixtures for a mixed concrete/symbolic **root
computation** Allowance whose incoming-incidence owner is shared or extruded and
already has a positive lower when its negative restore starts. This is a static
fixture/source-order search complementary to the constructive R lane. It does
not repeat the reviewed `candidate_effect_annotation.rs:346` derivation.

Authority: contextual attachment/admission design §3.1 and §4, especially Bound
insertion, Opposite replay, Capture/freshening and SCC intrusion; the latest
`tasks/current.md` next-action paragraph; and the four conditions in
`2026-10-10-canonical-bound-fiber-source-witness.md`, “Exact missing witness and
next action.” Approved annotation polarity, attachment grouping and actual
parent/copy identity remain fixed. Rules and the researcher contract were read;
the yulang-proofs skill was applied for claim/source separation.

**No qualifying existing fixture was reconstructed in this bounded search.**
The source siblings either provide actual-argument effects after the relevant
first local lookup, provide effects on another port, or contain a mixed row in
a nested callback interface rather than a root computation annotation. This
is a negative search report, not a proof that no fixture or ordinary program
can qualify. In particular, the complete later module-use traces were not
derived. The primary requested stopping at this bounded search.

## Search envelope and discriminators

`rg --files crates/yu-solver/tests/` enumerated 20 Rust files. Two lexical searches
over that directory located mixed concrete/symbolic row spellings and symbolic
effect annotations. The mixed spelling search returned six lines: four in
`candidate_effect_annotation.rs` and two in `candidate_formal_effect_polarity.rs`.
The broader symbolic-row search returned 17 lines. These are line counts,
not parsed-program counts. Rust `format!` variants were inspected where matched;
this is not an exhaustive Rust string/macro evaluator.

The whole effect-annotation and formal-polarity files were read. Relevant
function-formal, primitive-formal and local-recursion slices were inspected.
Other tests were searched for annotation/effect/source constructors; their
complete Rust control flow was not audited. No fixture, test or probe was added.

| Existing source locator | Bounded finding |
| --- | --- |
| `candidate_effect_annotation.rs:345` | Direct `tick::next()` precedes root `[tick, 'e]` admission. This supplies an early initializer effect, but no source trace establishing a positive lower on the particular shared incoming-incidence copy was obtained. The concrete root member is an allowance, not a positive seed. Full later module capture/extrusion/restore is unverified. |
| `candidate_effect_annotation.rs:346` | Previously reviewed empty-lower shared-owner trace, retained as a dependency rather than rederived. |
| `candidate_effect_annotation.rs:403` | The same local `maker f` prefix has a final `local` lookup before the later `maker {effect}::next` actual-argument application. Changing `tick` to `other` changes a later provider, not that prefix's positive-lower timing. |
| `candidate_effect_annotation.rs:425` | `listed` and `residual` are two later fresh `maker` applications. Neither occurs in the original `maker` body before its final `local` lookup. No full trace of the later fresh uses is claimed. |
| `candidate_effect_annotation.rs:286,315` | Root rows are singleton symbolic `['e]`, not mixed concrete/symbolic Allowances. The latter fixture explicitly supplies its actual argument later. |
| `candidate_effect_annotation.rs:134,138,145` | Symbolic annotation is on the returned Function's result-effect port; there is no explicit mixed root computation row. |
| `candidate_formal_effect_polarity.rs:24–25,45` | `[io, 'e]` belongs to the nested callback result in `consume:(int -> [io, 'e] ()) -> ()`. It is not the root computation row of a local initializer. Line 45's provider applications occur after `first = bridge` and `second = bridge`. |
| `candidate_annotated_function_formals.rs:216,235,259,279` | Singleton symbolic Function ports; no mixed root annotation. |
| `candidate_annotated_primitive_formals.rs:425–438` | Root checks are `[]`, `[E]` or `[tick]`, with no symbolic tail. The effectful named-value initializer at :404 has no explicit mixed root row. |
| `candidate_local_self_recursion.rs:97–104` | Recursion with concrete Function result rows; no mixed root computation annotation. |

The :403/:425 exclusions concern only the original final local lookup, under
ordinary HIR projection, valid indices, successful operations and no external
state injection. They do not exclude a qualifying later lookup. Authored
`solve(...).unwrap()` and conflict assertions are source intentions; they were
not run and do not establish parser/HIR success or runtime acceptance here.

## Exact owning operation and required ordering

`candidate_source.rs:229–280` assigns level 1 to the body, preserves the level
through Lambda, and adds one per block initializer. Thus the sibling `maker`
prefix has `f` at level 1, the `local` initializer/annotation at level 2 with
boundary 1, and `ignored`'s application at level 3. Blocks append each
initializer/install before their final expression (`263–302`), and execution
visits the action list in order (`549–574`). The `maker` schedule completes
before its dependent external applications; the graph plan executes source
schedules before capture/publication (`candidate_scheme.rs:681–737`).

For the already established shared-owner route, write the older negative copy
as `C1`, invocation parent as `I3`, local annotation tail as `T2`, and root view
as `R[{tick};T2]`. A genuine negative extrusion records the parent and inserts
`BoundKey(I3, Positive, C1)`; it copies **upper** bounds and does not thereby
insert a positive lower on `C1` (`candidate_extrusion.rs:96–163`). The reviewed
dependency supplies the specific incidence `C1 - Allowance(R)`.

The ordinary owner that can supply the missing physical lower is
`candidate_apply_effect` (`candidate_extrusion.rs:726–749`). To create
`BoundKey(C1, Positive, b)` by this route, an actual comparison must reach
`b <: C1` with either a nonrow operand or a row `b` older than `C1`. Equal-level
or younger row lowers are stored negatively on `b`, so merely showing a row
edge towards `C1` does not establish the required positive vector entry.
The insertion must finish before the targeted negative restore's saved
opposite count (`candidate_extrusion.rs:611–615`). This identifies the actual
constructor and ordering requirement without inventing a test program.

A source provider carrying a concrete operation/annotation member can in
principle reach this operation through ordinary Function/result-effect
comparison and Support expansion; the exact source route and delivery to
`C1`, rather than `I3`, `T2` or an annotation port, still need evidence.
Support expansion enumerates members/tail (`candidate_effect.rs:760–782`).
The root checking constructor deliberately supplies only a negative check
(`1172–1207`); it cannot supply this missing lower by naming `tick` in `[tick, 'e]`.
An unmatched member checked against Allowance may instead flow into its tail
(`803–812`), another distinct owner.

Capture of local `T2` emits incoming negative Allowances before its own vectors
(`candidate_scheme.rs:488–500`). Shared rows are not expanded (`440–442`), so
their existing physical lowers must already live in the session or be supplied
by earlier reconstruction work. Freshening preserves older owners
(`841–853`), restores in captured-bound order (`998–1032`), and only then links
the fresh local value to its use (`1128–1133`). Therefore a provider constraint
caused only by consuming that same fresh value is too late to justify its
already-started incidence restore. Earlier source actions or earlier use-time
restores are possible routes, not established fixture facts here.

For a within-loop omission witness, nonempty positive storage alone is also
insufficient: a later outer index requires at least two physical opposite
entries at the saved count, then a first callback must change the relevant
owner/vector. The remaining exact missed obligation, ordinary replay failure
and diagnostic non-rescue remain the original R conditions 2–4. None was
established by this search.

## Checks, resources, and remaining scope

Commands: `cat` rule/skill/design/fixture reads; `tail` current-task read;
bounded `rg` locators; `nl -ba ... | sed -n ...` source slices; `wc -l`; and
`sha256sum`. Several initial broad locator captures truncated; subsequent
narrow reads supplied the cited constructor/schedule slices. No Git command,
Cargo/build/test, solver execution, mutation campaign, benchmark, descendant,
interactive question or config change occurred. Only this leased note changed.

Zero heavyweight processes, executable samples, seeds or enumeration ranges.
Independent static reads were batched; resource-intensive jobs were not run.
CPU/RAM totals and task wall time were not measured. An independent
regression-auditor review reproduced the fixture inventory, found no omitted
qualifying sibling or overclaim, and accepted the constructor discriminator.
The primary rechecked every listed source/design dependency hash against the
baseline commit; all match. The source search shares the implementation/
authority premises of the proof lane and has no separate runtime oracle.
Failed allocations, unsupported HIR,
external mutation and alternative producer schedules invalidate the conditional
schedule statements. Arbitrary source programs, later module uses, exact fiber
counts, qualifying SCCs, diagnostics and R closure remain unverified.

Recommended next action: obtain one narrowly authorized source trace at the
normal `candidate_apply_effect(b, C)` producer seam, recording the **positive
physical key on the canonical shared owner before restoration**. Require the
source occurrence and level ordering; a lower on its tail/root port or created
after linking the fresh use fails the discriminator. Do not repeat an
empty-lower fixture trace or enlarge a supplied-transition toy model.

## Dependency snapshot

The primary compared the current worktree dependencies with the assigned
baseline `ddbb588d27de14bd31702ad4a3b18c5309e76bcd`; all listed hashes match.
No dependency was changed by this producer.

```text
46207880936209875117a48aba44fb19ed2736afcd827e8d6d5bab5ee41109a2  tests/candidate_effect_annotation.rs
dc89def4c2653960e29474135d4e2f91c076bd8a27eb54b048088820a915d636  tests/candidate_formal_effect_polarity.rs
ced364cdbca6c19752e0aa2e36b1516f9337484a8c10323fd632fb81a04163d0  tests/candidate_annotated_function_formals.rs
137b51c32f14ada552954648171c091526d8b26e786f3c36cddf3c134830281d  tests/candidate_annotated_primitive_formals.rs
a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a  tests/candidate_local_self_recursion.rs
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  src/candidate_source.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  src/candidate_scheme.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  src/candidate_extrusion.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  src/shadow_apply.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  src/lib.rs
```

Paths in the block are relative to `crates/yu-solver/`. The exact command
`sha256sum crates/yu-solver/tests/*.rs | sha256sum` yielded directory inventory
digest `89d28ce834b071a607fcaae7503f3c641b425c82d96897a538a51ec7011e9e6a`
(digest of sha256sum output, including relative path names).
Design SHA-256: `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
Four-condition witness note: `715143ea458825c88d41aa0ce7cb57be8290dd5586c1bd7cc0f86e1537721c77`.
Reviewed shared-Allowance trace: `7b8d31ebd4435dd021964b9ea5d2e9b74c463caa0e18edc436e4ce5d32341750`.

## Commit packet

- Exact lease: `notes/progress/2026-10-10-positive-lower-incidence-fixture-search.md`.
- Baseline: `ddbb588d27de14bd31702ad4a3b18c5309e76bcd`.
- Changed dependency hashes: none; all listed dependencies match the baseline.
- Review: independent regression-auditor review found no blocking or major finding; its scope and omissions are recorded above.
- Checks: static fixture/source/rule reads, dependency-hash equality against baseline, and `git diff --check`; no executable verification.
- Proposed commit: `research: bound positive-lower incoming-Allowance fixture search`.
- Shared deltas intentionally left for primary/curator: preserve R as open; record the sibling timing exclusions and exact pre-restore positive-owner discriminator. Do not mark the untraced direct-operation/module-use case impossible. No shared task/index/theory/question files changed.
