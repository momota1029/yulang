# Conditional source construction in the inference playground

Status: experimental source implementation reviewed and verified; local theorem
and bounded source/action bridge independently reviewed and accepted.
Branch: `research/simple-sub-intrusion`.
Baseline: `13c100980a75e294fb78200de51cf702d7499483`.
Authority: the user's continued implementation/proof/repair instruction and
[top-level principles §1.1](../design/2026-10-11-yulang-inference-top-level-principles.md).
Mode: M2, two independent implementation reviewers (`compiler_referee`,
`spec_auditor`); one separate bounded proof review. Benchmark process/sample
budget and consumption: zero. Convergence: close all accepted major findings,
retain prior clean scope and verify the changed owners.

## Executable result

The actual parser/HIR/candidate pipeline now accepts the existing inline syntax:

```yulang
my example = if true: 1 else: "str"
```

Run it with:

```sh
cargo run -q -p yu-playground -- tools/inference-playground/examples/conditional-union.yu
```

The finite exported graph retains both `IntPositive` and `StrPositive` bounds.
Changing true to false preserves both contributions. An Int-only consumer
conflicts even for the constant-true source, and the CLI withholds its output.
This does not add a principal-type prettyprinter or perform constant folding.

HIR retains Boolean/String and ordered If/elsif arms with an explicit else.
Each child has its authentic source occurrence and restored lexical scope.
Boolean resolution follows frozen Oracle `a58eefc31`,
`crates/infer/src/lowering/name_ref.rs:72–83`: lexical binding, exact Boolean
literal, then module lookup. Strings with interpolation and conditionals
without else remain outside this private carrier; no language rejection is
inferred. The existing parser grammar and default HIR route are unchanged.

Every condition receives a Bool demand. All branch values constrain one fresh
result; every condition/body/else computation effect constrains its effect.
Deferred native endpoint resolution preserves parameters, module/local uses
and ascriptions. Distinct Bool/Str tags and polarities survive the shared
canonical types, candidate capture/freshening, F5c boxed/flat transport and
finite graph observation. Legacy test adapters gained distinct corresponding
cases without altering previous expected outcomes.

## Review repair and cost

Both independent implementation reviewers identified the same major defect:
packing all facts into one If occurrence's `u8` slots imposed a 51-arm cap.
The source generator now uses each direct child's own unique occurrence with
fixed slots 50 (value) and 51 (effect). Existing child constructors use lower
slots. Nested conditionals receive their incoming link on their own occurrence
and emit outgoing links on their children; endpoint aliasing does not alias
source occurrences.

The spec auditor approved replacing the newly introduced cap-rejection test
before the repair: it had no authoritative baseline contract and encoded the
incidental packing limit. A 62-arm success test now retains Int, a late Str
branch and Unit; a late invalid condition still conflicts. An internal test
checks exactly one value and one effect fact for each of the 125 distinct
children, with no parent-occurrence substitution. A local polymorphic-use
test retains both captured primitive branches and rejects an Int consumer.
Both delta reviews closed the finding with no new findings. README and the
remaining source envelope passed the conformance delta review.

Collection adds linear work/storage in the actual conditional children and
accounts for retained strings/arm vectors. New primitive cases have constant
size; ordinary leaf precollection and existing Int/Unit counters are unchanged.
The source action has a fixed payload rather than another retained arm vector.
No new cache, timing experiment or solver-time bound is introduced.

## Proof and unresolved graph decision

The [join/source bridge](../theory/2026-10-14-conditional-constraint-join.md)
derives, for one shared assignment and any finite branch list, that fresh
result lower bounds have exactly the join as their least admissible result,
and that eliminating that result against upper consumers preserves the
constraints. It identifies the actual HIR, action generation, native admission
and consumers, rather than treating inert stored records as execution evidence.
Fresh independent `compiler_referee` review passed the frozen theorem and
all 22 implementation dependency hashes without findings. The primary accepts
shared-assignment elimination, the least-result/empty-consumer law, actual
all-child construction, child-occurrence uniqueness, native activation and
the bounded consumer correspondence. This closes the local value-generation
obligation; the original global parent obligations keep their scope and owners.

Definition-owned Value references traverse every new child. If-result and
Apply-through-If incidence remain a separate narrow choice in the
[reviewed Draft](../design/2026-10-14-conditional-value-references.md).
The primary sent the concrete alternatives for user selection; no answer is
assumed. Existing Name/Apply fragment boundaries remain in force. The earlier
intrusion activation theorem is reused only under its established graph/event
premises; complete conditional-result SCC correspondence is still open.

Follow-up clarification at `e9a7700b7`: an independent architecture audit found
that the proposed A/B extension cannot change current semantic SCC membership
or intrusion qualification. No existing edge enters an Expression Value, and
named owners reach only named Values. The draft now records this correction.
The open choice concerns outgoing source-reference ownership and does not block
independent effect/handler construction. The reviewed join derivation and its
code dependencies are unchanged; its recorded Draft hash identifies the earlier
review snapshot, not this subsequent explanatory correction.

Global soundness, required principality, source-global event applicability,
intrusion typing preservation, effects/hygiene constructor correspondence and
production/F5 cutover retain their original open gates. The established hygiene
proof is available for the next executable permission/protection seam.

## Verification

Cargo commands used `CARGO_BUILD_JOBS=2`, `timeout 300s`, and one test thread.
Final focused coverage totals 138 cases, including 28 type doc tests; repeated
reruns and overlapping early filters are not counted twice.

| Command (after `cargo`) | Result |
| --- | --- |
| `test -q -p yu-types -- --test-threads=1` | 39 unit, 4 integration and 28 doc tests passed |
| `test -q -p yu-hir --features shadow --test conditional_local_source -- --test-threads=1` | 6 passed |
| `test -q -p yu-solver --features shadow-apply-candidate --test candidate_conditionals -- --test-threads=1` | 10 passed |
| Same solver command, `--lib bool_str_primitive_tests` | 1 passed |
| Same solver command, `--lib conditional_constraints_use_distinct_direct_child_occurrences` | 1 passed |
| Same solver command, `--lib selected_flat_candidate_matches_boxed_q_r_and_normalization_counters` | 1 passed |
| Same solver command, `--test candidate_annotated_primitive_formals --test candidate_intrusion_observation --test candidate_lifecycle_retirement --test candidate_unit_source` | 21 + 3 + 2 + 4 passed |
| `test -q -p yu-playground -- --test-threads=1` | 3 writer unit and 15 CLI tests passed |
| `check -q -p yu-solver --features shadow-apply-candidate` | passed |
| `check -q -p yu-solver` | passed without warnings |
| `check -q --workspace` | passed without warnings after the repair |

`rustfmt --edition 2024 --check` passed on the new HIR/solver integration tests
and tool CLI tests. Only those test files were formatted; compact pre-existing
solver modules were not broadly reformatted. `git diff --check` passed.

The first ascribed-branch fixture used unsupported `"str":str` syntax;
correcting it to the existing `"str" as str` grammar preserved its intended
test. Initial library-test compilation identified four exhaustive test-helper
consumers; each now maps the distinct primitives without weakening assertions.

No full workspace test suite or benchmark ran. The previously established
solver-to-core development-dependency graph-check failure and conflicting
candidate `fresh_use` observation test mismatch were not altered or rerun.
They remain separate recorded issues from the preceding checkpoint.

## Integration ownership

The primary synchronizes `tasks/current.md`, `tasks/research-lab.md`, the design
index/direction, the previous playground checkpoint and this record. All child
write leases are frozen at integration. The unrelated pending negative-formal
permission question directory stays unstaged and uncommitted. This checkpoint
contains the coherent experimental source slice, executable examples, proof
artifact and explicit unresolved graph proposal; it claims no production cutover.
