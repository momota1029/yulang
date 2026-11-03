# Compiler engineering rules

## Core priorities

Yulang code should make the entrypoint, owner, principal data flow, and phase boundary visible. Prefer explicit responsibility over superficially short code.

- Each logical fact has one authority.
- Avoid calculating the same fact in several layers.
- Keep compiler phases and their outputs explicit.
- Do not add local rules to support other local rules when one general invariant can explain both.
- Preserve meaningful types, boundaries, and names; avoid abstraction created only to look organized.
- A test-specific branch is not a language or compiler rule.

The broad architecture is not fixed yet; the old `docs/yulang3-architecture.md` is in the archive tag as reference only. Task-specific Authoritative design documents govern.

## File order

Put the file's main public or conceptual entrypoint first:

- principal `pub struct` or `pub enum`;
- public entry function;
- central result type;
- module orchestration that explains the flow.

Place tables, private helpers, adapters, and implementation detail after the main role. A reader should understand the file's purpose from the first tens of lines.

Avoid files that begin with miscellaneous helpers, internal tables, or implementation machinery while the public entrypoint is buried later.

## Module boundaries

Split by responsibility when a file begins to combine several of:

- orchestration;
- syntax-family handling;
- lowering;
- inference;
- normalization or simplification;
- resolution or scope;
- diagnostics;
- formatting;
- fixtures, golden tests, or test helpers.

The parent module keeps the public entrypoint, top-level wiring, and minimal re-exports needed for navigation. Put detail in children named by responsibility, such as `lower_expr`, `diagnostics`, `scope`, `resolve`, `normalize`, `tables`, or `fixtures`.

Avoid vague modules such as `utils`, `misc`, `common`, and `helpers` unless an established local convention gives them a precise meaning.

## Diagnostics boundary

Core processing should return structured results, causes, spans, and source locations. Presentation text and formatting belong as far toward diagnostics as practical.

Avoid:

- building user-facing strings inside lowering;
- large diagnostic-text branches inside inference;
- detecting the same error cause independently in several layers;
- rescanning CST later to recover spans that the owning phase could have carried.

## Experimental mechanisms

Before introducing an experimental rule or optimization, state:

- its owning responsibility;
- entrypoint and consumers;
- whether it is on a hot path;
- failure and rollback behavior;
- how it can be removed or replaced.

Do not hide experiments inside central processing. Give them a named boundary and a falsifiable gate.

## Code comments

Comments preserve non-obvious design decisions: why a responsibility lives here, why recomputation is avoided, why order matters, the source algorithm, or a fragile invariant.

Do not comment by paraphrasing code, preserving dead implementation history, or leaving ownerless TODOs. A TODO states the completion condition and intended owner.

## Engineering checklist

Before closing a change, check:

- Is the entrypoint easy to find?
- Is the owner of each fact clear?
- Did helpers obscure the main role?
- Did a phase gain a hidden dependency on another layer?
- Did diagnostics leak into core semantics?
- Did a name/path string become semantic?
- Did a fixture-specific exception appear?
- Did the change add a rescan or repeated computation?
- Could the same rule be stated as a language, IR, or constraint invariant?
