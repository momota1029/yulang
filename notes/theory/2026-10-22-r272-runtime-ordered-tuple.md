# R272 — ordered Tuple runtime construction

Status: provisional implementation packet in progress; unreviewed. The parent Yulang2 sample and proof-backed compiler/evaluator goals remain open.

## Parent application

R270 and R271 preserve Tuple children through candidate traversal and the source Value-reference graph. R256 identifies the next source-owner obstruction: runtime compilation rejects `LocalSourceForm::Tuple`, and runtime values cannot represent products. R149 requires arbitrary finite ordered products and left-to-right evaluation, including correct behavior when evaluation suspends or captures a continuation.

This packet adds provisional runtime construction and preservation of already-evaluated tuple prefixes. It does not establish public type support or prove source/native correspondence.

## Planned evidence

- Source Tuple compiles to a constructor with ordered child labels.
- Runtime frames evaluate children in order and retain each full received view.
- Immutable prefix nodes are safe to share when continuation frames are copied; a resumed branch appends without mutating the prior prefix.
- Focused runtime tests exercise direct/nested values and effectful child resumption without replay.

No independent review is available under the user's solo-work instruction. Candidate inference, source/native proof, public types, imports, host integration, exact R149 outputs and production remain OPEN.
