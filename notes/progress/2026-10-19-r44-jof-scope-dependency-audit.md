# R44 primary audit: JOF scope versus output dependencies

Status: **primary finding; candidate revision required; not independent review**
Sprint: `call-output-owner-jof-20261019-r44`, revision 1 candidate
Parent: unchanged inference/evaluator theorem and Simple-sub A/B, **OPEN, 0 → 0**
Author: Luna primary `/root`

## Finding

The R44 draft sets `Delta_A := Gamma_q` for the output declaration
`Desc(C_q, rho_A, ValueDescription, sigma_q, Delta_A)`. The pinned
authoritative source-Generalize construction defines an ordinary endpoint
record as

```text
Desc(C,q,sort,sigma,Delta)
```

where `Delta` is its **free dependency telescope**. This is separate from
`sigma`, the original type scope in which the declaration is available. The
definition explicitly permits an independently specified inference
introduction to own such a declaration, so it does not rule out a JOF output
owner. It does require that the owner establish the declaration's actual
dependencies.

R44 proves only the conditional scoping fact that, if `Gamma_q` is an
authentic well-formed context before `sigma_q`, then its identity inclusion is
available there. It does not prove that every entry of `Gamma_q` is a free
dependency of the fresh output description `A_q`. Full-context availability
therefore does not discharge the `Desc` constructor premise. Treating the
context and dependency telescope as interchangeable could make an otherwise
unused challenge, event field, provider, or local description an artificial
dependency, changing Generalize's per-frame and alias behavior.

This is a concrete design defect in the current formulation, not evidence that
the source language has no Application output owner. It also does not establish
that `Delta_A` should be empty or that any particular context entry is absent.

## Corrected candidate obligation

Keep the source scope and dependency telescope distinct:

```text
sigma_A = actual source cursor after both operand schemas
Delta_A = D_q, the exact ordered free-dependency telescope supplied by the
          independent Application output-owner constructor
```

The owner must construct `D_q` before the q-local output-indexed Call headers
are formed. It may use the actual operand interfaces and previously formed
source records; it may not recover dependencies from `Q_q`, a solved endpoint,
native levels, or a successful query. A well-formed instance additionally
needs a typed inclusion of each `D_q` entry into the prefix available at
`sigma_A`, preserving source order and predecessor dependencies. Later Call
headers remain formed under the full actual context and may refer to `A_q`;
that fact alone does not enlarge `D_q`.

Once `D_q` is constructed, Generalize must apply its existing retain/fix walk
to those actual typed edges in both incoming frames and for aliases. This
audit supplies no `D_q`, no concrete C/D copy pair, and no frame projection;
those premises remain open. The candidate cannot be promoted or implemented
from this audit.

## Proof actually established

Let `Gamma` be a well-formed ordered telescope and let `D` be a typed ordered
sub-telescope whose entries all occur in `Gamma` before cursor `sigma`. If the
fresh descriptor owner preserves those entry types and predecessor edges,
then its declaration is well scoped at `sigma` by the source `Desc` rule.
The proof is direct: every free dependency is available in the declaration's
original scope, in its original order; freshness prevents capture of an
existing source declaration. This is a local formation lemma only. It does
not construct the actual `D_q` or establish JOF's q instance.

## Evidence and next step

- Authoritative source: `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, §3.3 and §§5.1–5.2; SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Typed-computation core: `notes/design/2026-10-02-typed-computation-core-elaboration.md`, application row and §3; SHA-256 `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`.
- R44 candidate under audit: `notes/design/2026-10-19-call-output-owner-jof-r44-draft.md`; SHA-256 `af9765c72edb19ef7c888e0c6751518ba3a1ccf79c5c99d7297796c1346d84fb`.

The exact next proof premise is the independently formed source constructor
that owns `A_q` and supplies `D_q`, followed by the actual q-indexed header
formation and the two-frame/alias Generalize map. Fresh independent
`compiler_referee` and `spec_auditor` review remains required; this primary
audit is not self-certification. No Rust, evaluator, fixture, test, build,
Cargo or runtime change follows from this finding. The original parent remains
**OPEN, 0 → 0**.
