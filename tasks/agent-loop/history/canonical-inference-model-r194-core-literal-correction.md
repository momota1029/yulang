# R194 source-literal evidence correction

Status: primary adjudication of a fresh independent read-only audit. This
supplement narrows the R194 obstruction report; it does not edit its frozen
contract, module or handoff.

## Corrected claim

The broad statement that no total eight-kind mathematical literal type table
exists is too strong. `notes/theory/lean/YulangClosure/CoreSyntax.lean`
defines:

- `Original.Literal.base` and `Original.Literal.toVal` for all eight literal
  kinds (`:139–157`);
- independent `ValTyped` constructors for Unit, Bool, Int, floatBits, String,
  bytes, path and char (`:209–216`).

The file has no adoption/status header. This is concrete core typing evidence,
but its existence alone does not establish that it is the complete accepted
interpretation of `OriginalSource.Literal` or the inference algorithm.
`PaperExecutionSyntax.literalType` (`:576–584`) also maps all eight kinds, but
that module calls itself a syntax layer (`:5–7`) and describes its extrinsic
typing as partial (`:613–618`); it is secondary corroboration, not the missing
source-to-solver bridge.

## Exact remaining boundary

`OriginalSource.Literal` has different raw payload types for three rows:

| Kind | CoreSyntax payload | OriginalSource payload | Remaining equation |
| --- | --- | --- | --- |
| floatBits | `UInt64` | `Nat` | A total, representation-preserving decode and supported-payload condition; no truncation. |
| bytes | `List UInt8` | `List Nat` | A total byte-range-preserving decode and supported-payload condition. |
| path | `List UInt8` | `String` | An independently justified source path encoding. |

Unit, Bool, Int and String payload carriers align. `character String` and core
`char String` also align as carriers; any source lexical validity condition
still belongs to the actual source rule, not to the type table.

Even after this syntax/core map, the original generated literal rule at
`OriginalSourceGeneration.lean:85–89` emits a `.literalDeclaration` atom.
`OriginalSourceInterpretation.lean:843–850` requires that atom to identify a
declaration relation on the same assignment's full descriptor/value/root/event
row, plus independent `valueForm = .ground` and `ground` facts. The core table
does not provide those fields. Nor does it define how the actual Simple-sub
literal constraints are independently satisfied and read back through that
same assignment into the source judgment and `sameScoped`.

Thus the corrected next outcome is **source-payload/core mapping plus the
independent literal constraint/readout equation**, applied to the literal
induction edge of the original soundness root. It is not a request to choose
the eight base types again. No root premise is discharged by this audit.

## Independent audit

Fresh reviewer `/root/r194_model_review`; requested and observed model/effort
UNKNOWN; read-only, no Lean/build/test/Git/edit operation. Verdict: counterevidence
narrowed the obstruction; it did not close it.

Hashes checked before the reviewer's content reads:

| File | SHA-256 |
| --- | --- |
| `CoreSyntax.lean` | `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375` |
| `PaperExecutionSyntax.lean` | `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d` |

The pinned original-source syntax, generation and interpretation hashes match
the R194 activation receipt. Root metric remains **0/4 roots; zero premises
discharged**. The prior failed Lean `rfl` attempt remains unrelated to this
source-semantic adjudication and supplied no theorem or counterexample.
