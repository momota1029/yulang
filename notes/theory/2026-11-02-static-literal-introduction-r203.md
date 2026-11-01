# R203 — Static literal introduction for the abstract inference model

Status: **candidate rule; independent specification review PASS**
Authority: user's standing authorization to select natural mathematical definitions for Lean soundness; no change to the original source domain or runtime semantics.
Parent baseline and prior model: `Contracts.lean` remains uninstantiated; this addendum refines only R199 §4.1.

## 1. Why this is the next definition

The user-approved inference principle requires source-directed typing without execution. The complete inference model needs a literal introduction rule that reads the raw source payload and assigns its declared base type independently of solver success. R199 §4.1 already identifies `PaperTypes.literalType` and `PaperValueTyped.literal` as a lossless, kernel-defined candidate type/value projection. This note makes that candidate rule explicit without identifying it with the selected Source-Generalize operational relation.

## 2. Payload-preserving bridge

The raw `OriginalSource.Literal` and `PaperTypes.Literal` constructors have the same payload carrier for each form. Define:

```text
toPaperLiteral : OriginalSource.Literal → PaperTypes.Literal
toPaperLiteral(.unit)             = .unit
toPaperLiteral(.bool b)           = .boolean b
toPaperLiteral(.int n)            = .integer n
toPaperLiteral(.floatBits bits)   = .floatBits bits
toPaperLiteral(.string text)      = .string text
toPaperLiteral(.bytes bytes)      = .bytes bytes
toPaperLiteral(.path path)        = .path path
toPaperLiteral(.character value)  = .character value
```

No payload is decoded, normalized, narrowed to a machine width, or rejected here. In particular, the source float payload is `Nat`, bytes are `List Nat`, paths and character payloads are `String`; the bridge preserves them exactly.

Define the static base type by the existing paper rule:

```text
sourceLiteralType(l) := PaperTypes.literalType(toPaperLiteral(l))
```

Expanded:

| Original source constructor | Static base type |
| --- | --- |
| `unit` | `Unit` |
| `bool _` | `Bool` |
| `int _` | `Int` |
| `floatBits _` | `Float` |
| `string _` | `String` |
| `bytes _` | `Bytes` |
| `path _` | `Path` |
| `character _` | `Char` |

## 3. Introduction rule

Let `sourceLiteralValue(l) = PaperTypes.Value.literal (toPaperLiteral(l))`. For every declaration table, graph environment, type environment, source literal and enclosing original scope, the static value rule is:

```text
────────────────────────────────────────────────────────────────────
PaperValueTyped declarations graphEnvironment typeEnvironment
  sourceLiteralValue(l) (sourceLiteralType(l))
```

This is exactly the existing `PaperValueTyped.literal` constructor. It has no premise about solver success, generated constraints, runtime execution, a declaration registry, or graph membership. It is an introduction rule for this base type; it does **not** make base typing the only possible checking/declaration alternative. Original union, top, annotation, conversion and source-specific checking rules remain separate.

The literal itself contributes no immediate performed operation. This local fact does not erase an enclosing call's effects or equate permission, actual inflow and residual. The paper value relation has no effect-row index, so this clause by itself proves no complete contextual effect judgment or Return law. The enclosing source rule must retain those original obligations and the same correlated scope witness.

## 4. Exact boundary

This candidate rule answers the static type/value projection for every raw payload. It does not supply the selected Source-Generalize §3.1 literal relation (`LiteralDeclaration` over descriptor/value/root/event), its independent ground and value-form laws, or the original Return/contextual-effect/world/future laws. It also does not prove that a satisfying Simple-sub assignment reads back `sourceLiteralType(l)` at the same occurrence, scope and shared witness.

That reflection is still an explicit future theorem obligation:

```text
GeneratesLiteral(s, q, l, d) ∧ Solves(d, a)
  → exists the one shared witness ω,
      sourceLiteralValueTyping(q, l, sourceLiteralType(l), ω)
      ∧ sameScoped(s, q, ω, a)
```

The theorem must use the actual abstract generator/solver equations. It may not assume `LiteralDeclaration`, `Ground`, source typing, or the target conclusion. A later source-to-runtime theorem separately realizes this static derivation. No parent premise is discharged by the present definition, and the original 13/11/3 source forms and all four roots remain open.

## 5. Falsifiers and review target

Reject this rule if the constructor map changes any raw payload, if a source-approved literal has a different declared base type, or if its rule creates a nonlocal effect or drops an enclosing effect obligation. Also reject any promotion of this literal clause into a narrowed whole-language judgment or an exhaustive typing policy.

R203 review must authenticate the frozen source/model inputs and check the payload carriers, all eight type equations, use of `PaperValueTyped.literal`, purity wording, and the distinction from Source-Generalize/runtime meaning. Parent delta remains `0/4 roots; 0/5 packages` unless a separate theorem applies the rule to an unchanged root.
