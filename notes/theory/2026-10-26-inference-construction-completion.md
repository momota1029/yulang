# Successor integration of original inference constructions

This is an integration and complete theorem-audit checkpoint. It does not
establish the original whole-language inference-soundness theorem. The previous
accepted checkpoint is `efa0e4453`; this successor includes the published
immutable bind/capture readout, the separately published retained rewrite-target
construction, and the exact repaired source-event construction. Component and
integration acceptance are recorded by their independent review receipts.

## Exact target and unchanged claim

`YulangClosure.InferenceConstruction` now imports these additional modules:

| Module | Original obligation advanced | Deliberate limit of the conclusion |
| --- | --- | --- |
| `OriginalWorldReadout` | Computes actual immutable parameter bind, every populated cell, saved capture lookup and complete older Shared-frame preservation. | Plain bind after entry preprocessing; it supplies recursive binding fields, not the entire source-owned post-bind world. |
| `OriginalTerminationClosure` | Retains a raw pair's rewrite target across admission replacement and excludes a new body expansion for an already retained pair. | Successful uncancelled store projections; no total inference termination, rollback theorem or finite universe of future raw pairs. |
| `OriginalSourceEvents` | Constructs original source-owner routes, formal retained-evidence packets, lossless raw history records and the local Shared decoder application. | No full original semantic-domain coverage, global event readout, generated retained-output delivery or complete `PhiW`. |

The original `YulangClosure.SourceProblem.InferenceSoundness` still requires
generation and solving to yield the actual source judgment with the same
scoped assignment. `NativeCorrespondence` separately requires actual native
success to provide generated solved data with the appropriate native
realization. Neither follows from an import surface, a census, generic
reconstruction over a supplied kernel, or assumed local soundness laws.

No original expression/pattern/statement constructor, independent challenge,
response, raw Resume, future use, complete Call, mutable State, effect or
primitive obligation is removed. The default root, project configuration,
dependencies, Rust implementation and expected outputs are unchanged by this
integration.

## SourceEvents rejection and repaired dependency

The first SourceEvents packet was rejected before publication. Its choice-right
edge and a forest's next sibling both used tag 1, producing identical owners
and parameter registrations in a concrete generic rule-tree example. A second
finding exposed three private generated declarations missing from a namespace-
filtered scratch census: the correct old count was 52 constants / 19 theorems,
not 49 / 17. The rejected code, prose, logs, manifest and independent receipt
remain preserved.

The repaired code is `df3469e907867c6f884b17b589d078b58a3dd674a589e1d16baa05b0f004e61b`.
Both walks use tag 3 for choice-right. Complete tree/forest route inventories,
mutual no-duplicate proofs and ordered sublists establish unique owner and
entry routes for arbitrary constructors, without assuming unique Site numbers.
Reserved retained-evidence tag 2 is excluded from ordinary routes at every
depth. The old collision, nested choices, both complete key constructors and
actual retained owners are checked. The complete current-module-origin census
now includes private generated declarations regardless of namespace.

The immutable repaired author packet has 785 originating constants, including
268 theorem constants and 72 required roots. Its current audit module contains
97 constants, including 34 theorems and 24 named probe roots. These isolated
counts are not summed into the integrated theorem count.

## Complete integrated census

The exact explicit import target and unchanged default root built successfully
in one graph of **130 jobs**. The independent audit source enumerates actual
originating theorem constants, including private/generated names, and prints
each complete type and transitive axiom set. It then verifies every required
root is a theorem in that inventory.

| Inventory | Result |
| --- | ---: |
| Selected originating modules | 67 |
| Unique originating theorem constants | 9,954 |
| Required fully qualified theorem roots | 1,763 |
| Private theorem constants included | 1,077 |
| Exact source/configuration inputs | 132 |
| Earlier theorem records retained byte-for-byte | 9,595 |
| New integrated theorem records | 359 |

The increments are 67 WorldReadout, 25 TerminationClosure and 267 SourceEvents
theorems. SourceEvents' isolated `OriginalSourceEnvironment.put.eq_1` already
originates in `SourcePrincipalTransport` in the combined graph. Its name and
original owner are retained, so it is counted once. There is no declaration
overlap between SourceEvents and the 120 isolated WorldReadout constants.

Every earlier theorem's full rendered type, axiom report and originating
module matches the previous accepted 9,595-record census exactly. All 9,954
records were checked for complete matching delimiters, exact unique names,
required-root coverage and absence of replacement or omitted-term markers.

| Exact transitive axiom set | Theorems |
| --- | ---: |
| None | 5,398 |
| `propext` | 2,519 |
| `Quot.sound` | 9 |
| `propext`, `Quot.sound` | 1,547 |
| `propext`, `Classical.choice`, `Quot.sound` | 481 |

No project axiom, `sorryAx` or unchecked evaluation assumption was accepted.
This is not an axiom-free proof collection: the displayed standard axiom sets
are the actual kernel dependencies. The 668 warning first-lines are exactly
the existing multiset from unchanged legacy inputs; no new warning appears.

## Reproduction and fixed evidence

From `notes/theory/lean`, with the pinned Lean 4.35.0 / Lake 5.0.0-src+eb6cafb:

```sh
lake --no-cache build +YulangClosure.InferenceConstruction YulangClosure
lake --no-cache env lean -j1 -M1536 AuditInferenceConstruction.lean
```

The ordinary modules retain the project `-j1 -M1024` setting. The complete
combined audit uses the existing local `-M1536` allowance. Both runs used one
CPU and one Lean thread in a primary-owned isolated project, with 240-second
build and 120-second audit deadlines. Build took 13.930 seconds, with peak
aggregate RSS 1,019,527,168 bytes; audit took 76.445 seconds, with peak aggregate
RSS 1,394,864,128 bytes. Both exited 0 without timeout or resource termination.

| Evidence | SHA-256 |
| --- | --- |
| 132-input manifest | `84464c2be7c7516a041cbf4608ccbc2850e2db7107111e4c2fb188c85ec5ffab` |
| Explicit construction target | `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0` |
| Complete audit source | `65c72b50c0ca3476025d8977b7fbc760774ea09254b6171c6d85482e3f29017b` |
| Build log | `1f20591bf0d2d47a4521d079e5899622ee9af9831103272fff3b5e98c849ddd4` |
| Complete audit log | `1e6b6649893d8e7ef43606b21b26d9db25a977179a04b67f8760b631ff07cd3b` |
| Complete 9,954-record parsed census | `22dd8c1864d498b154a9377e1c92347d953939a7fdcce8b1d4a8b34b95f6baa2` |

Scratch evidence is `/workspace/scratch/f98087c7ac1a/completion-validation-r4`.
Its cache was copied from the exact previous accepted integration inputs;
the three added modules and explicit target were rebuilt. The previous frozen
evidence was not overwritten. A routine Git-diff read initially used the
scratch directory instead of the repository, exited 129 and was repeated in
the correct directory; it changed no file and launched no Lean check. That
diagnostic error is recorded separately from the two successful validations.

## First remaining original constructor

The raw bind/capture equations and source retained-evidence metadata are now
available together. The next required construction is their original semantic
connection: the actual ParameterOrigin must select one formal contract before
invocation; the same scoped assignment must provide its retained evidence;
the generated Lambda suffix must deliver it to `Decoded.installed` at the
actual new cell; and complete post-bind `PhiW`/`B_H.W` must follow from that
data, the actual Force-return certificate and independent original guards.

The current plain Endpoint assignment, first-Site callable lookup and erased
Runtime response do not yet supply all occurrence/parent/raw-operand fields
needed for that connection. A desired readout equality, post hoc replacement
of already fixed `Inputs`, a decoder-image restriction or preservation of only
some world conjuncts would leave the original obligation open. Full Function
future coverage, finite Checking soundness in the concrete original kernel,
general recursive introduction, native-success correspondence and the complete
same-scoped inference theorem also remain open.
