# R164 source intake — original typed Union owner boundary

Status: **STOPPED at an absent original branch/result constructor**. This is a
source-owner analysis under the admitted R164 contract, not a semantic change,
source implementation, or counterexample to the selected theory.

## Audited scope

The intake compares the exact Union/alternative owner in these governing inputs:

- Generic source relation contract §2.1,
  `notes/design/2026-10-05-source-contracts-and-common-allowance.md`, SHA-256
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
- IF constructor formation §3.2,
  `notes/theory/2026-10-08-call-source-interface-construction.md`, SHA-256
  `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`.
- Native signature authority §§2–5,
  `notes/design/2026-10-08-native-signature-formation-definition.md`, SHA-256
  `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`.
- Selected incidence construction §§2–8,
  `notes/theory/2026-10-08-source-signature-incidence-construction.md`, SHA-256
  `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`.
- Existing formal interface owners:
  `SourceSignatureConstruction.lean` SHA-256
  `ed07890e29b4dcb38cabd18ec0e196efde9e95c64902942a9906a470b38c3311` and
  `SourceContributionConstruction.lean` SHA-256
  `9755a65a2b3e6b97f7da5bf21c844fb7f5292c12925de9f9081fccaa322380a1`.

This scope answers whether these selected definitions supply the typed Union
constructor required by R163; it is not a repository-wide absence claim.

## Source evidence

| Owner | What it supplies | What it leaves open |
|---|---|---|
| Generic relation clauses §2.1 | `Union` means one original whole-tuple alternative. | No pair of distinct branch/result telescopes, injections between them, or dependent result-field equations. |
| IF §3.2 | For an actual `Union(q1,q2)`, retain both contextual operand slots and full interfaces, the original result interface, and tagged alternative-to-result clauses. The contextual inclusion is not a function that maps every operand tuple into a satisfying root tuple; the original root relation determines satisfaction. | No constructor body or local typing rule defines a tagged clause's branch/result relation or its dependent field action. |
| Native signature authority §2 | Retain the full original typed port schemas and dependent fields. Original operator typing and complete primitive contracts remain independent inputs. | Does not define the missing Union operator typing or its field equations. |
| Incidence construction §3.4 | Build the Union catalogue from both complete branch catalogues plus actual result ports. `PortProv` must retain the original dependent field map. A licensed result retains its selected actual branch and original branch/result map; unselected schemas remain present without gaining licenses. | The row states the constructor's required output but does not define an original typed-Union constructor that produces the branch/result map. |
| `SourceSignatureConstruction.Node.alternative` | Records site, left index, right index and result catalogue as graph topology. | No dependent branch/result relation or field transport. |
| `SourceContributionConstruction.Relations.alternative` | Accepts a value indexed by site, selected Bool tag, shared whole tuple, child packet and result packet. | This is supplied as an arbitrary relation family; it has no derivation from an original typed Union clause. `alternativeLeft`/`alternativeRight` consume a witness; they do not construct it. |
| Existing `DeclContribution.project` | Projects a field already licensed by the selected child and routes/inserts it at the receiver. | Does not prove that the child projection is a governed field of the original result telescope. |

The generic whole-tuple alternative does not settle the stronger dependent
port relation. Treating its two alternatives as identity maps would silently
equate branch and result field indices. Treating `Relations.alternative` as
an input would assume the exact supplier sought. Neither is authorized by the
selected sources.

## Exact missing law and boundary

For each authentic original typed Union clause and selected tag `b`, the
original owner must provide a derivation that constructs:

1. the unchanged left and right complete branch telescopes and the unchanged
   original result telescope;
2. a relation from the selected branch witness and the one shared whole tuple
   to a result witness in that result telescope;
3. the dependent governed-field equations identifying precisely which original
   result fields are transported from that selected branch, preserving each
   field's source owner and route; and
4. empty/unselected branch schemas without licensing a branch absent an actual
   selected relation witness.

The audited sources name this law but provide no rule deriving it. Defining it
now would add an operator semantic decision. Therefore R164 stops before a
`Relations.alternative` instance and before a positive Alt theorem. No source
semantics or Rust implementation changed.

## Downstream status

The R163 conditional Alt projection and receiver insertion remain reusable once
an authentic relation/field supplier exists. The five-owner Rust maps through
R163 still show no such constructor or consumer; because R164 produced no
supplier, no new Rust delta was authorized. Original R159 P/A, annotation and
port realization, source/native closure, and production gates remain open.

The next semantic question is narrowly stated: which original typed Union rule
(or already selected operator contract) defines the branch-to-result relation
and dependent governed-field equations on these telescopes? Any proposed new
rule needs its exact typing premises, branch/result carrier, field dependency
behavior, owner preservation and empty-fiber behavior exposed for review before
adoption.
