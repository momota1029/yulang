# R84 normalized declaration closure — handoff revision 1 (FROZEN)


Sprint EFFECT-PERMISSION-ROOT-ELABORATION/20261031-R84; leaf /root/r83_proof.
Baseline a3f8b4a40e57b6053663e0de69b9ebdd3e0c6c49; admission pushed at 6b3b4b615.
Exact leases: `notes/theory/lean/YulangClosure/ConstructedPhysicalRootR84.lean`
and this handoff only. Primary owns manifest, Git, all authorizations, audit
execution, independent review, records and theorem-status adjudication.
Outcome: constructed-but-unchecked candidate. No theorem is accepted.
No descendants; requested/effective model/effort UNKNOWN to this leaf.

## Authority, original claim and dependency identity

Root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md, the Lean proof
skill and references/sources.md + references/execution.md were read in this
continuing leaf session; the R84 contract/admission/manifest and frozen R83
receipt pins were read and revalidated before construction.
Original obligation/corrections remain
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1–3,5,
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6,
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3, and
`docs/yulang-whole-proof-closure-ja.md` §1. Every supported original source,
lawful history and actual retained extrusion, original lexical/type/event scope,
recursive sharing, generalization/use, complete Call, records/methods, effects
and hygiene, and one joint source strategy/witness remain in original A/B.
Research drafts do not supply semantic authority or new premises.

Immediate original parent is
`YulangClosure.OccurrenceQualifiedConsumerR66.Root` (89–95), with unchanged
Incidence (50–55), rootQuery (66–67), all fourteen BeforeAncestry fields (71–84)
and source_incidence_checked (144–146). R83/R82 Root constructors, Primitive
checks, source/native coordinates, mixed witness and all thirteen claims are
preserved. No Root/BeforeAncestry/successful reader/ancestry/ownership aggregate
or source extraction is supplied as an assumption.

The twenty-module source graph and 220 selected declaration records / 215 named
queries are inherited from the reviewed R83 inventory and rehashed. All
source bytes, local import edges, declaration ranges, namespaces, original
contexts, and the actual failed audit2 input reconstruction MATCH the current
R84 manifest. External Std is not a local-module edge. Luna corrected
misreported R81 line numbers in its contract/admission/audit-result while this
leaf was reading: the first source-only pin comparison failed against the
superseded manifest. No R84 write had occurred. On explicit primary notice the
leaf revalidated manifest e49d8af545c13e7c2524ca9eccb5f8d3584cf1276d7ffea461d17b3022fb37dc;
all nine direct receipt/source pins and twenty local module pins match.
This primary-owned record correction is not a mathematical or Lean failure.

## Every R83 audit2 error classified individually

Audit2 exact input: 92,550 bytes / SHA-256
`65d6e1c9ccd282bd905203da157135bd9eccf8f0cb1a22a55672c34b52caa302`;
stdout: 83,756 bytes / SHA-256
`39b395b0a68dae8af921d6e2f93e652dfc48efe465283f88d5229177352bb3ae`;
stderr empty / SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
Primary recorded exit 1, no timeout, elapsed 10.2 seconds. Complete original
streams remain in the frozen R83 handoff pinned below. No audit is rerun here.
The diagnostic block and every prerequisite axiom list are retained later as
failed-audit evidence; none is accepted theorem evidence.

| # | Flattened location | Exact pinned source | Classification and concrete obligation |
| --- | --- | --- | --- |
| 1 | 1246:24 | R77 choice_three_premises:223 | Invalid simp theorem: notation-expanded unique has function type. Select the actual R55.unique definition identifier in the simp list. |
| 2 | 1244:78 | R77 choice_three_premises:221 | Actual residual existential: unique selects some a and plan a = plan c.plan. Unfold R55.internalInputs.plan and R55.unique; c.plans rewrites the entire filter to [c.plan]; Option.map returns the required plan. This goal is addressed, not discarded as a cascade. |
| 3 | 1493:10 | R81 primitive_records_derive_source_probe:146 | Invalid simp argument in constructionRead. Supply the real R55.unique identifier. |
| 4 | 1493:4 | same source:146 | Actual no-progress goal for unique construction filter. hc is exactly the full registration-filter singleton; unfolding unique and rewriting hc yields some (construction c.origin). |
| 5 | 1497:10 | same declaration:150 | Invalid simp argument in permissionRead. Supply the real R55.unique identifier. |
| 6 | 1497:4 | same source:150 | Actual no-progress goal for permission filter. hp is exactly its full singleton; unfolding unique and rewriting hp yields some (permission d.permission). |
| 7 | 1501:10 | same declaration:154 | Invalid simp argument in receiptRead. Supply the real R55.unique identifier. |
| 8 | 1501:4 | same source:154 | Actual no-progress goal for receipt filter. hr is exactly its full use-filter singleton; unfolding unique and rewriting hr yields some (receipt c.receipt). |

R81 have declarations start at 143/147/151; their failing simp commands are
146/150/154. Earlier prose saying 151/155/159 was corrected by Luna; pinned
source and retained stdin determine the mapping. The c.plans-unused warning
occurs alongside failed simplification, not an independently proved unused
premise. Other actual warnings are pre-existing deprecated if_neg and dif_pos
(stdin 1545:6 and 1673:8). No linter suppression or unrelated rewrite is added.
There are no other audit2 error headers. Later queries reach error-recovered
constants and print sorryAx; that is independently fatal evidence, never a
reason to accept those constants or ignore their obligations.

## Why the normalization preserves types and computation

R55 unique at source 104–105 is the actual definition:

```lean
def unique {A : Type} (predicate : A → Bool) (xs : List A) : Option A :=
  match xs.filter predicate with | [item] => some item | _ => none
```

R57 unique at source 191 has exactly the same polymorphic type and delegates
its body to `SourceInternalContextR55.unique test xs`. Thus both ambiguous
open-name candidates reduce to the same complete-filter singleton selection.
R77/R81 operate on source records, so every originally unqualified unique CODE
token in selected declarations becomes the definition identifier
`YulangClosure.SourceInternalContextR55.unique`. This includes all four failing
simp lists. No local notation remains. The plan enumerates all six changed
declarations, 24 substitutions, exact old/new source, hashes and ranges.
Reversing just those substitutions recovers every original declaration byte
for byte. All binder types, hypotheses, constructor branches, record fields,
indexes and equations remain; the types are unchanged modulo definitional
name resolution. Neither the theorem conclusion nor its proof premises moves
into a new assumed proposition.

Installed pinned Lean source was read without executing Lean:
Lean/Elab/Tactic/Simp.lean:210–242 resolves identifier arguments; :269–283 treats
a constant definition as an unfolding entry; :302–320 and :352–370 otherwise
elaborate a term as a simp theorem. Lean/Meta/Tactic/Simp/SimpTheorems.lean:
392–394 rejects a non-Prop theorem type. The R83 local notation produced syntax
rather than an identifier at that early resolution point; function elaboration
then entered theorem processing and failed. The fully qualified real identifier
uses the definition-unfolding path. This is a source-grounded normalization
proposal, not a claim that the new prefix has elaborated.

R84 additionally renames its namespace and qualifies the native unique code
uses to `YulangClosure.ProviderNativeContextR57.unique`, and the two native
Origin type occurrences to `YulangClosure.ProviderNativeContextR57.Origin`.
That is the original R57 inline-drain record; R77.Origin aliases the different
source Construction type. This removes the original latent alias ambiguity
while retaining the intended R82 native record, its fields and constructors.
No extra equality instance or semantic definition is introduced. All thirteen
theorem source signatures are byte-identical after namespace renaming; exact
per-token reversibility was checked. Printed kernel types remain unavailable.

## Assembly and invocation gates

Start `import Std\n`; for each listed module emit `namespace <namespace>\n`,
then one `open <opens joined by spaces>\n` if nonempty. Walk declarations in
listed order; insert the exact context once immediately before the first
declaration starting after context_range[1]. Extract each inclusive source
range and verify its SHA; use the exact normalized_source when its record has
normalization_index, verifying both old and new SHA. Otherwise use the original
slice. Append one EXTRA newline after each slice; end each namespace with
`end <namespace>\n`. Do not insert R83's local notations. This produces the
exact normalized_prefix_body pinned in JSON.

Slot 1 = prefix body + prefix_queries. Full body stripping is exactly
`"\n".join(line for line in candidate.split("\n") if not line.startswith("import "))`.
Slot 3 = accepted prefix body + stripped candidate + `"\n"` + full_queries.
The JSON has the exact complete query strings; there is no pp.width option.
Slot-3 hash below assumes this frozen slot-1 prefix. A slot-2 change requires
re-freezing its dependent full-input hash before slot-3 authorization.

Slots 2 and 4 require actual predecessor diagnostics. Their exact replacement
bytes/hashes are PENDING_ACTUAL_DIAGNOSTICS, as Luna explicitly acknowledged.
Each has an assembly recipe and hard gate in JSON; neither is a runnable or
authorized identical retry. After slot 1 failure, permit only one independently
reviewed diagnostic-directed prefix repair. If that prefix fails, stop without
a candidate invocation. After accepted prefix, slot 3 checks the full candidate;
a pass stops. A failed slot 3 permits one independently reviewed repair in
slot 4 with unchanged statements and source pins. No fifth invocation.

Each proposed invocation requires its own separate primary authorization commit
and push, after exact input review. Expected command, NOT RUN by this leaf:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`,
cwd `notes/theory/lean`, LEAN_NUM_THREADS=1, timeout 120 s. Executable pin is
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
At most four invocations / 480 seconds total, 1 GiB cap unchanged. The skill
checker/Lake cannot be used under this exact no-execution/no-scratch packet;
Luna owns stdin checking. Actual R84 executable version, exits, printed types,
axiom results and peak elaboration memory are NOT RUN / NOT MEASURED.
Toolchain source files were previously read: Lean 4.35.0 pin, YulangClosure,
no external packages, -j1/-M1024. No global defaults or dependencies changed.

The JSON inventory preserves required equality contexts, source type contracts
and conservative prerequisite references for every included declaration. Full
structure/inductive declarations supply all generated constructors/projections/
recursors/injectivity/DecidableEq. Five anonymous Decidable instances remain
identified by exact source line; R81's local synthesis bound 512 and R84's 2048
remain. R57 Drain/Origin equality still comes from the unchanged candidate
deriving-instance commands. Unannotated definition result types require actual
prefix #check; exact source expressions here are not fabricated printed types.
R48/R49/R58–R62/R78/R79 contribute no selected declarations, for the unchanged
R83 source-coverage reasons: no provider/consumer/search/ancestry/policy/captured/
collected bridge is used by the original thirteen statements. Full included
constructors are retained; this source slicing removes no case from any claim.

## Exact normalized declaration plan

```json
{
  "schema": 1,
  "manifest_path": "tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84-inputs.json",
  "manifest_sha256": "e49d8af545c13e7c2524ca9eccb5f8d3584cf1276d7ffea461d17b3022fb37dc",
  "base_R83_plan_handoff": "tasks/agent-loop/inbox/effect-permission-root-closure-r83-proof.md",
  "base_R83_plan_handoff_sha256": "c623f7a999572cc32cadf2e48a0b7b2f7640178319973a70f64379084ebd26b7",
  "modules": [
    {
      "module": "YulangClosure.ComputationPermissionEntryR39",
      "path": "notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean",
      "sha256": "748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e",
      "namespace": "YulangClosure.ComputationPermissionEntryR39",
      "opens": [],
      "context_range": [
        76,
        76
      ],
      "context": "variable {Id : Type} [DecidableEq Id]\n",
      "declarations": [
        {
          "name": "Role",
          "kind": "inductive",
          "range": [
            14,
            16
          ],
          "declaration_line": 14,
          "sha256": "f98ff76ca7d5ca27c021c33d6fa46be2090589907b420430a0b959c366777b1e",
          "references": [],
          "type_contract": "inductive Role where\n  | value | computation\n  deriving DecidableEq",
          "normalized_sha256": "f98ff76ca7d5ca27c021c33d6fa46be2090589907b420430a0b959c366777b1e",
          "normalized_bytes": 68,
          "normalized_prefix_line_range": [
            3,
            5
          ],
          "r83_audit2_prefix_line_range": [
            3,
            5
          ]
        },
        {
          "name": "Registration",
          "kind": "structure",
          "range": [
            30,
            38
          ],
          "declaration_line": 30,
          "sha256": "dd02e5873574d162fa666e6304a36bfa56c6a5b9422bb598acf63848a3c792b9",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Role"
          ],
          "type_contract": "structure Registration (Id : Type) where\n  owner : Id\n  lambda : Nat\n  parameter : Id\n  recipe : Nat\n  scope : Id\n  role : Role\n  entry : Option Id\n  deriving DecidableEq",
          "normalized_sha256": "dd02e5873574d162fa666e6304a36bfa56c6a5b9422bb598acf63848a3c792b9",
          "normalized_bytes": 171,
          "normalized_prefix_line_range": [
            7,
            15
          ],
          "r83_audit2_prefix_line_range": [
            7,
            15
          ]
        },
        {
          "name": "SourceExpr",
          "kind": "inductive",
          "range": [
            47,
            50
          ],
          "declaration_line": 47,
          "sha256": "9ec5f4f0a64657c30b9d52121260cdf7f9a3a7e2bea84d1cc6daa82fc9f5e66d",
          "references": [],
          "type_contract": "inductive SourceExpr (Id : Type) where\n  | lambda (occurrence parameter : Id)\n  | other (occurrence : Id)\n  deriving DecidableEq",
          "normalized_sha256": "9ec5f4f0a64657c30b9d52121260cdf7f9a3a7e2bea84d1cc6daa82fc9f5e66d",
          "normalized_bytes": 129,
          "normalized_prefix_line_range": [
            17,
            20
          ],
          "r83_audit2_prefix_line_range": [
            17,
            20
          ]
        },
        {
          "name": "Inputs",
          "kind": "structure",
          "range": [
            52,
            61
          ],
          "declaration_line": 52,
          "sha256": "9674bc1e4763bd45d08670426ef8438cc53e19d0b86a0335e2482d021e08088e",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.ComputationPermissionEntryR39.SourceExpr"
          ],
          "type_contract": "structure Inputs (Id : Type) where\n  formals : List (Registration Id)\n  recipes : List Id\n  /-- Execution schedule, retained only to exhibit the rejected old guard. -/\n  schedules : List Id\n  /-- Authentic LocalSource expressions keyed by exact source owner. -/\n  sources : List (Id × List (SourceExpr Id))\n  owners : List (Id × Id)\n  occupiedDomains : List Nat\n  retainedRegistrations : List Nat",
          "normalized_sha256": "9674bc1e4763bd45d08670426ef8438cc53e19d0b86a0335e2482d021e08088e",
          "normalized_bytes": 399,
          "normalized_prefix_line_range": [
            22,
            31
          ],
          "r83_audit2_prefix_line_range": [
            22,
            31
          ]
        },
        {
          "name": "Permission",
          "kind": "structure",
          "range": [
            63,
            74
          ],
          "declaration_line": 63,
          "sha256": "cc1eade2ac2e1dfb9f52d330b62dfa55f7a2e036e181be2ecd8542ee8b94fa2a",
          "references": [],
          "type_contract": "structure Permission (Id : Type) where\n  registration : Nat\n  parameter : Nat\n  formalIdentity : Id\n  occurrence : Id\n  owner : Id\n  scope : Id\n  annotationPosition : Id\n  rowPosition : Id\n  entry : Id\n  concrete : List Id\n  deriving DecidableEq",
          "normalized_sha256": "cc1eade2ac2e1dfb9f52d330b62dfa55f7a2e036e181be2ecd8542ee8b94fa2a",
          "normalized_bytes": 246,
          "normalized_prefix_line_range": [
            33,
            44
          ],
          "r83_audit2_prefix_line_range": [
            33,
            44
          ]
        },
        {
          "name": "localSource",
          "kind": "def",
          "range": [
            83,
            86
          ],
          "declaration_line": 83,
          "sha256": "2441ddd7219da05962ac83459a0dabc5cf43d550812f57140faa70b0f9401a4e",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.SourceExpr"
          ],
          "type_contract": "def localSource : List (Id × List (SourceExpr Id)) → Id → Option (List (SourceExpr Id))\n  | [], _ => none\n  | (owner, expressions) :: rest, key =>\n      if owner = key then some expressions else localSource rest key",
          "normalized_sha256": "2441ddd7219da05962ac83459a0dabc5cf43d550812f57140faa70b0f9401a4e",
          "normalized_bytes": 221,
          "normalized_prefix_line_range": [
            47,
            50
          ],
          "r83_audit2_prefix_line_range": [
            47,
            50
          ]
        },
        {
          "name": "sourceLambda",
          "kind": "def",
          "range": [
            90,
            95
          ],
          "declaration_line": 90,
          "sha256": "b203988c4a0fb3a6fbffa87ab257df44a1fe3589b7e5e14683401135faab4589",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Inputs",
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.ComputationPermissionEntryR39.localSource"
          ],
          "type_contract": "def sourceLambda (e : Inputs Id) (f : Registration Id) : Option (Id × Id)",
          "normalized_sha256": "b203988c4a0fb3a6fbffa87ab257df44a1fe3589b7e5e14683401135faab4589",
          "normalized_bytes": 287,
          "normalized_prefix_line_range": [
            52,
            57
          ],
          "r83_audit2_prefix_line_range": [
            52,
            57
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.InternalPermissionIncidenceR45",
      "path": "notes/theory/lean/YulangClosure/InternalPermissionIncidenceR45.lean",
      "sha256": "9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f",
      "namespace": "YulangClosure.InternalPermissionIncidenceR45",
      "opens": [
        "ComputationPermissionEntryR39"
      ],
      "context_range": [
        104,
        105
      ],
      "context": "variable {Artifact Id Term Fact : Type}\n  [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]\n",
      "declarations": [
        {
          "name": "UseId",
          "kind": "structure",
          "range": [
            16,
            19
          ],
          "declaration_line": 16,
          "sha256": "f9012a8d266e5cb1b6ec44799f02acbbf89532669483276132067769129f1263",
          "references": [],
          "type_contract": "structure UseId (Artifact Id : Type) where\n  artifact : Artifact\n  occurrence : Id\n  deriving DecidableEq",
          "normalized_sha256": "f9012a8d266e5cb1b6ec44799f02acbbf89532669483276132067769129f1263",
          "normalized_bytes": 106,
          "normalized_prefix_line_range": [
            62,
            65
          ],
          "r83_audit2_prefix_line_range": [
            62,
            65
          ]
        },
        {
          "name": "Kind",
          "kind": "inductive",
          "range": [
            21,
            23
          ],
          "declaration_line": 21,
          "sha256": "fc96bcae545f8c36b7936a9cfb81eb720429282a210f846f505b836e39cfc76a",
          "references": [],
          "type_contract": "inductive Kind where\n  | internal | incomingInt | incomingBottomTrivial | incomingStructured\n  deriving DecidableEq",
          "normalized_sha256": "fc96bcae545f8c36b7936a9cfb81eb720429282a210f846f505b836e39cfc76a",
          "normalized_bytes": 116,
          "normalized_prefix_line_range": [
            67,
            69
          ],
          "r83_audit2_prefix_line_range": [
            67,
            69
          ]
        },
        {
          "name": "Construction",
          "kind": "structure",
          "range": [
            25,
            30
          ],
          "declaration_line": 25,
          "sha256": "2826adbabbcd35c33db29aa598b9d5bba7958e0cd2b1066d8a594e830db9c092",
          "references": [],
          "type_contract": "structure Construction (Id Term : Type) where\n  registration : Nat\n  lambda : Id\n  function : Term\n  entry : Id\n  deriving DecidableEq",
          "normalized_sha256": "2826adbabbcd35c33db29aa598b9d5bba7958e0cd2b1066d8a594e830db9c092",
          "normalized_bytes": 135,
          "normalized_prefix_line_range": [
            71,
            76
          ],
          "r83_audit2_prefix_line_range": [
            71,
            76
          ]
        },
        {
          "name": "Plan",
          "kind": "structure",
          "range": [
            32,
            39
          ],
          "declaration_line": 32,
          "sha256": "b4e023c19929748c4c65dfe4632a610cecf9780c0f3577451924ae40a180bf60",
          "references": [],
          "type_contract": "structure Plan (Id Term : Type) where\n  sourceOwner : Id\n  targetOwner : Id\n  targetRootComponent : Nat\n  useValueComponent : Nat\n  targetRoot : Term\n  useValue : Term\n  deriving DecidableEq",
          "normalized_sha256": "b4e023c19929748c4c65dfe4632a610cecf9780c0f3577451924ae40a180bf60",
          "normalized_bytes": 191,
          "normalized_prefix_line_range": [
            78,
            85
          ],
          "r83_audit2_prefix_line_range": [
            78,
            85
          ]
        },
        {
          "name": "Receipt",
          "kind": "structure",
          "range": [
            41,
            45
          ],
          "declaration_line": 41,
          "sha256": "eda3257811fed2b5f164c0694506ac46cfd6f971fc4649c86ea6245aae1963bd",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Kind",
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Receipt (Artifact Id Fact : Type) where\n  use : UseId Artifact Id\n  kind : Kind\n  fact : Option Fact\n  deriving DecidableEq",
          "normalized_sha256": "eda3257811fed2b5f164c0694506ac46cfd6f971fc4649c86ea6245aae1963bd",
          "normalized_bytes": 134,
          "normalized_prefix_line_range": [
            87,
            91
          ],
          "r83_audit2_prefix_line_range": [
            87,
            91
          ]
        },
        {
          "name": "Query",
          "kind": "structure",
          "range": [
            47,
            55
          ],
          "declaration_line": 47,
          "sha256": "9783a20479796e43f661c3f1db747f52b397fea107f36a9d3b931c98950c283c",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Query (Artifact Id : Type) where\n  use : UseId Artifact Id\n  sourceOwner : Id\n  targetOwner : Id\n  registration : Nat\n  lambda : Id\n  annotationPosition : Id\n  rowPosition : Id\n  deriving DecidableEq",
          "normalized_sha256": "9783a20479796e43f661c3f1db747f52b397fea107f36a9d3b931c98950c283c",
          "normalized_bytes": 210,
          "normalized_prefix_line_range": [
            93,
            101
          ],
          "r83_audit2_prefix_line_range": [
            93,
            101
          ]
        },
        {
          "name": "Probe",
          "kind": "structure",
          "range": [
            57,
            67
          ],
          "declaration_line": 57,
          "sha256": "f113674fa82b1cd923bb88fbc67575b909fcc5125d9638feb327ac888aeb8204",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Permission",
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.InternalPermissionIncidenceR45.Construction",
            "YulangClosure.InternalPermissionIncidenceR45.Plan",
            "YulangClosure.InternalPermissionIncidenceR45.Receipt"
          ],
          "type_contract": "structure Probe (Artifact Id Term Fact : Type) where\n  formal : Registration Id\n  registeredRoot : Term\n  recipeRootComponent : Nat\n  construction : Construction Id Term\n  permission : Permission Id\n  plan : Plan Id Term\n  receipt : Receipt Artifact Id Fact\n  fact : Fact\n  child : Term\n  deriving DecidableEq",
          "normalized_sha256": "f113674fa82b1cd923bb88fbc67575b909fcc5125d9638feb327ac888aeb8204",
          "normalized_bytes": 310,
          "normalized_prefix_line_range": [
            103,
            113
          ],
          "r83_audit2_prefix_line_range": [
            103,
            113
          ]
        },
        {
          "name": "Inputs",
          "kind": "structure",
          "range": [
            69,
            87
          ],
          "declaration_line": 69,
          "sha256": "e7f13e543c8e3a0da35bf5ba1a7390ede23e3f53902f7755b472ef294db9a071",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Inputs",
            "YulangClosure.ComputationPermissionEntryR39.Permission",
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.InternalPermissionIncidenceR45.Construction",
            "YulangClosure.InternalPermissionIncidenceR45.Plan",
            "YulangClosure.InternalPermissionIncidenceR45.Receipt",
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Inputs (Artifact Id Term Fact : Type) where\n  artifact : Artifact\n  source : ComputationPermissionEntryR39.Inputs Id\n  formals : Nat → Option (Registration Id × Term)\n  constructions : List (Construction Id Term)\n  permissions : List (Permission Id)\n  receipts : List (Receipt Artifact Id Fact)\n  plan : UseId Artifact Id → Option (Plan Id Term)\n  /-- Actual admitted route-fact endpoints, not an unadmitted planned pair. -/\n  routeFact : Fact → Option (Id × Term × Term)\n  /-- Actual LambdaRecipe formal_registration and root_component fields. -/\n  lambdaRecipe : Id → Option (Nat × Nat)\n  componentTerm : Nat → Option Term\n  /-- Actual admitted source-Lambda slot-2 fact endpoints. -/\n  lambdaFact : Id → Option (Term × Term)\n  /-- Returns some only for the actual positive Function's argument-effect. -/\n  positiveFunctionChild : Term → Option Term\n  /-- Returns some only for an actual negative effect-variable entry term. -/\n  negativeEntry : Term → Option Id",
          "normalized_sha256": "e7f13e543c8e3a0da35bf5ba1a7390ede23e3f53902f7755b472ef294db9a071",
          "normalized_bytes": 996,
          "normalized_prefix_line_range": [
            115,
            133
          ],
          "r83_audit2_prefix_line_range": [
            115,
            133
          ]
        },
        {
          "name": "Certificate",
          "kind": "structure",
          "range": [
            89,
            102
          ],
          "declaration_line": 89,
          "sha256": "7ea9d66c49520d6e6480b6c79e9c6d53b5d2b89cbeee6a3d8cec4b863aa174e2",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Permission",
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Certificate (Artifact Id Term Fact : Type) where\n  use : UseId Artifact Id\n  sourceOwner : Id\n  targetOwner : Id\n  registration : Nat\n  formal : Registration Id\n  lambda : Id\n  function : Term\n  argumentEffect : Term\n  originalRoot : Term\n  useValue : Term\n  fact : Fact\n  permission : Permission Id\n  deriving DecidableEq",
          "normalized_sha256": "7ea9d66c49520d6e6480b6c79e9c6d53b5d2b89cbeee6a3d8cec4b863aa174e2",
          "normalized_bytes": 333,
          "normalized_prefix_line_range": [
            135,
            148
          ],
          "r83_audit2_prefix_line_range": [
            135,
            148
          ]
        },
        {
          "name": "constructionsFor",
          "kind": "def",
          "range": [
            107,
            108
          ],
          "declaration_line": 107,
          "sha256": "986ba26f1d9df7569407e205d458f4ece91e3a2483d73f0e3f14e79394031b61",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs"
          ],
          "type_contract": "def constructionsFor (e : Inputs Artifact Id Term Fact) (registration : Nat) :=\n  e.constructions.filter (fun c => c.registration == registration)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "986ba26f1d9df7569407e205d458f4ece91e3a2483d73f0e3f14e79394031b61",
          "normalized_bytes": 147,
          "normalized_prefix_line_range": [
            152,
            153
          ],
          "r83_audit2_prefix_line_range": [
            152,
            153
          ]
        },
        {
          "name": "permissionsFor",
          "kind": "def",
          "range": [
            110,
            111
          ],
          "declaration_line": 110,
          "sha256": "b27fd027d286823fd8f076269d848014425f6a91ad78b520d46664197bb595c0",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs"
          ],
          "type_contract": "def permissionsFor (e : Inputs Artifact Id Term Fact) (registration : Nat) :=\n  e.permissions.filter (fun p => p.registration == registration)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "b27fd027d286823fd8f076269d848014425f6a91ad78b520d46664197bb595c0",
          "normalized_bytes": 143,
          "normalized_prefix_line_range": [
            155,
            156
          ],
          "r83_audit2_prefix_line_range": [
            155,
            156
          ]
        },
        {
          "name": "receiptsFor",
          "kind": "def",
          "range": [
            113,
            114
          ],
          "declaration_line": 113,
          "sha256": "fc7738d3011a33051d0f886135ff9294e8e51da6b37baf6e52937aca300c3fcc",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "def receiptsFor (e : Inputs Artifact Id Term Fact) (use : UseId Artifact Id) :=\n  e.receipts.filter (fun r => r.use == use)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "fc7738d3011a33051d0f886135ff9294e8e51da6b37baf6e52937aca300c3fcc",
          "normalized_bytes": 124,
          "normalized_prefix_line_range": [
            158,
            159
          ],
          "r83_audit2_prefix_line_range": [
            158,
            159
          ]
        },
        {
          "name": "OwnerReads",
          "kind": "def",
          "range": [
            118,
            132
          ],
          "declaration_line": 118,
          "sha256": "820a90680948fa157e4620825b758842834071d7b20a1f016d649fcf8294406d",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.sourceLambda",
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query",
            "YulangClosure.InternalPermissionIncidenceR45.constructionsFor",
            "YulangClosure.InternalPermissionIncidenceR45.permissionsFor",
            "YulangClosure.InternalPermissionIncidenceR45.receiptsFor"
          ],
          "type_contract": "def OwnerReads (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) : Prop",
          "normalized_sha256": "820a90680948fa157e4620825b758842834071d7b20a1f016d649fcf8294406d",
          "normalized_bytes": 1015,
          "normalized_prefix_line_range": [
            161,
            175
          ],
          "r83_audit2_prefix_line_range": [
            161,
            175
          ]
        },
        {
          "name": "Identity",
          "kind": "def",
          "range": [
            136,
            149
          ],
          "declaration_line": 136,
          "sha256": "bae55f450864529925ed7f432e9ebb317bd271632c733ca111d7b70685a7878b",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query"
          ],
          "type_contract": "def Identity (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) : Prop",
          "normalized_sha256": "bae55f450864529925ed7f432e9ebb317bd271632c733ca111d7b70685a7878b",
          "normalized_bytes": 1084,
          "normalized_prefix_line_range": [
            177,
            190
          ],
          "r83_audit2_prefix_line_range": [
            177,
            190
          ]
        },
        {
          "name": "@151",
          "kind": "instance",
          "range": [
            151,
            153
          ],
          "declaration_line": 151,
          "sha256": "a3a4fdc3660d06c68c85d1f55a7fe246728a77ab4601f3da3c6216a82a2c26e4",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.OwnerReads",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query"
          ],
          "type_contract": "instance (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) : Decidable (OwnerReads e q p)",
          "normalized_sha256": "a3a4fdc3660d06c68c85d1f55a7fe246728a77ab4601f3da3c6216a82a2c26e4",
          "normalized_bytes": 179,
          "normalized_prefix_line_range": [
            192,
            194
          ],
          "r83_audit2_prefix_line_range": [
            192,
            194
          ]
        },
        {
          "name": "@155",
          "kind": "instance",
          "range": [
            155,
            157
          ],
          "declaration_line": 155,
          "sha256": "cba2344ce10877fadb047527b81cd2ea1763228eb2508f062486c0fddb003627",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Identity",
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query"
          ],
          "type_contract": "instance (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) : Decidable (Identity e q p)",
          "normalized_sha256": "cba2344ce10877fadb047527b81cd2ea1763228eb2508f062486c0fddb003627",
          "normalized_bytes": 175,
          "normalized_prefix_line_range": [
            196,
            198
          ],
          "r83_audit2_prefix_line_range": [
            196,
            198
          ]
        },
        {
          "name": "certificate",
          "kind": "def",
          "range": [
            159,
            162
          ],
          "declaration_line": 159,
          "sha256": "9b3ebc555493411adfda9155c7192c943aabc1032af35081a0095308588ee91b",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Certificate",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query"
          ],
          "type_contract": "def certificate (q : Query Artifact Id) (p : Probe Artifact Id Term Fact) :\n    Certificate Artifact Id Term Fact",
          "normalized_sha256": "9b3ebc555493411adfda9155c7192c943aabc1032af35081a0095308588ee91b",
          "normalized_bytes": 292,
          "normalized_prefix_line_range": [
            200,
            203
          ],
          "r83_audit2_prefix_line_range": [
            200,
            203
          ]
        },
        {
          "name": "extract",
          "kind": "def",
          "range": [
            164,
            166
          ],
          "declaration_line": 164,
          "sha256": "600bcfdb3e4055b310c5e2982adda2d90e41b31cf31d6b4b9690a46b0bb485f2",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Certificate",
            "YulangClosure.InternalPermissionIncidenceR45.Identity",
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.OwnerReads",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query",
            "YulangClosure.InternalPermissionIncidenceR45.certificate"
          ],
          "type_contract": "def extract (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) : Option (Certificate Artifact Id Term Fact)",
          "normalized_sha256": "600bcfdb3e4055b310c5e2982adda2d90e41b31cf31d6b4b9690a46b0bb485f2",
          "normalized_bytes": 236,
          "normalized_prefix_line_range": [
            205,
            207
          ],
          "r83_audit2_prefix_line_range": [
            205,
            207
          ]
        },
        {
          "name": "accepted_iff",
          "kind": "theorem",
          "range": [
            168,
            173
          ],
          "declaration_line": 168,
          "sha256": "421803f433c6f65f5c2d57b34ae37d409f34a4dd9e49de714e92202fd3e5a228",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Certificate",
            "YulangClosure.InternalPermissionIncidenceR45.Identity",
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.OwnerReads",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query",
            "YulangClosure.InternalPermissionIncidenceR45.certificate",
            "YulangClosure.InternalPermissionIncidenceR45.extract"
          ],
          "type_contract": "theorem accepted_iff (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) (out : Certificate Artifact Id Term Fact) :\n    extract e q p = some out ↔\n      OwnerReads e q p ∧ Identity e q p ∧ out = certificate q p",
          "normalized_sha256": "421803f433c6f65f5c2d57b34ae37d409f34a4dd9e49de714e92202fd3e5a228",
          "normalized_bytes": 317,
          "normalized_prefix_line_range": [
            209,
            214
          ],
          "r83_audit2_prefix_line_range": [
            209,
            214
          ]
        },
        {
          "name": "accepted_payload",
          "kind": "theorem",
          "range": [
            214,
            223
          ],
          "declaration_line": 214,
          "sha256": "0307436696b470c601cb6cd790ac6a6ed86e759cd622491a88259c415fdf3dee",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Certificate",
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.InternalPermissionIncidenceR45.Query",
            "YulangClosure.InternalPermissionIncidenceR45.accepted_iff",
            "YulangClosure.InternalPermissionIncidenceR45.extract",
            "YulangClosure.InternalPermissionIncidenceR45.permissionsFor"
          ],
          "type_contract": "theorem accepted_payload (e : Inputs Artifact Id Term Fact) (q : Query Artifact Id)\n    (p : Probe Artifact Id Term Fact) (out : Certificate Artifact Id Term Fact)\n    (accepted : extract e q p = some out) :\n    out.permission = p.permission ∧ out.permission ∈ e.permissions ∧\n      out.permission.concrete = p.permission.concrete ∧\n      ∀ (i : Nat), out.permission.concrete[i]? = p.permission.concrete[i]?",
          "normalized_sha256": "0307436696b470c601cb6cd790ac6a6ed86e759cd622491a88259c415fdf3dee",
          "normalized_bytes": 681,
          "normalized_prefix_line_range": [
            216,
            225
          ],
          "r83_audit2_prefix_line_range": [
            216,
            225
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.CurrentEmissionOwnershipR47",
      "path": "notes/theory/lean/YulangClosure/CurrentEmissionOwnershipR47.lean",
      "sha256": "d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c",
      "namespace": "YulangClosure.CurrentEmissionOwnershipR47",
      "opens": [
        "InternalPermissionIncidenceR45"
      ],
      "context_range": [
        117,
        117
      ],
      "context": "variable {Artifact Id Fact : Type} [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Fact]\n",
      "declarations": [
        {
          "name": "RowKey",
          "kind": "inductive",
          "range": [
            14,
            16
          ],
          "declaration_line": 14,
          "sha256": "f1aba2eafa88591acf713f26f2793b43e0740a1df5fe27754cec3b530c1aaf77",
          "references": [],
          "type_contract": "inductive RowKey (Id : Type) where\n  | value (raw : Id) | effect (raw : Id)\n  deriving DecidableEq",
          "normalized_sha256": "f1aba2eafa88591acf713f26f2793b43e0740a1df5fe27754cec3b530c1aaf77",
          "normalized_bytes": 99,
          "normalized_prefix_line_range": [
            230,
            232
          ],
          "r83_audit2_prefix_line_range": [
            230,
            232
          ]
        },
        {
          "name": "Endpoint",
          "kind": "inductive",
          "range": [
            18,
            21
          ],
          "declaration_line": 18,
          "sha256": "fdc0c7ebbcacc2a481f687a1f0404dfd5f8139f1875c25e85d0db4dd0d351cfc",
          "references": [],
          "type_contract": "inductive Endpoint (Id : Type) where\n  | valueRow (raw : Id) | effectRow (raw : Id)\n  | valueAtom (key : Id) | effectAtom (key : Id)\n  deriving DecidableEq",
          "normalized_sha256": "fdc0c7ebbcacc2a481f687a1f0404dfd5f8139f1875c25e85d0db4dd0d351cfc",
          "normalized_bytes": 156,
          "normalized_prefix_line_range": [
            234,
            237
          ],
          "r83_audit2_prefix_line_range": [
            234,
            237
          ]
        },
        {
          "name": "Polarity",
          "kind": "inductive",
          "range": [
            23,
            25
          ],
          "declaration_line": 23,
          "sha256": "f279b096bc852fb279b53793d9877740bb49941af529b7d2ca373c5954432371",
          "references": [],
          "type_contract": "inductive Polarity where\n  | positive | negative\n  deriving DecidableEq",
          "normalized_sha256": "f279b096bc852fb279b53793d9877740bb49941af529b7d2ca373c5954432371",
          "normalized_bytes": 72,
          "normalized_prefix_line_range": [
            239,
            241
          ],
          "r83_audit2_prefix_line_range": [
            239,
            241
          ]
        },
        {
          "name": "Bound",
          "kind": "structure",
          "range": [
            27,
            31
          ],
          "declaration_line": 27,
          "sha256": "89dcbb36f31b251e90c662fd06f94e9a7332b1c91d47088febcc7dbeca5bf68b",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.CurrentEmissionOwnershipR47.Polarity",
            "YulangClosure.CurrentEmissionOwnershipR47.RowKey"
          ],
          "type_contract": "structure Bound (Id : Type) where\n  owner : RowKey Id\n  polarity : Polarity\n  item : Endpoint Id\n  deriving DecidableEq",
          "normalized_sha256": "89dcbb36f31b251e90c662fd06f94e9a7332b1c91d47088febcc7dbeca5bf68b",
          "normalized_bytes": 120,
          "normalized_prefix_line_range": [
            243,
            247
          ],
          "r83_audit2_prefix_line_range": [
            243,
            247
          ]
        },
        {
          "name": "rowEndpoint",
          "kind": "def",
          "range": [
            33,
            35
          ],
          "declaration_line": 33,
          "sha256": "c04cdb6b3a2bbf2cc424749badfa424e8c3dd097ea85e12f0049d1eb91cd93a0",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.CurrentEmissionOwnershipR47.RowKey"
          ],
          "type_contract": "def rowEndpoint {Id : Type} : RowKey Id → Endpoint Id\n  | .value raw => .valueRow raw\n  | .effect raw => .effectRow raw",
          "normalized_sha256": "c04cdb6b3a2bbf2cc424749badfa424e8c3dd097ea85e12f0049d1eb91cd93a0",
          "normalized_bytes": 122,
          "normalized_prefix_line_range": [
            249,
            251
          ],
          "r83_audit2_prefix_line_range": [
            249,
            251
          ]
        },
        {
          "name": "boundPair",
          "kind": "def",
          "range": [
            37,
            40
          ],
          "declaration_line": 37,
          "sha256": "75d76e53e555528d970d1ee6fc0f1f7fd811297a9ed1f1e4b8c37c426ff4afeb",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound",
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.CurrentEmissionOwnershipR47.rowEndpoint"
          ],
          "type_contract": "def boundPair {Id : Type} (bound : Bound Id) : Endpoint Id × Endpoint Id",
          "normalized_sha256": "75d76e53e555528d970d1ee6fc0f1f7fd811297a9ed1f1e4b8c37c426ff4afeb",
          "normalized_bytes": 215,
          "normalized_prefix_line_range": [
            253,
            256
          ],
          "r83_audit2_prefix_line_range": [
            253,
            256
          ]
        },
        {
          "name": "Lane",
          "kind": "inductive",
          "range": [
            42,
            45
          ],
          "declaration_line": 42,
          "sha256": "e5c8d46162c460f55031f0c4aecc12210d5a40a86cd13673011ffecff0a3c90a",
          "references": [],
          "type_contract": "inductive Lane where\n  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom\n  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom\n  deriving DecidableEq",
          "normalized_sha256": "e5c8d46162c460f55031f0c4aecc12210d5a40a86cd13673011ffecff0a3c90a",
          "normalized_bytes": 184,
          "normalized_prefix_line_range": [
            258,
            261
          ],
          "r83_audit2_prefix_line_range": [
            258,
            261
          ]
        },
        {
          "name": "Slot",
          "kind": "structure",
          "range": [
            47,
            51
          ],
          "declaration_line": 47,
          "sha256": "93b872900d117b467a1a702c5b9e18a237366b89f9554c3dbe3a36360c849a16",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Lane",
            "YulangClosure.CurrentEmissionOwnershipR47.RowKey"
          ],
          "type_contract": "structure Slot (Id : Type) where\n  owner : RowKey Id\n  lane : Lane\n  index : Nat\n  deriving DecidableEq",
          "normalized_sha256": "93b872900d117b467a1a702c5b9e18a237366b89f9554c3dbe3a36360c849a16",
          "normalized_bytes": 104,
          "normalized_prefix_line_range": [
            263,
            267
          ],
          "r83_audit2_prefix_line_range": [
            263,
            267
          ]
        },
        {
          "name": "RowBounds",
          "kind": "structure",
          "range": [
            53,
            57
          ],
          "declaration_line": 53,
          "sha256": "6d742768d8e8f104877d14f215039b926019df859bfe4920e03a89c9e9dd3d26",
          "references": [],
          "type_contract": "structure RowBounds (Id : Type) where\n  lowerRows : List Id\n  upperRows : List Id\n  lowerAtoms : List Id\n  upperAtoms : List Id",
          "normalized_sha256": "6d742768d8e8f104877d14f215039b926019df859bfe4920e03a89c9e9dd3d26",
          "normalized_bytes": 128,
          "normalized_prefix_line_range": [
            269,
            273
          ],
          "r83_audit2_prefix_line_range": [
            269,
            273
          ]
        },
        {
          "name": "Admission",
          "kind": "structure",
          "range": [
            59,
            62
          ],
          "declaration_line": 59,
          "sha256": "3b0e9ae8c034836d62d81a00dbb19a9cf71f668b7919842f4c3a335dad593848",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound"
          ],
          "type_contract": "structure Admission (Id : Type) where\n  bound : Bound Id\n  relation : Option Nat\n  deriving DecidableEq",
          "normalized_sha256": "3b0e9ae8c034836d62d81a00dbb19a9cf71f668b7919842f4c3a335dad593848",
          "normalized_bytes": 104,
          "normalized_prefix_line_range": [
            275,
            278
          ],
          "r83_audit2_prefix_line_range": [
            275,
            278
          ]
        },
        {
          "name": "Readback",
          "kind": "structure",
          "range": [
            66,
            69
          ],
          "declaration_line": 66,
          "sha256": "1397b539abcd56e80f37ac1b7858b1bfb52929ea3a907221b1a38f68faaf953b",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound",
            "YulangClosure.CurrentEmissionOwnershipR47.Slot"
          ],
          "type_contract": "structure Readback (Id : Type) where\n  slot : Slot Id\n  bound : Bound Id\n  deriving DecidableEq",
          "normalized_sha256": "1397b539abcd56e80f37ac1b7858b1bfb52929ea3a907221b1a38f68faaf953b",
          "normalized_bytes": 96,
          "normalized_prefix_line_range": [
            280,
            283
          ],
          "r83_audit2_prefix_line_range": [
            280,
            283
          ]
        },
        {
          "name": "Emission",
          "kind": "structure",
          "range": [
            71,
            76
          ],
          "declaration_line": 71,
          "sha256": "ded6ca7209d7b76bf211616a2e804edc6945ade440063bedfd6c1f0cd64d8076",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound",
            "YulangClosure.CurrentEmissionOwnershipR47.Readback",
            "YulangClosure.CurrentEmissionOwnershipR47.Slot"
          ],
          "type_contract": "structure Emission (Id : Type) where\n  admission : Nat\n  bound : Bound Id\n  physical : Slot Id\n  readback : Readback Id\n  deriving DecidableEq",
          "normalized_sha256": "ded6ca7209d7b76bf211616a2e804edc6945ade440063bedfd6c1f0cd64d8076",
          "normalized_bytes": 143,
          "normalized_prefix_line_range": [
            285,
            290
          ],
          "r83_audit2_prefix_line_range": [
            285,
            290
          ]
        },
        {
          "name": "Inputs",
          "kind": "structure",
          "range": [
            78,
            94
          ],
          "declaration_line": 78,
          "sha256": "397a3505a37b9c1ff89a975b842d1efecf5f1753f801adaef064aeb5bdd9d462",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Admission",
            "YulangClosure.CurrentEmissionOwnershipR47.Emission",
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.CurrentEmissionOwnershipR47.RowBounds",
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Inputs (Artifact Id Fact : Type) where\n  artifact : Artifact\n  admissions : List (Admission Id)\n  emissions : List (Emission Id)\n  valueRows : Id → Option (RowBounds Id)\n  effectRows : Id → Option (RowBounds Id)\n  liveRelations : List Nat\n  dependencies : List (Nat × Nat)\n  relationPair : Nat → Option (Endpoint Id × Endpoint Id)\n  rootSource : Nat → Option (Id × Nat)\n  sourceFact : Id × Nat → Option Fact\n  /-- Actual completed Origin/drain candidates matching exact source cause/task. -/\n  rootCandidates : UseId Artifact Id → Fact → List Nat\n  rootCause : Nat → Option (Id × Nat)\n  /-- Actual drain task reconciled with that admitted source FactId's pair. -/\n  rootTask : Nat → Option Fact\n  rootCompleted : Nat → Bool",
          "normalized_sha256": "397a3505a37b9c1ff89a975b842d1efecf5f1753f801adaef064aeb5bdd9d462",
          "normalized_bytes": 759,
          "normalized_prefix_line_range": [
            292,
            308
          ],
          "r83_audit2_prefix_line_range": [
            292,
            308
          ]
        },
        {
          "name": "Query",
          "kind": "structure",
          "range": [
            96,
            101
          ],
          "declaration_line": 96,
          "sha256": "5882bb23b5ebf4cc431243708a98150e9775e25fe8ceda7f93c8be8cb3ebe239",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.UseId"
          ],
          "type_contract": "structure Query (Artifact Id Fact : Type) where\n  use : UseId Artifact Id\n  internalFact : Fact\n  rawEntry : Id\n  rootRelation : Nat\n  deriving DecidableEq",
          "normalized_sha256": "5882bb23b5ebf4cc431243708a98150e9775e25fe8ceda7f93c8be8cb3ebe239",
          "normalized_bytes": 156,
          "normalized_prefix_line_range": [
            310,
            315
          ],
          "r83_audit2_prefix_line_range": [
            310,
            315
          ]
        },
        {
          "name": "Probe",
          "kind": "structure",
          "range": [
            103,
            110
          ],
          "declaration_line": 103,
          "sha256": "21dd3634d5ef0631ce77a6ac6cdcc380df56727536cdf21414a0421ed1bfdc87",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Admission",
            "YulangClosure.CurrentEmissionOwnershipR47.Emission"
          ],
          "type_contract": "structure Probe (Id : Type) where\n  admissionIndex : Nat\n  emissionIndex : Nat\n  admission : Admission Id\n  emission : Emission Id\n  relation : Nat\n  ancestry : List Nat\n  deriving DecidableEq",
          "normalized_sha256": "21dd3634d5ef0631ce77a6ac6cdcc380df56727536cdf21414a0421ed1bfdc87",
          "normalized_bytes": 193,
          "normalized_prefix_line_range": [
            317,
            324
          ],
          "r83_audit2_prefix_line_range": [
            317,
            324
          ]
        },
        {
          "name": "currentBound",
          "kind": "def",
          "range": [
            121,
            155
          ],
          "declaration_line": 121,
          "sha256": "d5d6dfbcf2164d502f02da0984c9bf21fae8d5a8cd98165c07cbc7625b48f90e",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound",
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.CurrentEmissionOwnershipR47.Slot"
          ],
          "type_contract": "def currentBound (e : Inputs Artifact Id Fact) (slot : Slot Id) : Option (Bound Id)",
          "normalized_sha256": "d5d6dfbcf2164d502f02da0984c9bf21fae8d5a8cd98165c07cbc7625b48f90e",
          "normalized_bytes": 1570,
          "normalized_prefix_line_range": [
            327,
            361
          ],
          "r83_audit2_prefix_line_range": [
            327,
            361
          ]
        },
        {
          "name": "emissionsForSlot",
          "kind": "def",
          "range": [
            157,
            158
          ],
          "declaration_line": 157,
          "sha256": "32a9fcd1e1464dbf5488ccc5f3bfadf7a2c54ec5deb75878c50b5f02a4a7e711",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.CurrentEmissionOwnershipR47.Slot"
          ],
          "type_contract": "def emissionsForSlot (e : Inputs Artifact Id Fact) (slot : Slot Id) :=\n  e.emissions.filter (fun emission => emission.physical == slot)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "32a9fcd1e1464dbf5488ccc5f3bfadf7a2c54ec5deb75878c50b5f02a4a7e711",
          "normalized_bytes": 136,
          "normalized_prefix_line_range": [
            363,
            364
          ],
          "r83_audit2_prefix_line_range": [
            363,
            364
          ]
        },
        {
          "name": "RootMatches",
          "kind": "def",
          "range": [
            185,
            190
          ],
          "declaration_line": 185,
          "sha256": "6bd230eb8b6f284a13ff09981d88815f9401362549c440c98b03111119d55c6c",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.CurrentEmissionOwnershipR47.Query"
          ],
          "type_contract": "def RootMatches (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) : Prop",
          "normalized_sha256": "6bd230eb8b6f284a13ff09981d88815f9401362549c440c98b03111119d55c6c",
          "normalized_bytes": 460,
          "normalized_prefix_line_range": [
            366,
            371
          ],
          "r83_audit2_prefix_line_range": [
            366,
            371
          ]
        },
        {
          "name": "@192",
          "kind": "instance",
          "range": [
            192,
            193
          ],
          "declaration_line": 192,
          "sha256": "80cbcfa2baeb65e44cf397b19588d62d0523057d5061ea17deb2c89289d0cb3d",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.CurrentEmissionOwnershipR47.Query",
            "YulangClosure.CurrentEmissionOwnershipR47.RootMatches"
          ],
          "type_contract": "instance (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact) :\n    Decidable (RootMatches e q)",
          "normalized_sha256": "80cbcfa2baeb65e44cf397b19588d62d0523057d5061ea17deb2c89289d0cb3d",
          "normalized_bytes": 143,
          "normalized_prefix_line_range": [
            373,
            374
          ],
          "r83_audit2_prefix_line_range": [
            373,
            374
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.SourceInternalContextR55",
      "path": "notes/theory/lean/YulangClosure/SourceInternalContextR55.lean",
      "sha256": "7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123",
      "namespace": "YulangClosure.SourceInternalContextR55",
      "opens": [],
      "context_range": [
        13,
        13
      ],
      "context": "variable {Artifact Id Term Fact : Type}\n",
      "declarations": [
        {
          "name": "NativeRole",
          "kind": "inductive",
          "range": [
            15,
            15
          ],
          "declaration_line": 15,
          "sha256": "162cb07321217ac709cd8a1d3f92de9cb41905b53e1956f068ca5d4435dfb881",
          "references": [],
          "type_contract": "inductive NativeRole where | value | computation deriving DecidableEq",
          "normalized_sha256": "162cb07321217ac709cd8a1d3f92de9cb41905b53e1956f068ca5d4435dfb881",
          "normalized_bytes": 70,
          "normalized_prefix_line_range": [
            379,
            379
          ],
          "r83_audit2_prefix_line_range": [
            379,
            379
          ]
        },
        {
          "name": "Formal",
          "kind": "structure",
          "range": [
            16,
            24
          ],
          "declaration_line": 16,
          "sha256": "037e46ef462560289f70dc51fe28e3ed29bfb349e5b676dad3a24bb775147f68",
          "references": [
            "YulangClosure.SourceInternalContextR55.NativeRole"
          ],
          "type_contract": "structure Formal (Id Term : Type) where\n  owner : Id\n  lambdaIndex : Nat\n  parameter : Id\n  recipePosition : Nat\n  scope : Id\n  role : NativeRole\n  entryEffect : Option Id\n  nativeRoot : Option Term",
          "normalized_sha256": "037e46ef462560289f70dc51fe28e3ed29bfb349e5b676dad3a24bb775147f68",
          "normalized_bytes": 199,
          "normalized_prefix_line_range": [
            381,
            389
          ],
          "r83_audit2_prefix_line_range": [
            381,
            389
          ]
        },
        {
          "name": "Expression",
          "kind": "inductive",
          "range": [
            26,
            29
          ],
          "declaration_line": 26,
          "sha256": "34354b9d03ccf200e98721d32b6ad60fc9118fb1ba37f2387ce4eed6848331b9",
          "references": [],
          "type_contract": "inductive Expression (Id : Type) where\n  | lambda (occurrence parameter : Id)\n  | other (occurrence : Id)\n  deriving DecidableEq",
          "normalized_sha256": "34354b9d03ccf200e98721d32b6ad60fc9118fb1ba37f2387ce4eed6848331b9",
          "normalized_bytes": 129,
          "normalized_prefix_line_range": [
            391,
            394
          ],
          "r83_audit2_prefix_line_range": [
            391,
            394
          ]
        },
        {
          "name": "LocalSource",
          "kind": "structure",
          "range": [
            30,
            32
          ],
          "declaration_line": 30,
          "sha256": "58ffa9305f528d62e91b165ded3325ad36f74a0228cbfd1733d3a70e85d4d8bd",
          "references": [
            "YulangClosure.SourceInternalContextR55.Expression"
          ],
          "type_contract": "structure LocalSource (Id : Type) where\n  owner : Id\n  expressions : List (Expression Id)",
          "normalized_sha256": "58ffa9305f528d62e91b165ded3325ad36f74a0228cbfd1733d3a70e85d4d8bd",
          "normalized_bytes": 90,
          "normalized_prefix_line_range": [
            396,
            398
          ],
          "r83_audit2_prefix_line_range": [
            396,
            398
          ]
        },
        {
          "name": "Permission",
          "kind": "structure",
          "range": [
            34,
            44
          ],
          "declaration_line": 34,
          "sha256": "df3fbd23213f7051489c82d69caea1b6d6fe7f7f1e288722ed6435f2f907273c",
          "references": [
            "YulangClosure.SourceInternalContextR55.formal"
          ],
          "type_contract": "structure Permission (Id : Type) where\n  registration : Nat\n  parameterPosition : Nat\n  formal : Id\n  occurrence : Id\n  sourceOwner : Id\n  scope : Id\n  annotationPosition : Id\n  sourceRow : Id\n  entryEffect : Id\n  concrete : List Id",
          "normalized_sha256": "df3fbd23213f7051489c82d69caea1b6d6fe7f7f1e288722ed6435f2f907273c",
          "normalized_bytes": 233,
          "normalized_prefix_line_range": [
            400,
            410
          ],
          "r83_audit2_prefix_line_range": [
            400,
            410
          ]
        },
        {
          "name": "Construction",
          "kind": "structure",
          "range": [
            46,
            50
          ],
          "declaration_line": 46,
          "sha256": "6d830694a40329e2842914fbdb695cfeb57e92b2aefe403f493903799e1f2adb",
          "references": [],
          "type_contract": "structure Construction (Id Term : Type) where\n  registration : Nat\n  lambda : Id\n  function : Term\n  entryEffect : Id",
          "normalized_sha256": "6d830694a40329e2842914fbdb695cfeb57e92b2aefe403f493903799e1f2adb",
          "normalized_bytes": 118,
          "normalized_prefix_line_range": [
            412,
            416
          ],
          "r83_audit2_prefix_line_range": [
            412,
            416
          ]
        },
        {
          "name": "Use",
          "kind": "structure",
          "range": [
            52,
            55
          ],
          "declaration_line": 52,
          "sha256": "3617082fa04cc9a564d50417f3ca9d19fd1ee433c95c5aa42e51a020fbec5e9d",
          "references": [],
          "type_contract": "structure Use (Artifact Id : Type) where\n  artifact : Artifact\n  occurrence : Id\n  deriving DecidableEq",
          "normalized_sha256": "3617082fa04cc9a564d50417f3ca9d19fd1ee433c95c5aa42e51a020fbec5e9d",
          "normalized_bytes": 104,
          "normalized_prefix_line_range": [
            418,
            421
          ],
          "r83_audit2_prefix_line_range": [
            418,
            421
          ]
        },
        {
          "name": "RouteKind",
          "kind": "inductive",
          "range": [
            56,
            56
          ],
          "declaration_line": 56,
          "sha256": "2a6429851a5bed18a3c089f007d93e5a324e482ddd6d2eadfd7a5ee9d5f977e0",
          "references": [],
          "type_contract": "inductive RouteKind where | internal | incomingInt | incomingBottomTrivial | incomingStructured deriving DecidableEq",
          "normalized_sha256": "2a6429851a5bed18a3c089f007d93e5a324e482ddd6d2eadfd7a5ee9d5f977e0",
          "normalized_bytes": 117,
          "normalized_prefix_line_range": [
            423,
            423
          ],
          "r83_audit2_prefix_line_range": [
            423,
            423
          ]
        },
        {
          "name": "Receipt",
          "kind": "structure",
          "range": [
            57,
            60
          ],
          "declaration_line": 57,
          "sha256": "48440001b440ea51a36885b8cf50a60ec4422e4d83f02de267ff3c80af492e9d",
          "references": [
            "YulangClosure.SourceInternalContextR55.RouteKind",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "structure Receipt (Artifact Id Fact : Type) where\n  use : Use Artifact Id\n  kind : RouteKind\n  fact : Option Fact",
          "normalized_sha256": "48440001b440ea51a36885b8cf50a60ec4422e4d83f02de267ff3c80af492e9d",
          "normalized_bytes": 114,
          "normalized_prefix_line_range": [
            425,
            428
          ],
          "r83_audit2_prefix_line_range": [
            425,
            428
          ]
        },
        {
          "name": "Plan",
          "kind": "structure",
          "range": [
            61,
            68
          ],
          "declaration_line": 61,
          "sha256": "5cdd93693e1107e4927df7198642aeff969c459aca9f10d8ba3ecc73a74794bc",
          "references": [
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "structure Plan (Artifact Id Term : Type) where\n  use : Use Artifact Id\n  sourceOwner : Id\n  targetOwner : Id\n  targetRootComponent : Nat\n  useValueComponent : Nat\n  targetRoot : Term\n  useValue : Term",
          "normalized_sha256": "5cdd93693e1107e4927df7198642aeff969c459aca9f10d8ba3ecc73a74794bc",
          "normalized_bytes": 201,
          "normalized_prefix_line_range": [
            430,
            437
          ],
          "r83_audit2_prefix_line_range": [
            430,
            437
          ]
        },
        {
          "name": "Recipe",
          "kind": "structure",
          "range": [
            69,
            72
          ],
          "declaration_line": 69,
          "sha256": "716ce46978dc4048d7c48f0cd527c478ee5ce1e729d23a875696e8c9478e3f18",
          "references": [],
          "type_contract": "structure Recipe (Id : Type) where\n  occurrence : Id\n  formalRegistration : Option Nat\n  rootComponent : Nat",
          "normalized_sha256": "716ce46978dc4048d7c48f0cd527c478ee5ce1e729d23a875696e8c9478e3f18",
          "normalized_bytes": 109,
          "normalized_prefix_line_range": [
            439,
            442
          ],
          "r83_audit2_prefix_line_range": [
            439,
            442
          ]
        },
        {
          "name": "AdmittedFact",
          "kind": "structure",
          "range": [
            73,
            78
          ],
          "declaration_line": 73,
          "sha256": "e093ca949cacb00cdda1db49ec71935cce08e5c7fa616cab3e0dd3cd8e32ceb4",
          "references": [],
          "type_contract": "structure AdmittedFact (Id Term Fact : Type) where\n  fact : Fact\n  occurrence : Id\n  slot : Nat\n  lower : Term\n  upper : Term",
          "normalized_sha256": "e093ca949cacb00cdda1db49ec71935cce08e5c7fa616cab3e0dd3cd8e32ceb4",
          "normalized_bytes": 126,
          "normalized_prefix_line_range": [
            444,
            449
          ],
          "r83_audit2_prefix_line_range": [
            444,
            449
          ]
        },
        {
          "name": "TermView",
          "kind": "inductive",
          "range": [
            79,
            82
          ],
          "declaration_line": 79,
          "sha256": "d9059028276f185b90956ecf40b8cfc4548e641e2ac5d0f0fae0946bffe7c68f",
          "references": [],
          "type_contract": "inductive TermView (Id Term : Type) where\n  | positiveFunction (argumentEffect : Term)\n  | negativeEffectVariable (rawEntry : Id)\n  | other",
          "normalized_sha256": "d9059028276f185b90956ecf40b8cfc4548e641e2ac5d0f0fae0946bffe7c68f",
          "normalized_bytes": 140,
          "normalized_prefix_line_range": [
            451,
            454
          ],
          "r83_audit2_prefix_line_range": [
            451,
            454
          ]
        },
        {
          "name": "Native",
          "kind": "structure",
          "range": [
            86,
            102
          ],
          "declaration_line": 86,
          "sha256": "fe5229f9c2c8569e11db5124c82488bc03b043e140ba134bd07a24f1fda3a989",
          "references": [
            "YulangClosure.SourceInternalContextR55.AdmittedFact",
            "YulangClosure.SourceInternalContextR55.Construction",
            "YulangClosure.SourceInternalContextR55.Formal",
            "YulangClosure.SourceInternalContextR55.LocalSource",
            "YulangClosure.SourceInternalContextR55.Permission",
            "YulangClosure.SourceInternalContextR55.Plan",
            "YulangClosure.SourceInternalContextR55.Receipt",
            "YulangClosure.SourceInternalContextR55.Recipe",
            "YulangClosure.SourceInternalContextR55.TermView"
          ],
          "type_contract": "structure Native (Artifact Id Term Fact : Type) where\n  artifact : Artifact\n  formals : List (Formal Id Term)\n  parameterRecipes : List Id\n  schedules : List Id\n  sources : List (LocalSource Id)\n  sourceOwners : List (Id × Id)\n  occupiedDomains : List Nat\n  retainedRegistrations : List Nat\n  constructions : List (Construction Id Term)\n  permissions : List (Permission Id)\n  receipts : List (Receipt Artifact Id Fact)\n  plans : List (Plan Artifact Id Term)\n  recipes : List (Recipe Id)\n  admittedFacts : List (AdmittedFact Id Term Fact)\n  componentTerms : List (Nat × Term)\n  termViews : List (Term × TermView Id Term)",
          "normalized_sha256": "fe5229f9c2c8569e11db5124c82488bc03b043e140ba134bd07a24f1fda3a989",
          "normalized_bytes": 623,
          "normalized_prefix_line_range": [
            456,
            472
          ],
          "r83_audit2_prefix_line_range": [
            456,
            472
          ]
        },
        {
          "name": "unique",
          "kind": "def",
          "range": [
            104,
            105
          ],
          "declaration_line": 104,
          "sha256": "533e7418d666c50916aa46e84acc3ec0fee7675a1a6815a3a9de2bc1603eabcb",
          "references": [],
          "type_contract": "def unique {A : Type} (predicate : A → Bool) (xs : List A) : Option A",
          "normalized_sha256": "533e7418d666c50916aa46e84acc3ec0fee7675a1a6815a3a9de2bc1603eabcb",
          "normalized_bytes": 142,
          "normalized_prefix_line_range": [
            474,
            475
          ],
          "r83_audit2_prefix_line_range": [
            474,
            475
          ]
        },
        {
          "name": "formal",
          "kind": "def",
          "range": [
            107,
            109
          ],
          "declaration_line": 107,
          "sha256": "5fa8359d6bb1f9b65076c782194a44c1915ffe129e1644ccb5f48e576af83dff",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Registration",
            "YulangClosure.SourceInternalContextR55.Formal"
          ],
          "type_contract": "def formal (f : Formal Id Term) : ComputationPermissionEntryR39.Registration Id",
          "normalized_sha256": "5fa8359d6bb1f9b65076c782194a44c1915ffe129e1644ccb5f48e576af83dff",
          "normalized_bytes": 242,
          "normalized_prefix_line_range": [
            477,
            479
          ],
          "r83_audit2_prefix_line_range": [
            477,
            479
          ]
        },
        {
          "name": "expression",
          "kind": "def",
          "range": [
            110,
            112
          ],
          "declaration_line": 110,
          "sha256": "484e709dcb34d6c90d37a214941109c33a0dcaeba70ae8244f36d59ba6a33686",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.SourceExpr",
            "YulangClosure.SourceInternalContextR55.Expression"
          ],
          "type_contract": "def expression : Expression Id → ComputationPermissionEntryR39.SourceExpr Id\n  | .lambda occurrence parameter => .lambda occurrence parameter\n  | .other occurrence => .other occurrence",
          "normalized_sha256": "484e709dcb34d6c90d37a214941109c33a0dcaeba70ae8244f36d59ba6a33686",
          "normalized_bytes": 187,
          "normalized_prefix_line_range": [
            481,
            483
          ],
          "r83_audit2_prefix_line_range": [
            481,
            483
          ]
        },
        {
          "name": "sourceInputs",
          "kind": "def",
          "range": [
            114,
            117
          ],
          "declaration_line": 114,
          "sha256": "2c3c9b7d84db7acd970901e752bda9f55a8033524acbe2a5819a19d573cf8918",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Inputs",
            "YulangClosure.SourceInternalContextR55.Native",
            "YulangClosure.SourceInternalContextR55.expression",
            "YulangClosure.SourceInternalContextR55.formal"
          ],
          "type_contract": "def sourceInputs (n : Native Artifact Id Term Fact) : ComputationPermissionEntryR39.Inputs Id",
          "normalized_sha256": "2c3c9b7d84db7acd970901e752bda9f55a8033524acbe2a5819a19d573cf8918",
          "normalized_bytes": 308,
          "normalized_prefix_line_range": [
            485,
            488
          ],
          "r83_audit2_prefix_line_range": [
            485,
            488
          ]
        },
        {
          "name": "permission",
          "kind": "def",
          "range": [
            118,
            120
          ],
          "declaration_line": 118,
          "sha256": "ac16d7ece8be5444efd3bd440faadfeb5d09f0e0f6b1167534226d8b84422117",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Permission",
            "YulangClosure.SourceInternalContextR55.Permission"
          ],
          "type_contract": "def permission (p : Permission Id) : ComputationPermissionEntryR39.Permission Id",
          "normalized_sha256": "ac16d7ece8be5444efd3bd440faadfeb5d09f0e0f6b1167534226d8b84422117",
          "normalized_bytes": 242,
          "normalized_prefix_line_range": [
            490,
            492
          ],
          "r83_audit2_prefix_line_range": [
            490,
            492
          ]
        },
        {
          "name": "construction",
          "kind": "def",
          "range": [
            121,
            122
          ],
          "declaration_line": 121,
          "sha256": "460a7a419b7e65b3c11550a93c5979a9c11f863e4f319e22c04f044abbbcec84",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Construction",
            "YulangClosure.SourceInternalContextR55.Construction"
          ],
          "type_contract": "def construction (c : Construction Id Term) : InternalPermissionIncidenceR45.Construction Id Term",
          "normalized_sha256": "460a7a419b7e65b3c11550a93c5979a9c11f863e4f319e22c04f044abbbcec84",
          "normalized_bytes": 161,
          "normalized_prefix_line_range": [
            494,
            495
          ],
          "r83_audit2_prefix_line_range": [
            494,
            495
          ]
        },
        {
          "name": "use",
          "kind": "def",
          "range": [
            123,
            123
          ],
          "declaration_line": 123,
          "sha256": "cc9e657fee45ca6535044b3a3d5fc6dc6fb6e095a096bea9c0b80cf6edb3b933",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.UseId",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def use (u : Use Artifact Id) : InternalPermissionIncidenceR45.UseId Artifact Id",
          "normalized_sha256": "cc9e657fee45ca6535044b3a3d5fc6dc6fb6e095a096bea9c0b80cf6edb3b933",
          "normalized_bytes": 115,
          "normalized_prefix_line_range": [
            497,
            497
          ],
          "r83_audit2_prefix_line_range": [
            497,
            497
          ]
        },
        {
          "name": "receipt",
          "kind": "def",
          "range": [
            124,
            127
          ],
          "declaration_line": 124,
          "sha256": "d61dc8c1f925361412dd4b2bf40c974a6f25b07b262d8a30391897b583d9cb6b",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Receipt",
            "YulangClosure.SourceInternalContextR55.Receipt",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "def receipt (r : Receipt Artifact Id Fact) : InternalPermissionIncidenceR45.Receipt Artifact Id Fact",
          "normalized_sha256": "d61dc8c1f925361412dd4b2bf40c974a6f25b07b262d8a30391897b583d9cb6b",
          "normalized_bytes": 309,
          "normalized_prefix_line_range": [
            499,
            502
          ],
          "r83_audit2_prefix_line_range": [
            499,
            502
          ]
        },
        {
          "name": "plan",
          "kind": "def",
          "range": [
            128,
            129
          ],
          "declaration_line": 128,
          "sha256": "20588970a3d97cb5361944c9d06abe9f4e77c5e70618784b10f3cd557245b854",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Plan",
            "YulangClosure.SourceInternalContextR55.Plan"
          ],
          "type_contract": "def plan (p : Plan Artifact Id Term) : InternalPermissionIncidenceR45.Plan Id Term",
          "normalized_sha256": "20588970a3d97cb5361944c9d06abe9f4e77c5e70618784b10f3cd557245b854",
          "normalized_bytes": 193,
          "normalized_prefix_line_range": [
            504,
            505
          ],
          "r83_audit2_prefix_line_range": [
            504,
            505
          ]
        },
        {
          "name": "internalInputs",
          "kind": "def",
          "range": [
            131,
            153
          ],
          "declaration_line": 131,
          "sha256": "c2594e0f15bc271971f2dc5befdb4864ae484a5c01b9e0ef5743ca89ec54b12f",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.SourceInternalContextR55.Native",
            "YulangClosure.SourceInternalContextR55.construction",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.permission",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.receipt",
            "YulangClosure.SourceInternalContextR55.sourceInputs",
            "YulangClosure.SourceInternalContextR55.unique",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "def internalInputs [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]\n    (n : Native Artifact Id Term Fact) : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact",
          "normalized_sha256": "c2594e0f15bc271971f2dc5befdb4864ae484a5c01b9e0ef5743ca89ec54b12f",
          "normalized_bytes": 1829,
          "normalized_prefix_line_range": [
            507,
            529
          ],
          "r83_audit2_prefix_line_range": [
            507,
            529
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.ProviderNativeContextR57",
      "path": "notes/theory/lean/YulangClosure/ProviderNativeContextR57.lean",
      "sha256": "804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63",
      "namespace": "YulangClosure.ProviderNativeContextR57",
      "opens": [],
      "context_range": [
        142,
        142
      ],
      "context": "variable {S T : Type} [DecidableEq S] [DecidableEq T]\n",
      "declarations": [
        {
          "name": "ValueEndpoint",
          "kind": "inductive",
          "range": [
            9,
            17
          ],
          "declaration_line": 9,
          "sha256": "e0bf08f588ba104eabd6eaf9c75dc0a2fa4eccb393a9cb6a53e78963b852f3c6",
          "references": [
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "inductive ValueEndpoint (Term : Type) where\n  | bottomPositive | bottomNegative | topNegative\n  | intPositive | intNegative | unitPositive | boolPositive | strPositive\n  | unitNegative | boolNegative | strNegative | row (ordinal : Nat)\n  | positiveFunction (term : Term) | negativeFunction (term : Term)\n  | positiveVariant (term : Term) | negativeVariant (term : Term)\n  | positiveRecord (term : Term) | negativeRecord (term : Term)\n  | positiveTuple (term : Term) (arity : Nat) | negativeTuple (term : Term) (arity : Nat)\n  deriving DecidableEq",
          "normalized_sha256": "e0bf08f588ba104eabd6eaf9c75dc0a2fa4eccb393a9cb6a53e78963b852f3c6",
          "normalized_bytes": 547,
          "normalized_prefix_line_range": [
            533,
            541
          ],
          "r83_audit2_prefix_line_range": [
            533,
            541
          ]
        },
        {
          "name": "EffectEndpoint",
          "kind": "inductive",
          "range": [
            18,
            21
          ],
          "declaration_line": 18,
          "sha256": "b41d350272edc3d685d9b9de80b2b264434bbadf892c60c9496a458aedecf8bf",
          "references": [
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "inductive EffectEndpoint where\n  | bottomPositive | emptyNegative | contribution (index : Nat) | allowance (index : Nat)\n  | support (view : Nat) | annotationMember (view ordinal : Nat) | row (ordinal : Nat)\n  deriving DecidableEq",
          "normalized_sha256": "b41d350272edc3d685d9b9de80b2b264434bbadf892c60c9496a458aedecf8bf",
          "normalized_bytes": 231,
          "normalized_prefix_line_range": [
            543,
            546
          ],
          "r83_audit2_prefix_line_range": [
            543,
            546
          ]
        },
        {
          "name": "Key",
          "kind": "inductive",
          "range": [
            22,
            27
          ],
          "declaration_line": 22,
          "sha256": "3c728779e4f97dcfe1ed34797b7c1535167743cb0ededc525f198250df535659",
          "references": [
            "YulangClosure.ProviderNativeContextR57.EffectEndpoint",
            "YulangClosure.ProviderNativeContextR57.ValueEndpoint",
            "YulangClosure.ProviderNativeContextR57.endpoint"
          ],
          "type_contract": "inductive Key (Source Term : Type) where\n  | source (key : Source)\n  | valueRow (state ordinal : Nat) | effectRow (state ordinal : Nat)\n  | valueAtom (state : Nat) (endpoint : ValueEndpoint Term)\n  | effectAtom (state : Nat) (endpoint : EffectEndpoint)\n  deriving DecidableEq",
          "normalized_sha256": "3c728779e4f97dcfe1ed34797b7c1535167743cb0ededc525f198250df535659",
          "normalized_bytes": 276,
          "normalized_prefix_line_range": [
            548,
            553
          ],
          "r83_audit2_prefix_line_range": [
            548,
            553
          ]
        },
        {
          "name": "Fact",
          "kind": "inductive",
          "range": [
            28,
            30
          ],
          "declaration_line": 28,
          "sha256": "22727229a20aabb06c40f4634931fcbbd323b61135b4be6bbfc2b27fb0aca08e",
          "references": [],
          "type_contract": "inductive Fact where\n  | semantic (store index : Nat) | collected (batch index : Nat)\n  deriving DecidableEq",
          "normalized_sha256": "22727229a20aabb06c40f4634931fcbbd323b61135b4be6bbfc2b27fb0aca08e",
          "normalized_bytes": 109,
          "normalized_prefix_line_range": [
            555,
            557
          ],
          "r83_audit2_prefix_line_range": [
            555,
            557
          ]
        },
        {
          "name": "Endpoint",
          "kind": "inductive",
          "range": [
            31,
            33
          ],
          "declaration_line": 31,
          "sha256": "c378fbfd3c2bc159901ea3773d5e2e6c7fe87bfc888a23d6c28bc2be18ce9198",
          "references": [
            "YulangClosure.ProviderNativeContextR57.EffectEndpoint",
            "YulangClosure.ProviderNativeContextR57.ValueEndpoint",
            "YulangClosure.ProviderNativeContextR57.endpoint"
          ],
          "type_contract": "inductive Endpoint (Term : Type) where\n  | value (endpoint : ValueEndpoint Term) | effect (endpoint : EffectEndpoint)\n  deriving DecidableEq",
          "normalized_sha256": "c378fbfd3c2bc159901ea3773d5e2e6c7fe87bfc888a23d6c28bc2be18ce9198",
          "normalized_bytes": 141,
          "normalized_prefix_line_range": [
            559,
            561
          ],
          "r83_audit2_prefix_line_range": [
            559,
            561
          ]
        },
        {
          "name": "endpoint",
          "kind": "def",
          "range": [
            35,
            39
          ],
          "declaration_line": 35,
          "sha256": "ace6847188258f04b5642f02e25ade1166a4b84e12b27071863c956708a0e24a",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.ProviderNativeContextR57.Endpoint",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "def endpoint {S T : Type} (state : Nat) : Endpoint T → CurrentEmissionOwnershipR47.Endpoint (Key S T)\n  | .value (.row index) => .valueRow (.valueRow state index)\n  | .effect (.row index) => .effectRow (.effectRow state index)\n  | .value item => .valueAtom (.valueAtom state item)\n  | .effect item => .effectAtom (.effectAtom state item)",
          "normalized_sha256": "ace6847188258f04b5642f02e25ade1166a4b84e12b27071863c956708a0e24a",
          "normalized_bytes": 340,
          "normalized_prefix_line_range": [
            563,
            567
          ],
          "r83_audit2_prefix_line_range": [
            563,
            567
          ]
        },
        {
          "name": "Row",
          "kind": "inductive",
          "range": [
            41,
            41
          ],
          "declaration_line": 41,
          "sha256": "092df579ca4bdea654653bc17878c13bb6dddbd67e4fb72ef1acdeae12dbdfbf",
          "references": [],
          "type_contract": "inductive Row where | value (index : Nat) | effect (index : Nat) deriving DecidableEq",
          "normalized_sha256": "092df579ca4bdea654653bc17878c13bb6dddbd67e4fb72ef1acdeae12dbdfbf",
          "normalized_bytes": 86,
          "normalized_prefix_line_range": [
            569,
            569
          ],
          "r83_audit2_prefix_line_range": [
            569,
            569
          ]
        },
        {
          "name": "Polarity",
          "kind": "inductive",
          "range": [
            42,
            42
          ],
          "declaration_line": 42,
          "sha256": "905c5880dd7c7e86c38d6d80229cbd6312bf9f79b9329cec73f20e1dc9bbffd8",
          "references": [],
          "type_contract": "inductive Polarity where | positive | negative deriving DecidableEq",
          "normalized_sha256": "905c5880dd7c7e86c38d6d80229cbd6312bf9f79b9329cec73f20e1dc9bbffd8",
          "normalized_bytes": 68,
          "normalized_prefix_line_range": [
            571,
            571
          ],
          "r83_audit2_prefix_line_range": [
            571,
            571
          ]
        },
        {
          "name": "Lane",
          "kind": "inductive",
          "range": [
            43,
            46
          ],
          "declaration_line": 43,
          "sha256": "e5c8d46162c460f55031f0c4aecc12210d5a40a86cd13673011ffecff0a3c90a",
          "references": [],
          "type_contract": "inductive Lane where\n  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom\n  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom\n  deriving DecidableEq",
          "normalized_sha256": "e5c8d46162c460f55031f0c4aecc12210d5a40a86cd13673011ffecff0a3c90a",
          "normalized_bytes": 184,
          "normalized_prefix_line_range": [
            573,
            576
          ],
          "r83_audit2_prefix_line_range": [
            573,
            576
          ]
        },
        {
          "name": "Bound",
          "kind": "structure",
          "range": [
            47,
            51
          ],
          "declaration_line": 47,
          "sha256": "4f8e4ad02f59508130c9afdbbea9214561b25c0d2977db6b8f8a0182f9a6f9c1",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Endpoint",
            "YulangClosure.ProviderNativeContextR57.Polarity",
            "YulangClosure.ProviderNativeContextR57.Row",
            "YulangClosure.ProviderNativeContextR57.polarity"
          ],
          "type_contract": "structure Bound (T : Type) where\n  owner : Row\n  polarity : Polarity\n  item : Endpoint T\n  deriving DecidableEq",
          "normalized_sha256": "4f8e4ad02f59508130c9afdbbea9214561b25c0d2977db6b8f8a0182f9a6f9c1",
          "normalized_bytes": 112,
          "normalized_prefix_line_range": [
            578,
            582
          ],
          "r83_audit2_prefix_line_range": [
            578,
            582
          ]
        },
        {
          "name": "Slot",
          "kind": "structure",
          "range": [
            52,
            56
          ],
          "declaration_line": 52,
          "sha256": "fa63672b3a3b3222d52f7c08bd820b5bb18a122da6f99d60c70f37a8aa11b6c6",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Lane",
            "YulangClosure.ProviderNativeContextR57.Row",
            "YulangClosure.ProviderNativeContextR57.lane"
          ],
          "type_contract": "structure Slot where\n  owner : Row\n  lane : Lane\n  index : Nat\n  deriving DecidableEq",
          "normalized_sha256": "fa63672b3a3b3222d52f7c08bd820b5bb18a122da6f99d60c70f37a8aa11b6c6",
          "normalized_bytes": 86,
          "normalized_prefix_line_range": [
            584,
            588
          ],
          "r83_audit2_prefix_line_range": [
            584,
            588
          ]
        },
        {
          "name": "Admission",
          "kind": "structure",
          "range": [
            57,
            61
          ],
          "declaration_line": 57,
          "sha256": "ac801592a07811180b813c293601f115b27e91fbc106733880b8fe559b2204a3",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Bound",
            "YulangClosure.ProviderNativeContextR57.bound"
          ],
          "type_contract": "structure Admission (T : Type) where\n  state : Nat\n  bound : Bound T\n  relation : Option Nat\n  deriving DecidableEq",
          "normalized_sha256": "ac801592a07811180b813c293601f115b27e91fbc106733880b8fe559b2204a3",
          "normalized_bytes": 116,
          "normalized_prefix_line_range": [
            590,
            594
          ],
          "r83_audit2_prefix_line_range": [
            590,
            594
          ]
        },
        {
          "name": "Emission",
          "kind": "structure",
          "range": [
            62,
            69
          ],
          "declaration_line": 62,
          "sha256": "6150050f492ea2df8d7988b4481176659dab0bc47056813acf8f06e45cb256a6",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Bound",
            "YulangClosure.ProviderNativeContextR57.Slot",
            "YulangClosure.ProviderNativeContextR57.admission",
            "YulangClosure.ProviderNativeContextR57.bound",
            "YulangClosure.ProviderNativeContextR57.physical"
          ],
          "type_contract": "structure Emission (T : Type) where\n  state : Nat\n  admission : Nat\n  bound : Bound T\n  physical : Slot\n  readbackSlot : Slot\n  readbackBound : Bound T\n  deriving DecidableEq",
          "normalized_sha256": "6150050f492ea2df8d7988b4481176659dab0bc47056813acf8f06e45cb256a6",
          "normalized_bytes": 175,
          "normalized_prefix_line_range": [
            596,
            603
          ],
          "r83_audit2_prefix_line_range": [
            596,
            603
          ]
        },
        {
          "name": "Physical",
          "kind": "structure",
          "range": [
            70,
            77
          ],
          "declaration_line": 70,
          "sha256": "6289edf1125d76b04f425e2ea0cb32f15ca281f84f54ccff492fbf5476a4346f",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Admission",
            "YulangClosure.ProviderNativeContextR57.Emission",
            "YulangClosure.ProviderNativeContextR57.admission",
            "YulangClosure.ProviderNativeContextR57.emission"
          ],
          "type_contract": "structure Physical (T : Type) where\n  admissionIndex : Nat\n  emissionIndex : Nat\n  admission : Admission T\n  emission : Emission T\n  relation : Nat\n  ancestry : List Nat\n  deriving DecidableEq",
          "normalized_sha256": "6289edf1125d76b04f425e2ea0cb32f15ca281f84f54ccff492fbf5476a4346f",
          "normalized_bytes": 193,
          "normalized_prefix_line_range": [
            605,
            612
          ],
          "r83_audit2_prefix_line_range": [
            605,
            612
          ]
        },
        {
          "name": "Bounds",
          "kind": "structure",
          "range": [
            78,
            82
          ],
          "declaration_line": 78,
          "sha256": "0bc4b3895b00770b6eb974b73494a6cfd4d6964795484802f84821327db9f6ea",
          "references": [],
          "type_contract": "structure Bounds (A : Type) where\n  lowerRows : List Nat\n  upperRows : List Nat\n  lowerAtoms : List A\n  upperAtoms : List A",
          "normalized_sha256": "0bc4b3895b00770b6eb974b73494a6cfd4d6964795484802f84821327db9f6ea",
          "normalized_bytes": 124,
          "normalized_prefix_line_range": [
            614,
            618
          ],
          "r83_audit2_prefix_line_range": [
            614,
            618
          ]
        },
        {
          "name": "ValueRow",
          "kind": "structure",
          "range": [
            83,
            87
          ],
          "declaration_line": 83,
          "sha256": "7f5ea32aeb662376dc69afc54f61e03e4f24945f19eb7f7fb23a65de647b5ee9",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Bounds",
            "YulangClosure.ProviderNativeContextR57.ValueEndpoint"
          ],
          "type_contract": "structure ValueRow (T : Type) where\n  state : Nat\n  index : Nat\n  canonical : Nat\n  bounds : Bounds (ValueEndpoint T)",
          "normalized_sha256": "7f5ea32aeb662376dc69afc54f61e03e4f24945f19eb7f7fb23a65de647b5ee9",
          "normalized_bytes": 118,
          "normalized_prefix_line_range": [
            620,
            624
          ],
          "r83_audit2_prefix_line_range": [
            620,
            624
          ]
        },
        {
          "name": "EffectRow",
          "kind": "structure",
          "range": [
            88,
            92
          ],
          "declaration_line": 88,
          "sha256": "1acb99cfba534d1337ed26522820c8f9dc9b8eb8e29f0879e5422670da59228f",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Bounds",
            "YulangClosure.ProviderNativeContextR57.EffectEndpoint"
          ],
          "type_contract": "structure EffectRow where\n  state : Nat\n  index : Nat\n  canonical : Nat\n  bounds : Bounds EffectEndpoint",
          "normalized_sha256": "1acb99cfba534d1337ed26522820c8f9dc9b8eb8e29f0879e5422670da59228f",
          "normalized_bytes": 105,
          "normalized_prefix_line_range": [
            626,
            630
          ],
          "r83_audit2_prefix_line_range": [
            626,
            630
          ]
        },
        {
          "name": "Relation",
          "kind": "structure",
          "range": [
            93,
            97
          ],
          "declaration_line": 93,
          "sha256": "fa2cc1f86c006c4e1c6e0a361dca2e9a460743d0fdd6d5888c5ee375029f9258",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Endpoint"
          ],
          "type_contract": "structure Relation (T : Type) where\n  state : Nat\n  index : Nat\n  lower : Endpoint T\n  upper : Endpoint T",
          "normalized_sha256": "fa2cc1f86c006c4e1c6e0a361dca2e9a460743d0fdd6d5888c5ee375029f9258",
          "normalized_bytes": 106,
          "normalized_prefix_line_range": [
            632,
            636
          ],
          "r83_audit2_prefix_line_range": [
            632,
            636
          ]
        },
        {
          "name": "Dependency",
          "kind": "structure",
          "range": [
            98,
            101
          ],
          "declaration_line": 98,
          "sha256": "5f2e5f7fb288a49daa9dbfad59a7978480b2e531727293f60e2ede8866f92827",
          "references": [],
          "type_contract": "structure Dependency where\n  state : Nat\n  parent : Nat\n  child : Nat",
          "normalized_sha256": "5f2e5f7fb288a49daa9dbfad59a7978480b2e531727293f60e2ede8866f92827",
          "normalized_bytes": 70,
          "normalized_prefix_line_range": [
            638,
            641
          ],
          "r83_audit2_prefix_line_range": [
            638,
            641
          ]
        },
        {
          "name": "SourceFact",
          "kind": "structure",
          "range": [
            102,
            109
          ],
          "declaration_line": 102,
          "sha256": "0193135cb5f497ef4acf9ac7a0283d2b9382ef942f42d1a58fdcc4d75d2b65db",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Endpoint",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "structure SourceFact (S T : Type) where\n  identity : Fact\n  occurrence : S\n  slot : Nat\n  rawLower : Endpoint T\n  rawUpper : Endpoint T\n  canonicalLower : Endpoint T\n  canonicalUpper : Endpoint T",
          "normalized_sha256": "0193135cb5f497ef4acf9ac7a0283d2b9382ef942f42d1a58fdcc4d75d2b65db",
          "normalized_bytes": 196,
          "normalized_prefix_line_range": [
            643,
            650
          ],
          "r83_audit2_prefix_line_range": [
            643,
            650
          ]
        },
        {
          "name": "Drain",
          "kind": "structure",
          "range": [
            110,
            121
          ],
          "declaration_line": 110,
          "sha256": "099c9e52b26315896d5fcd561c915e25128dbcd72c7ce7d07d13e9d685684bf6",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Endpoint",
            "YulangClosure.ProviderNativeContextR57.completed",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "structure Drain (S T : Type) where\n  state : Nat\n  originIndex : Nat\n  createdSeed : Nat\n  selectedRelation : Nat\n  cause : S\n  slot : Nat\n  taskLower : Endpoint T\n  taskUpper : Endpoint T\n  incoming : Option Nat\n  replay : Bool\n  completed : Bool",
          "normalized_sha256": "099c9e52b26315896d5fcd561c915e25128dbcd72c7ce7d07d13e9d685684bf6",
          "normalized_bytes": 248,
          "normalized_prefix_line_range": [
            652,
            663
          ],
          "r83_audit2_prefix_line_range": [
            652,
            663
          ]
        },
        {
          "name": "Origin",
          "kind": "structure",
          "range": [
            122,
            127
          ],
          "declaration_line": 122,
          "sha256": "e0781b5a6378c4f4afb6f446986fa88e5d14dbd9c28fadead9b4bf5016edd68f",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Drain",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "structure Origin (S T : Type) where\n  state : Nat\n  relation : Nat\n  occurrence : S\n  slot : Nat\n  drain : Option (Drain S T)",
          "normalized_sha256": "e0781b5a6378c4f4afb6f446986fa88e5d14dbd9c28fadead9b4bf5016edd68f",
          "normalized_bytes": 126,
          "normalized_prefix_line_range": [
            665,
            670
          ],
          "r83_audit2_prefix_line_range": [
            665,
            670
          ]
        },
        {
          "name": "ViewOrigin",
          "kind": "inductive",
          "range": [
            128,
            128
          ],
          "declaration_line": 128,
          "sha256": "08811726f6a6d250fbcaf158d3873ceea88308f6794aaef2bc2ce9cdb9e40a56",
          "references": [],
          "type_contract": "inductive ViewOrigin (S : Type) where | annotation | operation (occurrence declaration : S) deriving DecidableEq",
          "normalized_sha256": "08811726f6a6d250fbcaf158d3873ceea88308f6794aaef2bc2ce9cdb9e40a56",
          "normalized_bytes": 113,
          "normalized_prefix_line_range": [
            672,
            672
          ],
          "r83_audit2_prefix_line_range": [
            672,
            672
          ]
        },
        {
          "name": "View",
          "kind": "structure",
          "range": [
            129,
            136
          ],
          "declaration_line": 129,
          "sha256": "179be5a5e17944031c3e945e619c097e080fb07496b252a356d33dd9aa9bd5e5",
          "references": [
            "YulangClosure.ProviderNativeContextR57.ViewOrigin"
          ],
          "type_contract": "structure View (S : Type) where\n  state : Nat\n  index : Nat\n  origin : ViewOrigin S\n  position : S\n  allowed : List S\n  tail : Option Nat\n  deriving DecidableEq",
          "normalized_sha256": "179be5a5e17944031c3e945e619c097e080fb07496b252a356d33dd9aa9bd5e5",
          "normalized_bytes": 161,
          "normalized_prefix_line_range": [
            674,
            681
          ],
          "r83_audit2_prefix_line_range": [
            674,
            681
          ]
        },
        {
          "name": "Operation",
          "kind": "structure",
          "range": [
            137,
            140
          ],
          "declaration_line": 137,
          "sha256": "94417206a9808466144dc31867ee618f06ff8b04a45c939069af67e0bab1c383",
          "references": [],
          "type_contract": "structure Operation (S : Type) where\n  occurrence : S\n  declaration : S\n  family : S",
          "normalized_sha256": "94417206a9808466144dc31867ee618f06ff8b04a45c939069af67e0bab1c383",
          "normalized_bytes": 85,
          "normalized_prefix_line_range": [
            683,
            686
          ],
          "r83_audit2_prefix_line_range": [
            683,
            686
          ]
        },
        {
          "name": "row",
          "kind": "def",
          "range": [
            144,
            146
          ],
          "declaration_line": 144,
          "sha256": "502a8d4c3799d167c9a623529d20d68d5b3ff4da133116acb585e96500b881a6",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.RowKey",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Row"
          ],
          "type_contract": "def row (state : Nat) : Row → CurrentEmissionOwnershipR47.RowKey (Key S T)\n  | .value index => .value (.valueRow state index)\n  | .effect index => .effect (.effectRow state index)",
          "normalized_sha256": "502a8d4c3799d167c9a623529d20d68d5b3ff4da133116acb585e96500b881a6",
          "normalized_bytes": 182,
          "normalized_prefix_line_range": [
            689,
            691
          ],
          "r83_audit2_prefix_line_range": [
            689,
            691
          ]
        },
        {
          "name": "polarity",
          "kind": "def",
          "range": [
            147,
            147
          ],
          "declaration_line": 147,
          "sha256": "32c516327946b06b4fb508c049575693ca457a8f62ec729bfe520058cd3cbbbe",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Polarity",
            "YulangClosure.ProviderNativeContextR57.Polarity"
          ],
          "type_contract": "def polarity : Polarity → CurrentEmissionOwnershipR47.Polarity | .positive => .positive | .negative => .negative",
          "normalized_sha256": "32c516327946b06b4fb508c049575693ca457a8f62ec729bfe520058cd3cbbbe",
          "normalized_bytes": 115,
          "normalized_prefix_line_range": [
            693,
            693
          ],
          "r83_audit2_prefix_line_range": [
            693,
            693
          ]
        },
        {
          "name": "lane",
          "kind": "def",
          "range": [
            148,
            152
          ],
          "declaration_line": 148,
          "sha256": "13b8d34d90a5d5f047c820c8ed34f5186fdd2503baf751fdffc8e96af984849e",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Lane",
            "YulangClosure.ProviderNativeContextR57.Lane"
          ],
          "type_contract": "def lane : Lane → CurrentEmissionOwnershipR47.Lane\n  | .valueLowerRow => .valueLowerRow | .valueUpperRow => .valueUpperRow\n  | .valueLowerAtom => .valueLowerAtom | .valueUpperAtom => .valueUpperAtom\n  | .effectLowerRow => .effectLowerRow | .effectUpperRow => .effectUpperRow\n  | .effectLowerAtom => .effectLowerAtom | .effectUpperAtom => .effectUpperAtom",
          "normalized_sha256": "13b8d34d90a5d5f047c820c8ed34f5186fdd2503baf751fdffc8e96af984849e",
          "normalized_bytes": 357,
          "normalized_prefix_line_range": [
            695,
            699
          ],
          "r83_audit2_prefix_line_range": [
            695,
            699
          ]
        },
        {
          "name": "bound",
          "kind": "def",
          "range": [
            153,
            153
          ],
          "declaration_line": 153,
          "sha256": "d7fc498a96c7658085960aa4ffece9f1e643bf141365c3a28bde0d34a6b93d9f",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Bound",
            "YulangClosure.ProviderNativeContextR57.Bound",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.endpoint",
            "YulangClosure.ProviderNativeContextR57.polarity",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def bound (state : Nat) (b : Bound T) : CurrentEmissionOwnershipR47.Bound (Key S T)",
          "normalized_sha256": "d7fc498a96c7658085960aa4ffece9f1e643bf141365c3a28bde0d34a6b93d9f",
          "normalized_bytes": 155,
          "normalized_prefix_line_range": [
            701,
            701
          ],
          "r83_audit2_prefix_line_range": [
            701,
            701
          ]
        },
        {
          "name": "slot",
          "kind": "def",
          "range": [
            154,
            154
          ],
          "declaration_line": 154,
          "sha256": "f0d0cba64f5e7fcaa16b54cf465bfe51fc2e5d1f7350534bd3396e619b3174ed",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Slot",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Slot",
            "YulangClosure.ProviderNativeContextR57.lane",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def slot (state : Nat) (s : Slot) : CurrentEmissionOwnershipR47.Slot (Key S T)",
          "normalized_sha256": "f0d0cba64f5e7fcaa16b54cf465bfe51fc2e5d1f7350534bd3396e619b3174ed",
          "normalized_bytes": 128,
          "normalized_prefix_line_range": [
            703,
            703
          ],
          "r83_audit2_prefix_line_range": [
            703,
            703
          ]
        },
        {
          "name": "admission",
          "kind": "def",
          "range": [
            155,
            155
          ],
          "declaration_line": 155,
          "sha256": "017b6566c2f5364c77b91b34796e3672baa572e513c897c60722e627ae493691",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Admission",
            "YulangClosure.ProviderNativeContextR57.Admission",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.bound"
          ],
          "type_contract": "def admission (a : Admission T) : CurrentEmissionOwnershipR47.Admission (Key S T)",
          "normalized_sha256": "017b6566c2f5364c77b91b34796e3672baa572e513c897c60722e627ae493691",
          "normalized_bytes": 125,
          "normalized_prefix_line_range": [
            705,
            705
          ],
          "r83_audit2_prefix_line_range": [
            705,
            705
          ]
        },
        {
          "name": "emission",
          "kind": "def",
          "range": [
            156,
            158
          ],
          "declaration_line": 156,
          "sha256": "962a4d0976df8b28e6fba2d8ea9544fc720fb04686d5438f1ba159bc4fef559d",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Emission",
            "YulangClosure.ProviderNativeContextR57.Emission",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.bound",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "def emission (e : Emission T) : CurrentEmissionOwnershipR47.Emission (Key S T)",
          "normalized_sha256": "962a4d0976df8b28e6fba2d8ea9544fc720fb04686d5438f1ba159bc4fef559d",
          "normalized_bytes": 220,
          "normalized_prefix_line_range": [
            707,
            709
          ],
          "r83_audit2_prefix_line_range": [
            707,
            709
          ]
        },
        {
          "name": "physical",
          "kind": "def",
          "range": [
            159,
            160
          ],
          "declaration_line": 159,
          "sha256": "cdf630b08782ec30090bef21ed0bde063dee7129a983f59e023aa7eec586c9eb",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Probe",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Physical",
            "YulangClosure.ProviderNativeContextR57.admission",
            "YulangClosure.ProviderNativeContextR57.emission"
          ],
          "type_contract": "def physical (p : Physical T) : CurrentEmissionOwnershipR47.Probe (Key S T)",
          "normalized_sha256": "cdf630b08782ec30090bef21ed0bde063dee7129a983f59e023aa7eec586c9eb",
          "normalized_bytes": 189,
          "normalized_prefix_line_range": [
            711,
            712
          ],
          "r83_audit2_prefix_line_range": [
            711,
            712
          ]
        },
        {
          "name": "valueBounds",
          "kind": "def",
          "range": [
            164,
            166
          ],
          "declaration_line": 164,
          "sha256": "cad27edb8eb3105ae79a608cae79f351faa27de17744b3ee813e44792911521e",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.RowBounds",
            "YulangClosure.ProviderNativeContextR57.Bounds",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.ValueEndpoint"
          ],
          "type_contract": "def valueBounds (state : Nat) (b : Bounds (ValueEndpoint T)) : CurrentEmissionOwnershipR47.RowBounds (Key S T)",
          "normalized_sha256": "cad27edb8eb3105ae79a608cae79f351faa27de17744b3ee813e44792911521e",
          "normalized_bytes": 281,
          "normalized_prefix_line_range": [
            714,
            716
          ],
          "r83_audit2_prefix_line_range": [
            714,
            716
          ]
        },
        {
          "name": "effectBounds",
          "kind": "def",
          "range": [
            167,
            169
          ],
          "declaration_line": 167,
          "sha256": "60c77ba526fa9abd99eddc8252a85685f84730342f2a7c4591663e6b0f4e53fa",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.RowBounds",
            "YulangClosure.ProviderNativeContextR57.Bounds",
            "YulangClosure.ProviderNativeContextR57.EffectEndpoint",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "def effectBounds (state : Nat) (b : Bounds EffectEndpoint) : CurrentEmissionOwnershipR47.RowBounds (Key S T)",
          "normalized_sha256": "60c77ba526fa9abd99eddc8252a85685f84730342f2a7c4591663e6b0f4e53fa",
          "normalized_bytes": 283,
          "normalized_prefix_line_range": [
            718,
            720
          ],
          "r83_audit2_prefix_line_range": [
            718,
            720
          ]
        },
        {
          "name": "Native",
          "kind": "structure",
          "range": [
            173,
            189
          ],
          "declaration_line": 173,
          "sha256": "a8cc9e732e9d1e63167ba7eca8ea3e421323d506952eb86ec8797237c7837812",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Admission",
            "YulangClosure.ProviderNativeContextR57.Dependency",
            "YulangClosure.ProviderNativeContextR57.EffectRow",
            "YulangClosure.ProviderNativeContextR57.Emission",
            "YulangClosure.ProviderNativeContextR57.Operation",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.Relation",
            "YulangClosure.ProviderNativeContextR57.SourceFact",
            "YulangClosure.ProviderNativeContextR57.ValueRow",
            "YulangClosure.ProviderNativeContextR57.View",
            "YulangClosure.ProviderNativeContextR57.dependencies"
          ],
          "type_contract": "structure Native (S T : Type) where\n  artifact : Nat\n  state : Nat\n  store : Nat\n  batch : Nat\n  entryRow : Nat\n  entryRoot : Nat\n  admissions : List (Admission T)\n  emissions : List (Emission T)\n  valueRows : List (ValueRow T)\n  effectRows : List EffectRow\n  relations : List (Relation T)\n  dependencies : List Dependency\n  origins : List (Origin S T)\n  facts : List (SourceFact S T)\n  views : List (View S)\n  operations : List (Operation S)",
          "normalized_sha256": "a8cc9e732e9d1e63167ba7eca8ea3e421323d506952eb86ec8797237c7837812",
          "normalized_bytes": 443,
          "normalized_prefix_line_range": [
            722,
            738
          ],
          "r83_audit2_prefix_line_range": [
            722,
            738
          ]
        },
        {
          "name": "unique",
          "kind": "def",
          "range": [
            191,
            191
          ],
          "declaration_line": 191,
          "sha256": "2f3de26b21802e35ed54738297d95bd4c2bbfeaca422fb8dbb6315480dde14d9",
          "references": [
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "def unique {A : Type} (test : A → Bool) (xs : List A) : Option A",
          "normalized_sha256": "2f3de26b21802e35ed54738297d95bd4c2bbfeaca422fb8dbb6315480dde14d9",
          "normalized_bytes": 110,
          "normalized_prefix_line_range": [
            740,
            740
          ],
          "r83_audit2_prefix_line_range": [
            740,
            740
          ]
        },
        {
          "name": "factRead",
          "kind": "def",
          "range": [
            192,
            192
          ],
          "declaration_line": 192,
          "sha256": "b7978580d2e8499ff58cc153e997c257d4c361757639e503cc644594b678ec80",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.SourceFact",
            "YulangClosure.ProviderNativeContextR57.unique"
          ],
          "type_contract": "def factRead (n : Native S T) (id : Fact) : Option (SourceFact S T)",
          "normalized_sha256": "b7978580d2e8499ff58cc153e997c257d4c361757639e503cc644594b678ec80",
          "normalized_bytes": 122,
          "normalized_prefix_line_range": [
            742,
            742
          ],
          "r83_audit2_prefix_line_range": [
            742,
            742
          ]
        },
        {
          "name": "sourceFact",
          "kind": "def",
          "range": [
            193,
            198
          ],
          "declaration_line": 193,
          "sha256": "64592b4a86c5e3ff6bedecd845707b0e2a6d81b059b90ee1d8d5447c1365c94d",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.SourceFact",
            "YulangClosure.ProviderNativeContextR57.unique"
          ],
          "type_contract": "def sourceFact (n : Native S T) (key : Key S T × Nat) : Option Fact",
          "normalized_sha256": "64592b4a86c5e3ff6bedecd845707b0e2a6d81b059b90ee1d8d5447c1365c94d",
          "normalized_bytes": 425,
          "normalized_prefix_line_range": [
            744,
            749
          ],
          "r83_audit2_prefix_line_range": [
            744,
            749
          ]
        },
        {
          "name": "relationRead",
          "kind": "def",
          "range": [
            199,
            200
          ],
          "declaration_line": 199,
          "sha256": "60785288f8c888be1386d3b7defd3eb9ea239e3d3de0f7bace369ada8d57c5ff",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Relation",
            "YulangClosure.ProviderNativeContextR57.unique"
          ],
          "type_contract": "def relationRead (n : Native S T) (index : Nat) : Option (Relation T)",
          "normalized_sha256": "60785288f8c888be1386d3b7defd3eb9ea239e3d3de0f7bace369ada8d57c5ff",
          "normalized_bytes": 152,
          "normalized_prefix_line_range": [
            751,
            752
          ],
          "r83_audit2_prefix_line_range": [
            751,
            752
          ]
        },
        {
          "name": "originRead",
          "kind": "def",
          "range": [
            201,
            202
          ],
          "declaration_line": 201,
          "sha256": "8abc16b9af051cc22687a1de907764939e55c6e9b31cf7ba9362c9f9ffe8ac5d",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.unique"
          ],
          "type_contract": "def originRead (n : Native S T) (relation : Nat) : Option (Origin S T)",
          "normalized_sha256": "8abc16b9af051cc22687a1de907764939e55c6e9b31cf7ba9362c9f9ffe8ac5d",
          "normalized_bytes": 157,
          "normalized_prefix_line_range": [
            754,
            755
          ],
          "r83_audit2_prefix_line_range": [
            754,
            755
          ]
        },
        {
          "name": "rootDrain",
          "kind": "def",
          "range": [
            203,
            203
          ],
          "declaration_line": 203,
          "sha256": "ecf1018e844e366caf5259891bc44edc1939ecbaeb28e1edebd85a26c23ec7ec",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Drain",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.originRead"
          ],
          "type_contract": "def rootDrain (n : Native S T) (relation : Nat) : Option (Drain S T)",
          "normalized_sha256": "ecf1018e844e366caf5259891bc44edc1939ecbaeb28e1edebd85a26c23ec7ec",
          "normalized_bytes": 114,
          "normalized_prefix_line_range": [
            757,
            757
          ],
          "r83_audit2_prefix_line_range": [
            757,
            757
          ]
        },
        {
          "name": "rootTask",
          "kind": "def",
          "range": [
            204,
            208
          ],
          "declaration_line": 204,
          "sha256": "b1930cd0934ee1d2a43c55ba815934efb42ea50dc31e2bc085d37a0abd80c0a2",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.factRead",
            "YulangClosure.ProviderNativeContextR57.rootDrain",
            "YulangClosure.ProviderNativeContextR57.sourceFact"
          ],
          "type_contract": "def rootTask (n : Native S T) (relation : Nat) : Option Fact",
          "normalized_sha256": "b1930cd0934ee1d2a43c55ba815934efb42ea50dc31e2bc085d37a0abd80c0a2",
          "normalized_bytes": 272,
          "normalized_prefix_line_range": [
            759,
            763
          ],
          "r83_audit2_prefix_line_range": [
            759,
            763
          ]
        },
        {
          "name": "completed",
          "kind": "def",
          "range": [
            209,
            216
          ],
          "declaration_line": 209,
          "sha256": "2c73151dc05c54c08b7bfe17500c42aac7d38a6652a1b128182bb632d39133df",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.originRead",
            "YulangClosure.ProviderNativeContextR57.rootDrain"
          ],
          "type_contract": "def completed (n : Native S T) (relation : Nat) : Bool",
          "normalized_sha256": "2c73151dc05c54c08b7bfe17500c42aac7d38a6652a1b128182bb632d39133df",
          "normalized_bytes": 489,
          "normalized_prefix_line_range": [
            765,
            772
          ],
          "r83_audit2_prefix_line_range": [
            765,
            772
          ]
        },
        {
          "name": "dependencies",
          "kind": "def",
          "range": [
            217,
            218
          ],
          "declaration_line": 217,
          "sha256": "fedac33b9900580901c9f77e4cd6a44b0b997b4bd3842958b3b82328c83f3035",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Native"
          ],
          "type_contract": "def dependencies (n : Native S T) : List (Nat × Nat)",
          "normalized_sha256": "fedac33b9900580901c9f77e4cd6a44b0b997b4bd3842958b3b82328c83f3035",
          "normalized_bytes": 156,
          "normalized_prefix_line_range": [
            774,
            775
          ],
          "r83_audit2_prefix_line_range": [
            774,
            775
          ]
        },
        {
          "name": "rootCandidates",
          "kind": "def",
          "range": [
            219,
            226
          ],
          "declaration_line": 219,
          "sha256": "0bc2c9db07f35216c17e6f222e14d6e2e1ccca17efd9e105d6877f45eabf6689",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.UseId",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.factRead",
            "YulangClosure.ProviderNativeContextR57.relationRead"
          ],
          "type_contract": "def rootCandidates (n : Native S T) (u : InternalPermissionIncidenceR45.UseId Nat (Key S T)) (id : Fact) : List Nat",
          "normalized_sha256": "0bc2c9db07f35216c17e6f222e14d6e2e1ccca17efd9e105d6877f45eabf6689",
          "normalized_bytes": 536,
          "normalized_prefix_line_range": [
            777,
            784
          ],
          "r83_audit2_prefix_line_range": [
            777,
            784
          ]
        },
        {
          "name": "current",
          "kind": "def",
          "range": [
            228,
            248
          ],
          "declaration_line": 228,
          "sha256": "2f06e12048fca58581768a59cc5463c0049e37cd1fa09329570a934ee17b1401",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Relation",
            "YulangClosure.ProviderNativeContextR57.admission",
            "YulangClosure.ProviderNativeContextR57.completed",
            "YulangClosure.ProviderNativeContextR57.dependencies",
            "YulangClosure.ProviderNativeContextR57.effectBounds",
            "YulangClosure.ProviderNativeContextR57.emission",
            "YulangClosure.ProviderNativeContextR57.endpoint",
            "YulangClosure.ProviderNativeContextR57.originRead",
            "YulangClosure.ProviderNativeContextR57.relationRead",
            "YulangClosure.ProviderNativeContextR57.rootCandidates",
            "YulangClosure.ProviderNativeContextR57.rootDrain",
            "YulangClosure.ProviderNativeContextR57.rootTask",
            "YulangClosure.ProviderNativeContextR57.sourceFact",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.ProviderNativeContextR57.valueBounds"
          ],
          "type_contract": "def current (n : Native S T) : CurrentEmissionOwnershipR47.Inputs Nat (Key S T) Fact",
          "normalized_sha256": "2f06e12048fca58581768a59cc5463c0049e37cd1fa09329570a934ee17b1401",
          "normalized_bytes": 1275,
          "normalized_prefix_line_range": [
            786,
            806
          ],
          "r83_audit2_prefix_line_range": [
            786,
            806
          ]
        },
        {
          "name": "fixtureBound",
          "kind": "def",
          "range": [
            750,
            750
          ],
          "declaration_line": 750,
          "sha256": "32bd4f58fc98c5bdfe2a70ad06cc255f5f309139450e6cbe00ff375bce84d4d1",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Bound",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def fixtureBound (row : Nat) : Bound Nat",
          "normalized_sha256": "32bd4f58fc98c5bdfe2a70ad06cc255f5f309139450e6cbe00ff375bce84d4d1",
          "normalized_bytes": 106,
          "normalized_prefix_line_range": [
            808,
            808
          ],
          "r83_audit2_prefix_line_range": [
            808,
            808
          ]
        },
        {
          "name": "fixtureSlot",
          "kind": "def",
          "range": [
            751,
            751
          ],
          "declaration_line": 751,
          "sha256": "0bac4cfde0271c2c145d37f4aa1dcb2912eca554df6a37ec3d92f45f010d4d95",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Slot",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def fixtureSlot (row : Nat) : Slot",
          "normalized_sha256": "0bac4cfde0271c2c145d37f4aa1dcb2912eca554df6a37ec3d92f45f010d4d95",
          "normalized_bytes": 77,
          "normalized_prefix_line_range": [
            810,
            810
          ],
          "r83_audit2_prefix_line_range": [
            810,
            810
          ]
        },
        {
          "name": "fixtureAdmission",
          "kind": "def",
          "range": [
            752,
            752
          ],
          "declaration_line": 752,
          "sha256": "20412fcd0149052994efe1f27b4a3cc287aeb0981e3ff2047b37c4a13866162f",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Admission",
            "YulangClosure.ProviderNativeContextR57.fixtureBound",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def fixtureAdmission (row relation : Nat) : Admission Nat",
          "normalized_sha256": "20412fcd0149052994efe1f27b4a3cc287aeb0981e3ff2047b37c4a13866162f",
          "normalized_bytes": 102,
          "normalized_prefix_line_range": [
            812,
            812
          ],
          "r83_audit2_prefix_line_range": [
            812,
            812
          ]
        },
        {
          "name": "fixtureEmission",
          "kind": "def",
          "range": [
            753,
            754
          ],
          "declaration_line": 753,
          "sha256": "af53cebda2974799f858f9f9c37a211eeb34b8c1798fd853856cbe3480796b05",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Emission",
            "YulangClosure.ProviderNativeContextR57.fixtureBound",
            "YulangClosure.ProviderNativeContextR57.fixtureSlot",
            "YulangClosure.ProviderNativeContextR57.row"
          ],
          "type_contract": "def fixtureEmission (row index : Nat) : Emission Nat",
          "normalized_sha256": "af53cebda2974799f858f9f9c37a211eeb34b8c1798fd853856cbe3480796b05",
          "normalized_bytes": 143,
          "normalized_prefix_line_range": [
            814,
            815
          ],
          "r83_audit2_prefix_line_range": [
            814,
            815
          ]
        },
        {
          "name": "fixtureView",
          "kind": "def",
          "range": [
            757,
            757
          ],
          "declaration_line": 757,
          "sha256": "13afe73861f7d77bf54da26d67e1a69fb9d8caac79088116626efed4764752ba",
          "references": [
            "YulangClosure.ProviderNativeContextR57.View"
          ],
          "type_contract": "def fixtureView : View Nat",
          "normalized_sha256": "13afe73861f7d77bf54da26d67e1a69fb9d8caac79088116626efed4764752ba",
          "normalized_bytes": 77,
          "normalized_prefix_line_range": [
            817,
            817
          ],
          "r83_audit2_prefix_line_range": [
            817,
            817
          ]
        },
        {
          "name": "fixtureNative",
          "kind": "def",
          "range": [
            758,
            775
          ],
          "declaration_line": 758,
          "sha256": "125c46b5f9200398c9ab28ef02bbe8e16083e9317aef421b7384e7346af05f37",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.dependencies",
            "YulangClosure.ProviderNativeContextR57.fixtureAdmission",
            "YulangClosure.ProviderNativeContextR57.fixtureEmission",
            "YulangClosure.ProviderNativeContextR57.fixtureView"
          ],
          "type_contract": "def fixtureNative : Native Nat Nat",
          "normalized_sha256": "125c46b5f9200398c9ab28ef02bbe8e16083e9317aef421b7384e7346af05f37",
          "normalized_bytes": 1189,
          "normalized_prefix_line_range": [
            819,
            836
          ],
          "r83_audit2_prefix_line_range": [
            819,
            836
          ]
        },
        {
          "name": "fixtureFormal",
          "kind": "def",
          "range": [
            785,
            786
          ],
          "declaration_line": 785,
          "sha256": "3741087d8dc019c27e6c8e01f5ee03b61443c80c0d463a0389f4e14da1f1ff60",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Formal"
          ],
          "type_contract": "def fixtureFormal : SourceInternalContextR55.Formal (Key Nat Nat) Nat",
          "normalized_sha256": "3741087d8dc019c27e6c8e01f5ee03b61443c80c0d463a0389f4e14da1f1ff60",
          "normalized_bytes": 166,
          "normalized_prefix_line_range": [
            838,
            839
          ],
          "r83_audit2_prefix_line_range": [
            838,
            839
          ]
        },
        {
          "name": "fixtureConstruction",
          "kind": "def",
          "range": [
            787,
            788
          ],
          "declaration_line": 787,
          "sha256": "90fddc23e8234ba3e8fb4e8c07f993ccf11d30a28531fdeba81f6dc617eb6f50",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Construction"
          ],
          "type_contract": "def fixtureConstruction : SourceInternalContextR55.Construction (Key Nat Nat) Nat",
          "normalized_sha256": "90fddc23e8234ba3e8fb4e8c07f993ccf11d30a28531fdeba81f6dc617eb6f50",
          "normalized_bytes": 128,
          "normalized_prefix_line_range": [
            841,
            842
          ],
          "r83_audit2_prefix_line_range": [
            841,
            842
          ]
        },
        {
          "name": "fixturePermission",
          "kind": "def",
          "range": [
            789,
            791
          ],
          "declaration_line": 789,
          "sha256": "bc06c14bfa62765c9803cd16b264b36ba84cdeef0fa937bd8b4649a27425ed94",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Permission"
          ],
          "type_contract": "def fixturePermission : SourceInternalContextR55.Permission (Key Nat Nat)",
          "normalized_sha256": "bc06c14bfa62765c9803cd16b264b36ba84cdeef0fa937bd8b4649a27425ed94",
          "normalized_bytes": 213,
          "normalized_prefix_line_range": [
            844,
            846
          ],
          "r83_audit2_prefix_line_range": [
            844,
            846
          ]
        },
        {
          "name": "fixtureUse",
          "kind": "def",
          "range": [
            792,
            792
          ],
          "declaration_line": 792,
          "sha256": "503131138e545f280c599527f8b999e3c934ea7adba8eb044ce48eb29665ebd6",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def fixtureUse : SourceInternalContextR55.Use Nat (Key Nat Nat)",
          "normalized_sha256": "503131138e545f280c599527f8b999e3c934ea7adba8eb044ce48eb29665ebd6",
          "normalized_bytes": 89,
          "normalized_prefix_line_range": [
            848,
            848
          ],
          "r83_audit2_prefix_line_range": [
            848,
            848
          ]
        },
        {
          "name": "fixtureReceipt",
          "kind": "def",
          "range": [
            793,
            793
          ],
          "declaration_line": 793,
          "sha256": "e40c7b486dacaa8b4134a36a0013b630b3e2f10adf7f8901943529c0b1732f60",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.fixtureUse",
            "YulangClosure.SourceInternalContextR55.Receipt"
          ],
          "type_contract": "def fixtureReceipt : SourceInternalContextR55.Receipt Nat (Key Nat Nat) Fact",
          "normalized_sha256": "e40c7b486dacaa8b4134a36a0013b630b3e2f10adf7f8901943529c0b1732f60",
          "normalized_bytes": 131,
          "normalized_prefix_line_range": [
            850,
            850
          ],
          "r83_audit2_prefix_line_range": [
            850,
            850
          ]
        },
        {
          "name": "fixturePlan",
          "kind": "def",
          "range": [
            794,
            795
          ],
          "declaration_line": 794,
          "sha256": "6d1b6fd3830d6b29c095f77b3d7ccc4df0ea03ac85296fdeffcaf867435ccf93",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.fixtureUse",
            "YulangClosure.SourceInternalContextR55.Plan"
          ],
          "type_contract": "def fixturePlan : SourceInternalContextR55.Plan Nat (Key Nat Nat) Nat",
          "normalized_sha256": "6d1b6fd3830d6b29c095f77b3d7ccc4df0ea03ac85296fdeffcaf867435ccf93",
          "normalized_bytes": 133,
          "normalized_prefix_line_range": [
            852,
            853
          ],
          "r83_audit2_prefix_line_range": [
            852,
            853
          ]
        },
        {
          "name": "fixtureInternal",
          "kind": "def",
          "range": [
            796,
            801
          ],
          "declaration_line": 796,
          "sha256": "5aa2fcd2036aeebb0264ecb9913b1c72f0aa938e24b2ba8125557296c3ee9efe",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.fixtureConstruction",
            "YulangClosure.ProviderNativeContextR57.fixtureFormal",
            "YulangClosure.ProviderNativeContextR57.fixturePermission",
            "YulangClosure.ProviderNativeContextR57.fixturePlan",
            "YulangClosure.ProviderNativeContextR57.fixtureReceipt",
            "YulangClosure.SourceInternalContextR55.Native"
          ],
          "type_contract": "def fixtureInternal : SourceInternalContextR55.Native Nat (Key Nat Nat) Nat Fact",
          "normalized_sha256": "5aa2fcd2036aeebb0264ecb9913b1c72f0aa938e24b2ba8125557296c3ee9efe",
          "normalized_bytes": 557,
          "normalized_prefix_line_range": [
            855,
            860
          ],
          "r83_audit2_prefix_line_range": [
            855,
            860
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.OccurrenceQualifiedFactReadersR65",
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedFactReadersR65.lean",
      "sha256": "3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b",
      "namespace": "YulangClosure.OccurrenceQualifiedFactReadersR65",
      "opens": [
        "ProviderNativeContextR57"
      ],
      "context_range": [
        40,
        40
      ],
      "context": "variable {S T : Type} [DecidableEq S] [DecidableEq T]\n",
      "declarations": [
        {
          "name": "FactRow",
          "kind": "structure",
          "range": [
            13,
            21
          ],
          "declaration_line": 13,
          "sha256": "d11e0924f6069843dc4a0023a636304ea741d4d2270e8893a917f43f50bc689d",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Endpoint",
            "YulangClosure.ProviderNativeContextR57.Fact"
          ],
          "type_contract": "structure FactRow (T : Type) where\n  identity : Fact\n  lower : T\n  upper : T\n  rawLower : Endpoint T\n  rawUpper : Endpoint T\n  canonicalLower : Endpoint T\n  canonicalUpper : Endpoint T\n  deriving DecidableEq",
          "normalized_sha256": "d11e0924f6069843dc4a0023a636304ea741d4d2270e8893a917f43f50bc689d",
          "normalized_bytes": 208,
          "normalized_prefix_line_range": [
            865,
            873
          ],
          "r83_audit2_prefix_line_range": [
            865,
            873
          ]
        },
        {
          "name": "Edge",
          "kind": "structure",
          "range": [
            23,
            28
          ],
          "declaration_line": 23,
          "sha256": "2e792cfccb99187fbb94953dd999921e8194446f52e26bde81034f3bdd96415f",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "structure Edge (S : Type) where\n  edgeIndex : Nat\n  fact : Fact\n  occurrence : S\n  slot : Nat\n  deriving DecidableEq",
          "normalized_sha256": "2e792cfccb99187fbb94953dd999921e8194446f52e26bde81034f3bdd96415f",
          "normalized_bytes": 117,
          "normalized_prefix_line_range": [
            875,
            880
          ],
          "r83_audit2_prefix_line_range": [
            875,
            880
          ]
        },
        {
          "name": "Inventory",
          "kind": "structure",
          "range": [
            30,
            33
          ],
          "declaration_line": 30,
          "sha256": "b12d72867a3c36192e04bde3dda0576168141d85102b2952a5a9260c4b3e5667",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow"
          ],
          "type_contract": "structure Inventory (S T : Type) where\n  store : Nat\n  facts : List (FactRow T)\n  edges : List (Edge S)",
          "normalized_sha256": "b12d72867a3c36192e04bde3dda0576168141d85102b2952a5a9260c4b3e5667",
          "normalized_bytes": 104,
          "normalized_prefix_line_range": [
            882,
            885
          ],
          "r83_audit2_prefix_line_range": [
            882,
            885
          ]
        },
        {
          "name": "Read",
          "kind": "structure",
          "range": [
            35,
            38
          ],
          "declaration_line": 35,
          "sha256": "104d725398b1ff9803537eddc9edc5f97fdb77bee686aebe11e81d99917339d1",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow"
          ],
          "type_contract": "structure Read (S T : Type) where\n  edge : Edge S\n  fact : FactRow T\n  deriving DecidableEq",
          "normalized_sha256": "104d725398b1ff9803537eddc9edc5f97fdb77bee686aebe11e81d99917339d1",
          "normalized_bytes": 92,
          "normalized_prefix_line_range": [
            887,
            890
          ],
          "r83_audit2_prefix_line_range": [
            887,
            890
          ]
        },
        {
          "name": "candidates",
          "kind": "def",
          "range": [
            43,
            44
          ],
          "declaration_line": 43,
          "sha256": "5f77a8e3fa68b43f63510cbd844dd88878b259a82ef1573c647f11384fe849ca",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "def candidates (n : Inventory S T) (occurrence : S) (slot : Nat) : List (Edge S)",
          "normalized_sha256": "5f77a8e3fa68b43f63510cbd844dd88878b259a82ef1573c647f11384fe849ca",
          "normalized_bytes": 174,
          "normalized_prefix_line_range": [
            893,
            894
          ],
          "r83_audit2_prefix_line_range": [
            893,
            894
          ]
        },
        {
          "name": "resolve",
          "kind": "def",
          "range": [
            52,
            58
          ],
          "declaration_line": 52,
          "sha256": "d983fb191949457c7c5d67701554c55b31d38a6da438d52ecf1d4f61e3ec20ad",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.ProviderNativeContextR57.Fact"
          ],
          "type_contract": "def resolve (n : Inventory S T) (id : Fact) : Option (FactRow T)",
          "normalized_sha256": "d983fb191949457c7c5d67701554c55b31d38a6da438d52ecf1d4f61e3ec20ad",
          "normalized_bytes": 278,
          "normalized_prefix_line_range": [
            896,
            902
          ],
          "r83_audit2_prefix_line_range": [
            896,
            902
          ]
        },
        {
          "name": "readAt",
          "kind": "def",
          "range": [
            60,
            63
          ],
          "declaration_line": 60,
          "sha256": "c031e6e29e7871ba913c8e4b213c7b13553a02cdefa8002b6dab267450fe8c6e",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Read",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.candidates",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.resolve",
            "YulangClosure.ProviderNativeContextR57.slot"
          ],
          "type_contract": "def readAt (n : Inventory S T) (occurrence : S) (slot : Nat) : Option (Read S T)",
          "normalized_sha256": "c031e6e29e7871ba913c8e4b213c7b13553a02cdefa8002b6dab267450fe8c6e",
          "normalized_bytes": 211,
          "normalized_prefix_line_range": [
            904,
            907
          ],
          "r83_audit2_prefix_line_range": [
            904,
            907
          ]
        },
        {
          "name": "sourceFact",
          "kind": "def",
          "range": [
            209,
            212
          ],
          "declaration_line": 209,
          "sha256": "5511d8b523faba52fdbfe2f49aa9b6d12dcc47d80e307edfaabdf7c51a4fa842",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.readAt",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "def sourceFact (n : Inventory S T) (key : Key S T × Nat) : Option Fact",
          "normalized_sha256": "5511d8b523faba52fdbfe2f49aa9b6d12dcc47d80e307edfaabdf7c51a4fa842",
          "normalized_bytes": 199,
          "normalized_prefix_line_range": [
            909,
            912
          ],
          "r83_audit2_prefix_line_range": [
            909,
            912
          ]
        },
        {
          "name": "routeFact",
          "kind": "def",
          "range": [
            215,
            220
          ],
          "declaration_line": 215,
          "sha256": "6be3c87428faf4049608221d89e8aa506300aacaf5e3a0763901f1b718590ff4",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.readAt",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "def routeFact (n : Inventory S T) (occurrence : Key S T) (id : Fact) : Option (Key S T × T × T)",
          "normalized_sha256": "6be3c87428faf4049608221d89e8aa506300aacaf5e3a0763901f1b718590ff4",
          "normalized_bytes": 317,
          "normalized_prefix_line_range": [
            914,
            919
          ],
          "r83_audit2_prefix_line_range": [
            914,
            919
          ]
        },
        {
          "name": "lambdaFact",
          "kind": "def",
          "range": [
            222,
            225
          ],
          "declaration_line": 222,
          "sha256": "a87000593a2955bb4e5e044af43287907d57248b15c9073c703de61fdc23f44c",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.readAt",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "def lambdaFact (n : Inventory S T) (occurrence : Key S T) : Option (T × T)",
          "normalized_sha256": "a87000593a2955bb4e5e044af43287907d57248b15c9073c703de61fdc23f44c",
          "normalized_bytes": 220,
          "normalized_prefix_line_range": [
            921,
            924
          ],
          "r83_audit2_prefix_line_range": [
            921,
            924
          ]
        },
        {
          "name": "internalInputs",
          "kind": "def",
          "range": [
            246,
            250
          ],
          "declaration_line": 246,
          "sha256": "503a04f467084b0d24c954112eaec5c52d3998096554c4017b795c25f7216d65",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Inputs",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.lambdaFact",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.routeFact",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Native",
            "YulangClosure.SourceInternalContextR55.internalInputs"
          ],
          "type_contract": "def internalInputs (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)\n    (n : Inventory S T) (useOccurrence : Key S T) : InternalPermissionIncidenceR45.Inputs Nat (Key S T) T Fact",
          "normalized_sha256": "503a04f467084b0d24c954112eaec5c52d3998096554c4017b795c25f7216d65",
          "normalized_bytes": 329,
          "normalized_prefix_line_range": [
            926,
            930
          ],
          "r83_audit2_prefix_line_range": [
            926,
            930
          ]
        },
        {
          "name": "rootTask",
          "kind": "def",
          "range": [
            260,
            266
          ],
          "declaration_line": 260,
          "sha256": "3e4cd855efb5f0819b29c20c7e9ab3ab17afd103005f9174338676ac42f788bb",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.readAt",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.rootDrain"
          ],
          "type_contract": "def rootTask (native : Native S T) (n : Inventory S T) (relation : Nat) : Option Fact",
          "normalized_sha256": "3e4cd855efb5f0819b29c20c7e9ab3ab17afd103005f9174338676ac42f788bb",
          "normalized_bytes": 397,
          "normalized_prefix_line_range": [
            932,
            938
          ],
          "r83_audit2_prefix_line_range": [
            932,
            938
          ]
        },
        {
          "name": "rootCandidates",
          "kind": "def",
          "range": [
            268,
            281
          ],
          "declaration_line": 268,
          "sha256": "d7e567d12aef38269c801f68897883104835d6d4bf4594b0c9cf2cb4a322a310",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.UseId",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.readAt",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Origin",
            "YulangClosure.ProviderNativeContextR57.relationRead"
          ],
          "type_contract": "def rootCandidates (native : Native S T) (n : Inventory S T)\n    (use : InternalPermissionIncidenceR45.UseId Nat (Key S T)) (id : Fact) : List Nat",
          "normalized_sha256": "d7e567d12aef38269c801f68897883104835d6d4bf4594b0c9cf2cb4a322a310",
          "normalized_bytes": 822,
          "normalized_prefix_line_range": [
            940,
            953
          ],
          "r83_audit2_prefix_line_range": [
            940,
            953
          ]
        },
        {
          "name": "current",
          "kind": "def",
          "range": [
            283,
            288
          ],
          "declaration_line": 283,
          "sha256": "674815e5847cebfaa1fa5ca9ba1d4b3f0a9e79b5a2e83db2527ec8e68d087d3e",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Inputs",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.rootCandidates",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.rootTask",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.sourceFact",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.current",
            "YulangClosure.ProviderNativeContextR57.sourceFact"
          ],
          "type_contract": "def current (native : Native S T) (n : Inventory S T) : CurrentEmissionOwnershipR47.Inputs Nat (Key S T) Fact",
          "normalized_sha256": "674815e5847cebfaa1fa5ca9ba1d4b3f0a9e79b5a2e83db2527ec8e68d087d3e",
          "normalized_bytes": 408,
          "normalized_prefix_line_range": [
            955,
            960
          ],
          "r83_audit2_prefix_line_range": [
            955,
            960
          ]
        },
        {
          "name": "fixtureRoute",
          "kind": "def",
          "range": [
            398,
            400
          ],
          "declaration_line": 398,
          "sha256": "52b91af5db938894cef2d51ad8dd795c4488f523128b513742dd68c398e9aade",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow"
          ],
          "type_contract": "def fixtureRoute : FactRow Nat",
          "normalized_sha256": "52b91af5db938894cef2d51ad8dd795c4488f523128b513742dd68c398e9aade",
          "normalized_bytes": 198,
          "normalized_prefix_line_range": [
            962,
            964
          ],
          "r83_audit2_prefix_line_range": [
            962,
            964
          ]
        },
        {
          "name": "fixtureLambda",
          "kind": "def",
          "range": [
            401,
            403
          ],
          "declaration_line": 401,
          "sha256": "d828fce6151eec4252ed832dead7636f6bf01a2ee5026152b06e1fbd5f09ba00",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow"
          ],
          "type_contract": "def fixtureLambda : FactRow Nat",
          "normalized_sha256": "d828fce6151eec4252ed832dead7636f6bf01a2ee5026152b06e1fbd5f09ba00",
          "normalized_bytes": 199,
          "normalized_prefix_line_range": [
            966,
            968
          ],
          "r83_audit2_prefix_line_range": [
            966,
            968
          ]
        },
        {
          "name": "fixtureFirst",
          "kind": "def",
          "range": [
            404,
            404
          ],
          "declaration_line": 404,
          "sha256": "3d7bd354876313784f8f10e55c781c64a3b1f6a34b6d375e51b2c254524c5256",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge"
          ],
          "type_contract": "def fixtureFirst : Edge Nat",
          "normalized_sha256": "3d7bd354876313784f8f10e55c781c64a3b1f6a34b6d375e51b2c254524c5256",
          "normalized_bytes": 62,
          "normalized_prefix_line_range": [
            970,
            970
          ],
          "r83_audit2_prefix_line_range": [
            970,
            970
          ]
        },
        {
          "name": "fixtureSecond",
          "kind": "def",
          "range": [
            405,
            405
          ],
          "declaration_line": 405,
          "sha256": "8065485326ae47b5272cfbc1cc600863153ec44505d54591c66249b479e0ea3f",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge"
          ],
          "type_contract": "def fixtureSecond : Edge Nat",
          "normalized_sha256": "8065485326ae47b5272cfbc1cc600863153ec44505d54591c66249b479e0ea3f",
          "normalized_bytes": 63,
          "normalized_prefix_line_range": [
            972,
            972
          ],
          "r83_audit2_prefix_line_range": [
            972,
            972
          ]
        },
        {
          "name": "fixtureLambdaEdge",
          "kind": "def",
          "range": [
            406,
            406
          ],
          "declaration_line": 406,
          "sha256": "d9586c1276489b8f7d9ab839de0429d9672285247cadbb304ea9c83108390cb1",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Edge"
          ],
          "type_contract": "def fixtureLambdaEdge : Edge Nat",
          "normalized_sha256": "d9586c1276489b8f7d9ab839de0429d9672285247cadbb304ea9c83108390cb1",
          "normalized_bytes": 66,
          "normalized_prefix_line_range": [
            974,
            974
          ],
          "r83_audit2_prefix_line_range": [
            974,
            974
          ]
        },
        {
          "name": "fixtureInventory",
          "kind": "def",
          "range": [
            407,
            408
          ],
          "declaration_line": 407,
          "sha256": "3e0eedb5220188ae95232f4b9f8145ad1ee8fe3d6e754bf102a896296e7959bb",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureFirst",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureLambda",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureLambdaEdge",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureRoute",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureSecond"
          ],
          "type_contract": "def fixtureInventory : Inventory Nat Nat",
          "normalized_sha256": "3e0eedb5220188ae95232f4b9f8145ad1ee8fe3d6e754bf102a896296e7959bb",
          "normalized_bytes": 135,
          "normalized_prefix_line_range": [
            976,
            977
          ],
          "r83_audit2_prefix_line_range": [
            976,
            977
          ]
        },
        {
          "name": "fixtureSource",
          "kind": "def",
          "range": [
            417,
            419
          ],
          "declaration_line": 417,
          "sha256": "d03134598123298a949bc59da11760329d19b9582160f3581ccec39099f77945",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.fixtureInternal",
            "YulangClosure.ProviderNativeContextR57.fixtureReceipt",
            "YulangClosure.SourceInternalContextR55.Native"
          ],
          "type_contract": "def fixtureSource : SourceInternalContextR55.Native Nat (Key Nat Nat) Nat Fact",
          "normalized_sha256": "d03134598123298a949bc59da11760329d19b9582160f3581ccec39099f77945",
          "normalized_bytes": 230,
          "normalized_prefix_line_range": [
            979,
            981
          ],
          "r83_audit2_prefix_line_range": [
            979,
            981
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.OccurrenceQualifiedConsumerR66",
      "path": "notes/theory/lean/YulangClosure/OccurrenceQualifiedConsumerR66.lean",
      "sha256": "5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1",
      "namespace": "YulangClosure.OccurrenceQualifiedConsumerR66",
      "opens": [
        "ProviderNativeContextR57"
      ],
      "context_range": [
        14,
        14
      ],
      "context": "variable {S T : Type} [DecidableEq S] [DecidableEq T]\n",
      "declarations": [
        {
          "name": "Source",
          "kind": "abbrev",
          "range": [
            15,
            15
          ],
          "declaration_line": 15,
          "sha256": "fc0f441a20560bfa1540d6ffab8abc19f8a3f5196d4ec111727d4ff4b6379497",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Native"
          ],
          "type_contract": "abbrev Source (S T : Type) := SourceInternalContextR55.Native Nat (Key S T) T Fact",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "fc0f441a20560bfa1540d6ffab8abc19f8a3f5196d4ec111727d4ff4b6379497",
          "normalized_bytes": 83,
          "normalized_prefix_line_range": [
            987,
            987
          ],
          "r83_audit2_prefix_line_range": [
            987,
            987
          ]
        },
        {
          "name": "Request",
          "kind": "abbrev",
          "range": [
            16,
            16
          ],
          "declaration_line": 16,
          "sha256": "299060ad0dd6c5c81475426334ae3da1f79b6a496e11108bef984ddc04e1b1bd",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Query",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "abbrev Request (S T : Type) := InternalPermissionIncidenceR45.Query Nat (Key S T)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "299060ad0dd6c5c81475426334ae3da1f79b6a496e11108bef984ddc04e1b1bd",
          "normalized_bytes": 82,
          "normalized_prefix_line_range": [
            989,
            989
          ],
          "r83_audit2_prefix_line_range": [
            989,
            989
          ]
        },
        {
          "name": "ownerSelection",
          "kind": "def",
          "range": [
            21,
            32
          ],
          "declaration_line": 21,
          "sha256": "db0c45b8afa2628abade752b551ea21af1c14c6d6e7874dc0fd748cd6a1f3fb2",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Construction",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "def ownerSelection (s : Source S T) (target : Key S T) (component : Nat) :\n    Option (SourceInternalContextR55.Construction (Key S T) T)",
          "normalized_sha256": "db0c45b8afa2628abade752b551ea21af1c14c6d6e7874dc0fd748cd6a1f3fb2",
          "normalized_bytes": 616,
          "normalized_prefix_line_range": [
            991,
            1002
          ],
          "r83_audit2_prefix_line_range": [
            991,
            1002
          ]
        },
        {
          "name": "sourceProbe",
          "kind": "def",
          "range": [
            36,
            48
          ],
          "declaration_line": 36,
          "sha256": "334425ac2d7c193de48f3414f2ce82f4bf9f75c2efb942d2898043103c75a2f2",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source",
            "YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "def sourceProbe (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) : Option (InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact)",
          "normalized_sha256": "334425ac2d7c193de48f3414f2ce82f4bf9f75c2efb942d2898043103c75a2f2",
          "normalized_bytes": 1043,
          "normalized_prefix_line_range": [
            1004,
            1016
          ],
          "r83_audit2_prefix_line_range": [
            1004,
            1016
          ]
        },
        {
          "name": "Incidence",
          "kind": "structure",
          "range": [
            50,
            55
          ],
          "declaration_line": 50,
          "sha256": "93c1c69fb69ebd719a82f7832e05fa8de3d10295f5ba542f048e8b859b1781de",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.Identity",
            "YulangClosure.InternalPermissionIncidenceR45.OwnerReads",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source",
            "YulangClosure.OccurrenceQualifiedConsumerR66.sourceProbe",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key"
          ],
          "type_contract": "structure Incidence (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) where\n  probe : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact\n  read : sourceProbe s inventory q = some probe\n  owners : InternalPermissionIncidenceR45.OwnerReads (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe\n  identity : InternalPermissionIncidenceR45.Identity (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q probe\n  parameterRecipe : s.parameterRecipes[probe.formal.recipe]? = some probe.formal.parameter",
          "normalized_sha256": "93c1c69fb69ebd719a82f7832e05fa8de3d10295f5ba542f048e8b859b1781de",
          "normalized_bytes": 612,
          "normalized_prefix_line_range": [
            1018,
            1023
          ],
          "r83_audit2_prefix_line_range": [
            1018,
            1023
          ]
        },
        {
          "name": "rootQuery",
          "kind": "def",
          "range": [
            66,
            67
          ],
          "declaration_line": 66,
          "sha256": "13404f512263656dcbd638d62e47e78f102aba1334f78c519d276449b2085d76",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Query",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Incidence",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native"
          ],
          "type_contract": "def rootQuery (_n : Native S T) (q : Request S T) (i : Incidence s inventory q) (root : Nat) :\n    CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact",
          "normalized_sha256": "13404f512263656dcbd638d62e47e78f102aba1334f78c519d276449b2085d76",
          "normalized_bytes": 210,
          "normalized_prefix_line_range": [
            1025,
            1026
          ],
          "r83_audit2_prefix_line_range": [
            1025,
            1026
          ]
        },
        {
          "name": "BeforeAncestry",
          "kind": "def",
          "range": [
            71,
            84
          ],
          "declaration_line": 71,
          "sha256": "15e1c4aea4edf89463b31526a9708345eea1715aa236d3ae5549e6c4c5c6fa6d",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Probe",
            "YulangClosure.CurrentEmissionOwnershipR47.Query",
            "YulangClosure.CurrentEmissionOwnershipR47.RootMatches",
            "YulangClosure.CurrentEmissionOwnershipR47.boundPair",
            "YulangClosure.CurrentEmissionOwnershipR47.currentBound",
            "YulangClosure.CurrentEmissionOwnershipR47.emissionsForSlot",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.current",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native"
          ],
          "type_contract": "def BeforeAncestry (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact)\n    (p : CurrentEmissionOwnershipR47.Probe (Key S T)) : Prop",
          "normalized_sha256": "15e1c4aea4edf89463b31526a9708345eea1715aa236d3ae5549e6c4c5c6fa6d",
          "normalized_bytes": 1365,
          "normalized_prefix_line_range": [
            1028,
            1041
          ],
          "r83_audit2_prefix_line_range": [
            1028,
            1041
          ]
        },
        {
          "name": "@86",
          "kind": "instance",
          "range": [
            86,
            87
          ],
          "declaration_line": 86,
          "sha256": "76c931d8f90d7c580655d478c2c3081e2e1d1ea6266138c7cc352ab6c31539f6",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Probe",
            "YulangClosure.CurrentEmissionOwnershipR47.Query",
            "YulangClosure.OccurrenceQualifiedConsumerR66.BeforeAncestry",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.Native"
          ],
          "type_contract": "instance (n : Native S T) (q : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact) (p : CurrentEmissionOwnershipR47.Probe (Key S T)) :\n    Decidable (BeforeAncestry inventory n q p)",
          "normalized_sha256": "76c931d8f90d7c580655d478c2c3081e2e1d1ea6266138c7cc352ab6c31539f6",
          "normalized_bytes": 228,
          "normalized_prefix_line_range": [
            1043,
            1044
          ],
          "r83_audit2_prefix_line_range": [
            1043,
            1044
          ]
        },
        {
          "name": "Root",
          "kind": "structure",
          "range": [
            89,
            95
          ],
          "declaration_line": 89,
          "sha256": "8a799dc2e43e734743c0c8c959456eef6f260dfbde09c2e898de22dcd6adb4d5",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.BeforeAncestry",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Incidence",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source",
            "YulangClosure.OccurrenceQualifiedConsumerR66.rootQuery",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.ProviderNativeContextR57.Native",
            "YulangClosure.ProviderNativeContextR57.Physical",
            "YulangClosure.ProviderNativeContextR57.physical"
          ],
          "type_contract": "structure Root (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T) (q : Request S T) where\n  incidence : Incidence s inventory q\n  sameArtifact : s.artifact = n.artifact\n  entry : incidence.probe.permission.entry = .effectRow n.state n.entryRow\n  value : Physical T\n  root : Nat\n  checked : BeforeAncestry inventory n (rootQuery n q incidence root) (physical value)",
          "normalized_sha256": "8a799dc2e43e734743c0c8c959456eef6f260dfbde09c2e898de22dcd6adb4d5",
          "normalized_bytes": 410,
          "normalized_prefix_line_range": [
            1046,
            1052
          ],
          "r83_audit2_prefix_line_range": [
            1046,
            1052
          ]
        },
        {
          "name": "source_incidence_checked",
          "kind": "theorem",
          "range": [
            144,
            146
          ],
          "declaration_line": 144,
          "sha256": "3eba0a6c6fd5f05a0a73e1ce673842a1e487624fafe3cf7c394bcfa3944d906f",
          "references": [
            "YulangClosure.InternalPermissionIncidenceR45.certificate",
            "YulangClosure.InternalPermissionIncidenceR45.extract",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Incidence",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs"
          ],
          "type_contract": "theorem source_incidence_checked (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (q : Request S T) (i : Incidence s inventory q) :\n    InternalPermissionIncidenceR45.extract (OccurrenceQualifiedFactReadersR65.internalInputs s inventory q.use.occurrence) q i.probe = some (InternalPermissionIncidenceR45.certificate q i.probe)",
          "normalized_sha256": "3eba0a6c6fd5f05a0a73e1ce673842a1e487624fafe3cf7c394bcfa3944d906f",
          "normalized_bytes": 431,
          "normalized_prefix_line_range": [
            1054,
            1056
          ],
          "r83_audit2_prefix_line_range": [
            1054,
            1056
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.SourceInternalChoiceR77",
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "namespace": "YulangClosure.SourceInternalChoiceR77",
      "opens": [
        "SourceInternalContextR55",
        "ProviderNativeContextR57"
      ],
      "context_range": [
        13,
        13
      ],
      "context": "variable {S T : Type} [DecidableEq S] [DecidableEq T]\n",
      "declarations": [
        {
          "name": "Source",
          "kind": "abbrev",
          "range": [
            15,
            15
          ],
          "declaration_line": 15,
          "sha256": "a2cdf002c79574833d7f95084e3cf183c000f8d47419c9219c7dabc59b729cac",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source"
          ],
          "type_contract": "abbrev Source (S T : Type) := OccurrenceQualifiedConsumerR66.Source S T",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "a2cdf002c79574833d7f95084e3cf183c000f8d47419c9219c7dabc59b729cac",
          "normalized_bytes": 72,
          "normalized_prefix_line_range": [
            1062,
            1062
          ],
          "r83_audit2_prefix_line_range": [
            1063,
            1063
          ]
        },
        {
          "name": "Origin",
          "kind": "abbrev",
          "range": [
            16,
            16
          ],
          "declaration_line": 16,
          "sha256": "5b804ae409a3731cd54b636b0aa2d856768edb755508533af39f534cc60d39a7",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Construction"
          ],
          "type_contract": "abbrev Origin (S T : Type) := Construction (Key S T) T",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "5b804ae409a3731cd54b636b0aa2d856768edb755508533af39f534cc60d39a7",
          "normalized_bytes": 55,
          "normalized_prefix_line_range": [
            1064,
            1064
          ],
          "r83_audit2_prefix_line_range": [
            1065,
            1065
          ]
        },
        {
          "name": "Failure",
          "kind": "inductive",
          "range": [
            18,
            22
          ],
          "declaration_line": 18,
          "sha256": "a6ede9b6703858374f53b9f09b8d6b8df744f1176dd54d564505b7184a12ceeb",
          "references": [],
          "type_contract": "inductive Failure where\n  | recipe (registration : Nat)\n  | secondOrigin (registration : Nat)\n  | noOrigin\n  deriving DecidableEq",
          "normalized_sha256": "a6ede9b6703858374f53b9f09b8d6b8df744f1176dd54d564505b7184a12ceeb",
          "normalized_bytes": 130,
          "normalized_prefix_line_range": [
            1066,
            1070
          ],
          "r83_audit2_prefix_line_range": [
            1067,
            1071
          ]
        },
        {
          "name": "visit",
          "kind": "def",
          "range": [
            25,
            34
          ],
          "declaration_line": 25,
          "sha256": "07a8da70156115676aa6d29761920ea4a44e28399c3ea5f136b8634aa95e28fd",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Failure",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "def visit (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    Except Failure (Option (Origin S T))",
          "normalized_sha256": "d96bdc1043e8b39b5630af5f513bc8ae3ca6598b31e87779c3d1bd273f9414fd",
          "normalized_bytes": 546,
          "normalized_prefix_line_range": [
            1072,
            1081
          ],
          "r83_audit2_prefix_line_range": [
            1073,
            1082
          ],
          "normalization_index": 0
        },
        {
          "name": "walk",
          "kind": "def",
          "range": [
            38,
            47
          ],
          "declaration_line": 38,
          "sha256": "6f05694752f1c1b57e627f9ce50cfce990cf208b523512bd58eebc1c89360133",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Failure",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.visit"
          ],
          "type_contract": "def walk (s : Source S T) (target : Key S T) (component : Nat) :\n    List (Origin S T) → List (Origin S T) → Except Failure (List (Origin S T))\n  | [], selected => .ok selected\n  | c :: rest, selected =>\n    match visit s target component c with\n    | .error err => .error err\n    | .ok none => walk s target component rest selected\n    | .ok (some chosen) => match selected with\n      | [] => walk s target component rest [chosen]\n      | _ :: _ => .error (.secondOrigin c.registration)",
          "normalized_sha256": "6f05694752f1c1b57e627f9ce50cfce990cf208b523512bd58eebc1c89360133",
          "normalized_bytes": 492,
          "normalized_prefix_line_range": [
            1083,
            1092
          ],
          "r83_audit2_prefix_line_range": [
            1084,
            1093
          ]
        },
        {
          "name": "orderedSelection",
          "kind": "def",
          "range": [
            49,
            55
          ],
          "declaration_line": 49,
          "sha256": "e6e686cbccd8d8389445fabb0550c3c97d25bb643f65c519100a40221b48a651",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Failure",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.walk"
          ],
          "type_contract": "def orderedSelection (s : Source S T) (target : Key S T) (component : Nat) :\n    Except Failure (Origin S T)",
          "normalized_sha256": "e6e686cbccd8d8389445fabb0550c3c97d25bb643f65c519100a40221b48a651",
          "normalized_bytes": 282,
          "normalized_prefix_line_range": [
            1094,
            1100
          ],
          "r83_audit2_prefix_line_range": [
            1095,
            1101
          ]
        },
        {
          "name": "visit_agrees",
          "kind": "theorem",
          "range": [
            58,
            73
          ],
          "declaration_line": 58,
          "sha256": "23674b35d203c7d2155fb4fb0d4f3d7d9ffa308e184d526ee97ab80f62bac35a",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.visit",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "theorem visit_agrees (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    (visit s target component c).toOption =\n      (match s.formals[c.registration]? with\n      | none => some none\n      | some f => if f.role = .computation ∧ f.owner = target then do\n          let recipe ← unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes\n          some (if recipe.rootComponent = component then some c else none)\n        else some none)",
          "normalized_sha256": "50ca23a957d3587c6d22a5384cd3f01d83a990e340cd0f09a19f69d0544b07ba",
          "normalized_bytes": 899,
          "normalized_prefix_line_range": [
            1102,
            1117
          ],
          "r83_audit2_prefix_line_range": [
            1103,
            1118
          ],
          "normalization_index": 1
        },
        {
          "name": "walk_accounts_for_all",
          "kind": "theorem",
          "range": [
            77,
            113
          ],
          "declaration_line": 77,
          "sha256": "cc544d0bdd7a82dca0b29243393c5c0415b1ba4948b7753d4073b64407f2c139",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.visit",
            "YulangClosure.SourceInternalChoiceR77.walk"
          ],
          "type_contract": "theorem walk_accounts_for_all (s : Source S T) (target : Key S T) (component : Nat)\n    (origins selected out : List (Origin S T))\n    (accepted : walk s target component origins selected = .ok out) :\n    ∃ rows, origins.mapM (fun c => (visit s target component c).toOption) = some rows ∧\n      selected ++ rows.filterMap id = out",
          "normalized_sha256": "cc544d0bdd7a82dca0b29243393c5c0415b1ba4948b7753d4073b64407f2c139",
          "normalized_bytes": 1760,
          "normalized_prefix_line_range": [
            1119,
            1155
          ],
          "r83_audit2_prefix_line_range": [
            1120,
            1156
          ]
        },
        {
          "name": "ordered_selection_agrees",
          "kind": "theorem",
          "range": [
            117,
            147
          ],
          "declaration_line": 117,
          "sha256": "4690312cdec1e9ee59fab6a79037218d3bed8ff0d221e8452e94e58225857371",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.orderedSelection",
            "YulangClosure.SourceInternalChoiceR77.visit_agrees",
            "YulangClosure.SourceInternalChoiceR77.walk",
            "YulangClosure.SourceInternalChoiceR77.walk_accounts_for_all",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "theorem ordered_selection_agrees (s : Source S T) (target : Key S T) (component : Nat)\n    (c : Origin S T) (accepted : orderedSelection s target component = .ok c) :\n    OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c",
          "normalized_sha256": "1b8139911c1965e150076d453a88cb1c3f3bc3809817dc1fd09da0af25f775bb",
          "normalized_bytes": 1611,
          "normalized_prefix_line_range": [
            1157,
            1187
          ],
          "r83_audit2_prefix_line_range": [
            1158,
            1188
          ],
          "normalization_index": 2
        },
        {
          "name": "Choice",
          "kind": "structure",
          "range": [
            164,
            180
          ],
          "declaration_line": 164,
          "sha256": "499c02b1874e2786f3dfa07342b7bfb9c5fa0f344c7c0dc69899b30581761cc1",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Origin",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.orderedSelection",
            "YulangClosure.SourceInternalContextR55.Formal",
            "YulangClosure.SourceInternalContextR55.Plan",
            "YulangClosure.SourceInternalContextR55.Receipt",
            "YulangClosure.SourceInternalContextR55.Recipe",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.receipt",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "structure Choice (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T) where\n  plan : Plan Nat (Key S T) T\n  origin : Origin S T\n  formal : Formal (Key S T) T\n  recipe : Recipe (Key S T)\n  receipt : Receipt Nat (Key S T) Fact\n  artifact : u.artifact = s.artifact\n  plans : s.plans.filter (fun p => decide (use p.use = use u)) = [plan]\n  owners : plan.sourceOwner = receiving ∧ plan.targetOwner = target\n  routes : s.receipts.filter (fun r => decide (r.use = u)) = [receipt]\n  internal : receipt.kind = .internal ∧ receipt.fact.isSome = true\n  selected : orderedSelection s target plan.targetRootComponent = .ok origin\n  indexed : s.formals[origin.registration]? = some formal\n  recipes : s.recipes.filter (fun r => decide (r.formalRegistration = some origin.registration)) = [recipe]\n  lambda : recipe.occurrence = origin.lambda\n  component : recipe.rootComponent = plan.targetRootComponent\n  parameter : s.parameterRecipes[formal.recipePosition]? = some formal.parameter",
          "normalized_sha256": "499c02b1874e2786f3dfa07342b7bfb9c5fa0f344c7c0dc69899b30581761cc1",
          "normalized_bytes": 992,
          "normalized_prefix_line_range": [
            1189,
            1205
          ],
          "r83_audit2_prefix_line_range": [
            1190,
            1206
          ]
        },
        {
          "name": "construct",
          "kind": "def",
          "range": [
            185,
            215
          ],
          "declaration_line": 185,
          "sha256": "9bd8a864f01f42d4a3854ae756e1632fb8777a873ff6d153ab76b0c1f6277d9c",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.orderedSelection",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.receipt",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "def construct (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T) :\n    Option (Choice s u receiving target)",
          "normalized_sha256": "9bd8a864f01f42d4a3854ae756e1632fb8777a873ff6d153ab76b0c1f6277d9c",
          "normalized_bytes": 1595,
          "normalized_prefix_line_range": [
            1207,
            1237
          ],
          "r83_audit2_prefix_line_range": [
            1208,
            1238
          ]
        },
        {
          "name": "choice_three_premises",
          "kind": "theorem",
          "range": [
            217,
            223
          ],
          "declaration_line": 217,
          "sha256": "ef4dc5957c8207a6a48d3f78689405e75892d22a83d9831523c4672e7c81cedd",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.ordered_selection_agrees",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.internalInputs",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.unique",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "theorem choice_three_premises (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) :\n    (internalInputs s).plan (use u) = some (SourceInternalContextR55.plan c.plan) ∧\n    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧\n    s.parameterRecipes[c.formal.recipePosition]? = some c.formal.parameter",
          "normalized_sha256": "26bbb05f4a9e0bdc1673e702d27491e14a5be2eded8d40e0bdd6d7335094d8b3",
          "normalized_bytes": 606,
          "normalized_prefix_line_range": [
            1239,
            1245
          ],
          "r83_audit2_prefix_line_range": [
            1240,
            1246
          ],
          "normalization_index": 3
        },
        {
          "name": "choice_applies_r66",
          "kind": "theorem",
          "range": [
            227,
            234
          ],
          "declaration_line": 227,
          "sha256": "ae6e4169beafb7898ab80941e73992827b7656be3c5ead7d90e23023bc746bb4",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.choice_three_premises",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "theorem choice_applies_r66 (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T) (c : Choice s u receiving target) :\n    (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =\n      some (SourceInternalContextR55.plan c.plan) ∧\n    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧\n    s.parameterRecipes[(SourceInternalContextR55.formal c.formal).recipe]? =\n      some (SourceInternalContextR55.formal c.formal).parameter",
          "normalized_sha256": "ae6e4169beafb7898ab80941e73992827b7656be3c5ead7d90e23023bc746bb4",
          "normalized_bytes": 654,
          "normalized_prefix_line_range": [
            1247,
            1254
          ],
          "r83_audit2_prefix_line_range": [
            1248,
            1255
          ]
        },
        {
          "name": "fixture",
          "kind": "def",
          "range": [
            262,
            262
          ],
          "declaration_line": 262,
          "sha256": "b83015ec76e557b91fa35fd85f809d35029d95b8e52c35bca1a67a168ecf2bcc",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureSource"
          ],
          "type_contract": "def fixture := OccurrenceQualifiedFactReadersR65.fixtureSource",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "b83015ec76e557b91fa35fd85f809d35029d95b8e52c35bca1a67a168ecf2bcc",
          "normalized_bytes": 63,
          "normalized_prefix_line_range": [
            1256,
            1256
          ],
          "r83_audit2_prefix_line_range": [
            1257,
            1257
          ]
        },
        {
          "name": "fixtureUse",
          "kind": "def",
          "range": [
            263,
            263
          ],
          "declaration_line": 263,
          "sha256": "95fa6af06669788bf1c61f34947497c8652bedf3d14ac9860769b737f9640606",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def fixtureUse : Use Nat (Key Nat Nat)",
          "normalized_sha256": "95fa6af06669788bf1c61f34947497c8652bedf3d14ac9860769b737f9640606",
          "normalized_bytes": 64,
          "normalized_prefix_line_range": [
            1258,
            1258
          ],
          "r83_audit2_prefix_line_range": [
            1259,
            1259
          ]
        },
        {
          "name": "HirForm",
          "kind": "inductive",
          "range": [
            317,
            322
          ],
          "declaration_line": 317,
          "sha256": "e5142bbcd8f11f81537b94a69f7dbbef6fcc8b84bc458de5804ce0bbd1079253",
          "references": [],
          "type_contract": "inductive HirForm (Id : Type) where\n  | name (target : Id)\n  | group (inner : Nat)\n  | apply (callee argument : Nat)\n  | other\n  deriving DecidableEq",
          "normalized_sha256": "e5142bbcd8f11f81537b94a69f7dbbef6fcc8b84bc458de5804ce0bbd1079253",
          "normalized_bytes": 150,
          "normalized_prefix_line_range": [
            1260,
            1265
          ],
          "r83_audit2_prefix_line_range": [
            1261,
            1266
          ]
        },
        {
          "name": "HirNode",
          "kind": "structure",
          "range": [
            324,
            327
          ],
          "declaration_line": 324,
          "sha256": "8fcfbde366ac81c6db5f917559b43c21c323f67c289244b1a7c17c461774facb",
          "references": [
            "YulangClosure.SourceInternalChoiceR77.HirForm"
          ],
          "type_contract": "structure HirNode (Id : Type) where\n  occurrence : Id\n  form : HirForm Id\n  deriving DecidableEq",
          "normalized_sha256": "8fcfbde366ac81c6db5f917559b43c21c323f67c289244b1a7c17c461774facb",
          "normalized_bytes": 97,
          "normalized_prefix_line_range": [
            1267,
            1270
          ],
          "r83_audit2_prefix_line_range": [
            1268,
            1271
          ]
        },
        {
          "name": "OwnerSource",
          "kind": "structure",
          "range": [
            329,
            331
          ],
          "declaration_line": 329,
          "sha256": "f06aa2bcb3e21d7d402be9ba78650fafe3da7d905e6e10209ddd684d3534cf05",
          "references": [
            "YulangClosure.SourceInternalChoiceR77.HirNode"
          ],
          "type_contract": "structure OwnerSource (Id : Type) where\n  owner : Id\n  expressions : List (HirNode Id)",
          "normalized_sha256": "f06aa2bcb3e21d7d402be9ba78650fafe3da7d905e6e10209ddd684d3534cf05",
          "normalized_bytes": 87,
          "normalized_prefix_line_range": [
            1272,
            1274
          ],
          "r83_audit2_prefix_line_range": [
            1273,
            1275
          ]
        },
        {
          "name": "SourceCall",
          "kind": "structure",
          "range": [
            333,
            339
          ],
          "declaration_line": 333,
          "sha256": "1428ea2bd8fbc9ee2db8862cf7e1d423394e26aeb7bb3349f681ecba7f5a0290",
          "references": [
            "YulangClosure.SourceInternalContextR55.expression"
          ],
          "type_contract": "structure SourceCall (Id : Type) where\n  owner : Id\n  checking : Id\n  expression : Nat\n  callee : Nat\n  argument : Nat\n  deriving DecidableEq",
          "normalized_sha256": "1428ea2bd8fbc9ee2db8862cf7e1d423394e26aeb7bb3349f681ecba7f5a0290",
          "normalized_bytes": 142,
          "normalized_prefix_line_range": [
            1276,
            1282
          ],
          "r83_audit2_prefix_line_range": [
            1277,
            1283
          ]
        },
        {
          "name": "peel",
          "kind": "def",
          "range": [
            343,
            354
          ],
          "declaration_line": 343,
          "sha256": "d3af3a1ec81152a4f16e75279db506ed3406598c801b364681e4894665f3716e",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.HirNode"
          ],
          "type_contract": "def peel (nodes : List (HirNode (Key S T))) :\n    Nat → List Nat → Nat → Option (Key S T × Key S T)\n  | 0, _, _ => none\n  | fuel + 1, seen, index =>\n    if index ∈ seen then none else\n      match nodes[index]? with\n      | none => none\n      | some node => match node.form with\n        | .name target => some (node.occurrence, target)\n        | .group inner => peel nodes fuel (index :: seen) inner\n        | .apply _ _ => none\n        | .other => none",
          "normalized_sha256": "d3af3a1ec81152a4f16e75279db506ed3406598c801b364681e4894665f3716e",
          "normalized_bytes": 462,
          "normalized_prefix_line_range": [
            1284,
            1295
          ],
          "r83_audit2_prefix_line_range": [
            1285,
            1296
          ]
        },
        {
          "name": "alignedCalls",
          "kind": "def",
          "range": [
            393,
            400
          ],
          "declaration_line": 393,
          "sha256": "3aef6e6487aafe9a7b70f492b4723f190d3952426b4c98717b4f0624095afd6d",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.peel",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def alignedCalls (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))\n    (u : Use Nat (Key S T)) (receiving target : Key S T) : List (SourceCall (Key S T))",
          "normalized_sha256": "3aef6e6487aafe9a7b70f492b4723f190d3952426b4c98717b4f0624095afd6d",
          "normalized_bytes": 542,
          "normalized_prefix_line_range": [
            1297,
            1304
          ],
          "r83_audit2_prefix_line_range": [
            1298,
            1305
          ]
        },
        {
          "name": "alignedUses",
          "kind": "def",
          "range": [
            405,
            409
          ],
          "declaration_line": 405,
          "sha256": "503ac0ddb3e3bfd33110ca32e18b957370d76bf296ebbf08e048c4f817fddfd7",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.alignedCalls",
            "YulangClosure.SourceInternalContextR55.Plan"
          ],
          "type_contract": "def alignedUses (s : Source S T) (source : OwnerSource (Key S T))\n    (calls : List (SourceCall (Key S T))) (receiving target : Key S T) :\n    List (Plan Nat (Key S T) T)",
          "normalized_sha256": "503ac0ddb3e3bfd33110ca32e18b957370d76bf296ebbf08e048c4f817fddfd7",
          "normalized_bytes": 336,
          "normalized_prefix_line_range": [
            1306,
            1310
          ],
          "r83_audit2_prefix_line_range": [
            1307,
            1311
          ]
        },
        {
          "name": "Alignment",
          "kind": "structure",
          "range": [
            411,
            422
          ],
          "declaration_line": 411,
          "sha256": "5fff46935194b4c83896f9ac51d11c7e89acbf8293eba8408a6dc76b175db6e3",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.HirNode",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.alignedCalls",
            "YulangClosure.SourceInternalChoiceR77.peel",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "structure Alignment (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))\n    (u : Use Nat (Key S T)) (receiving target : Key S T) where\n  call : SourceCall (Key S T)\n  applyNode : HirNode (Key S T)\n  sourceOwner : source.owner = receiving\n  uniqueCall : alignedCalls source calls u receiving target = [call]\n  callOwner : call.owner = receiving\n  applyIndexed : source.expressions[call.expression]? = some applyNode\n  checking : applyNode.occurrence = call.checking\n  applied : applyNode.form = .apply call.callee call.argument\n  resolved : peel source.expressions (source.expressions.length + 1) [] call.callee =\n    some (u.occurrence, target)",
          "normalized_sha256": "5fff46935194b4c83896f9ac51d11c7e89acbf8293eba8408a6dc76b175db6e3",
          "normalized_bytes": 664,
          "normalized_prefix_line_range": [
            1312,
            1323
          ],
          "r83_audit2_prefix_line_range": [
            1313,
            1324
          ]
        },
        {
          "name": "AlignedChoice",
          "kind": "structure",
          "range": [
            424,
            431
          ],
          "declaration_line": 424,
          "sha256": "0d23fa452e18d74b377ab554b5dc3fedf53b942d5e9cc6c15ea07a1c63d3bc57",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Alignment",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.alignedUses",
            "YulangClosure.SourceInternalContextR55.Plan",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "structure AlignedChoice (s : Source S T) (source : OwnerSource (Key S T))\n    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))\n    (receiving target : Key S T) where\n  selectedUse : Plan Nat (Key S T) T\n  uniqueUse : alignedUses s source calls receiving target = [selectedUse]\n  exactUse : selectedUse.use = u\n  choice : Choice s u receiving target\n  alignment : Alignment source calls u receiving target",
          "normalized_sha256": "0d23fa452e18d74b377ab554b5dc3fedf53b942d5e9cc6c15ea07a1c63d3bc57",
          "normalized_bytes": 418,
          "normalized_prefix_line_range": [
            1325,
            1332
          ],
          "r83_audit2_prefix_line_range": [
            1326,
            1333
          ]
        },
        {
          "name": "constructAligned",
          "kind": "def",
          "range": [
            437,
            465
          ],
          "declaration_line": 437,
          "sha256": "a331b1b7b5250a49c5837c0bdc5b4ca223d50ef93857008816b33a734659d6ad",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.AlignedChoice",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.Source",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.alignedCalls",
            "YulangClosure.SourceInternalChoiceR77.alignedUses",
            "YulangClosure.SourceInternalChoiceR77.construct",
            "YulangClosure.SourceInternalChoiceR77.peel",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def constructAligned (s : Source S T) (source : OwnerSource (Key S T))\n    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))\n    (receiving target : Key S T) : Option (AlignedChoice s source calls u receiving target)",
          "normalized_sha256": "a331b1b7b5250a49c5837c0bdc5b4ca223d50ef93857008816b33a734659d6ad",
          "normalized_bytes": 1428,
          "normalized_prefix_line_range": [
            1334,
            1362
          ],
          "r83_audit2_prefix_line_range": [
            1335,
            1363
          ]
        },
        {
          "name": "fixtureOwnerSource",
          "kind": "def",
          "range": [
            499,
            502
          ],
          "declaration_line": 499,
          "sha256": "06798c0c6c7e54184aadf7aed468ae102aa902c04c62320090494442a8f12135",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource"
          ],
          "type_contract": "def fixtureOwnerSource : OwnerSource (Key Nat Nat)",
          "normalized_sha256": "06798c0c6c7e54184aadf7aed468ae102aa902c04c62320090494442a8f12135",
          "normalized_bytes": 208,
          "normalized_prefix_line_range": [
            1364,
            1367
          ],
          "r83_audit2_prefix_line_range": [
            1365,
            1368
          ]
        },
        {
          "name": "fixtureCall",
          "kind": "def",
          "range": [
            503,
            503
          ],
          "declaration_line": 503,
          "sha256": "5e8e296dca29053848e65773dd4f0e84b40cd98f0d4e36742f485b36a72f1cb0",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.SourceCall"
          ],
          "type_contract": "def fixtureCall : SourceCall (Key Nat Nat)",
          "normalized_sha256": "5e8e296dca29053848e65773dd4f0e84b40cd98f0d4e36742f485b36a72f1cb0",
          "normalized_bytes": 85,
          "normalized_prefix_line_range": [
            1369,
            1369
          ],
          "r83_audit2_prefix_line_range": [
            1370,
            1370
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.ConstructedSourceIncidenceR81",
      "path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "sha256": "3b9e9ac800dccce633c09bf3d7ed0f59f06e910eb42e3a4858e6588f3985bb37",
      "namespace": "YulangClosure.ConstructedSourceIncidenceR81",
      "opens": [
        "SourceInternalContextR55",
        "ProviderNativeContextR57",
        "SourceInternalChoiceR77"
      ],
      "context_range": [
        14,
        14
      ],
      "context": "variable {S T : Type} [DecidableEq S] [DecidableEq T]\n",
      "declarations": [
        {
          "name": "Source",
          "kind": "abbrev",
          "range": [
            16,
            16
          ],
          "declaration_line": 16,
          "sha256": "a2cdf002c79574833d7f95084e3cf183c000f8d47419c9219c7dabc59b729cac",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.Source"
          ],
          "type_contract": "abbrev Source (S T : Type) := OccurrenceQualifiedConsumerR66.Source S T",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "a2cdf002c79574833d7f95084e3cf183c000f8d47419c9219c7dabc59b729cac",
          "normalized_bytes": 72,
          "normalized_prefix_line_range": [
            1375,
            1375
          ],
          "r83_audit2_prefix_line_range": [
            1377,
            1377
          ]
        },
        {
          "name": "Inventory",
          "kind": "abbrev",
          "range": [
            17,
            17
          ],
          "declaration_line": 17,
          "sha256": "f9441a3d0066da9fd0a58b6ce24d7ac6f5e7df5c0a2840db49433bf070ebe2d8",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory"
          ],
          "type_contract": "abbrev Inventory (S T : Type) := OccurrenceQualifiedFactReadersR65.Inventory S T",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "f9441a3d0066da9fd0a58b6ce24d7ac6f5e7df5c0a2840db49433bf070ebe2d8",
          "normalized_bytes": 81,
          "normalized_prefix_line_range": [
            1377,
            1377
          ],
          "r83_audit2_prefix_line_range": [
            1379,
            1379
          ]
        },
        {
          "name": "Records",
          "kind": "structure",
          "range": [
            19,
            23
          ],
          "declaration_line": 19,
          "sha256": "591ce32f2711050732cd867bbef74565fce27b53ef5680b6c949e152dd192d99",
          "references": [
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalContextR55.Permission",
            "YulangClosure.SourceInternalContextR55.permission"
          ],
          "type_contract": "structure Records (S T : Type) where\n  permission : SourceInternalContextR55.Permission (Key S T)\n  root : T\n  child : T\n  fact : Fact",
          "normalized_sha256": "591ce32f2711050732cd867bbef74565fce27b53ef5680b6c949e152dd192d99",
          "normalized_bytes": 135,
          "normalized_prefix_line_range": [
            1379,
            1383
          ],
          "r83_audit2_prefix_line_range": [
            1381,
            1385
          ]
        },
        {
          "name": "request",
          "kind": "def",
          "range": [
            27,
            30
          ],
          "declaration_line": 27,
          "sha256": "a2dc76fcaa176503751d44cf5b79b8f95157285cceee4fc5715ed64990b7ca85",
          "references": [
            "YulangClosure.OccurrenceQualifiedConsumerR66.Request",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "def request (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (annotation row : Key S T) :\n    OccurrenceQualifiedConsumerR66.Request S T",
          "normalized_sha256": "a2dc76fcaa176503751d44cf5b79b8f95157285cceee4fc5715ed64990b7ca85",
          "normalized_bytes": 272,
          "normalized_prefix_line_range": [
            1385,
            1388
          ],
          "r83_audit2_prefix_line_range": [
            1387,
            1390
          ]
        },
        {
          "name": "projected",
          "kind": "def",
          "range": [
            32,
            36
          ],
          "declaration_line": 32,
          "sha256": "5ea925e6494b62a6653a7087d1edd9217e6655dfa0dc2674ce09959fa92d3896",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.InternalPermissionIncidenceR45.Probe",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.construction",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.permission",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.receipt"
          ],
          "type_contract": "def projected {s : Source S T} {u : Use Nat (Key S T)}\n    {receiving target : Key S T} (c : Choice s u receiving target) (d : Records S T) :\n    InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact",
          "normalized_sha256": "5ea925e6494b62a6653a7087d1edd9217e6655dfa0dc2674ce09959fa92d3896",
          "normalized_bytes": 364,
          "normalized_prefix_line_range": [
            1390,
            1394
          ],
          "r83_audit2_prefix_line_range": [
            1392,
            1396
          ]
        },
        {
          "name": "readRecords",
          "kind": "def",
          "range": [
            40,
            46
          ],
          "declaration_line": 40,
          "sha256": "3a4b39320d1328fe5e46c4c63463bebeb6ca4d9d4c50c11d35429b6b1ab00808",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.internalInputs",
            "YulangClosure.SourceInternalContextR55.unique"
          ],
          "type_contract": "def readRecords (s : Source S T) (u : Use Nat (Key S T))\n    (receiving target : Key S T) (c : Choice s u receiving target) : Option (Records S T)",
          "normalized_sha256": "3b15d19e2a68d2b44d4a006df02302a11e8ea29e0759bd029a8c7dde4ecdd29d",
          "normalized_bytes": 542,
          "normalized_prefix_line_range": [
            1396,
            1402
          ],
          "r83_audit2_prefix_line_range": [
            1398,
            1404
          ],
          "normalization_index": 4
        },
        {
          "name": "PrimitiveRecords",
          "kind": "def",
          "range": [
            53,
            81
          ],
          "declaration_line": 53,
          "sha256": "9fe10e643756f5adc5f2dde61cac6375e81e4bf2966d24846e7cf449192b18c9",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.sourceLambda",
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.lambdaFact",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.routeFact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.construction",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.internalInputs",
            "YulangClosure.SourceInternalContextR55.permission",
            "YulangClosure.SourceInternalContextR55.receipt",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "def PrimitiveRecords (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T) : Prop",
          "normalized_sha256": "9fe10e643756f5adc5f2dde61cac6375e81e4bf2966d24846e7cf449192b18c9",
          "normalized_bytes": 2109,
          "normalized_prefix_line_range": [
            1404,
            1432
          ],
          "r83_audit2_prefix_line_range": [
            1406,
            1434
          ]
        },
        {
          "name": "@86",
          "kind": "instance",
          "range": [
            85,
            91
          ],
          "declaration_line": 86,
          "sha256": "831ec8e9b4f2ced3295d2f08004bcd1109c0440fb7d3b6389a2bf73fa6374e67",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "set_option synthInstance.maxSize 512 in\ninstance (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T) :\n    Decidable (PrimitiveRecords s inventory u receiving target c d annotation row)",
          "normalized_sha256": "831ec8e9b4f2ced3295d2f08004bcd1109c0440fb7d3b6389a2bf73fa6374e67",
          "normalized_bytes": 374,
          "normalized_prefix_line_range": [
            1434,
            1440
          ],
          "r83_audit2_prefix_line_range": [
            1436,
            1442
          ]
        },
        {
          "name": "primitive_records_derive_fields",
          "kind": "theorem",
          "range": [
            95,
            128
          ],
          "declaration_line": 95,
          "sha256": "135a656b0f023f811fdb770550a1ae3898d8bea07fbf950dfe20cc21cebc2fe1",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Role",
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ConstructedSourceIncidenceR81.projected",
            "YulangClosure.ConstructedSourceIncidenceR81.request",
            "YulangClosure.InternalPermissionIncidenceR45.Identity",
            "YulangClosure.InternalPermissionIncidenceR45.Kind",
            "YulangClosure.InternalPermissionIncidenceR45.OwnerReads",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.choice_applies_r66",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "theorem primitive_records_derive_fields (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)\n    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :\n    InternalPermissionIncidenceR45.OwnerReads\n      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)\n      (request u receiving target c annotation row) (projected c d) ∧\n    InternalPermissionIncidenceR45.Identity\n      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)\n      (request u receiving target c annotation row) (projected c d) ∧\n    s.parameterRecipes[(projected c d).formal.recipe]? = some (projected c d).formal.parameter",
          "normalized_sha256": "135a656b0f023f811fdb770550a1ae3898d8bea07fbf950dfe20cc21cebc2fe1",
          "normalized_bytes": 2101,
          "normalized_prefix_line_range": [
            1442,
            1475
          ],
          "r83_audit2_prefix_line_range": [
            1444,
            1477
          ]
        },
        {
          "name": "primitive_records_derive_source_probe",
          "kind": "theorem",
          "range": [
            132,
            211
          ],
          "declaration_line": 132,
          "sha256": "73d82f02e93824c30a7da18312b70160f0455ab0116b347624bc928200c4c6a8",
          "references": [
            "YulangClosure.ComputationPermissionEntryR39.Permission",
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ConstructedSourceIncidenceR81.projected",
            "YulangClosure.ConstructedSourceIncidenceR81.request",
            "YulangClosure.InternalPermissionIncidenceR45.Construction",
            "YulangClosure.InternalPermissionIncidenceR45.Receipt",
            "YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection",
            "YulangClosure.OccurrenceQualifiedConsumerR66.sourceProbe",
            "YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs",
            "YulangClosure.ProviderNativeContextR57.Fact",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.ProviderNativeContextR57.unique",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.choice_applies_r66",
            "YulangClosure.SourceInternalContextR55.Use",
            "YulangClosure.SourceInternalContextR55.construction",
            "YulangClosure.SourceInternalContextR55.internalInputs",
            "YulangClosure.SourceInternalContextR55.permission",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.receipt",
            "YulangClosure.SourceInternalContextR55.unique",
            "YulangClosure.SourceInternalContextR55.use"
          ],
          "type_contract": "theorem primitive_records_derive_source_probe (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)\n    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :\n    OccurrenceQualifiedConsumerR66.sourceProbe s inventory\n      (request u receiving target c annotation row) = some (projected c d)",
          "normalized_sha256": "74a0596b653127494c6f4f79f30d0eb02edd6bea563a9887bf2cf22d1f90e711",
          "normalized_bytes": 6576,
          "normalized_prefix_line_range": [
            1477,
            1556
          ],
          "r83_audit2_prefix_line_range": [
            1479,
            1558
          ],
          "normalization_index": 5
        },
        {
          "name": "assemble",
          "kind": "def",
          "range": [
            214,
            222
          ],
          "declaration_line": 214,
          "sha256": "f88a4beb30ba3753512f333f4389acbb4d4f59060c28346369e4a721074e4dc5",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_fields",
            "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
            "YulangClosure.ConstructedSourceIncidenceR81.projected",
            "YulangClosure.ConstructedSourceIncidenceR81.request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Incidence",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def assemble (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)\n    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :\n    OccurrenceQualifiedConsumerR66.Incidence s inventory (request u receiving target c annotation row)",
          "normalized_sha256": "f88a4beb30ba3753512f333f4389acbb4d4f59060c28346369e4a721074e4dc5",
          "normalized_bytes": 656,
          "normalized_prefix_line_range": [
            1558,
            1566
          ],
          "r83_audit2_prefix_line_range": [
            1560,
            1568
          ]
        },
        {
          "name": "Constructed",
          "kind": "structure",
          "range": [
            224,
            229
          ],
          "declaration_line": 224,
          "sha256": "621d4bfa97ea154c6045e1ebdff9a8e2e4bb2dd9f0c6f2c6db1cfc6a24c83924",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ConstructedSourceIncidenceR81.request",
            "YulangClosure.OccurrenceQualifiedConsumerR66.Incidence",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.AlignedChoice",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "structure Constructed (s : Source S T) (inventory : Inventory S T)\n    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))\n    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T) where\n  aligned : AlignedChoice s source calls u receiving target\n  incidence : OccurrenceQualifiedConsumerR66.Incidence s inventory\n    (request u receiving target aligned.choice annotation row)",
          "normalized_sha256": "621d4bfa97ea154c6045e1ebdff9a8e2e4bb2dd9f0c6f2c6db1cfc6a24c83924",
          "normalized_bytes": 410,
          "normalized_prefix_line_range": [
            1568,
            1573
          ],
          "r83_audit2_prefix_line_range": [
            1570,
            1575
          ]
        },
        {
          "name": "construct",
          "kind": "def",
          "range": [
            233,
            241
          ],
          "declaration_line": 233,
          "sha256": "cd4db051dc3553a92182f6a299af97d63fc9538028e152d796a3c7e00c90c3a4",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Constructed",
            "YulangClosure.ConstructedSourceIncidenceR81.Inventory",
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.Source",
            "YulangClosure.ConstructedSourceIncidenceR81.assemble",
            "YulangClosure.ConstructedSourceIncidenceR81.readRecords",
            "YulangClosure.ProviderNativeContextR57.Key",
            "YulangClosure.ProviderNativeContextR57.row",
            "YulangClosure.SourceInternalChoiceR77.OwnerSource",
            "YulangClosure.SourceInternalChoiceR77.SourceCall",
            "YulangClosure.SourceInternalChoiceR77.constructAligned",
            "YulangClosure.SourceInternalContextR55.Use"
          ],
          "type_contract": "def construct (s : Source S T) (inventory : Inventory S T)\n    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))\n    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T) :\n    Option (Constructed s inventory source calls u receiving target annotation row)",
          "normalized_sha256": "cd4db051dc3553a92182f6a299af97d63fc9538028e152d796a3c7e00c90c3a4",
          "normalized_bytes": 643,
          "normalized_prefix_line_range": [
            1575,
            1583
          ],
          "r83_audit2_prefix_line_range": [
            1577,
            1585
          ]
        },
        {
          "name": "fixture",
          "kind": "abbrev",
          "range": [
            299,
            299
          ],
          "declaration_line": 299,
          "sha256": "cdb5cb9714dbe085ac4fa23e8dc362f283a88106b08e2ea1c55ec9d4284f2f7d",
          "references": [
            "YulangClosure.SourceInternalChoiceR77.fixture"
          ],
          "type_contract": "abbrev fixture := SourceInternalChoiceR77.fixture",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "cdb5cb9714dbe085ac4fa23e8dc362f283a88106b08e2ea1c55ec9d4284f2f7d",
          "normalized_bytes": 50,
          "normalized_prefix_line_range": [
            1585,
            1585
          ],
          "r83_audit2_prefix_line_range": [
            1587,
            1587
          ]
        },
        {
          "name": "fixtureInventory",
          "kind": "abbrev",
          "range": [
            300,
            300
          ],
          "declaration_line": 300,
          "sha256": "50950c19385381cd0fb4ab71d16c5b8caadcfac211a4e73e1cc5f014bedb9bd0",
          "references": [
            "YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureInventory"
          ],
          "type_contract": "abbrev fixtureInventory := OccurrenceQualifiedFactReadersR65.fixtureInventory",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "50950c19385381cd0fb4ab71d16c5b8caadcfac211a4e73e1cc5f014bedb9bd0",
          "normalized_bytes": 78,
          "normalized_prefix_line_range": [
            1587,
            1587
          ],
          "r83_audit2_prefix_line_range": [
            1589,
            1589
          ]
        },
        {
          "name": "fixtureSource",
          "kind": "abbrev",
          "range": [
            301,
            301
          ],
          "declaration_line": 301,
          "sha256": "b9eca655dda4156051e32fc1ca14fa44d7aa0938bbb217026b011fa18930ba33",
          "references": [
            "YulangClosure.SourceInternalChoiceR77.fixtureOwnerSource"
          ],
          "type_contract": "abbrev fixtureSource := fixtureOwnerSource",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "b9eca655dda4156051e32fc1ca14fa44d7aa0938bbb217026b011fa18930ba33",
          "normalized_bytes": 43,
          "normalized_prefix_line_range": [
            1589,
            1589
          ],
          "r83_audit2_prefix_line_range": [
            1591,
            1591
          ]
        },
        {
          "name": "fixtureCalls",
          "kind": "abbrev",
          "range": [
            302,
            302
          ],
          "declaration_line": 302,
          "sha256": "b902b91b0ab32588a7455a5974ba39f6d2b2b11d0c2e921c8112beba613b5450",
          "references": [
            "YulangClosure.SourceInternalChoiceR77.fixtureCall"
          ],
          "type_contract": "abbrev fixtureCalls := [fixtureCall]",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "b902b91b0ab32588a7455a5974ba39f6d2b2b11d0c2e921c8112beba613b5450",
          "normalized_bytes": 37,
          "normalized_prefix_line_range": [
            1591,
            1591
          ],
          "r83_audit2_prefix_line_range": [
            1593,
            1593
          ]
        },
        {
          "name": "fixtureChoiceWitness",
          "kind": "def",
          "range": [
            307,
            323
          ],
          "declaration_line": 307,
          "sha256": "bbfb28ea90aea0a77e09fa0034895eebd9fd61c32d19009e22a8d7c2e5abf8a0",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ProviderNativeContextR57.fixtureConstruction",
            "YulangClosure.ProviderNativeContextR57.fixtureFormal",
            "YulangClosure.ProviderNativeContextR57.fixturePlan",
            "YulangClosure.ProviderNativeContextR57.fixtureReceipt",
            "YulangClosure.SourceInternalChoiceR77.Choice",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse",
            "YulangClosure.SourceInternalContextR55.formal",
            "YulangClosure.SourceInternalContextR55.plan",
            "YulangClosure.SourceInternalContextR55.receipt"
          ],
          "type_contract": "def fixtureChoiceWitness : Choice fixture SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)",
          "normalized_sha256": "bbfb28ea90aea0a77e09fa0034895eebd9fd61c32d19009e22a8d7c2e5abf8a0",
          "normalized_bytes": 627,
          "normalized_prefix_line_range": [
            1593,
            1609
          ],
          "r83_audit2_prefix_line_range": [
            1595,
            1611
          ]
        },
        {
          "name": "fixtureAlignedWitness",
          "kind": "def",
          "range": [
            325,
            340
          ],
          "declaration_line": 325,
          "sha256": "3654551508b97135d25fd220ea1d847486e0da9755bd4e33e931e2e4d02f807f",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureCalls",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureSource",
            "YulangClosure.ProviderNativeContextR57.fixturePlan",
            "YulangClosure.SourceInternalChoiceR77.AlignedChoice",
            "YulangClosure.SourceInternalChoiceR77.fixtureCall",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "def fixtureAlignedWitness : AlignedChoice fixture fixtureSource fixtureCalls\n    SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)",
          "normalized_sha256": "3654551508b97135d25fd220ea1d847486e0da9755bd4e33e931e2e4d02f807f",
          "normalized_bytes": 565,
          "normalized_prefix_line_range": [
            1611,
            1626
          ],
          "r83_audit2_prefix_line_range": [
            1613,
            1628
          ]
        },
        {
          "name": "finite_aligned_reader",
          "kind": "theorem",
          "range": [
            342,
            344
          ],
          "declaration_line": 342,
          "sha256": "16e7c2a9b6ede02f7ab0f34e8e540f41e34633def8f7be506464312045b483c6",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureAlignedWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureCalls",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureSource",
            "YulangClosure.SourceInternalChoiceR77.constructAligned",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "theorem finite_aligned_reader :\n    constructAligned fixture fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse\n      (.source 10) (.source 1) = some fixtureAlignedWitness",
          "normalized_sha256": "16e7c2a9b6ede02f7ab0f34e8e540f41e34633def8f7be506464312045b483c6",
          "normalized_bytes": 193,
          "normalized_prefix_line_range": [
            1628,
            1630
          ],
          "r83_audit2_prefix_line_range": [
            1630,
            1632
          ]
        },
        {
          "name": "fixtureRecords",
          "kind": "def",
          "range": [
            346,
            347
          ],
          "declaration_line": 346,
          "sha256": "105fc980a5039f94ac7f194c2e212bb5afd019daad8f1b1a393e9651f5f4b2b7",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Records",
            "YulangClosure.ProviderNativeContextR57.fixturePermission"
          ],
          "type_contract": "def fixtureRecords : Records Nat Nat",
          "normalized_sha256": "105fc980a5039f94ac7f194c2e212bb5afd019daad8f1b1a393e9651f5f4b2b7",
          "normalized_bytes": 116,
          "normalized_prefix_line_range": [
            1632,
            1633
          ],
          "r83_audit2_prefix_line_range": [
            1634,
            1635
          ]
        },
        {
          "name": "finite_native_reader",
          "kind": "theorem",
          "range": [
            349,
            351
          ],
          "declaration_line": 349,
          "sha256": "7769df5736fc8d73956ad7e3093a7206c9ba331ae5c2a0fcd7d1c4bf20bcca85",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.readRecords",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "theorem finite_native_reader :\n    readRecords fixture SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)\n      fixtureChoiceWitness = some fixtureRecords",
          "normalized_sha256": "7769df5736fc8d73956ad7e3093a7206c9ba331ae5c2a0fcd7d1c4bf20bcca85",
          "normalized_bytes": 174,
          "normalized_prefix_line_range": [
            1635,
            1637
          ],
          "r83_audit2_prefix_line_range": [
            1637,
            1639
          ]
        },
        {
          "name": "finite_primitive_records",
          "kind": "theorem",
          "range": [
            353,
            355
          ],
          "declaration_line": 353,
          "sha256": "8b92079b4264fe31d82d1b7b73faaa2e12f4324d0b88e4ba097813135f7ab8ff",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureInventory",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureRecords",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "theorem finite_primitive_records :\n    PrimitiveRecords fixture fixtureInventory SourceInternalChoiceR77.fixtureUse\n      (.source 10) (.source 1) fixtureChoiceWitness fixtureRecords (.source 6) (.source 5)",
          "normalized_sha256": "8b92079b4264fe31d82d1b7b73faaa2e12f4324d0b88e4ba097813135f7ab8ff",
          "normalized_bytes": 220,
          "normalized_prefix_line_range": [
            1639,
            1641
          ],
          "r83_audit2_prefix_line_range": [
            1641,
            1643
          ]
        },
        {
          "name": "fixtureOutput",
          "kind": "def",
          "range": [
            359,
            363
          ],
          "declaration_line": 359,
          "sha256": "d2eb61aefc4523b71af078b572ff382a2da2585f4c4cdfcf6e8b231400ce3fe4",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.Constructed",
            "YulangClosure.ConstructedSourceIncidenceR81.assemble",
            "YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records",
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureAlignedWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureCalls",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureInventory",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureSource",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "def fixtureOutput : Constructed fixture fixtureInventory fixtureSource fixtureCalls\n    SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)",
          "normalized_sha256": "d2eb61aefc4523b71af078b572ff382a2da2585f4c4cdfcf6e8b231400ce3fe4",
          "normalized_bytes": 395,
          "normalized_prefix_line_range": [
            1643,
            1647
          ],
          "r83_audit2_prefix_line_range": [
            1645,
            1649
          ]
        },
        {
          "name": "fixtureResult",
          "kind": "def",
          "range": [
            365,
            366
          ],
          "declaration_line": 365,
          "sha256": "5f7034dd5f4f14f668b7c697868f1e6aad635ac872e5ff971b450d60e3619b31",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.construct",
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureCalls",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureInventory",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureSource",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "def fixtureResult := construct fixture fixtureInventory fixtureSource fixtureCalls\n  SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)",
          "result_type": "inferred; exact defining expression retained; prefix #check required",
          "normalized_sha256": "5f7034dd5f4f14f668b7c697868f1e6aad635ac872e5ff971b450d60e3619b31",
          "normalized_bytes": 169,
          "normalized_prefix_line_range": [
            1649,
            1650
          ],
          "r83_audit2_prefix_line_range": [
            1651,
            1652
          ]
        },
        {
          "name": "finite_constructs_output",
          "kind": "theorem",
          "range": [
            368,
            387
          ],
          "declaration_line": 368,
          "sha256": "805773d4a7b05478ee27c680853b8c32ffc82ae8e93d13cb20b06fc0f0b86046",
          "references": [
            "YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.assemble",
            "YulangClosure.ConstructedSourceIncidenceR81.construct",
            "YulangClosure.ConstructedSourceIncidenceR81.finite_aligned_reader",
            "YulangClosure.ConstructedSourceIncidenceR81.finite_native_reader",
            "YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records",
            "YulangClosure.ConstructedSourceIncidenceR81.fixture",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureAlignedWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureInventory",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureOutput",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureRecords",
            "YulangClosure.ConstructedSourceIncidenceR81.fixtureResult",
            "YulangClosure.ConstructedSourceIncidenceR81.readRecords",
            "YulangClosure.SourceInternalChoiceR77.fixtureUse"
          ],
          "type_contract": "theorem finite_constructs_output : fixtureResult = some fixtureOutput",
          "normalized_sha256": "805773d4a7b05478ee27c680853b8c32ffc82ae8e93d13cb20b06fc0f0b86046",
          "normalized_bytes": 1209,
          "normalized_prefix_line_range": [
            1652,
            1671
          ],
          "r83_audit2_prefix_line_range": [
            1654,
            1673
          ]
        }
      ]
    },
    {
      "module": "YulangClosure.DistinctSourceEmissionRootR75",
      "path": "notes/theory/lean/YulangClosure/DistinctSourceEmissionRootR75.lean",
      "sha256": "e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821",
      "namespace": "YulangClosure.DistinctSourceEmissionRootR75",
      "opens": [
        "CurrentEmissionOwnershipR47"
      ],
      "context_range": [
        17,
        17
      ],
      "context": "variable {Artifact Id Fact : Type}\n",
      "declarations": [
        {
          "name": "IsValue",
          "kind": "def",
          "range": [
            19,
            21
          ],
          "declaration_line": 19,
          "sha256": "8ea22ed9b7966b36ffe18b3d99766e15a5dcf4e09927980f049e7477d15d1701",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint"
          ],
          "type_contract": "def IsValue : Endpoint Id → Prop\n  | .valueRow _ | .valueAtom _ => True\n  | .effectRow _ | .effectAtom _ => False",
          "normalized_sha256": "8ea22ed9b7966b36ffe18b3d99766e15a5dcf4e09927980f049e7477d15d1701",
          "normalized_bytes": 116,
          "normalized_prefix_line_range": [
            1677,
            1679
          ],
          "r83_audit2_prefix_line_range": [
            1679,
            1681
          ]
        },
        {
          "name": "IsEffect",
          "kind": "def",
          "range": [
            23,
            25
          ],
          "declaration_line": 23,
          "sha256": "dea779efdc00cef360748250ccc9f27b69819c875d764319b0bbd019b3d3ef47",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint"
          ],
          "type_contract": "def IsEffect : Endpoint Id → Prop\n  | .effectRow _ | .effectAtom _ => True\n  | .valueRow _ | .valueAtom _ => False",
          "normalized_sha256": "dea779efdc00cef360748250ccc9f27b69819c875d764319b0bbd019b3d3ef47",
          "normalized_bytes": 117,
          "normalized_prefix_line_range": [
            1681,
            1683
          ],
          "r83_audit2_prefix_line_range": [
            1683,
            1685
          ]
        },
        {
          "name": "ValuePair",
          "kind": "def",
          "range": [
            27,
            28
          ],
          "declaration_line": 27,
          "sha256": "464218c15d3be81b9431d169886dfe91bebcac0060a8a9b20d916cd71b6313e5",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.DistinctSourceEmissionRootR75.IsValue"
          ],
          "type_contract": "def ValuePair (pair : Endpoint Id × Endpoint Id) : Prop",
          "normalized_sha256": "464218c15d3be81b9431d169886dfe91bebcac0060a8a9b20d916cd71b6313e5",
          "normalized_bytes": 96,
          "normalized_prefix_line_range": [
            1685,
            1686
          ],
          "r83_audit2_prefix_line_range": [
            1687,
            1688
          ]
        },
        {
          "name": "EffectPair",
          "kind": "def",
          "range": [
            30,
            31
          ],
          "declaration_line": 30,
          "sha256": "6efd68fb9dbff1ce467405ff09bb31f16e03d9d67a726ae587420a8ddcd877f6",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.DistinctSourceEmissionRootR75.IsEffect"
          ],
          "type_contract": "def EffectPair (pair : Endpoint Id × Endpoint Id) : Prop",
          "normalized_sha256": "6efd68fb9dbff1ce467405ff09bb31f16e03d9d67a726ae587420a8ddcd877f6",
          "normalized_bytes": 99,
          "normalized_prefix_line_range": [
            1688,
            1689
          ],
          "r83_audit2_prefix_line_range": [
            1690,
            1691
          ]
        },
        {
          "name": "value_effect_disjoint",
          "kind": "theorem",
          "range": [
            33,
            35
          ],
          "declaration_line": 33,
          "sha256": "4311c4d1b3e407e64e24b51e819ad93f7a14a9f1a283d5fbf11dbd70e076a1cf",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.DistinctSourceEmissionRootR75.IsEffect",
            "YulangClosure.DistinctSourceEmissionRootR75.IsValue"
          ],
          "type_contract": "theorem value_effect_disjoint (v e : Endpoint Id)\n    (value : IsValue v) (effect : IsEffect e) : v ≠ e",
          "normalized_sha256": "4311c4d1b3e407e64e24b51e819ad93f7a14a9f1a283d5fbf11dbd70e076a1cf",
          "normalized_bytes": 167,
          "normalized_prefix_line_range": [
            1691,
            1693
          ],
          "r83_audit2_prefix_line_range": [
            1693,
            1695
          ]
        },
        {
          "name": "typed_relation_ids_distinct",
          "kind": "theorem",
          "range": [
            39,
            50
          ],
          "declaration_line": 39,
          "sha256": "84a63b1f74375baa7d6cb6666acbb44898d1f4319719f4697867bd7167157519",
          "references": [
            "YulangClosure.CurrentEmissionOwnershipR47.Endpoint",
            "YulangClosure.DistinctSourceEmissionRootR75.EffectPair",
            "YulangClosure.DistinctSourceEmissionRootR75.ValuePair",
            "YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint"
          ],
          "type_contract": "theorem typed_relation_ids_distinct\n    (read : Nat → Option (Endpoint Id × Endpoint Id))\n    (source emission : Nat) (sourcePair emissionPair : Endpoint Id × Endpoint Id)\n    (sourceRead : read source = some sourcePair)\n    (emissionRead : read emission = some emissionPair)\n    (sourceTyped : ValuePair sourcePair) (emissionTyped : EffectPair emissionPair) :\n    source ≠ emission",
          "normalized_sha256": "84a63b1f74375baa7d6cb6666acbb44898d1f4319719f4697867bd7167157519",
          "normalized_bytes": 638,
          "normalized_prefix_line_range": [
            1695,
            1706
          ],
          "r83_audit2_prefix_line_range": [
            1697,
            1708
          ]
        }
      ]
    }
  ],
  "normalizations": [
    {
      "declaration": "YulangClosure.SourceInternalChoiceR77.visit",
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_range": [
        25,
        34
      ],
      "source_file_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "original_declaration_sha256": "07a8da70156115676aa6d29761920ea4a44e28399c3ea5f136b8634aa95e28fd",
      "normalized_declaration_sha256": "d96bdc1043e8b39b5630af5f513bc8ae3ca6598b31e87779c3d1bd273f9414fd",
      "original_source": "def visit (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    Except Failure (Option (Origin S T)) :=\n  match s.formals[c.registration]? with\n  | none => .ok none\n  | some f =>\n    if f.role = .computation ∧ f.owner = target then\n      match unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes with\n      | none => .error (.recipe c.registration)\n      | some recipe => .ok (if recipe.rootComponent = component then some c else none)\n    else .ok none\n",
      "normalized_source": "def visit (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    Except Failure (Option (Origin S T)) :=\n  match s.formals[c.registration]? with\n  | none => .ok none\n  | some f =>\n    if f.role = .computation ∧ f.owner = target then\n      match YulangClosure.SourceInternalContextR55.unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes with\n      | none => .error (.recipe c.registration)\n      | some recipe => .ok (if recipe.rootComponent = component then some c else none)\n    else .ok none\n",
      "token_changes": [
        {
          "offset": 267,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 7,
          "column": 13,
          "source_line": 31
        }
      ],
      "r83_audit2_prefix_line_range": [
        1073,
        1082
      ],
      "normalized_prefix_line_range": [
        1072,
        1081
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    },
    {
      "declaration": "YulangClosure.SourceInternalChoiceR77.visit_agrees",
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_range": [
        58,
        73
      ],
      "source_file_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "original_declaration_sha256": "23674b35d203c7d2155fb4fb0d4f3d7d9ffa308e184d526ee97ab80f62bac35a",
      "normalized_declaration_sha256": "50ca23a957d3587c6d22a5384cd3f01d83a990e340cd0f09a19f69d0544b07ba",
      "original_source": "theorem visit_agrees (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    (visit s target component c).toOption =\n      (match s.formals[c.registration]? with\n      | none => some none\n      | some f => if f.role = .computation ∧ f.owner = target then do\n          let recipe ← unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes\n          some (if recipe.rootComponent = component then some c else none)\n        else some none) := by\n  unfold visit\n  cases hf : s.formals[c.registration]? with\n  | none => rfl\n  | some f =>\n    by_cases eligible : f.role = .computation ∧ f.owner = target\n    · simp only [eligible]\n      cases hr : unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes <;> rfl\n    · simp [eligible, Except.toOption]\n",
      "normalized_source": "theorem visit_agrees (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :\n    (visit s target component c).toOption =\n      (match s.formals[c.registration]? with\n      | none => some none\n      | some f => if f.role = .computation ∧ f.owner = target then do\n          let recipe ← YulangClosure.SourceInternalContextR55.unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes\n          some (if recipe.rootComponent = component then some c else none)\n        else some none) := by\n  unfold visit\n  cases hf : s.formals[c.registration]? with\n  | none => rfl\n  | some f =>\n    by_cases eligible : f.role = .computation ∧ f.owner = target\n    · simp only [eligible]\n      cases hr : YulangClosure.SourceInternalContextR55.unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes <;> rfl\n    · simp [eligible, Except.toOption]\n",
      "token_changes": [
        {
          "offset": 302,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 6,
          "column": 24,
          "source_line": 63
        },
        {
          "offset": 686,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 15,
          "column": 18,
          "source_line": 72
        }
      ],
      "r83_audit2_prefix_line_range": [
        1103,
        1118
      ],
      "normalized_prefix_line_range": [
        1102,
        1117
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    },
    {
      "declaration": "YulangClosure.SourceInternalChoiceR77.ordered_selection_agrees",
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_range": [
        117,
        147
      ],
      "source_file_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "original_declaration_sha256": "4690312cdec1e9ee59fab6a79037218d3bed8ff0d221e8452e94e58225857371",
      "normalized_declaration_sha256": "1b8139911c1965e150076d453a88cb1c3f3bc3809817dc1fd09da0af25f775bb",
      "original_source": "theorem ordered_selection_agrees (s : Source S T) (target : Key S T) (component : Nat)\n    (c : Origin S T) (accepted : orderedSelection s target component = .ok c) :\n    OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c := by\n  unfold orderedSelection at accepted\n  cases hw : walk s target component s.constructions [] with\n  | error err => simp [hw] at accepted\n  | ok choices =>\n    cases choices with\n    | nil => simp [hw] at accepted\n    | cons chosen rest =>\n      cases rest with\n      | cons extra others => simp [hw] at accepted\n      | nil =>\n        have same : chosen = c := by simpa [hw] using accepted\n        subst chosen\n        obtain ⟨rows, read, equal⟩ := walk_accounts_for_all s target component s.constructions [] [c] hw\n        have rowMatches : rows.filterMap id = [c] := by simpa using equal\n        have nativeRead : s.constructions.mapM (fun c =>\n            match s.formals[c.registration]? with\n            | none => some none\n            | some f => if f.role = .computation ∧ f.owner = target then do\n                let recipe ← unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes\n                some (if recipe.rootComponent = component then some c else none)\n              else some none) = some rows := by\n          simpa only [visit_agrees] using read\n        unfold OccurrenceQualifiedConsumerR66.ownerSelection\n        rw [nativeRead]\n        change (match rows.filterMap id with\n          | [chosen] => some chosen\n          | _ => none) = some c\n        rw [rowMatches]\n",
      "normalized_source": "theorem ordered_selection_agrees (s : Source S T) (target : Key S T) (component : Nat)\n    (c : Origin S T) (accepted : orderedSelection s target component = .ok c) :\n    OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c := by\n  unfold orderedSelection at accepted\n  cases hw : walk s target component s.constructions [] with\n  | error err => simp [hw] at accepted\n  | ok choices =>\n    cases choices with\n    | nil => simp [hw] at accepted\n    | cons chosen rest =>\n      cases rest with\n      | cons extra others => simp [hw] at accepted\n      | nil =>\n        have same : chosen = c := by simpa [hw] using accepted\n        subst chosen\n        obtain ⟨rows, read, equal⟩ := walk_accounts_for_all s target component s.constructions [] [c] hw\n        have rowMatches : rows.filterMap id = [c] := by simpa using equal\n        have nativeRead : s.constructions.mapM (fun c =>\n            match s.formals[c.registration]? with\n            | none => some none\n            | some f => if f.role = .computation ∧ f.owner = target then do\n                let recipe ← YulangClosure.SourceInternalContextR55.unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes\n                some (if recipe.rootComponent = component then some c else none)\n              else some none) = some rows := by\n          simpa only [visit_agrees] using read\n        unfold OccurrenceQualifiedConsumerR66.ownerSelection\n        rw [nativeRead]\n        change (match rows.filterMap id with\n          | [chosen] => some chosen\n          | _ => none) = some c\n        rw [rowMatches]\n",
      "token_changes": [
        {
          "offset": 1086,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 22,
          "column": 30,
          "source_line": 138
        }
      ],
      "r83_audit2_prefix_line_range": [
        1158,
        1188
      ],
      "normalized_prefix_line_range": [
        1157,
        1187
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    },
    {
      "declaration": "YulangClosure.SourceInternalChoiceR77.choice_three_premises",
      "path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_range": [
        217,
        223
      ],
      "source_file_sha256": "0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682",
      "original_declaration_sha256": "ef4dc5957c8207a6a48d3f78689405e75892d22a83d9831523c4672e7c81cedd",
      "normalized_declaration_sha256": "26bbb05f4a9e0bdc1673e702d27491e14a5be2eded8d40e0bdd6d7335094d8b3",
      "original_source": "theorem choice_three_premises (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) :\n    (internalInputs s).plan (use u) = some (SourceInternalContextR55.plan c.plan) ∧\n    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧\n    s.parameterRecipes[c.formal.recipePosition]? = some c.formal.parameter := by\n  refine ⟨?_, ordered_selection_agrees s target c.plan.targetRootComponent c.origin c.selected, c.parameter⟩\n  simp [internalInputs, unique, c.plans]\n",
      "normalized_source": "theorem choice_three_premises (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) :\n    (internalInputs s).plan (use u) = some (SourceInternalContextR55.plan c.plan) ∧\n    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧\n    s.parameterRecipes[c.formal.recipePosition]? = some c.formal.parameter := by\n  refine ⟨?_, ordered_selection_agrees s target c.plan.targetRootComponent c.origin c.selected, c.parameter⟩\n  simp [internalInputs, YulangClosure.SourceInternalContextR55.unique, c.plans]\n",
      "token_changes": [
        {
          "offset": 542,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 7,
          "column": 25,
          "source_line": 223
        }
      ],
      "r83_audit2_prefix_line_range": [
        1240,
        1246
      ],
      "normalized_prefix_line_range": [
        1239,
        1245
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    },
    {
      "declaration": "YulangClosure.ConstructedSourceIncidenceR81.readRecords",
      "path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_range": [
        40,
        46
      ],
      "source_file_sha256": "3b9e9ac800dccce633c09bf3d7ed0f59f06e910eb42e3a4858e6588f3985bb37",
      "original_declaration_sha256": "3a4b39320d1328fe5e46c4c63463bebeb6ca4d9d4c50c11d35429b6b1ab00808",
      "normalized_declaration_sha256": "3b15d19e2a68d2b44d4a006df02302a11e8ea29e0759bd029a8c7dde4ecdd29d",
      "original_source": "def readRecords (s : Source S T) (u : Use Nat (Key S T))\n    (receiving target : Key S T) (c : Choice s u receiving target) : Option (Records S T) := do\n  let (_, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n  let p ← unique (fun p => decide (p.registration = c.origin.registration)) s.permissions\n  let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild c.origin.function\n  let fact ← c.receipt.fact\n  pure ⟨p, root, child, fact⟩\n",
      "normalized_source": "def readRecords (s : Source S T) (u : Use Nat (Key S T))\n    (receiving target : Key S T) (c : Choice s u receiving target) : Option (Records S T) := do\n  let (_, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n  let p ← YulangClosure.SourceInternalContextR55.unique (fun p => decide (p.registration = c.origin.registration)) s.permissions\n  let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild c.origin.function\n  let fact ← c.receipt.fact\n  pure ⟨p, root, child, fact⟩\n",
      "token_changes": [
        {
          "offset": 255,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 4,
          "column": 11,
          "source_line": 43
        }
      ],
      "r83_audit2_prefix_line_range": [
        1398,
        1404
      ],
      "normalized_prefix_line_range": [
        1396,
        1402
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    },
    {
      "declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_range": [
        132,
        211
      ],
      "source_file_sha256": "3b9e9ac800dccce633c09bf3d7ed0f59f06e910eb42e3a4858e6588f3985bb37",
      "original_declaration_sha256": "73d82f02e93824c30a7da18312b70160f0455ab0116b347624bc928200c4c6a8",
      "normalized_declaration_sha256": "74a0596b653127494c6f4f79f30d0eb02edd6bea563a9887bf2cf22d1f90e711",
      "original_source": "theorem primitive_records_derive_source_probe (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)\n    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :\n    OccurrenceQualifiedConsumerR66.sourceProbe s inventory\n      (request u receiving target c annotation row) = some (projected c d) := by\n  have premises := choice_applies_r66 s inventory u receiving target c\n  rcases checked with ⟨hf, hsf, hc, hp, hr, hl, hroute, hlam, hchild, hentry,\n    hrecipe, ht, hv, howner, hrole, hformalEntry, hroot, huse, receiptFact,\n    hregistration, hparameter, hformal, hpermissionOwner, hpermissionOccurrence,\n    hscope, hannotation, hrow, hpermissionEntry, hnonempty⟩\n  have constructionRead : unique (fun x : InternalPermissionIncidenceR45.Construction (Key S T) T =>\n      x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).constructions = some (construction c.origin) := by\n    simp [unique, hc]\n  have permissionRead : unique (fun x : ComputationPermissionEntryR39.Permission (Key S T) =>\n      x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).permissions = some (permission d.permission) := by\n    simp [unique, hp]\n  have receiptRead : unique (fun x : InternalPermissionIncidenceR45.Receipt Nat (Key S T) Fact =>\n      x.use == use u)\n      (SourceInternalContextR55.internalInputs s).receipts = some (receipt c.receipt) := by\n    simp [unique, hr]\n  -- Normalize the dependent if's query and use coordinates before rewriting.\n  -- In R80 `rw` built a motive containing the unreduced query Decidable term.\n  change (do\n    let selectedPlan ← (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u)\n    let selected ← OccurrenceQualifiedConsumerR66.ownerSelection s target selectedPlan.targetRootComponent\n    if selected.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, selectedPlan, r, fact, child⟩) = some (projected c d)\n  simp only [premises.1]\n  -- Reduce Option's outer bind explicitly before using global-selection agreement.\n  change (do\n    let selected ← OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent\n    if selected.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  rw [premises.2.1]\n  change (if c.origin.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  rw [if_neg (fun unequal => unequal rfl)]\n  change (do\n    let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n    let origin ← unique (fun x => x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).constructions\n    let p ← unique (fun x => x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).permissions\n    let r ← unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n    let fact ← r.fact\n    let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n    let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n    pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  simp [hf, constructionRead, permissionRead, receiptRead, receipt, receiptFact,\n    hrecipe, construction, hchild, projected]\n",
      "normalized_source": "theorem primitive_records_derive_source_probe (s : Source S T) (inventory : Inventory S T)\n    (u : Use Nat (Key S T)) (receiving target : Key S T)\n    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)\n    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :\n    OccurrenceQualifiedConsumerR66.sourceProbe s inventory\n      (request u receiving target c annotation row) = some (projected c d) := by\n  have premises := choice_applies_r66 s inventory u receiving target c\n  rcases checked with ⟨hf, hsf, hc, hp, hr, hl, hroute, hlam, hchild, hentry,\n    hrecipe, ht, hv, howner, hrole, hformalEntry, hroot, huse, receiptFact,\n    hregistration, hparameter, hformal, hpermissionOwner, hpermissionOccurrence,\n    hscope, hannotation, hrow, hpermissionEntry, hnonempty⟩\n  have constructionRead : YulangClosure.SourceInternalContextR55.unique (fun x : InternalPermissionIncidenceR45.Construction (Key S T) T =>\n      x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).constructions = some (construction c.origin) := by\n    simp [YulangClosure.SourceInternalContextR55.unique, hc]\n  have permissionRead : YulangClosure.SourceInternalContextR55.unique (fun x : ComputationPermissionEntryR39.Permission (Key S T) =>\n      x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).permissions = some (permission d.permission) := by\n    simp [YulangClosure.SourceInternalContextR55.unique, hp]\n  have receiptRead : YulangClosure.SourceInternalContextR55.unique (fun x : InternalPermissionIncidenceR45.Receipt Nat (Key S T) Fact =>\n      x.use == use u)\n      (SourceInternalContextR55.internalInputs s).receipts = some (receipt c.receipt) := by\n    simp [YulangClosure.SourceInternalContextR55.unique, hr]\n  -- Normalize the dependent if's query and use coordinates before rewriting.\n  -- In R80 `rw` built a motive containing the unreduced query Decidable term.\n  change (do\n    let selectedPlan ← (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u)\n    let selected ← OccurrenceQualifiedConsumerR66.ownerSelection s target selectedPlan.targetRootComponent\n    if selected.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← YulangClosure.SourceInternalContextR55.unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, selectedPlan, r, fact, child⟩) = some (projected c d)\n  simp only [premises.1]\n  -- Reduce Option's outer bind explicitly before using global-selection agreement.\n  change (do\n    let selected ← OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent\n    if selected.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← YulangClosure.SourceInternalContextR55.unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  rw [premises.2.1]\n  change (if c.origin.registration ≠ c.origin.registration then none else do\n      let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n      let origin ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).constructions\n      let p ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n        (SourceInternalContextR55.internalInputs s).permissions\n      let r ← YulangClosure.SourceInternalContextR55.unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n      let fact ← r.fact\n      let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n      let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n      pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  rw [if_neg (fun unequal => unequal rfl)]\n  change (do\n    let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration\n    let origin ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).constructions\n    let p ← YulangClosure.SourceInternalContextR55.unique (fun x => x.registration == c.origin.registration)\n      (SourceInternalContextR55.internalInputs s).permissions\n    let r ← YulangClosure.SourceInternalContextR55.unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts\n    let fact ← r.fact\n    let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda\n    let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function\n    pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)\n  simp [hf, constructionRead, permissionRead, receiptRead, receipt, receiptFact,\n    hrecipe, construction, hchild, projected]\n",
      "token_changes": [
        {
          "offset": 848,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 12,
          "column": 27,
          "source_line": 143
        },
        {
          "offset": 1081,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 15,
          "column": 11,
          "source_line": 146
        },
        {
          "offset": 1117,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 16,
          "column": 25,
          "source_line": 147
        },
        {
          "offset": 1345,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 19,
          "column": 11,
          "source_line": 150
        },
        {
          "offset": 1378,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 20,
          "column": 22,
          "source_line": 151
        },
        {
          "offset": 1579,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 23,
          "column": 11,
          "source_line": 154
        },
        {
          "offset": 2166,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 31,
          "column": 20,
          "source_line": 162
        },
        {
          "offset": 2304,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 33,
          "column": 15,
          "source_line": 164
        },
        {
          "offset": 2440,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 35,
          "column": 15,
          "source_line": 166
        },
        {
          "offset": 3256,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 46,
          "column": 20,
          "source_line": 177
        },
        {
          "offset": 3394,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 48,
          "column": 15,
          "source_line": 179
        },
        {
          "offset": 3530,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 50,
          "column": 15,
          "source_line": 181
        },
        {
          "offset": 4148,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 58,
          "column": 20,
          "source_line": 189
        },
        {
          "offset": 4286,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 60,
          "column": 15,
          "source_line": 191
        },
        {
          "offset": 4422,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 62,
          "column": 15,
          "source_line": 193
        },
        {
          "offset": 4995,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 70,
          "column": 18,
          "source_line": 201
        },
        {
          "offset": 5129,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 72,
          "column": 13,
          "source_line": 203
        },
        {
          "offset": 5261,
          "old": "unique",
          "new": "YulangClosure.SourceInternalContextR55.unique",
          "line": 74,
          "column": 13,
          "source_line": 205
        }
      ],
      "r83_audit2_prefix_line_range": [
        1479,
        1558
      ],
      "normalized_prefix_line_range": [
        1477,
        1556
      ],
      "preservation": "Identifier qualification only. R57.unique unfolds directly to R55.unique. Reverse these substitutions to recover exact source; no hypotheses, types, constructors, fields or computation change."
    }
  ],
  "diagnostics": [
    {
      "index": 1,
      "stdin_line": 1246,
      "stdin_column": 24,
      "diagnostic_header": "<stdin>:1246:24: error: Invalid simp theorem: Expected a proposition, but found",
      "source_declaration": "YulangClosure.SourceInternalChoiceR77.choice_three_premises",
      "source_path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_line": 223,
      "source_declaration_range": [
        217,
        223
      ]
    },
    {
      "index": 2,
      "stdin_line": 1244,
      "stdin_column": 78,
      "diagnostic_header": "<stdin>:1244:78: error: unsolved goals",
      "source_declaration": "YulangClosure.SourceInternalChoiceR77.choice_three_premises",
      "source_path": "notes/theory/lean/YulangClosure/SourceInternalChoiceR77.lean",
      "source_line": 221,
      "source_declaration_range": [
        217,
        223
      ]
    },
    {
      "index": 3,
      "stdin_line": 1493,
      "stdin_column": 10,
      "diagnostic_header": "<stdin>:1493:10: error: Invalid simp theorem: Expected a proposition, but found",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 146,
      "source_declaration_range": [
        132,
        211
      ]
    },
    {
      "index": 4,
      "stdin_line": 1493,
      "stdin_column": 4,
      "diagnostic_header": "<stdin>:1493:4: error: `simp` made no progress",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 146,
      "source_declaration_range": [
        132,
        211
      ]
    },
    {
      "index": 5,
      "stdin_line": 1497,
      "stdin_column": 10,
      "diagnostic_header": "<stdin>:1497:10: error: Invalid simp theorem: Expected a proposition, but found",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 150,
      "source_declaration_range": [
        132,
        211
      ]
    },
    {
      "index": 6,
      "stdin_line": 1497,
      "stdin_column": 4,
      "diagnostic_header": "<stdin>:1497:4: error: `simp` made no progress",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 150,
      "source_declaration_range": [
        132,
        211
      ]
    },
    {
      "index": 7,
      "stdin_line": 1501,
      "stdin_column": 10,
      "diagnostic_header": "<stdin>:1501:10: error: Invalid simp theorem: Expected a proposition, but found",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 154,
      "source_declaration_range": [
        132,
        211
      ]
    },
    {
      "index": 8,
      "stdin_line": 1501,
      "stdin_column": 4,
      "diagnostic_header": "<stdin>:1501:4: error: `simp` made no progress",
      "source_declaration": "YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe",
      "source_path": "notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR81.lean",
      "source_line": 154,
      "source_declaration_range": [
        132,
        211
      ]
    }
  ],
  "candidate": {
    "path": "notes/theory/lean/YulangClosure/ConstructedPhysicalRootR84.lean",
    "bytes": 22748,
    "sha256": "1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839",
    "base_path": "notes/theory/lean/YulangClosure/ConstructedPhysicalRootR83.lean",
    "base_sha256": "c96eaa40e4457f78c254bd15f65674a72c653618fcf3381477247a5b833317e6",
    "namespace_old": "YulangClosure.ConstructedPhysicalRootR83",
    "namespace_new": "YulangClosure.ConstructedPhysicalRootR84",
    "token_changes": [
      {
        "offset": 1646,
        "old": "Origin",
        "new": "YulangClosure.ProviderNativeContextR57.Origin",
        "line": 46,
        "column": 12
      },
      {
        "offset": 1860,
        "old": "Origin",
        "new": "YulangClosure.ProviderNativeContextR57.Origin",
        "line": 52,
        "column": 66
      },
      {
        "offset": 2771,
        "old": "unique",
        "new": "YulangClosure.ProviderNativeContextR57.unique",
        "line": 68,
        "column": 11
      },
      {
        "offset": 7745,
        "old": "unique",
        "new": "YulangClosure.ProviderNativeContextR57.unique",
        "line": 145,
        "column": 23
      }
    ],
    "preservation": "Namespace rename plus explicit native unique and Origin identifiers only; all thirteen source theorem signatures unchanged after namespace rename."
  },
  "prefix_body_bytes": 78934,
  "prefix_body_sha256": "ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49",
  "prefix_queries": "set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n#check @YulangClosure.ComputationPermissionEntryR39.Role\n#check @YulangClosure.ComputationPermissionEntryR39.Registration\n#check @YulangClosure.ComputationPermissionEntryR39.SourceExpr\n#check @YulangClosure.ComputationPermissionEntryR39.Inputs\n#check @YulangClosure.ComputationPermissionEntryR39.Permission\n#check @YulangClosure.ComputationPermissionEntryR39.localSource\n#check @YulangClosure.ComputationPermissionEntryR39.sourceLambda\n#check @YulangClosure.InternalPermissionIncidenceR45.UseId\n#check @YulangClosure.InternalPermissionIncidenceR45.Kind\n#check @YulangClosure.InternalPermissionIncidenceR45.Construction\n#check @YulangClosure.InternalPermissionIncidenceR45.Plan\n#check @YulangClosure.InternalPermissionIncidenceR45.Receipt\n#check @YulangClosure.InternalPermissionIncidenceR45.Query\n#check @YulangClosure.InternalPermissionIncidenceR45.Probe\n#check @YulangClosure.InternalPermissionIncidenceR45.Inputs\n#check @YulangClosure.InternalPermissionIncidenceR45.Certificate\n#check @YulangClosure.InternalPermissionIncidenceR45.constructionsFor\n#check @YulangClosure.InternalPermissionIncidenceR45.permissionsFor\n#check @YulangClosure.InternalPermissionIncidenceR45.receiptsFor\n#check @YulangClosure.InternalPermissionIncidenceR45.OwnerReads\n#check @YulangClosure.InternalPermissionIncidenceR45.Identity\n#check @YulangClosure.InternalPermissionIncidenceR45.certificate\n#check @YulangClosure.InternalPermissionIncidenceR45.extract\n#check @YulangClosure.InternalPermissionIncidenceR45.accepted_iff\n#print axioms YulangClosure.InternalPermissionIncidenceR45.accepted_iff\n#check @YulangClosure.InternalPermissionIncidenceR45.accepted_payload\n#print axioms YulangClosure.InternalPermissionIncidenceR45.accepted_payload\n#check @YulangClosure.CurrentEmissionOwnershipR47.RowKey\n#check @YulangClosure.CurrentEmissionOwnershipR47.Endpoint\n#check @YulangClosure.CurrentEmissionOwnershipR47.Polarity\n#check @YulangClosure.CurrentEmissionOwnershipR47.Bound\n#check @YulangClosure.CurrentEmissionOwnershipR47.rowEndpoint\n#check @YulangClosure.CurrentEmissionOwnershipR47.boundPair\n#check @YulangClosure.CurrentEmissionOwnershipR47.Lane\n#check @YulangClosure.CurrentEmissionOwnershipR47.Slot\n#check @YulangClosure.CurrentEmissionOwnershipR47.RowBounds\n#check @YulangClosure.CurrentEmissionOwnershipR47.Admission\n#check @YulangClosure.CurrentEmissionOwnershipR47.Readback\n#check @YulangClosure.CurrentEmissionOwnershipR47.Emission\n#check @YulangClosure.CurrentEmissionOwnershipR47.Inputs\n#check @YulangClosure.CurrentEmissionOwnershipR47.Query\n#check @YulangClosure.CurrentEmissionOwnershipR47.Probe\n#check @YulangClosure.CurrentEmissionOwnershipR47.currentBound\n#check @YulangClosure.CurrentEmissionOwnershipR47.emissionsForSlot\n#check @YulangClosure.CurrentEmissionOwnershipR47.RootMatches\n#check @YulangClosure.SourceInternalContextR55.NativeRole\n#check @YulangClosure.SourceInternalContextR55.Formal\n#check @YulangClosure.SourceInternalContextR55.Expression\n#check @YulangClosure.SourceInternalContextR55.LocalSource\n#check @YulangClosure.SourceInternalContextR55.Permission\n#check @YulangClosure.SourceInternalContextR55.Construction\n#check @YulangClosure.SourceInternalContextR55.Use\n#check @YulangClosure.SourceInternalContextR55.RouteKind\n#check @YulangClosure.SourceInternalContextR55.Receipt\n#check @YulangClosure.SourceInternalContextR55.Plan\n#check @YulangClosure.SourceInternalContextR55.Recipe\n#check @YulangClosure.SourceInternalContextR55.AdmittedFact\n#check @YulangClosure.SourceInternalContextR55.TermView\n#check @YulangClosure.SourceInternalContextR55.Native\n#check @YulangClosure.SourceInternalContextR55.unique\n#check @YulangClosure.SourceInternalContextR55.formal\n#check @YulangClosure.SourceInternalContextR55.expression\n#check @YulangClosure.SourceInternalContextR55.sourceInputs\n#check @YulangClosure.SourceInternalContextR55.permission\n#check @YulangClosure.SourceInternalContextR55.construction\n#check @YulangClosure.SourceInternalContextR55.use\n#check @YulangClosure.SourceInternalContextR55.receipt\n#check @YulangClosure.SourceInternalContextR55.plan\n#check @YulangClosure.SourceInternalContextR55.internalInputs\n#check @YulangClosure.ProviderNativeContextR57.ValueEndpoint\n#check @YulangClosure.ProviderNativeContextR57.EffectEndpoint\n#check @YulangClosure.ProviderNativeContextR57.Key\n#check @YulangClosure.ProviderNativeContextR57.Fact\n#check @YulangClosure.ProviderNativeContextR57.Endpoint\n#check @YulangClosure.ProviderNativeContextR57.endpoint\n#check @YulangClosure.ProviderNativeContextR57.Row\n#check @YulangClosure.ProviderNativeContextR57.Polarity\n#check @YulangClosure.ProviderNativeContextR57.Lane\n#check @YulangClosure.ProviderNativeContextR57.Bound\n#check @YulangClosure.ProviderNativeContextR57.Slot\n#check @YulangClosure.ProviderNativeContextR57.Admission\n#check @YulangClosure.ProviderNativeContextR57.Emission\n#check @YulangClosure.ProviderNativeContextR57.Physical\n#check @YulangClosure.ProviderNativeContextR57.Bounds\n#check @YulangClosure.ProviderNativeContextR57.ValueRow\n#check @YulangClosure.ProviderNativeContextR57.EffectRow\n#check @YulangClosure.ProviderNativeContextR57.Relation\n#check @YulangClosure.ProviderNativeContextR57.Dependency\n#check @YulangClosure.ProviderNativeContextR57.SourceFact\n#check @YulangClosure.ProviderNativeContextR57.Drain\n#check @YulangClosure.ProviderNativeContextR57.Origin\n#check @YulangClosure.ProviderNativeContextR57.ViewOrigin\n#check @YulangClosure.ProviderNativeContextR57.View\n#check @YulangClosure.ProviderNativeContextR57.Operation\n#check @YulangClosure.ProviderNativeContextR57.row\n#check @YulangClosure.ProviderNativeContextR57.polarity\n#check @YulangClosure.ProviderNativeContextR57.lane\n#check @YulangClosure.ProviderNativeContextR57.bound\n#check @YulangClosure.ProviderNativeContextR57.slot\n#check @YulangClosure.ProviderNativeContextR57.admission\n#check @YulangClosure.ProviderNativeContextR57.emission\n#check @YulangClosure.ProviderNativeContextR57.physical\n#check @YulangClosure.ProviderNativeContextR57.valueBounds\n#check @YulangClosure.ProviderNativeContextR57.effectBounds\n#check @YulangClosure.ProviderNativeContextR57.Native\n#check @YulangClosure.ProviderNativeContextR57.unique\n#check @YulangClosure.ProviderNativeContextR57.factRead\n#check @YulangClosure.ProviderNativeContextR57.sourceFact\n#check @YulangClosure.ProviderNativeContextR57.relationRead\n#check @YulangClosure.ProviderNativeContextR57.originRead\n#check @YulangClosure.ProviderNativeContextR57.rootDrain\n#check @YulangClosure.ProviderNativeContextR57.rootTask\n#check @YulangClosure.ProviderNativeContextR57.completed\n#check @YulangClosure.ProviderNativeContextR57.dependencies\n#check @YulangClosure.ProviderNativeContextR57.rootCandidates\n#check @YulangClosure.ProviderNativeContextR57.current\n#check @YulangClosure.ProviderNativeContextR57.fixtureBound\n#check @YulangClosure.ProviderNativeContextR57.fixtureSlot\n#check @YulangClosure.ProviderNativeContextR57.fixtureAdmission\n#check @YulangClosure.ProviderNativeContextR57.fixtureEmission\n#check @YulangClosure.ProviderNativeContextR57.fixtureView\n#check @YulangClosure.ProviderNativeContextR57.fixtureNative\n#check @YulangClosure.ProviderNativeContextR57.fixtureFormal\n#check @YulangClosure.ProviderNativeContextR57.fixtureConstruction\n#check @YulangClosure.ProviderNativeContextR57.fixturePermission\n#check @YulangClosure.ProviderNativeContextR57.fixtureUse\n#check @YulangClosure.ProviderNativeContextR57.fixtureReceipt\n#check @YulangClosure.ProviderNativeContextR57.fixturePlan\n#check @YulangClosure.ProviderNativeContextR57.fixtureInternal\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.FactRow\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.Edge\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.Inventory\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.Read\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.candidates\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.resolve\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.readAt\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.sourceFact\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.routeFact\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.lambdaFact\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.internalInputs\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.rootTask\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.rootCandidates\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.current\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureRoute\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureLambda\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureFirst\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureSecond\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureLambdaEdge\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureInventory\n#check @YulangClosure.OccurrenceQualifiedFactReadersR65.fixtureSource\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.Source\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.Request\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.ownerSelection\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.sourceProbe\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.Incidence\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.rootQuery\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.BeforeAncestry\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.Root\n#check @YulangClosure.OccurrenceQualifiedConsumerR66.source_incidence_checked\n#print axioms YulangClosure.OccurrenceQualifiedConsumerR66.source_incidence_checked\n#check @YulangClosure.SourceInternalChoiceR77.Source\n#check @YulangClosure.SourceInternalChoiceR77.Origin\n#check @YulangClosure.SourceInternalChoiceR77.Failure\n#check @YulangClosure.SourceInternalChoiceR77.visit\n#check @YulangClosure.SourceInternalChoiceR77.walk\n#check @YulangClosure.SourceInternalChoiceR77.orderedSelection\n#check @YulangClosure.SourceInternalChoiceR77.visit_agrees\n#print axioms YulangClosure.SourceInternalChoiceR77.visit_agrees\n#check @YulangClosure.SourceInternalChoiceR77.walk_accounts_for_all\n#print axioms YulangClosure.SourceInternalChoiceR77.walk_accounts_for_all\n#check @YulangClosure.SourceInternalChoiceR77.ordered_selection_agrees\n#print axioms YulangClosure.SourceInternalChoiceR77.ordered_selection_agrees\n#check @YulangClosure.SourceInternalChoiceR77.Choice\n#check @YulangClosure.SourceInternalChoiceR77.construct\n#check @YulangClosure.SourceInternalChoiceR77.choice_three_premises\n#print axioms YulangClosure.SourceInternalChoiceR77.choice_three_premises\n#check @YulangClosure.SourceInternalChoiceR77.choice_applies_r66\n#print axioms YulangClosure.SourceInternalChoiceR77.choice_applies_r66\n#check @YulangClosure.SourceInternalChoiceR77.fixture\n#check @YulangClosure.SourceInternalChoiceR77.fixtureUse\n#check @YulangClosure.SourceInternalChoiceR77.HirForm\n#check @YulangClosure.SourceInternalChoiceR77.HirNode\n#check @YulangClosure.SourceInternalChoiceR77.OwnerSource\n#check @YulangClosure.SourceInternalChoiceR77.SourceCall\n#check @YulangClosure.SourceInternalChoiceR77.peel\n#check @YulangClosure.SourceInternalChoiceR77.alignedCalls\n#check @YulangClosure.SourceInternalChoiceR77.alignedUses\n#check @YulangClosure.SourceInternalChoiceR77.Alignment\n#check @YulangClosure.SourceInternalChoiceR77.AlignedChoice\n#check @YulangClosure.SourceInternalChoiceR77.constructAligned\n#check @YulangClosure.SourceInternalChoiceR77.fixtureOwnerSource\n#check @YulangClosure.SourceInternalChoiceR77.fixtureCall\n#check @YulangClosure.ConstructedSourceIncidenceR81.Source\n#check @YulangClosure.ConstructedSourceIncidenceR81.Inventory\n#check @YulangClosure.ConstructedSourceIncidenceR81.Records\n#check @YulangClosure.ConstructedSourceIncidenceR81.request\n#check @YulangClosure.ConstructedSourceIncidenceR81.projected\n#check @YulangClosure.ConstructedSourceIncidenceR81.readRecords\n#check @YulangClosure.ConstructedSourceIncidenceR81.PrimitiveRecords\n#check @YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_fields\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_fields\n#check @YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe\n#check @YulangClosure.ConstructedSourceIncidenceR81.assemble\n#check @YulangClosure.ConstructedSourceIncidenceR81.Constructed\n#check @YulangClosure.ConstructedSourceIncidenceR81.construct\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixture\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureInventory\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureSource\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureCalls\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureChoiceWitness\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureAlignedWitness\n#check @YulangClosure.ConstructedSourceIncidenceR81.finite_aligned_reader\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.finite_aligned_reader\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureRecords\n#check @YulangClosure.ConstructedSourceIncidenceR81.finite_native_reader\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.finite_native_reader\n#check @YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureOutput\n#check @YulangClosure.ConstructedSourceIncidenceR81.fixtureResult\n#check @YulangClosure.ConstructedSourceIncidenceR81.finite_constructs_output\n#print axioms YulangClosure.ConstructedSourceIncidenceR81.finite_constructs_output\n#check @YulangClosure.DistinctSourceEmissionRootR75.IsValue\n#check @YulangClosure.DistinctSourceEmissionRootR75.IsEffect\n#check @YulangClosure.DistinctSourceEmissionRootR75.ValuePair\n#check @YulangClosure.DistinctSourceEmissionRootR75.EffectPair\n#check @YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint\n#print axioms YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint\n#check @YulangClosure.DistinctSourceEmissionRootR75.typed_relation_ids_distinct\n#print axioms YulangClosure.DistinctSourceEmissionRootR75.typed_relation_ids_distinct\n",
  "full_queries": "set_option pp.universes true\nset_option pp.explicit true\nset_option pp.fullNames true\n#check @YulangClosure.ConstructedPhysicalRootR84.value_endpoint_typed\n#print axioms YulangClosure.ConstructedPhysicalRootR84.value_endpoint_typed\n#check @YulangClosure.ConstructedPhysicalRootR84.effect_endpoint_typed\n#print axioms YulangClosure.ConstructedPhysicalRootR84.effect_endpoint_typed\n#check @YulangClosure.ConstructedPhysicalRootR84.primitive_derive_root_matches\n#print axioms YulangClosure.ConstructedPhysicalRootR84.primitive_derive_root_matches\n#check @YulangClosure.ConstructedPhysicalRootR84.primitive_derive_before_ancestry\n#print axioms YulangClosure.ConstructedPhysicalRootR84.primitive_derive_before_ancestry\n#check @YulangClosure.ConstructedPhysicalRootR84.primitive_distinct_relation_roles\n#print axioms YulangClosure.ConstructedPhysicalRootR84.primitive_distinct_relation_roles\n#check @YulangClosure.ConstructedPhysicalRootR84.constructed_applies_parent\n#print axioms YulangClosure.ConstructedPhysicalRootR84.constructed_applies_parent\n#check @YulangClosure.ConstructedPhysicalRootR84.finite_reads\n#print axioms YulangClosure.ConstructedPhysicalRootR84.finite_reads\n#check @YulangClosure.ConstructedPhysicalRootR84.finite_primitive\n#print axioms YulangClosure.ConstructedPhysicalRootR84.finite_primitive\n#check @YulangClosure.ConstructedPhysicalRootR84.finite_constructs_root\n#print axioms YulangClosure.ConstructedPhysicalRootR84.finite_constructs_root\n#check @YulangClosure.ConstructedPhysicalRootR84.finite_nonempty_mixed_witness\n#print axioms YulangClosure.ConstructedPhysicalRootR84.finite_nonempty_mixed_witness\n#check @YulangClosure.ConstructedPhysicalRootR84.duplicate_stale_and_substituted_rejected\n#print axioms YulangClosure.ConstructedPhysicalRootR84.duplicate_stale_and_substituted_rejected\n#check @YulangClosure.ConstructedPhysicalRootR84.incomplete_foreign_and_wrong_task_rejected\n#print axioms YulangClosure.ConstructedPhysicalRootR84.incomplete_foreign_and_wrong_task_rejected\n#check @YulangClosure.ConstructedPhysicalRootR84.collapsed_roles_and_parameter_substitution_rejected\n#print axioms YulangClosure.ConstructedPhysicalRootR84.collapsed_roles_and_parameter_substitution_rejected\n",
  "candidate_theorems": [
    "YulangClosure.ConstructedPhysicalRootR84.value_endpoint_typed",
    "YulangClosure.ConstructedPhysicalRootR84.effect_endpoint_typed",
    "YulangClosure.ConstructedPhysicalRootR84.primitive_derive_root_matches",
    "YulangClosure.ConstructedPhysicalRootR84.primitive_derive_before_ancestry",
    "YulangClosure.ConstructedPhysicalRootR84.primitive_distinct_relation_roles",
    "YulangClosure.ConstructedPhysicalRootR84.constructed_applies_parent",
    "YulangClosure.ConstructedPhysicalRootR84.finite_reads",
    "YulangClosure.ConstructedPhysicalRootR84.finite_primitive",
    "YulangClosure.ConstructedPhysicalRootR84.finite_constructs_root",
    "YulangClosure.ConstructedPhysicalRootR84.finite_nonempty_mixed_witness",
    "YulangClosure.ConstructedPhysicalRootR84.duplicate_stale_and_substituted_rejected",
    "YulangClosure.ConstructedPhysicalRootR84.incomplete_foreign_and_wrong_task_rejected",
    "YulangClosure.ConstructedPhysicalRootR84.collapsed_roles_and_parameter_substitution_rejected"
  ],
  "invocation_slots": [
    {
      "slot": 1,
      "gate": "Fresh independent review then separately committed/pushed exact authorization",
      "recipe": "normalized_prefix_body + prefix_queries",
      "bytes": 93368,
      "sha256": "e031132b1a5a42f22c5faba355a1af3d8639d0d577de9051e81f403bf465ebb3"
    },
    {
      "slot": 2,
      "gate": "Only after slot 1 fails: one actual diagnostic-directed prefix repair, fresh review and separate authorization",
      "recipe": "assemble exact reviewed declaration_repair_delta and append identical prefix_queries; freeze every changed declaration/body/input hash and byte count after actual diagnostics",
      "bytes": null,
      "sha256": null,
      "status": "PENDING_ACTUAL_DIAGNOSTICS; no runnable/authorized input"
    },
    {
      "slot": 3,
      "gate": "Only after prefix accepted in slot 1 or slot 2: fresh candidate review and separate exact authorization",
      "recipe": "accepted_normalized_prefix_body + import_stripped_candidate + \"\\n\" + full_queries",
      "bytes": 103791,
      "sha256": "5c35dd49b71508fea4755abf680327932099249de1d1f4f5f250ca2d949651f2",
      "hash_validity": "Exact here for frozen slot-1 prefix; any slot-2 change requires a new full-input freeze/hash before authorization"
    },
    {
      "slot": 4,
      "gate": "Only after slot 3 fails: one actual diagnostic-directed full candidate repair, unchanged claims/source pins, fresh review and separate authorization",
      "recipe": "accepted_prefix_body + import_stripped_reviewed_candidate_repair + \"\\n\" + identical full_queries; freeze exact candidate/full-input bytes/hashes after actual diagnostics",
      "bytes": null,
      "sha256": null,
      "status": "PENDING_ACTUAL_DIAGNOSTICS; no runnable/authorized input"
    }
  ]
}
```

## Material failed audit evidence (R83, not R84 acceptance)

```text
<stdin>:1246:24: error: Invalid simp theorem: Expected a proposition, but found
  (x_0 : Type) → (x_0 → Bool) → List x_0 → Option x_0
<stdin>:1244:78: error: unsolved goals
S T : Type
inst✝¹ : DecidableEq S
inst✝ : DecidableEq T
s : Source S T
u : Use Nat (Key S T)
receiving target : Key S T
c : Choice s u receiving target
⊢ ∃ a, unique (fun p => decide (use p.use = use u)) s.plans = some a ∧ plan a = plan c.plan
<stdin>:1246:32: warning: This simp argument is unused:
  c.plans

Hint: Omit it from the simp argument list.
  [apply] simp [internalInputs, unique]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1493:10: error: Invalid simp theorem: Expected a proposition, but found
  (x_0 : Type) → (x_0 → Bool) → List x_0 → Option x_0
<stdin>:1493:4: error: `simp` made no progress
<stdin>:1497:10: error: Invalid simp theorem: Expected a proposition, but found
  (x_0 : Type) → (x_0 → Bool) → List x_0 → Option x_0
<stdin>:1497:4: error: `simp` made no progress
<stdin>:1501:10: error: Invalid simp theorem: Expected a proposition, but found
  (x_0 : Type) → (x_0 → Bool) → List x_0 → Option x_0
<stdin>:1501:4: error: `simp` made no progress
<stdin>:1545:6: warning: `if_neg` has been deprecated: Use `ite_eq_right` instead

Hint: Replace the deprecated name:
  i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲
<stdin>:1673:8: warning: `dif_pos` has been deprecated: Use `dite_eq_left` instead

Hint: Replace the deprecated name:
  d̵i̵f̵_̵p̵o̵s̵d̲i̲t̲e̲_̲e̲q̲_̲l̲e̲f̲t̲
```

All sixteen actual prerequisite axiom reports from the FAILED R83 input follow.
These error-recovered reports do not accept any theorem or certify this R84 map.

```text
'YulangClosure.InternalPermissionIncidenceR45.accepted_iff' depends on axioms: [propext]
'YulangClosure.InternalPermissionIncidenceR45.accepted_payload' depends on axioms: [propext]
'YulangClosure.OccurrenceQualifiedConsumerR66.source_incidence_checked' depends on axioms: [propext]
'YulangClosure.SourceInternalChoiceR77.visit_agrees' depends on axioms: [propext]
'YulangClosure.SourceInternalChoiceR77.walk_accounts_for_all' depends on axioms: [propext, Quot.sound.{u}]
'YulangClosure.SourceInternalChoiceR77.ordered_selection_agrees' depends on axioms: [propext, Quot.sound.{u}]
'YulangClosure.SourceInternalChoiceR77.choice_three_premises' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
'YulangClosure.SourceInternalChoiceR77.choice_applies_r66' depends on axioms: [propext, sorryAx.{u}, Quot.sound.{u}]
'YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_fields' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
'YulangClosure.ConstructedSourceIncidenceR81.primitive_records_derive_source_probe' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
'YulangClosure.ConstructedSourceIncidenceR81.finite_aligned_reader' depends on axioms: [propext, Quot.sound.{u}]
'YulangClosure.ConstructedSourceIncidenceR81.finite_native_reader' depends on axioms: [propext]
'YulangClosure.ConstructedSourceIncidenceR81.finite_primitive_records' depends on axioms: [propext]
'YulangClosure.ConstructedSourceIncidenceR81.finite_constructs_output' depends on axioms: [propext,
 sorryAx.{u},
 Quot.sound.{u}]
'YulangClosure.DistinctSourceEmissionRootR75.value_effect_disjoint' depends on axioms: [propext]
'YulangClosure.DistinctSourceEmissionRootR75.typed_relation_ids_distinct' depends on axioms: [propext]
```

## Thirteen unchanged candidate source signatures / pending kernel output

The ambient `{S T : Type} [DecidableEq S] [DecidableEq T]` stays unchanged;
Lean includes only parameters actually used. Exact printed R84 types and full
transitive axiom lists must be returned by an accepted full audit; none exists
in this leaf. Each query name is in full_queries above. Source signatures:

### YulangClosure.ConstructedPhysicalRootR84.value_endpoint_typed

```lean
theorem value_endpoint_typed (state : Nat) (e : Endpoint T)
    (typed : valueEndpoint e = true) : DistinctSourceEmissionRootR75.IsValue (endpoint (S := S) state e)
```

### YulangClosure.ConstructedPhysicalRootR84.effect_endpoint_typed

```lean
theorem effect_endpoint_typed (state : Nat) (e : Endpoint T)
    (typed : effectEndpoint e = true) : DistinctSourceEmissionRootR75.IsEffect (endpoint (S := S) state e)
```

### YulangClosure.ConstructedPhysicalRootR84.primitive_derive_root_matches

```lean
theorem primitive_derive_root_matches
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) :
    CurrentEmissionOwnershipR47.RootMatches (OccurrenceQualifiedFactReadersR65.current n inventory)
      (OccurrenceQualifiedConsumerR66.rootQuery n q i d.origin.relation)
```

### YulangClosure.ConstructedPhysicalRootR84.primitive_derive_before_ancestry

```lean
theorem primitive_derive_before_ancestry
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) :
    OccurrenceQualifiedConsumerR66.BeforeAncestry inventory n
      (OccurrenceQualifiedConsumerR66.rootQuery n q i d.origin.relation) (physical (physicalValue index d))
```

### YulangClosure.ConstructedPhysicalRootR84.primitive_distinct_relation_roles

```lean
theorem primitive_distinct_relation_roles
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) : d.origin.relation ≠ d.relation
```

### YulangClosure.ConstructedPhysicalRootR84.constructed_applies_parent

```lean
theorem constructed_applies_parent
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : SourceInternalContextR55.Use Nat (Key S T)) (receiving target annotation row : Key S T)
    (out : Constructed s inventory n source calls u receiving target annotation row) :
    out.root.incidence = out.sourceOutput.incidence ∧
    InternalPermissionIncidenceR45.extract
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (ConstructedSourceIncidenceR81.request u receiving target out.sourceOutput.aligned.choice annotation row)
      out.root.incidence.probe = some (InternalPermissionIncidenceR45.certificate
        (ConstructedSourceIncidenceR81.request u receiving target out.sourceOutput.aligned.choice annotation row)
        out.root.incidence.probe) ∧ out.root.root ≠ out.root.value.relation :=
  ⟨out.sameIncidence,
    OccurrenceQualifiedConsumerR66.source_incidence_checked s inventory _ out.root.incidence,
    out.distinctRoles⟩

abbrev fixtureSource := ConstructedSourceIncidenceR81.fixture
abbrev fixtureInventory := ConstructedSourceIncidenceR81.fixtureInventory
abbrev fixtureOwner := ConstructedSourceIncidenceR81.fixtureSource
abbrev fixtureCalls := ConstructedSourceIncidenceR81.fixtureCalls
abbrev fixtureUse := SourceInternalChoiceR77.fixtureUse
abbrev fixtureNative := ProviderNativeContextR57.fixtureNative
abbrev fixtureIncidence := ConstructedSourceIncidenceR81.fixtureOutput.incidence
abbrev fixtureQuery := ConstructedSourceIncidenceR81.request fixtureUse (.source 10) (.source 1)
  ConstructedSourceIncidenceR81.fixtureOutput.aligned.choice (.source 6) (.source 5)

def fixtureRecords : Records Nat Nat :=
  ⟨100, fixtureEmission 4 0, fixtureAdmission 4 0, 0,
    ⟨OccurrenceQualifiedFactReadersR65.fixtureFirst, OccurrenceQualifiedFactReadersR65.fixtureRoute⟩,
    ⟨1, 2, 100, 0, some ⟨1, 0, 2, 2, 100, 0,
      .value (.positiveFunction 300), .value (.negativeFunction 400), none, false, true⟩⟩,
    ⟨1, 0, 2, 2, 100, 0,
      .value (.positiveFunction 300), .value (.negativeFunction 400), none, false, true⟩,
    ⟨1, 2, .value (.positiveFunction 300), .value (.negativeFunction 400)⟩,
    ⟨1, 0, .effect (.annotationMember 0 0), .effect (.row 4)⟩⟩

theorem finite_reads : readRecords fixtureNative fixtureInventory fixtureQuery 0 = some fixtureRecords
```

### YulangClosure.ConstructedPhysicalRootR84.finite_reads

```lean
theorem finite_reads : readRecords fixtureNative fixtureInventory fixtureQuery 0 = some fixtureRecords
```

### YulangClosure.ConstructedPhysicalRootR84.finite_primitive

```lean
theorem finite_primitive : Primitive fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 fixtureRecords
```

### YulangClosure.ConstructedPhysicalRootR84.finite_constructs_root

```lean
theorem finite_constructs_root : fixtureResult = some fixtureOutput
```

### YulangClosure.ConstructedPhysicalRootR84.finite_nonempty_mixed_witness

```lean
theorem finite_nonempty_mixed_witness :
    fixtureResult.isSome = true ∧ fixtureRoot.root = 2 ∧ fixtureRoot.value.relation = 0 ∧
    fixtureRoot.incidence.probe.permission.concrete = [.source 7, .source 7, .source 11] ∧
    fixtureRoot.incidence.probe.registeredRoot = 300 ∧
    fixtureRoot.incidence.probe.registeredRoot ≠ 700
```

### YulangClosure.ConstructedPhysicalRootR84.duplicate_stale_and_substituted_rejected

```lean
theorem duplicate_stale_and_substituted_rejected :
    runNative {fixtureNative with emissions := fixtureNative.emissions ++ [fixtureEmission 4 0]} = false ∧
    runNative {fixtureNative with effectRows := []} = false ∧
    runNative {fixtureNative with admissions := [fixtureAdmission 6 0, fixtureAdmission 6 1]} = false ∧
    runNative {fixtureNative with emissions := [{fixtureEmission 4 0 with readbackSlot := fixtureSlot 6}]} = false
```

### YulangClosure.ConstructedPhysicalRootR84.incomplete_foreign_and_wrong_task_rejected

```lean
theorem incomplete_foreign_and_wrong_task_rejected :
    runNative (mapDrain (fun d => {d with completed := false}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with state := 999}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with cause := 101}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with taskUpper := .value (.negativeFunction 999)}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with selectedRelation := 0}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with incoming := some 2}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with replay := true}) fixtureNative) = false
```

### YulangClosure.ConstructedPhysicalRootR84.collapsed_roles_and_parameter_substitution_rejected

```lean
theorem collapsed_roles_and_parameter_substitution_rejected :
    runNative {fixtureNative with admissions := [fixtureAdmission 4 2, fixtureAdmission 6 1]} = false ∧
    runNative {fixtureNative with relations := fixtureNative.relations.map
      (fun r => if r.index = 2 then {r with lower := .value (.positiveFunction 700)} else r)} = false ∧
    runNative {fixtureNative with origins := fixtureNative.origins.map (fun o => {o with occurrence := 101})} = false
```

## Parent application and represented/omitted cases

R84's primitive_derive_root_matches derives all seven exact R47 source-root
conditions from indexed Origin/inline Drain plus complete occurrence/task
candidate sets. primitive_derive_before_ancestry derives every fourteen original
R66 conjunct on the same indexed admission/emission and current slot. assemble
constructs the ORIGINAL R66 Root; construct first runs R81's original Constructed
constructor, then retains exactly that incidence. constructed_applies_parent
applies R66.source_incidence_checked to the SAME incidence; no new witness or
alternative owner relation is substituted. primitive_distinct_relation_roles
uses R75 endpoint constructor disjointness and native functional relation reads,
not assumed numeric inequality. These are proposed terms until actual acceptance.

All ValueEndpoint primitive/row/Function/variant/record/tuple constructors, all
EffectEndpoint constructors, both row kinds and all eight currentBound lanes
remain. Arbitrary source S and term T retain their original equality instances.
Source Group/Name/Apply/other forms and cycle/missing/other peel failures remain.
The mixed nonempty fixture keeps source Value relation 2 versus emission Effect
relation 0, registered root 300 versus parameter nativeRoot 700, permission
[7,7,11] and qualified semantic fact (2,0), with all original source coordinates.

The three unchanged rejection claims cover duplicate emission, missing/stale
current rows, substituted admission, foreign readback slot, incomplete/foreign
state/cause/task/selected-relation drains, incoming/replay, collapsed relation
roles, parameter-root substitution and foreign Origin occurrence. No expected
value, primitive check, constructor or source term was changed for acceptance.

Provider/R49 suppression/consumer, R58 search/completeness, R60 decode, R61
ancestry, R62 policy, R78 capture, R79 OrderedRoots and native extraction remain
omitted and OPEN. A prefix-only pass is not theorem acceptance. Finite tables
are mathematical records, not authenticated Rust execution. Original A/B,
full source soundness, principality, termination and production remain OPEN.

Read-only Rust source map remains exactly the R83 handoff's pinned r2 map:
candidate_context.rs:109 SourceDrainReceipt, :407 Origin, :641 CheckedBoundEmission,
:665 InternalUseRootEvidence, :3141 checked_emission_for_internal_use,
:3183 checked_internal_use_root; candidate_receiver.rs:582 InventoryEntryRequest,
:1161 InventoryInternalRootView, :1895–1939 owner projection and :4814–4816 carried
Origin/drain fields. R55/R57 records map indexed origin_index, created_seed,
selected_relation, occurrence/cause/task, incoming/replay/completed and the
source Value/emission Effect relation reads. Inline completion stays separate
from the rejected auxiliary completion-table condition. Rust pointer identity,
state ownership/lifetime, task/cause encoding and complete table extraction
are NOT proved by Lean record equality; Rust compilation/runtime is unverified.

First remaining premise/owner: Luna verification must accept the normalized
prefix then all thirteen R84 theorem type/axiom pairs, followed by fresh
independent review/adjudication. Source/native owner still must authenticate
these complete indexed tables from actual execution, prove pointer/state/slot
identity representation, supply R79 OrderedRoots and ancestry where required,
and discharge the original source-scope/shared-strategy A/B premise. No actual
counterexample is claimed. Mutual TODO R84-ROOT-CHECK-1: obtain exact accepted
inputs/output; falsifier any diagnostic, type/hypothesis change, omitted case,
forbidden axiom, failed rejection, non-equivalent normalization or resource cap.

## Actual leaf actions and resources

Only the two exact R84 paths were written; all frozen dependencies, Rust,
manifest/current/contract/status/index files and old handoffs stayed read-only.
No Git mutation, child, scheduling change, reviewer appointment, user/third-party
contact, compiler, Lean/Lake, tests, formatter, scratch/cache/target/.olean,
environment/worktree or subprocess checker. Used only shell source reads/searches
and Python standard-library in-memory parsing, hashes, normalization/assembly
and exact-lease writing. Zero compiler/checker invocations; no RSS measured.

Two source-preparation Python exits were 1 and were repaired without any Lean
execution: (1) receipt pin comparison caught concurrent primary-owned contract/
admission/audit-result correction; the acknowledged new manifest then matched;
(2) an overstrict pre-write reversibility assertion expected inequality after
reversing new candidate qualifications. The new identifiers had no pre-existing
full YulangClosure prefix, so reversal correctly equaled the original; the
assertion was replaced with an exact per-token inverse check, which passed.
That failed draft wrote no R84 file. Subsequent actual source/assembly commands
exit 0; these observations are not proof tests or kernel results.

Envelope 1600 s, no renewal; actual leaf launch timestamp is primary-owned.
Locally recorded work clock 12:28:06 UTC and candidate draft 12:31:31 UTC;
freeze clock and final hashes follow. All scratch/generated paths NONE; all
contributing descendants NONE. Candidate source and normalization require fresh
independent review together. No self-certification or theorem-status promotion.

Pinned identity record:

- `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84.md`: `28890c4ee0953c4a4e01a1f5a95b04b22eaa45616d87a4f3b5a9ad2a8d6604f0`.
- `tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-admission.md`: `057db44d1cff606b6b439493773b69145fbbd6e4d3e3e72c2bbb37e8e40caa0b`.
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `docs/yulang-whole-proof-closure-ja.md`: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
- `crates/yu-solver/src/candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `crates/yu-solver/src/candidate_receiver.rs`: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.
- `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Elab/Tactic/Simp.lean`: `22f8ae5a56c71ed9f65c58f242b626e2382916d624d89a5b73e5bbe7bc421978`.
- `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Meta/Tactic/Simp/SimpTheorems.lean`: `4464c13b99a98a25aebb001e842ec52f82cbf86efa5cb7fa6dd4d0c1e3645cf7`.

## Frozen revision 1 / STOPPED

Source-only reconstruction from this JSON matched all 220 original ranges and
hashes, six normalized declarations / 24 token substitutions, exact original
R83 audit2 receipt, all twenty module hashes/local edges, every normalized
prefix line interval, eight diagnostic mappings, and both proposed audit hashes.
Per-token reversal recovers the exact R83 namespace-renamed candidate; all
thirteen theorem source signatures match. These checks are not Lean execution.

Candidate 22,748 bytes, SHA-256
`1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839`.
Normalized dependency body 78,934 bytes, SHA-256
`ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49`.
Proposed slot-1 prefix input 93,368 bytes, SHA-256
`e031132b1a5a42f22c5faba355a1af3d8639d0d577de9051e81f403bf465ebb3`.
Proposed slot-3 full input 103,791 bytes, SHA-256
`5c35dd49b71508fea4755abf680327932099249de1d1f4f5f250ca2d949651f2`.
Slots 2/4 exact repair hashes remain PENDING_ACTUAL_DIAGNOSTICS. Slot 3 must be
rehashed if an actual reviewed slot-2 delta changes its prefix.

No R84 invocation, theorem acceptance, axiom census or measured elaboration cap
fit exists from this leaf. Prefix/type/axiom execution, independent review and
primary adjudication remain pending. Source/native/runtime, original R66/A-B,
whole-language and production gates remain OPEN. No counterexample invented.

Worker STOPPED. Writes to both exact R84 leases are frozen. No further change
without a new explicit primary handoff; no descendants, scratch or generated
outputs. Handoff final byte hash is sent in the freeze message (not self-embedded).

Freeze clock UTC: `2026-10-31T12:34:12.095191+00:00`.


# R84 handoff revision 2 — single slot-4 candidate repair (FROZEN)

Revision 1 and its exact assembly/failed evidence above remain immutable history.
This revision supersedes only the R84 candidate bytes and slot-4 input. The
accepted 220-declaration normalized prefix and thirteen query strings are unchanged.
Primary explicitly resumed the two exact R84 leases for this one repair. No
Lean execution, scratch/generated outputs, other-path writes, Git or descendants.
Original R66/A-B/source domain and all semantic witnesses remain unchanged.

## Ten slot-3 error headers, including all nine reviewed sites

The pinned raw result is retained at the JSON path/hash below. It records exit 1,
no timeout, 11.605 s and child peak RSS 883,340 KiB; these are PRIMARY observations,
not execution performed here. Its stdout has ten error headers, not nine:

- Source 126 / stdin1833: Decidable Primitive synthesis lacked DecidableEq
  (ProviderNativeContextR57.Relation T). Primitive compares both relationRead
  results as Option (Relation T); Relation has state/index/Endpoint T fields but
  no source deriving. A local candidate `deriving instance DecidableEq for
  ProviderNativeContextR57.Relation` provides exactly structural equality using
  existing Endpoint equality. No selected source declaration or existing instance
  overlaps this type; this adds no proposition hypothesis or semantic branch.
- Source144 / stdin1850: originRead proof's broad simp normalized decide(A ∧ B)
  to decide A && decide B before horigins could rewrite the full filter. `simp
  only` unfolds just the two unique definitions/originRead and uses horigins
  before Boolean normalization. This addresses the actual displayed goal.
- Source149 / stdin1857: reversed simp-unfold of declaration originCandidates is
  invalid. Source151 / stdin1855 is the actual candidate singleton/map goal.
  Both are addressed by explicit rootCandidates unfolding with hocc/hread,
  rewriting its positive guard from hstore/hu/hid, then congrArg List.map on the
  exact original hcandidates singleton. No candidate inventory is filtered away.
- Source186 / stdin1892: hpair's bound differs syntactically from the projected
  `(admission d.admission).bound`. Add admission to the same simpa unfolding list;
  its unchanged definition projects exactly bound d.admission.state d.admission.bound.
- Source297 / stdin2003: finite_primitive's decide reduced to sorry because its
  missing structural decider was error-recovered. The new Relation instance
  directly repairs that prerequisite, and `decide +kernel` requests genuine
  kernel reduction. No proof hole or native-evaluation axiom is used.
- Source311 / stdin2017: dependent rw could not see R81.fixtureResult and its
  rewritten Constructed.sameIncidence proof failed under implicit transparency.
  The entire theorem is now direct `rfl` on the unchanged finite constructor and
  fixture; this avoids substituting into dependent generated proof fields.
  It must still pass the slot-4 kernel check; no success is presumed here.
- Source342 / stdin2048 and source351 / stdin2057: two independent finite
  runNative reductions stopped on the semireducible construct application,
  even after listed decidable instances unfolded. These are not dismissed as
  Root cascades. Each unchanged rejection formula now uses `decide +kernel`,
  which reduces the whole closed term in the kernel, including construct and
  its repaired finite Primitive instance, rather than the elaborator's restricted
  whnf path. The third rejection uses the same exact checked reduction mode.
- Source355 / stdin2061: independent parser failure in the relations record-field
  map. Parenthesize the complete `.map (...)` expression (and the following
  origins map expression). Constructor values, list mapping, predicate, endpoints,
  numeric IDs and all three rejection conjuncts remain exactly the intended
  original source formula; the failed parser-recovered proposition is not reused.

Pinned Lean source `Lean/Elab/Tactic/Decide.lean` was read: evalDecideCore routes
cfg.kernel to doKernel separately from cfg.native; doKernel checks the proof
using the kernel (lines96–135), with no native computation axiom. `decide +kernel`
is not a checker bypass or a resource increase. It remains constrained by the
primary's -j1/-M1024 and 120-second final invocation. No option disables checking.

Every original theorem source signature matches revision1 byte-for-byte, except
necessary parentheses grouping the two already-intended map field expressions
in the final statement. Reversing those grouping parentheses recovers that exact
original signature. All thirteen statements, quantifiers, generic premises,
Primitive checks, definitions/constructors, mixed witness and rejection cases
remain. The new instance and proof terms are candidate code, not accepted proof.

The bound is unchanged: earliest launch 12:24:55 UTC, 1600-second hard envelope,
no renewal; primary supplied this authenticated accounting. Slot4 is the sole
remaining invocation and is NOT executed here. Any remaining elaboration/reduction
error closes incomplete, with no further retry or weakened hypothesis.

```json
{
  "revision": 2,
  "scope": "single R84 slot-4 candidate repair",
  "previous_candidate_sha256": "1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839",
  "previous_handoff_sha256": "c9ba9b410094cea83309b2df18e64f42fe4308ef7b158c708fb737d41ead618a",
  "candidate_bytes": 22427,
  "candidate_sha256": "5d8ad6429906cdf971dbb9ee44841223c1fcc28e6591e1a75d1f453ea4eac13d",
  "unchanged_prefix_body_bytes": 78934,
  "unchanged_prefix_body_sha256": "ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49",
  "slot4_input_bytes": 103470,
  "slot4_input_sha256": "93b365ddf908e223558d166efe7f76a1f5c370a5b1c9080716d0fb0ce92b3df0",
  "slot4_recipe": "identical accepted normalized_prefix_body + import_stripped_r2_candidate + \"\\n\" + identical full_queries from revision-1 JSON",
  "raw_slot3_result_path": "tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-slot3-raw-result.json",
  "raw_slot3_result_sha256": "db6ceb58d4fa88755d1b2136cef45ae46af0374e1a870919df361ba8b9ee7d91",
  "raw_slot3_stdout_sha256": "6b7e874b4ff08b5675505d4c2d685fc34d5a320b1eef1fc59f2abf9f254458d4",
  "source_changes": {
    "new_structural_instance": "deriving instance DecidableEq for ProviderNativeContextR57.Relation",
    "origin_read_proof": "simp only [originRead, R57.unique, R55.unique, horigins]",
    "root_candidates_proof": "unfold rootCandidates only, rewrite hocc/hread and positive guard, use congrArg (List.map Origin.relation) hcandidates",
    "pair_proof": "unfold admission in existing simpa",
    "finite_construction": "replace dependent rw chain by direct rfl, using exact same finite constructor/fixture; unexecuted",
    "finite_deciders": "decide +kernel for finite_primitive and all three rejection proofs",
    "parser_grouping": "parenthesize the complete relations.map and origins.map record-field values; exact intended formulas unchanged"
  },
  "theorem_count": 13,
  "kernel_status": "CONSTRUCTED_UNCHECKED; no slot-4 execution",
  "writes_stopped": true
}
```

STOPPED / WRITES STOPPED at `2026-10-31T12:49:08.913732+00:00`. No descendants or scratch/generated paths. Slot4 audit, fresh review and primary adjudication remain pending; R66/A-B/runtime/production remain OPEN.
