# Cycle123 exact theorem signatures

All 148 public theorem declarations in the 19 new modules. The 54 V3 target/assembly/regression declarations include adapted structural proofs; this is not a count of completed B4 bridges. Private key-identity helpers are checked transitively. Each signature below is the actual `#check @...` output with explicit arguments and universe printing, exit 0.

- Yulang.B4TargetV3: 13
- Yulang.B4TargetV3Functionality: 11
- Yulang.B4TargetV3Totality: 5
- Yulang.B4SkeletonV3: 2
- Yulang.B4TargetV3Regressions: 7
- Yulang.B4TargetV3TotalityRegressions: 16
- Yulang.GeneralDictionaryReadback: 9
- Yulang.GeneralDictionaryModelEvidence: 6
- Yulang.GeneralDictionaryReadbackExamples: 9
- Yulang.GeneralDictionaryPayloadOrder: 13
- Yulang.GeneralDictionarySemanticOrder: 10
- Yulang.GeneralDictionarySemanticOrderExamples: 10
- Yulang.GeneralDictionarySemanticUniqueness: 8
- Yulang.GeneralDictionaryUniquenessExamples: 4
- Yulang.GeneralDictionaryEmissionPlans: 7
- Yulang.GeneralDictionaryEmissionPlanExamples: 6
- Yulang.GeneralDictionaryPlanLookup: 3
- Yulang.GeneralDictionaryPlanLookupExamples: 4
- Yulang.GeneralDictionaryPlannedEvidence: 5

```text
@Yulang.B4TargetV3.tree_classifies.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (tree : Yulang.CommonRoleOutermostResolver.Tree) (d : v.Demand) (outcome : Yulang.CommonRoleOutermostResolver.Result),
  @Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d tree →
    Yulang.B4TargetV3.Completed tree outcome → @Yulang.B4TargetV3.Classify.{u_1} v b r s d outcome
@Yulang.B4TargetV3.children_classify.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (trees : List.{0} Yulang.CommonRoleOutermostResolver.Tree) (demands : List.{u_1} v.Demand)
  (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary),
  @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Tree
      (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s)) demands
      trees →
    @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} Yulang.CommonRoleOutermostResolver.Tree
        Yulang.CommonRoleOutermostResolver.Dictionary
        (fun tree dictionary =>
          Yulang.B4TargetV3.Completed tree (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
        trees dictionaries →
      @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Dictionary
        (fun d dictionary =>
          @Yulang.B4TargetV3.Classify.{u_1} v b r s d (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
        demands dictionaries
@Yulang.B4TargetV3.render_resolves.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary) (d : v.Demand),
  @Yulang.B4TargetV3.Classify.{u_1} v b r s d (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
    @Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d
      (Yulang.B4TargetV3.render dictionary)
@Yulang.B4TargetV3.renders_resolve.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary) (demands : List.{u_1} v.Demand),
  @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Dictionary
      (fun d dictionary =>
        @Yulang.B4TargetV3.Classify.{u_1} v b r s d (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
      demands dictionaries →
    @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Tree
      (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s)) demands
      (Yulang.B4TargetV3.renders dictionaries)
Yulang.B4TargetV3.render_completed : ∀ (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  Yulang.B4TargetV3.Completed (Yulang.B4TargetV3.render dictionary)
    (Yulang.CommonRoleOutermostResolver.Result.selected dictionary)
Yulang.B4TargetV3.renders_completed : ∀ (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary),
  @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} Yulang.CommonRoleOutermostResolver.Tree
    Yulang.CommonRoleOutermostResolver.Dictionary
    (fun tree dictionary =>
      Yulang.B4TargetV3.Completed tree (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
    (Yulang.B4TargetV3.renders dictionaries) dictionaries
@Yulang.B4TargetV3.classify_tree.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand}
  {outcome : Yulang.CommonRoleOutermostResolver.Result},
  @Yulang.B4TargetV3.Classify.{u_1} v b r s d outcome →
    @Exists.{1} Yulang.CommonRoleOutermostResolver.Tree fun tree =>
      And (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d tree)
        (Yulang.B4TargetV3.Completed tree outcome)
@Yulang.B4TargetV3.classify_tree_iff.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand}
  {outcome : Yulang.CommonRoleOutermostResolver.Result},
  Iff (@Yulang.B4TargetV3.Classify.{u_1} v b r s d outcome)
    (@Exists.{1} Yulang.CommonRoleOutermostResolver.Tree fun tree =>
      And (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d tree)
        (Yulang.B4TargetV3.Completed tree outcome))
@Yulang.B4TargetV3.dictionary_evidence.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v),
  @Yulang.B4TargetV3.EvidenceNode.{u_1} v b →
    ∀ (r : v.Registry),
      @Yulang.B4Target.SourceBoundary.Checked.{u_1} v b r →
        ∀ (s : v.State) (model : v.Model),
          @Yulang.B4Target.SourceBoundary.Models.{u_1} v b s model →
            ∀ (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary) (d : v.Demand),
              @Yulang.B4TargetV3.Classify.{u_1} v b r s d
                  (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                @Yulang.B4Target.SourceBoundary.Evidence.{u_1} v b r s model d dictionary
@Yulang.B4TargetV3.dictionaries_evidence.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v),
  @Yulang.B4TargetV3.EvidenceNode.{u_1} v b →
    ∀ (r : v.Registry),
      @Yulang.B4Target.SourceBoundary.Checked.{u_1} v b r →
        ∀ (s : v.State) (model : v.Model),
          @Yulang.B4Target.SourceBoundary.Models.{u_1} v b s model →
            ∀ (dictionaries : List.{0} Yulang.CommonRoleOutermostResolver.Dictionary) (demands : List.{u_1} v.Demand),
              @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Dictionary
                  (fun d dictionary =>
                    @Yulang.B4TargetV3.Classify.{u_1} v b r s d
                      (Yulang.CommonRoleOutermostResolver.Result.selected dictionary))
                  demands dictionaries →
                @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Dictionary
                  (fun d dictionary => @Yulang.B4Target.SourceBoundary.Evidence.{u_1} v b r s model d dictionary)
                  demands dictionaries
Yulang.B4TargetV3.diagnostic_refl : ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Yulang.B4TargetV3.DiagnosticPermutation tree tree
Yulang.B4TargetV3.diagnostics_refl : ∀ (trees : List.{0} Yulang.CommonRoleOutermostResolver.Tree),
  @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} Yulang.CommonRoleOutermostResolver.Tree
    Yulang.CommonRoleOutermostResolver.Tree Yulang.B4TargetV3.DiagnosticPermutation trees trees
@Yulang.B4TargetV3.same_diagnostic_refl.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v),
  (∀ (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
      @Yulang.B4Target.SourceBoundary.DictionaryEquivalent.{u_1} v b dictionary dictionary) →
    ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree), @Yulang.B4TargetV3.SameDiagnostic.{u_1} v b tree tree
@Yulang.B4TargetV3.rejection_not_pending.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  @Yulang.B4TargetV3.RejectReason.{u_1} v b r s d → Not (@Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d)
@Yulang.B4TargetV3.safe_survivor_not_rejected.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat}
  {children : List.{u_1} v.Demand},
  @Yulang.B4Target.SafeKnown.{u_1} v b r s d →
    @Yulang.B4Target.SourceBoundary.Survivor.{u_1} v b r s d key children →
      Not (@Yulang.B4TargetV3.RejectReason.{u_1} v b r s d)
@Yulang.B4TargetV3.unique_not_ambiguous.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat}
  {children : List.{u_1} v.Demand} {key₁ : Nat} {cs₁ : List.{u_1} v.Demand} {key₂ : Nat} {cs₂ : List.{u_1} v.Demand},
  @Yulang.B4Target.Unique.{u_1} v b r s d key children →
    @Yulang.B4Target.SourceBoundary.Survivor.{u_1} v b r s d key₁ cs₁ →
      @Yulang.B4Target.SourceBoundary.Survivor.{u_1} v b r s d key₂ cs₂ → @Ne.{1} Nat key₁ key₂ → False
@Yulang.B4TargetV3.inspection_not_rejected.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  @Yulang.B4Target.SourceBoundary.InspectionPending.{u_1} v b r s d →
    Not (@Yulang.B4Target.SourceBoundary.RootK2.{u_1} v b r s d) →
      Not (@Yulang.B4Target.SourceBoundary.CandidateK2.{u_1} v b r s d) →
        Not (@Yulang.B4TargetV3.RejectReason.{u_1} v b r s d)
@Yulang.B4TargetV3.local_functional.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand}
  {left right : Yulang.CommonRoleOutermostResolver.Frontier.{u_1} v.Demand},
  @Yulang.B4TargetV3.Local.{u_1} v b r s d left →
    @Yulang.B4TargetV3.Local.{u_1} v b r s d right →
      @Eq.{u_1 + 1} (Yulang.CommonRoleOutermostResolver.Frontier.{u_1} v.Demand) left right
@Yulang.B4TargetV3.resolves_functional.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (left right : Yulang.CommonRoleOutermostResolver.Tree) (d : v.Demand),
  @Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d left →
    @Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d right →
      @Eq.{1} Yulang.CommonRoleOutermostResolver.Tree left right
@Yulang.B4TargetV3.resolves_children_functional.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (r : v.Registry) (s : v.State)
  (left right : List.{0} Yulang.CommonRoleOutermostResolver.Tree) (demands : List.{u_1} v.Demand),
  @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Tree
      (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s)) demands
      left →
    @Yulang.CommonRoleOutermostResolver.All₂.{u_1, 0} v.Demand Yulang.CommonRoleOutermostResolver.Tree
        (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s)) demands
        right →
      @Eq.{1} (List.{0} Yulang.CommonRoleOutermostResolver.Tree) left right
@Yulang.B4TargetV3.classify_functional.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand}
  {left right : Yulang.CommonRoleOutermostResolver.Result},
  @Yulang.B4TargetV3.Classify.{u_1} v b r s d left →
    @Yulang.B4TargetV3.Classify.{u_1} v b r s d right → @Eq.{1} Yulang.CommonRoleOutermostResolver.Result left right
@Yulang.B4TargetV3.pending_only.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  @Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d →
    ∀ (out : Yulang.CommonRoleOutermostResolver.Result),
      Iff (@Yulang.B4TargetV3.Classify.{u_1} v b r s d out)
        (@Eq.{1} Yulang.CommonRoleOutermostResolver.Result out Yulang.CommonRoleOutermostResolver.Result.pending)
@Yulang.B4TargetV3.pending_tree_only.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  @Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d →
    ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
      Iff (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d tree)
        (@Eq.{1} Yulang.CommonRoleOutermostResolver.Tree tree Yulang.CommonRoleOutermostResolver.Tree.pending)
@Yulang.B4TargetV3.completed_exact.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (e : Yulang.B4TargetV3.Executor.{u_1} v),
  @Yulang.B4TargetV3.Exact.{u_1} v b e →
    ∀ (r : v.Registry),
      @Yulang.B4Target.SourceBoundary.Checked.{u_1} v b r →
        ∀ (s : v.State) (d : v.Demand) (out : Yulang.CommonRoleOutermostResolver.Result),
          Iff
            (Yulang.B4TargetV3.Completed
              (@Prod.snd.{u_1, 0} v.State Yulang.CommonRoleOutermostResolver.Tree
                (@Yulang.B4TargetV3.Executor.run.{u_1} v e r s d))
              out)
            (@Yulang.B4TargetV3.Classify.{u_1} v b r
              (@Prod.fst.{u_1, 0} v.State Yulang.CommonRoleOutermostResolver.Tree
                (@Yulang.B4TargetV3.Executor.run.{u_1} v e r s d))
              d out)
@Yulang.B4TargetV3.local_total.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  @Yulang.B4TargetV3.SurvivorChildrenFunctional.{u_1} v b r s d →
    @Exists.{u_1 + 1} (Yulang.CommonRoleOutermostResolver.Frontier.{u_1} v.Demand) fun frontier =>
      @Yulang.B4TargetV3.Local.{u_1} v b r s d frontier
@Yulang.B4TargetV3.inspection_pending_only.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Not (@Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d) →
    @Yulang.B4Target.SourceBoundary.InspectionPending.{u_1} v b r s d →
      Not (@Yulang.B4Target.SourceBoundary.RootK2.{u_1} v b r s d) →
        Not (@Yulang.B4Target.SourceBoundary.CandidateK2.{u_1} v b r s d) →
          ∀ (out : Yulang.CommonRoleOutermostResolver.Result),
            Iff (@Yulang.B4TargetV3.Classify.{u_1} v b r s d out)
              (@Eq.{1} Yulang.CommonRoleOutermostResolver.Result out Yulang.CommonRoleOutermostResolver.Result.pending)
@Yulang.B4TargetV3.inspection_pending_tree_only.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Not (@Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d) →
    @Yulang.B4Target.SourceBoundary.InspectionPending.{u_1} v b r s d →
      Not (@Yulang.B4Target.SourceBoundary.RootK2.{u_1} v b r s d) →
        Not (@Yulang.B4Target.SourceBoundary.CandidateK2.{u_1} v b r s d) →
          ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
            Iff
              (@Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d
                tree)
              (@Eq.{1} Yulang.CommonRoleOutermostResolver.Tree tree Yulang.CommonRoleOutermostResolver.Tree.pending)
@Yulang.B4TargetV3.rootK2_rejects.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Not (@Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d) →
    @Yulang.B4Target.SourceBoundary.RootK2.{u_1} v b r s d →
      @Yulang.B4TargetV3.Local.{u_1} v b r s d (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{u_1} v.Demand)
@Yulang.B4TargetV3.candidateK2_rejects.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Not (@Yulang.B4Target.SourceBoundary.RootPending.{u_1} v b r s d) →
    @Yulang.B4Target.SourceBoundary.CandidateK2.{u_1} v b r s d →
      @Yulang.B4TargetV3.Local.{u_1} v b r s d (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{u_1} v.Demand)
@Yulang.B4SkeletonV3.b4_of_bridges.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (e : Yulang.B4TargetV3.Executor.{u_1} v)
  (frontiers : Yulang.B4SkeletonV3.Frontiers.{u_1} v),
  @Yulang.B4SkeletonV3.B4Bridges.{u_1} v b e frontiers → @Yulang.B4SkeletonV3.B4Statement.{u_1} v b e
@Yulang.B4SkeletonV3.completed_of_bridges.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  (b : Yulang.B4Target.SourceBoundary.{u_1} v) (e : Yulang.B4TargetV3.Executor.{u_1} v)
  (frontiers : Yulang.B4SkeletonV3.Frontiers.{u_1} v),
  @Yulang.B4SkeletonV3.B4Bridges.{u_1} v b e frontiers →
    ∀ (r : v.Registry),
      @Yulang.B4Target.SourceBoundary.Checked.{u_1} v b r →
        ∀ (s : v.State) (d : v.Demand) (out : Yulang.CommonRoleOutermostResolver.Result),
          Iff
            (Yulang.B4TargetV3.Completed
              (@Prod.snd.{u_1, 0} v.State Yulang.CommonRoleOutermostResolver.Tree
                (@Yulang.B4TargetV3.Executor.run.{u_1} v e r s d))
              out)
            (@Yulang.B4TargetV3.Classify.{u_1} v b r
              (@Prod.fst.{u_1, 0} v.State Yulang.CommonRoleOutermostResolver.Tree
                (@Yulang.B4TargetV3.Executor.run.{u_1} v e r s d))
              d out)
Yulang.B4TargetV3Regressions.scalar_empty_classify : ∀ (role : Nat) (out : Yulang.CommonRoleOutermostResolver.Result),
  Iff
    (@Yulang.B4TargetV3.Classify.{0} Yulang.CommonRoleScalarTargetObstruction.vocabulary
      Yulang.CommonRoleScalarTargetObstruction.boundary (@List.nil.{0} Yulang.CommonRoleScalarRegistry.Entry)
      (@Yulang.CommonRoleSettledConstraints.State.empty (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      role out)
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Result out Yulang.CommonRoleOutermostResolver.Result.pending)
Yulang.B4TargetV3Regressions.scalar_empty_tree : ∀ (role : Nat) (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Iff
    (@Yulang.CommonRoleOutermostResolver.Resolves.{0} Yulang.CommonRoleScalarTargetObstruction.vocabulary.Demand
      (@Yulang.B4TargetV3.Local.{0} Yulang.CommonRoleScalarTargetObstruction.vocabulary
        Yulang.CommonRoleScalarTargetObstruction.boundary (@List.nil.{0} Yulang.CommonRoleScalarRegistry.Entry)
        (@Yulang.CommonRoleSettledConstraints.State.empty
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      role tree)
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Tree tree Yulang.CommonRoleOutermostResolver.Tree.pending)
Yulang.B4TargetV3Regressions.scalar_empty_not_rejected : ∀ (role : Nat),
  Not
    (@Yulang.B4TargetV3.RejectReason.{0} Yulang.CommonRoleScalarTargetObstruction.vocabulary
      Yulang.CommonRoleScalarTargetObstruction.boundary (@List.nil.{0} Yulang.CommonRoleScalarRegistry.Entry)
      (@Yulang.CommonRoleSettledConstraints.State.empty (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      role)
@Yulang.B4TargetV3Regressions.failed_child_tree.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d child : v.Demand} {key : Nat},
  @Yulang.B4Target.SafeKnown.{u_1} v b r s d →
    @Yulang.B4Target.Unique.{u_1} v b r s d key (@List.cons.{u_1} v.Demand child (@List.nil.{u_1} v.Demand)) →
      @Yulang.B4TargetV3.RejectReason.{u_1} v b r s child →
        @Yulang.CommonRoleOutermostResolver.Resolves.{u_1} v.Demand (@Yulang.B4TargetV3.Local.{u_1} v b r s) d
          (Yulang.CommonRoleOutermostResolver.Tree.selected key
            (@List.cons.{0} Yulang.CommonRoleOutermostResolver.Tree Yulang.CommonRoleOutermostResolver.Tree.rejected
              (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Tree)))
@Yulang.B4TargetV3Regressions.failed_child_not_root_rejected.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d child : v.Demand} {key : Nat},
  @Yulang.B4Target.SafeKnown.{u_1} v b r s d →
    @Yulang.B4Target.Unique.{u_1} v b r s d key (@List.cons.{u_1} v.Demand child (@List.nil.{u_1} v.Demand)) →
      Not (@Yulang.B4TargetV3.RejectReason.{u_1} v b r s d)
Yulang.B4TargetV3Regressions.failed_child_not_completed : ∀ (key : Nat)
  (out : Yulang.CommonRoleOutermostResolver.Result),
  Not
    (Yulang.B4TargetV3.Completed
      (Yulang.CommonRoleOutermostResolver.Tree.selected key
        (@List.cons.{0} Yulang.CommonRoleOutermostResolver.Tree Yulang.CommonRoleOutermostResolver.Tree.rejected
          (@List.nil.{0} Yulang.CommonRoleOutermostResolver.Tree)))
      out)
@Yulang.B4TargetV3Regressions.failed_child_no_classification.{u_1} : ∀ {v : Yulang.B4Target.Vocabulary.{u_1}}
  {b : Yulang.B4Target.SourceBoundary.{u_1} v} {r : v.Registry} {s : v.State} {d child : v.Demand} {key : Nat},
  @Yulang.B4Target.SafeKnown.{u_1} v b r s d →
    @Yulang.B4Target.Unique.{u_1} v b r s d key (@List.cons.{u_1} v.Demand child (@List.nil.{u_1} v.Demand)) →
      @Yulang.B4TargetV3.RejectReason.{u_1} v b r s child →
        ∀ (out : Yulang.CommonRoleOutermostResolver.Result), Not (@Yulang.B4TargetV3.Classify.{u_1} v b r s d out)
Yulang.B4TargetV3TotalityRegressions.inspecting_stable : @Yulang.B4Target.SourceBoundary.Stable.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit
  Unit.unit
Yulang.B4TargetV3TotalityRegressions.inspecting_classify : ∀ (out : Yulang.CommonRoleOutermostResolver.Result),
  Iff
    (@Yulang.B4TargetV3.Classify.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
      Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit Unit.unit out)
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Result out Yulang.CommonRoleOutermostResolver.Result.pending)
Yulang.B4TargetV3TotalityRegressions.inspecting_tree : ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Iff
    (@Yulang.CommonRoleOutermostResolver.Resolves.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand
      (@Yulang.B4TargetV3.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
        Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit)
      Unit.unit tree)
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Tree tree Yulang.CommonRoleOutermostResolver.Tree.pending)
Yulang.B4TargetV3TotalityRegressions.inspecting_not_rejected : Not
  (@Yulang.B4TargetV3.RejectReason.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
    Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit Unit.unit)
Yulang.B4TargetV3TotalityRegressions.old_inspecting_rejected : @Yulang.B4TargetV2.Local.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit
  Unit.unit
  (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
Yulang.B4TargetV3TotalityRegressions.inspecting_total : @Exists.{1}
  (Yulang.CommonRoleOutermostResolver.Frontier.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
  fun frontier =>
  @Yulang.B4TargetV3.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
    Yulang.B4TargetV3TotalityRegressions.inspecting Unit.unit Unit.unit Unit.unit frontier
Yulang.B4TargetV3TotalityRegressions.rootK2_inspecting_rejected : @Yulang.B4TargetV3.Local.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.rootK2Inspecting Unit.unit
  Unit.unit Unit.unit
  (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
Yulang.B4TargetV3TotalityRegressions.candidateK2_inspecting_rejected : @Yulang.B4TargetV3.Local.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.candidateK2Inspecting Unit.unit
  Unit.unit Unit.unit
  (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
Yulang.B4TargetV3TotalityRegressions.conflicting_stable : @Yulang.B4Target.SourceBoundary.Stable.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.conflicting Unit.unit Unit.unit
  Unit.unit
Yulang.B4TargetV3TotalityRegressions.conflicting_not_coherent : Not
  (@Yulang.B4TargetV3.SurvivorChildrenFunctional.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
    Yulang.B4TargetV3TotalityRegressions.conflicting Unit.unit Unit.unit Unit.unit)
Yulang.B4TargetV3TotalityRegressions.conflicting_no_local : ∀
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand),
  Not
    (@Yulang.B4TargetV3.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
      Yulang.B4TargetV3TotalityRegressions.conflicting Unit.unit Unit.unit Unit.unit frontier)
Yulang.B4TargetV3TotalityRegressions.unconditional_totality_false : Not
  (∀ (frontierBoundary : Yulang.B4Target.SourceBoundary.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary),
    @Exists.{1} (Yulang.CommonRoleOutermostResolver.Frontier.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
      fun frontier =>
      @Yulang.B4TargetV3.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary frontierBoundary Unit.unit Unit.unit
        Unit.unit frontier)
Yulang.B4TargetV3TotalityRegressions.nonempty_inspecting_stable : @Yulang.B4Target.SourceBoundary.Stable.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.nonemptyInspecting Unit.unit
  Unit.unit Unit.unit
Yulang.B4TargetV3TotalityRegressions.old_nonempty_inspection_hole : ∀
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand),
  Not
    (@Yulang.B4TargetV2.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
      Yulang.B4TargetV3TotalityRegressions.nonemptyInspecting Unit.unit Unit.unit Unit.unit frontier)
Yulang.B4TargetV3TotalityRegressions.nonempty_inspection_closed : ∀ (tree : Yulang.CommonRoleOutermostResolver.Tree),
  Iff
    (@Yulang.CommonRoleOutermostResolver.Resolves.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand
      (@Yulang.B4TargetV3.Local.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary
        Yulang.B4TargetV3TotalityRegressions.nonemptyInspecting Unit.unit Unit.unit)
      Unit.unit tree)
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Tree tree Yulang.CommonRoleOutermostResolver.Tree.pending)
Yulang.B4TargetV3TotalityRegressions.inspected_empty_rejected : @Yulang.B4TargetV3.Local.{0}
  Yulang.B4TargetV3TotalityRegressions.vocabulary Yulang.B4TargetV3TotalityRegressions.inspectedEmpty Unit.unit
  Unit.unit Unit.unit
  (@Yulang.CommonRoleOutermostResolver.Frontier.rejected.{0} Yulang.B4TargetV3TotalityRegressions.vocabulary.Demand)
@Yulang.GeneralDictionaryReadback.children_payload : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  (∀ (child : Yulang.GeneralSourceDictionaries.Dictionary roles),
      @Membership.mem.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
          (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (@List.instMembership.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) children child →
        @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule
          (@Yulang.GeneralSourceDictionaries.Dictionary.root roles child)
          (@Yulang.GeneralSourceDictionaries.erase roles child)) →
    @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
      Yulang.GeneralDictionaryReadback.Payload (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule)
      (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
        (Yulang.GeneralSourceDictionaries.Occurrence roles) (@Yulang.GeneralSourceDictionaries.Dictionary.root roles)
        children)
      (@Yulang.GeneralSourceDictionaries.eraseChildren roles children)
@Yulang.GeneralDictionaryReadback.indexed_to_payload : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  @Yulang.GeneralSourceDictionaries.Evidence roles localRule tree →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule
      (@Yulang.GeneralSourceDictionaries.Dictionary.root roles tree)
      (@Yulang.GeneralSourceDictionaries.erase roles tree)
@Yulang.GeneralDictionaryReadback.payload_to_indexed : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload) (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
      And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence payload tree)
        (@Yulang.GeneralSourceDictionaries.Evidence roles localRule tree)
@Yulang.GeneralDictionaryReadback.payloads_to_indexed : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (payloads : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (occurrences : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
      Yulang.GeneralDictionaryReadback.Payload (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule)
      occurrences payloads →
    @Exists.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) fun trees =>
      And
        (@Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
          (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
            (Yulang.GeneralSourceDictionaries.Occurrence roles)
            (@Yulang.GeneralSourceDictionaries.Dictionary.root roles) trees)
          occurrences)
        (And
          (@Eq.{1} (List.{0} Yulang.CommonRoleOutermostResolver.Dictionary)
            (@Yulang.GeneralSourceDictionaries.eraseChildren roles trees) payloads)
          (∀ (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
            @Membership.mem.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
                (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
                (@List.instMembership.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) trees tree →
              @Yulang.GeneralSourceDictionaries.Evidence roles localRule tree))
@Yulang.GeneralDictionaryReadback.payload_iff_erased : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
  Iff (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence payload)
    (@Yulang.GeneralSourceDictionaries.ErasedEvidence roles localRule occurrence payload)
@Yulang.GeneralDictionaryReadback.erased_evidence_node : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload),
  localRule occurrence key children →
    @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
        Yulang.CommonRoleOutermostResolver.Dictionary (@Yulang.GeneralSourceDictionaries.ErasedEvidence roles localRule)
        children dictionaries →
      @Yulang.GeneralSourceDictionaries.ErasedEvidence roles localRule occurrence
        (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryReadback.indexed_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional roles localRule →
    ∀ (first last : Yulang.GeneralSourceDictionaries.Dictionary roles),
      @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence roles)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root roles first)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root roles last) →
        @Eq.{1} Yulang.CommonRoleOutermostResolver.Dictionary (@Yulang.GeneralSourceDictionaries.erase roles first)
            (@Yulang.GeneralSourceDictionaries.erase roles last) →
          @Yulang.GeneralSourceDictionaries.Evidence roles localRule first →
            @Yulang.GeneralSourceDictionaries.Evidence roles localRule last →
              @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) first last
@Yulang.GeneralDictionaryReadback.indexed_children_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional roles localRule →
    ∀ (first last : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)),
      @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
          (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
            (Yulang.GeneralSourceDictionaries.Occurrence roles)
            (@Yulang.GeneralSourceDictionaries.Dictionary.root roles) first)
          (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
            (Yulang.GeneralSourceDictionaries.Occurrence roles)
            (@Yulang.GeneralSourceDictionaries.Dictionary.root roles) last) →
        @Eq.{1} (List.{0} Yulang.CommonRoleOutermostResolver.Dictionary)
            (@Yulang.GeneralSourceDictionaries.eraseChildren roles first)
            (@Yulang.GeneralSourceDictionaries.eraseChildren roles last) →
          (∀ (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
              @Membership.mem.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
                  (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
                  (@List.instMembership.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) first tree →
                @Yulang.GeneralSourceDictionaries.Evidence roles localRule tree) →
            (∀ (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
                @Membership.mem.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
                    (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
                    (@List.instMembership.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) last tree →
                  @Yulang.GeneralSourceDictionaries.Evidence roles localRule tree) →
              @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) first last
@Yulang.GeneralDictionaryReadback.payload_unique_readback : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional roles localRule →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (payload : Yulang.GeneralDictionaryReadback.Payload),
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence payload →
        @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
          And
            (And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence payload tree)
              (@Yulang.GeneralSourceDictionaries.Evidence roles localRule tree))
            (∀ (other : Yulang.GeneralSourceDictionaries.Dictionary roles),
              @Yulang.GeneralSourceDictionaries.Readback roles occurrence payload other →
                @Yulang.GeneralSourceDictionaries.Evidence roles localRule other →
                  @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) other tree)
@Yulang.GeneralDictionaryModelEvidence.stored_instance_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models state assignment →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      @Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages occurrence key children →
        @Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state packages assignment occurrence key children
@Yulang.GeneralDictionaryModelEvidence.indexed_all_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) tree →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment →
        @Yulang.GeneralSourceDictionaries.Evidence roles
          (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state packages assignment) tree
@Yulang.GeneralDictionaryModelEvidence.erased_uniform_witness : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralSourceDictionaries.ErasedEvidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
      And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence payload tree)
        (∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models state assignment →
            @Yulang.GeneralSourceDictionaries.Evidence roles
              (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state packages assignment) tree)
@Yulang.GeneralDictionaryModelEvidence.payload_all_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence payload →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment →
        @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
          (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state packages assignment) occurrence payload
@Yulang.GeneralDictionaryModelEvidence.stored_children_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  (∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (located₁ located₂ :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      packages occurrence key first located₁ →
        packages occurrence key last located₂ →
          @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)) first last) →
    @Yulang.GeneralDictionaryReadback.ChildrenFunctional roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages)
@Yulang.GeneralDictionaryModelEvidence.stored_unique_readback : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  (∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (located₁ located₂ :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      packages occurrence key first located₁ →
        packages occurrence key last located₂ →
          @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)) first last) →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (payload : Yulang.GeneralDictionaryReadback.Payload),
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
          (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence payload →
        @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
          And
            (And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence payload tree)
              (@Yulang.GeneralSourceDictionaries.Evidence roles
                (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) tree))
            (∀ (other : Yulang.GeneralSourceDictionaries.Dictionary roles),
              @Yulang.GeneralSourceDictionaries.Readback roles occurrence payload other →
                @Yulang.GeneralSourceDictionaries.Evidence roles
                    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) other →
                  @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) other tree)
Yulang.GeneralDictionaryReadbackExamples.stored_leaf : ∀ (identity : Nat),
  @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package)
    (@Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDictionaryEquationExamples.roles identity
        Yulang.GeneralDictionaryEquationExamples.demand)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles)))
Yulang.GeneralDictionaryReadbackExamples.stored_tree : @Yulang.GeneralSourceDictionaries.Evidence
  Yulang.GeneralDictionaryEquationExamples.roles
  (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
    Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package)
  Yulang.GeneralDictionaryReadbackExamples.tree
Yulang.GeneralDictionaryReadbackExamples.exact_readback : @Yulang.GeneralSourceDictionaries.Readback
  Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryReadbackExamples.root
  Yulang.GeneralDictionaryReadbackExamples.payload Yulang.GeneralDictionaryReadbackExamples.tree
Yulang.GeneralDictionaryReadbackExamples.stored_payload : @Yulang.GeneralDictionaryReadback.PayloadEvidence
  Yulang.GeneralDictionaryEquationExamples.roles
  (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
    Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package)
  Yulang.GeneralDictionaryReadbackExamples.root Yulang.GeneralDictionaryReadbackExamples.payload
Yulang.GeneralDictionaryReadbackExamples.nonvacuous_model : And
  (Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state
    Yulang.GeneralDictionaryEquationExamples.assignment)
  (@Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package
      Yulang.GeneralDictionaryEquationExamples.assignment)
    Yulang.GeneralDictionaryReadbackExamples.tree)
Yulang.GeneralDictionaryReadbackExamples.uniform_model_readback : @Exists.{1}
  (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles) fun witness =>
  And
    (@Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryReadbackExamples.root Yulang.GeneralDictionaryReadbackExamples.payload witness)
    (∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state model →
        @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
          (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package model)
          witness)
Yulang.GeneralDictionaryReadbackExamples.source_children_retained : And
  (@Eq.{1} (List.{0} Nat)
    (@List.map.{0, 0}
      (Prod.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles) Nat) Nat
      (fun event =>
        @Yulang.GeneralSourceDictionaries.Occurrence.identity Yulang.GeneralDictionaryEquationExamples.roles
          (@Prod.fst.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles)
            Nat event))
      (@Yulang.GeneralSourceDictionaries.observations Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryReadbackExamples.tree))
    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
      (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
        (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102))) (@List.nil.{0} Nat)))))
  (And
    (@Eq.{1} Yulang.CommonRoleOutermostResolver.Dictionary
      (@Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryReadbackExamples.left (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles))))
      (@Yulang.GeneralSourceDictionaries.erase Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryReadbackExamples.right (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@List.nil.{0}
            (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles)))))
    (Not
      (@Yulang.GeneralSourceDictionaries.DictionaryEquivalent Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryReadbackExamples.left (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles)))
        (@Yulang.GeneralSourceDictionaries.Dictionary.node Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryReadbackExamples.right (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@List.nil.{0}
            (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles))))))
Yulang.GeneralDictionaryReadbackExamples.package_children_unique : ∀
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles) (key : Nat)
  (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles))
  (located₁ located₂ :
    @Yulang.GeneralDictionaryStateEquations.Located Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDictionaryEquationExamples.roles occurrence)),
  Yulang.GeneralDictionaryReadbackExamples.Package occurrence key first located₁ →
    Yulang.GeneralDictionaryReadbackExamples.Package occurrence key last located₂ →
      @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles))
        first last
Yulang.GeneralDictionaryReadbackExamples.unique_indexed_witness : ∀
  (other : Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles),
  @Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryReadbackExamples.root Yulang.GeneralDictionaryReadbackExamples.payload other →
    @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionaryReadbackExamples.Package)
        other →
      @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles) other
        Yulang.GeneralDictionaryReadbackExamples.tree
Yulang.GeneralDictionaryPayloadOrder.equivalent_refl : ∀ (tree : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryPayloadOrder.Equivalent tree tree
@Yulang.GeneralDictionaryPayloadOrder.equivalent_symm : ∀ {first last : Yulang.GeneralDictionaryReadback.Payload},
  Yulang.GeneralDictionaryPayloadOrder.Equivalent first last →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent last first
@Yulang.GeneralDictionaryPayloadOrder.equivalent_trans : ∀ {a b c : Yulang.GeneralDictionaryReadback.Payload},
  Yulang.GeneralDictionaryPayloadOrder.Equivalent a b →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent b c → Yulang.GeneralDictionaryPayloadOrder.Equivalent a c
@Yulang.GeneralDictionaryPayloadOrder.equivalent_rootKey : ∀ {first last : Yulang.GeneralDictionaryReadback.Payload},
  Yulang.GeneralDictionaryPayloadOrder.Equivalent first last →
    @Eq.{1} Nat (Yulang.GeneralDictionaryPayloadOrder.rootKey first) (Yulang.GeneralDictionaryPayloadOrder.rootKey last)
@Yulang.GeneralDictionaryPayloadOrder.eraseChildren_map : ∀ {roles : Yulang.Roles.RoleDecls}
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  @Eq.{1} (List.{0} Yulang.CommonRoleOutermostResolver.Dictionary)
    (@Yulang.GeneralSourceDictionaries.eraseChildren roles children)
    (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles) Yulang.CommonRoleOutermostResolver.Dictionary
      (@Yulang.GeneralSourceDictionaries.erase roles) children)
@Yulang.GeneralDictionaryPayloadOrder.erase_equivalent : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralSourceDictionaries.Dictionary roles},
  @Yulang.GeneralSourceDictionaries.DictionaryEquivalent roles first last →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent (@Yulang.GeneralSourceDictionaries.erase roles first)
      (@Yulang.GeneralSourceDictionaries.erase roles last)
@Yulang.GeneralDictionaryPayloadOrder.all₂_perm_right.{u_1,
    u_2} : ∀ {α : Type u_1} {β : Type u_2} (relation : α → β → Prop) {left : List.{u_1} α} {right after : List.{u_2} β},
  @Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β relation left right →
    @List.Perm.{u_2} β right after →
      @Exists.{u_1 + 1} (List.{u_1} α) fun reordered =>
        And (@List.Perm.{u_1} α left reordered)
          (@Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β relation reordered after)
@Yulang.GeneralDictionaryPayloadOrder.all₂_replace_right.{u_1,
    u_2} : ∀ {α : Type u_1} {β : Type u_2} (relation : α → β → Prop) (leading trailing : List.{u_2} β)
  (left : List.{u_1} α) (before after : β),
  (∀ (a : α), relation a before → relation a after) →
    @Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β relation left
        (@HAppend.hAppend.{u_2, u_2, u_2} (List.{u_2} β) (List.{u_2} β) (List.{u_2} β)
          (@instHAppendOfAppend.{u_2} (List.{u_2} β) (@List.instAppend.{u_2} β)) leading
          (@List.cons.{u_2} β before trailing)) →
      @Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β relation left
        (@HAppend.hAppend.{u_2, u_2, u_2} (List.{u_2} β) (List.{u_2} β) (List.{u_2} β)
          (@instHAppendOfAppend.{u_2} (List.{u_2} β) (@List.instAppend.{u_2} β)) leading
          (@List.cons.{u_2} β after trailing))
@Yulang.GeneralDictionaryPayloadOrder.evidence_reorder : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralSourceDictionaries.PermutationInvariant roles localRule →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (before after : List.{0} Yulang.GeneralDictionaryReadback.Payload),
      @List.Perm.{0} Yulang.GeneralDictionaryReadback.Payload before after →
        @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence
            (Yulang.CommonRoleOutermostResolver.Dictionary.node key before) →
          @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence
            (Yulang.CommonRoleOutermostResolver.Dictionary.node key after)
@Yulang.GeneralDictionaryPayloadOrder.evidence_replace : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (leading trailing : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (before after : Yulang.GeneralDictionaryReadback.Payload),
  (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule child before →
        @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule child after) →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence
        (Yulang.CommonRoleOutermostResolver.Dictionary.node key
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Yulang.GeneralDictionaryReadback.Payload)
            (List.{0} Yulang.GeneralDictionaryReadback.Payload) (List.{0} Yulang.GeneralDictionaryReadback.Payload)
            (@instHAppendOfAppend.{0} (List.{0} Yulang.GeneralDictionaryReadback.Payload)
              (@List.instAppend.{0} Yulang.GeneralDictionaryReadback.Payload))
            leading (@List.cons.{0} Yulang.GeneralDictionaryReadback.Payload before trailing))) →
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence
        (Yulang.CommonRoleOutermostResolver.Dictionary.node key
          (@HAppend.hAppend.{0, 0, 0} (List.{0} Yulang.GeneralDictionaryReadback.Payload)
            (List.{0} Yulang.GeneralDictionaryReadback.Payload) (List.{0} Yulang.GeneralDictionaryReadback.Payload)
            (@instHAppendOfAppend.{0} (List.{0} Yulang.GeneralDictionaryReadback.Payload)
              (@List.instAppend.{0} Yulang.GeneralDictionaryReadback.Payload))
            leading (@List.cons.{0} Yulang.GeneralDictionaryReadback.Payload after trailing)))
@Yulang.GeneralDictionaryPayloadOrder.equivalent_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralDictionaryReadback.Payload}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralSourceDictionaries.PermutationInvariant roles localRule →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
      ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Iff (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence before)
          (@Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence after)
@Yulang.GeneralDictionaryPayloadOrder.equivalent_erased_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralDictionaryReadback.Payload}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralSourceDictionaries.PermutationInvariant roles localRule →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
      ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Iff (@Yulang.GeneralSourceDictionaries.ErasedEvidence roles localRule occurrence before)
          (@Yulang.GeneralSourceDictionaries.ErasedEvidence roles localRule occurrence after)
@Yulang.GeneralDictionaryPayloadOrder.erase_does_not_reflect : ∀ {roles : Yulang.Roles.RoleDecls}
  (demand : Yulang.GeneralSourceState.Demand roles) (first last key : Nat),
  @Ne.{1} Nat first last →
    have a :=
      @Yulang.GeneralSourceDictionaries.Dictionary.node roles
        (@Yulang.GeneralSourceDictionaries.Occurrence.mk roles first demand) key
        (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles));
    have b :=
      @Yulang.GeneralSourceDictionaries.Dictionary.node roles
        (@Yulang.GeneralSourceDictionaries.Occurrence.mk roles last demand) key
        (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles));
    And
      (Yulang.GeneralDictionaryPayloadOrder.Equivalent (@Yulang.GeneralSourceDictionaries.erase roles a)
        (@Yulang.GeneralSourceDictionaries.erase roles b))
      (Not (@Yulang.GeneralSourceDictionaries.DictionaryEquivalent roles a b))
@Yulang.GeneralDictionarySemanticOrder.unordered_intro : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (located :
    @Yulang.GeneralDictionaryStateEquations.Located roles state
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
  packages occurrence key children located →
    @Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key children located
@Yulang.GeneralDictionarySemanticOrder.unordered_perm : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @List.Perm.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles) first last →
    ∀
      (located :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      Iff (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key first located)
        (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key last located)
@Yulang.GeneralDictionarySemanticOrder.unordered_idempotent : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (located :
    @Yulang.GeneralDictionaryStateEquations.Located roles state
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
  Iff
    (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state
      (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages) occurrence key children located)
    (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key children located)
@Yulang.GeneralDictionarySemanticOrder.unordered_children_perm : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  (∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (located₁ located₂ :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      packages occurrence key first located₁ →
        packages occurrence key last located₂ →
          @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)) first last) →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (located₁ located₂ :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      @Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key first located₁ →
        @Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key last located₂ →
          @List.Perm.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles) first last
@Yulang.GeneralDictionarySemanticOrder.stored_invariant : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  @Yulang.GeneralSourceDictionaries.PermutationInvariant roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state
      (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages))
@Yulang.GeneralDictionarySemanticOrder.model_invariant : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (assignment : Yulang.GeneralSourceState.Assignment),
  @Yulang.GeneralSourceDictionaries.PermutationInvariant roles
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state
      (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages) assignment)
@Yulang.GeneralDictionarySemanticOrder.indexed_stored_semantic : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) tree →
    @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages))
      tree
@Yulang.GeneralDictionarySemanticOrder.equivalent_stored_payload : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence before →
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state
          (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages))
        occurrence after
@Yulang.GeneralDictionarySemanticOrder.equivalent_payload_all_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence before →
      ∀ (assignment : Yulang.GeneralSourceState.Assignment),
        Yulang.GeneralSourceState.Models state assignment →
          @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
            (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state
              (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages) assignment)
            occurrence after
@Yulang.GeneralDictionarySemanticOrder.equivalent_uniform_witness : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state packages) occurrence before →
      @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
        And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence after tree)
          (∀ (assignment : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models state assignment →
              @Yulang.GeneralSourceDictionaries.Evidence roles
                (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state
                  (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages) assignment)
                tree)
Yulang.GeneralDictionarySemanticOrderExamples.forward_stored : @Yulang.GeneralDictionaryReadback.PayloadEvidence
  Yulang.GeneralDictionaryEquationExamples.roles
  (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
    Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
  Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.forward
Yulang.GeneralDictionarySemanticOrderExamples.forward_backward_equivalent : Yulang.GeneralDictionaryPayloadOrder.Equivalent
  Yulang.GeneralDictionarySemanticOrderExamples.forward Yulang.GeneralDictionarySemanticOrderExamples.backward
Yulang.GeneralDictionarySemanticOrderExamples.forward_backward_distinct : @Ne.{1}
  Yulang.GeneralDictionaryReadback.Payload Yulang.GeneralDictionarySemanticOrderExamples.forward
  Yulang.GeneralDictionarySemanticOrderExamples.backward
Yulang.GeneralDictionarySemanticOrderExamples.left_wrong_key : ∀
  (children : List.{0} Yulang.GeneralDictionaryReadback.Payload),
  Not
    (@Yulang.GeneralDictionaryReadback.PayloadEvidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
      Yulang.GeneralDictionarySemanticOrderExamples.left
      (Yulang.CommonRoleOutermostResolver.Dictionary.node (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        children))
Yulang.GeneralDictionarySemanticOrderExamples.backward_not_canonical : Not
  (@Yulang.GeneralDictionaryReadback.PayloadEvidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
    Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.backward)
Yulang.GeneralDictionarySemanticOrderExamples.backward_semantic : @Yulang.GeneralDictionaryReadback.PayloadEvidence
  Yulang.GeneralDictionaryEquationExamples.roles
  (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
    Yulang.GeneralDictionaryEquationExamples.state
    (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package))
  Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.backward
Yulang.GeneralDictionarySemanticOrderExamples.backward_all_models : ∀
  (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state assignment →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
        assignment)
      Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.backward
Yulang.GeneralDictionarySemanticOrderExamples.backward_nonvacuous : And
  (Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state
    Yulang.GeneralDictionaryEquationExamples.assignment)
  (@Yulang.GeneralDictionaryReadback.PayloadEvidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state
      (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
      Yulang.GeneralDictionaryEquationExamples.assignment)
    Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.backward)
Yulang.GeneralDictionarySemanticOrderExamples.backward_uniform_source_witness : @Exists.{1}
  (Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles) fun tree =>
  And
    (@Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionarySemanticOrderExamples.root Yulang.GeneralDictionarySemanticOrderExamples.backward tree)
    (∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state model →
        @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
          (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryEquationExamples.state
            (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
              Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
            model)
          tree)
Yulang.GeneralDictionarySemanticOrderExamples.unordered_not_ordered_functional : Not
  (@Yulang.GeneralDictionaryReadback.ChildrenFunctional Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryEquationExamples.state
      (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)))
@Yulang.GeneralDictionarySemanticUniqueness.all₂_mono_members.{u_1,
    u_2} : ∀ {α : Type u_1} {β : Type u_2} (relation other : α → β → Prop) {first : List.{u_1} α} {last : List.{u_2} β},
  @Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β relation first last →
    (∀ (a : α),
        @Membership.mem.{u_1, u_1} α (List.{u_1} α) (@List.instMembership.{u_1} α) first a →
          ∀ (b : β),
            @Membership.mem.{u_2, u_2} β (List.{u_2} β) (@List.instMembership.{u_2} β) last b →
              relation a b → other a b) →
      @Yulang.CommonRoleOutermostResolver.All₂.{u_1, u_2} α β other first last
@Yulang.GeneralDictionarySemanticUniqueness.align_roots : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)),
  @List.Perm.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)
      (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
        (Yulang.GeneralSourceDictionaries.Occurrence roles) (@Yulang.GeneralSourceDictionaries.Dictionary.root roles)
        first)
      (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
        (Yulang.GeneralSourceDictionaries.Occurrence roles) (@Yulang.GeneralSourceDictionaries.Dictionary.root roles)
        last) →
    @Exists.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)) fun middle =>
      And (@List.Perm.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles) first middle)
        (@Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
          (Yulang.GeneralSourceDictionaries.Dictionary roles)
          (fun a b =>
            @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence roles)
              (@Yulang.GeneralSourceDictionaries.Dictionary.root roles a)
              (@Yulang.GeneralSourceDictionaries.Dictionary.root roles b))
          middle last)
@Yulang.GeneralDictionarySemanticUniqueness.replace_all_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (leading : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
  {first last : List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)},
  @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
      (Yulang.GeneralSourceDictionaries.Dictionary roles) (@Yulang.GeneralSourceDictionaries.DictionaryEquivalent roles)
      first last →
    @Yulang.GeneralSourceDictionaries.DictionaryEquivalent roles
      (@Yulang.GeneralSourceDictionaries.Dictionary.node roles occurrence key
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (@instHAppendOfAppend.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
            (@List.instAppend.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)))
          leading first))
      (@Yulang.GeneralSourceDictionaries.Dictionary.node roles occurrence key
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
          (@instHAppendOfAppend.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
            (@List.instAppend.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles)))
          leading last))
@Yulang.GeneralDictionarySemanticUniqueness.evidence_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralDictionarySemanticUniqueness.NodeFunctional roles localRule →
    ∀ (first : Yulang.GeneralSourceDictionaries.Dictionary roles),
      @Yulang.GeneralSourceDictionaries.Evidence roles localRule first →
        ∀ (last : Yulang.GeneralSourceDictionaries.Dictionary roles),
          @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence roles)
              (@Yulang.GeneralSourceDictionaries.Dictionary.root roles last)
              (@Yulang.GeneralSourceDictionaries.Dictionary.root roles first) →
            @Yulang.GeneralSourceDictionaries.Evidence roles localRule last →
              @Yulang.GeneralSourceDictionaries.DictionaryEquivalent roles first last
@Yulang.GeneralDictionarySemanticUniqueness.payload_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  (localRule : Yulang.GeneralSourceDictionaries.LocalInstance roles),
  @Yulang.GeneralDictionarySemanticUniqueness.NodeFunctional roles localRule →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (first last : Yulang.GeneralDictionaryReadback.Payload),
      @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence first →
        @Yulang.GeneralDictionaryReadback.PayloadEvidence roles localRule occurrence last →
          Yulang.GeneralDictionaryPayloadOrder.Equivalent first last
@Yulang.GeneralDictionarySemanticUniqueness.unordered_package_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  @Yulang.GeneralDictionarySemanticUniqueness.PackagesFunctional roles state packages →
    ∀ (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key₁ key₂ : Nat)
      (first last : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
      (located₁ located₂ :
        @Yulang.GeneralDictionaryStateEquations.Located roles state
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand roles occurrence)),
      @Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key₁ first located₁ →
        @Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages occurrence key₂ last located₂ →
          And (@Eq.{1} Nat key₁ key₂) (@List.Perm.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles) first last)
@Yulang.GeneralDictionarySemanticUniqueness.stored_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  @Yulang.GeneralDictionarySemanticUniqueness.PackagesFunctional roles state packages →
    @Yulang.GeneralDictionarySemanticUniqueness.NodeFunctional roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages))
@Yulang.GeneralDictionarySemanticUniqueness.model_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles state),
  @Yulang.GeneralDictionarySemanticUniqueness.PackagesFunctional roles state packages →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      @Yulang.GeneralDictionarySemanticUniqueness.NodeFunctional roles
        (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles state
          (@Yulang.GeneralDictionarySemanticOrder.Unordered roles state packages) assignment)
Yulang.GeneralDictionaryUniquenessExamples.package_functional : @Yulang.GeneralDictionarySemanticUniqueness.PackagesFunctional
  Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.state
  Yulang.GeneralDictionarySemanticOrderExamples.Package
Yulang.GeneralDictionaryUniquenessExamples.stored_source_unique : ∀
  (first last : Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles),
  @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package))
      first →
    @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state
          (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package))
        last →
      @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root Yulang.GeneralDictionaryEquationExamples.roles last)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root Yulang.GeneralDictionaryEquationExamples.roles first) →
        @Yulang.GeneralSourceDictionaries.DictionaryEquivalent Yulang.GeneralDictionaryEquationExamples.roles first last
Yulang.GeneralDictionaryUniquenessExamples.model_source_unique : ∀ (assignment : Yulang.GeneralSourceState.Assignment)
  (first last : Yulang.GeneralSourceDictionaries.Dictionary Yulang.GeneralDictionaryEquationExamples.roles),
  @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
        assignment)
      first →
    @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
        (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state
          (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package)
          assignment)
        last →
      @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root Yulang.GeneralDictionaryEquationExamples.roles last)
          (@Yulang.GeneralSourceDictionaries.Dictionary.root Yulang.GeneralDictionaryEquationExamples.roles first) →
        @Yulang.GeneralSourceDictionaries.DictionaryEquivalent Yulang.GeneralDictionaryEquationExamples.roles first last
Yulang.GeneralDictionaryUniquenessExamples.any_root_payload_equivalent : ∀
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.state
        (@Yulang.GeneralDictionarySemanticOrder.Unordered Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryEquationExamples.state Yulang.GeneralDictionarySemanticOrderExamples.Package))
      Yulang.GeneralDictionarySemanticOrderExamples.root payload →
    Yulang.GeneralDictionaryPayloadOrder.Equivalent payload Yulang.GeneralDictionarySemanticOrderExamples.backward
Yulang.GeneralDictionaryEmissionPlans.declaration_key_unique : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (first last : Yulang.GeneralDeclarations.Declaration),
      @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration (List.{0} Yulang.GeneralDeclarations.Declaration)
          (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations first →
        @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration (List.{0} Yulang.GeneralDeclarations.Declaration)
            (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations last →
          @Eq.{1} Nat first.id last.id → @Eq.{1} Yulang.GeneralDeclarations.Declaration first last
Yulang.GeneralDictionaryEmissionPlans.plan_children_functional : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional registry.roles
    (Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame)
Yulang.GeneralDictionaryEmissionPlans.visible_plan : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (present :
    @Membership.mem.{0, 0} Yulang.GeneralDeclarations.Declaration (List.{0} Yulang.GeneralDeclarations.Declaration)
      (@List.instMembership.{0} Yulang.GeneralDeclarations.Declaration) registry.declarations declaration),
  @Eq.{1} Nat declaration.role
      (@Yulang.GeneralSourceState.Demand.role registry.roles
        (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root)) →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root declaration.id
      (@Yulang.GeneralDictionaryEmissionPlans.children registry.roles registry.constructors frame root declaration ⋯)
@Yulang.GeneralDictionaryEmissionPlans.children_reorders : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Declaration} {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (firstChecked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles first)
      (lastChecked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles last),
      @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
        (@Yulang.GeneralDictionaryEmissionPlans.children roles constructors frame root first firstChecked)
        (@Yulang.GeneralDictionaryEmissionPlans.children roles constructors frame root last lastChecked)
Yulang.GeneralDictionaryEmissionPlans.plan_reorders_forward : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryEmissionPlans.Plan { constructors := constructors, roles := roles, declarations := first }
          one frame root key demands →
        Yulang.GeneralDictionaryEmissionPlans.Plan
          { constructors := constructors, roles := roles, declarations := last } two frame root key demands
Yulang.GeneralDictionaryEmissionPlans.plan_reorders_iff : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Iff
        (Yulang.GeneralDictionaryEmissionPlans.Plan
          { constructors := constructors, roles := roles, declarations := first } one frame root key demands)
        (Yulang.GeneralDictionaryEmissionPlans.Plan
          { constructors := constructors, roles := roles, declarations := last } two frame root key demands)
Yulang.GeneralDictionaryEmissionPlans.selected_plan_functional : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (selected : Yulang.GeneralSourceDictionaries.Occurrence registry.roles → Nat → Prop),
  (∀ (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (first last : Nat),
      selected root first → selected root last → @Eq.{1} Nat first last) →
    @Yulang.GeneralDictionarySemanticUniqueness.NodeFunctional registry.roles fun root key children =>
      And (selected root key) (Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key children)
Yulang.GeneralDictionaryEmissionPlanExamples.actual_child_plan : @Eq.{1}
  (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked)
  (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.roles
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
      (@Yulang.GeneralDeclarationDemands.childDemand Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDeclarationExamples.wrap Yulang.GeneralDeclarationExamples.containerChild ⋯
        Yulang.GeneralDeclarationExamples.wrapCapture Yulang.GeneralDeclarationExamples.wrapAllocation))
    (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryEmissionPlanExamples.wrap_plan : Yulang.GeneralDictionaryEmissionPlans.Plan
  Yulang.GeneralDeclarationExamples.registry Yulang.GeneralDeclarationExamples.registry_checked
  Yulang.GeneralDictionaryEmissionPlanExamples.frame Yulang.GeneralDictionaryEmissionPlanExamples.root
  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.registry.roles
    Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked)
Yulang.GeneralDictionaryEmissionPlanExamples.wrap_plan_unique : ∀
  (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Yulang.GeneralDictionaryEmissionPlans.Plan Yulang.GeneralDeclarationExamples.registry
      Yulang.GeneralDeclarationExamples.registry_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
      Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      demands →
    @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)) demands
      (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryEmissionPlanExamples.frame
        Yulang.GeneralDictionaryEmissionPlanExamples.root Yulang.GeneralDeclarationExamples.wrap
        Yulang.GeneralDeclarationExamples.wrap_checked)
Yulang.GeneralDictionaryEmissionPlanExamples.reversed_order : Yulang.GeneralRegistryReordering.Reorders
  Yulang.GeneralDeclarationExamples.registry Yulang.GeneralDictionaryEmissionPlanExamples.reversed
Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryEmissionPlanExamples.reversed
Yulang.GeneralDictionaryEmissionPlanExamples.reversed_same_plan : ∀
  (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Iff
    (Yulang.GeneralDictionaryEmissionPlans.Plan Yulang.GeneralDeclarationExamples.registry
      Yulang.GeneralDeclarationExamples.registry_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
      Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      demands)
    (Yulang.GeneralDictionaryEmissionPlans.Plan Yulang.GeneralDictionaryEmissionPlanExamples.reversed
      Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
      Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      demands)
Yulang.GeneralDictionaryPlanLookup.lookup_exact : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
  Iff
    (@Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)))
      (Yulang.GeneralDictionaryPlanLookup.lookup registry checked frame root key)
      (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)) demands))
    (Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key demands)
Yulang.GeneralDictionaryPlanLookup.lookup_none : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat),
  Iff
    (@Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)))
      (Yulang.GeneralDictionaryPlanLookup.lookup registry checked frame root key)
      (@none.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))))
    (∀ (demands : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)),
      Not (Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key demands))
Yulang.GeneralDictionaryPlanLookup.lookup_reorders : ∀ (constructors : Yulang.GeneralDeclarationPatterns.Constructors)
  (roles : Yulang.Roles.RoleDecls) (first last : List.{0} Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frame : Yulang.GeneralDictionaryEmissionPlans.Frame roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat),
      @Eq.{1}
        (Option.{0}
          (List.{0}
            (Yulang.GeneralSourceDictionaries.Occurrence
              { constructors := constructors, roles := roles, declarations := first }.roles)))
        (Yulang.GeneralDictionaryPlanLookup.lookup
          { constructors := constructors, roles := roles, declarations := first } one frame root key)
        (Yulang.GeneralDictionaryPlanLookup.lookup
          { constructors := constructors, roles := roles, declarations := last } two frame root key)
Yulang.GeneralDictionaryPlanLookupExamples.actual_lookup : @Eq.{1}
  (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDeclarationExamples.registry_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
    (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryEmissionPlanExamples.frame
      Yulang.GeneralDictionaryEmissionPlanExamples.root Yulang.GeneralDeclarationExamples.wrap
      Yulang.GeneralDeclarationExamples.wrap_checked))
Yulang.GeneralDictionaryPlanLookupExamples.missing_key : @Eq.{1}
  (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDeclarationExamples.registry_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99))))
  (@none.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
Yulang.GeneralDictionaryPlanLookupExamples.wrong_role : @Eq.{1}
  (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDeclarationExamples.registry_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (@none.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
Yulang.GeneralDictionaryPlanLookupExamples.reversed_lookup : @Eq.{1}
  (Option.{0}
    (List.{0}
      (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDictionaryEmissionPlanExamples.reversed
    Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked Yulang.GeneralDictionaryEmissionPlanExamples.frame
    Yulang.GeneralDictionaryEmissionPlanExamples.root (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
    (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDictionaryEmissionPlanExamples.frame
      Yulang.GeneralDictionaryEmissionPlanExamples.root Yulang.GeneralDeclarationExamples.wrap
      Yulang.GeneralDeclarationExamples.wrap_checked))
@Yulang.GeneralDictionaryPlannedEvidence.planned_children_functional : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional registry.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
      (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
@Yulang.GeneralDictionaryPlannedEvidence.lookup_node_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (located :
    @Yulang.GeneralDictionaryStateEquations.Located registry.roles state
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root)),
  @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)))
      (Yulang.GeneralDictionaryPlanLookup.lookup registry checked frame root key)
      (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)) children) →
    terms root key located →
      @Yulang.GeneralDictionaryStateEquations.Recorded state registry.roles
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root) located →
        @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
            Yulang.GeneralDictionaryReadback.Payload
            (@Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
              (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
                (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms)))
            children dictionaries →
          @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
            (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
              (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
            root (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryPlannedEvidence.lookup_node_all_models : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (located :
    @Yulang.GeneralDictionaryStateEquations.Located registry.roles state
      (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root)),
  @Eq.{1} (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)))
      (Yulang.GeneralDictionaryPlanLookup.lookup registry checked frame root key)
      (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)) children) →
    terms root key located →
      @Yulang.GeneralDictionaryStateEquations.Recorded state registry.roles
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root) located →
        @Yulang.CommonRoleOutermostResolver.All₂.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
            Yulang.GeneralDictionaryReadback.Payload
            (@Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
              (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
                (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms)))
            children dictionaries →
          ∀ (assignment : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models state assignment →
              @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
                (@Yulang.GeneralDictionaryModelEvidence.ModelInstance registry.roles state
                  (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms) assignment)
                root (Yulang.CommonRoleOutermostResolver.Dictionary.node key dictionaries)
@Yulang.GeneralDictionaryPlannedEvidence.planned_unique_readback : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
        (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
      root payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
      And
        (And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root payload tree)
          (@Yulang.GeneralSourceDictionaries.Evidence registry.roles
            (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
              (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
            tree))
        (∀ (other : Yulang.GeneralSourceDictionaries.Dictionary registry.roles),
          @Yulang.GeneralSourceDictionaries.Readback registry.roles root payload other →
            @Yulang.GeneralSourceDictionaries.Evidence registry.roles
                (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
                  (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
                other →
              @Eq.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) other tree)
@Yulang.GeneralDictionaryPlannedEvidence.planned_reordered_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (before after : Yulang.GeneralDictionaryReadback.Payload),
  Yulang.GeneralDictionaryPayloadOrder.Equivalent before after →
    @Yulang.GeneralDictionaryReadback.PayloadEvidence registry.roles
        (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
          (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
        root before →
      @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun tree =>
        And (@Yulang.GeneralSourceDictionaries.Readback registry.roles root after tree)
          (∀ (assignment : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models state assignment →
              @Yulang.GeneralSourceDictionaries.Evidence registry.roles
                (@Yulang.GeneralDictionaryModelEvidence.ModelInstance registry.roles state
                  (@Yulang.GeneralDictionarySemanticOrder.Unordered registry.roles state
                    (@Yulang.GeneralDictionaryPlannedEvidence.Planned state registry checked frame terms))
                  assignment)
                tree)
```
