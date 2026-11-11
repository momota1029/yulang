import Yulang.B4TargetV3

/-!
# Independent functionality of the I-19 target

No executor, frontier exactness, checked-registry, accessibility or model
premise is used. These are finite-derivation uniqueness results, not totality
or a proof that the general source B4 target has been implemented.
-/
namespace Yulang.B4TargetV3
open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary SafeKnown Unique)
universe u
variable {v : Vocabulary.{u}} {b : SourceBoundary v} {r : v.Registry} {s : v.State} {d : v.Demand}

theorem rejection_not_pending (reason : RejectReason b r s d) : ¬ b.RootPending r s d := reason.1

theorem safe_survivor_not_rejected (safe : SafeKnown b r s d)
    (survivor : b.Survivor r s d key children) : ¬ RejectReason b r s d := by
  rintro ⟨_, root | candidate | empty⟩
  · exact safe.2.1 root
  · exact safe.2.2.1 candidate
  · exact empty.2 key children survivor

theorem unique_not_ambiguous (unique : Unique b r s d key children)
    (first : b.Survivor r s d key₁ cs₁) (last : b.Survivor r s d key₂ cs₂)
    (distinct : key₁ ≠ key₂) : False := by
  exact distinct ((unique.2 _ _ first).1.trans (unique.2 _ _ last).1.symm)

/-- Unfinished inspection is below either K2 reason and above empty rejection. -/
theorem inspection_not_rejected (pending : b.InspectionPending r s d)
    (root : ¬ b.RootK2 r s d) (candidate : ¬ b.CandidateK2 r s d) :
    ¬ RejectReason b r s d := by
  rintro ⟨_, hr | hc | he⟩
  · exact root hr
  · exact candidate hc
  · exact he.1 pending

/-- Functional on every abstract boundary, without a coherence premise. -/
theorem local_functional (first : Local b r s d left) (last : Local b r s d right) : left = right := by
  cases first with
  | pending pending =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (reason.1 pending)
      | ambiguous safe _ _ _ => exact False.elim (safe.1 pending)
      | selected safe _ => exact False.elim (safe.1 pending)
  | inspectionPending started pending root candidate =>
      cases last with
      | pending => rfl
      | inspectionPending => rfl
      | rejected reason => exact False.elim (inspection_not_rejected pending root candidate reason)
      | ambiguous safe _ _ _ => exact False.elim (safe.2.2.2 pending)
      | selected safe _ => exact False.elim (safe.2.2.2 pending)
  | rejected reason =>
      cases last with
      | pending pending => exact False.elim (reason.1 pending)
      | inspectionPending _ pending root candidate =>
          exact False.elim (inspection_not_rejected pending root candidate reason)
      | rejected => rfl
      | ambiguous safe survivor _ _ => exact False.elim (safe_survivor_not_rejected safe survivor reason)
      | selected safe unique => exact False.elim (safe_survivor_not_rejected safe unique.1 reason)
  | ambiguous safe survivorFirst survivorLast distinct =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (safe_survivor_not_rejected safe survivorFirst reason)
      | ambiguous => rfl
      | selected _ unique => exact False.elim (unique_not_ambiguous unique survivorFirst survivorLast distinct)
  | selected safe unique =>
      cases last with
      | pending pending => exact False.elim (safe.1 pending)
      | inspectionPending _ pending _ _ => exact False.elim (safe.2.2.2 pending)
      | rejected reason => exact False.elim (safe_survivor_not_rejected safe unique.1 reason)
      | ambiguous _ first last distinct => exact False.elim (unique_not_ambiguous unique first last distinct)
      | selected _ other =>
          obtain ⟨keys, children⟩ := unique.2 _ _ other.1
          cases keys
          cases children
          rfl

mutual
  theorem resolves_functional (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (left right : Tree) (d : v.Demand) (first : Resolves (Local b r s) d left)
      (last : Resolves (Local b r s) d right) : left = right := by
    cases first with
    | pending localFirst =>
        cases last with
        | pending => rfl
        | rejected localLast => cases local_functional localFirst localLast
        | ambiguous localLast => cases local_functional localFirst localLast
        | selected localLast _ => cases local_functional localFirst localLast
    | rejected localFirst =>
        cases last with
        | rejected => rfl
        | pending localLast => cases local_functional localFirst localLast
        | ambiguous localLast => cases local_functional localFirst localLast
        | selected localLast _ => cases local_functional localFirst localLast
    | ambiguous localFirst =>
        cases last with
        | ambiguous => rfl
        | pending localLast => cases local_functional localFirst localLast
        | rejected localLast => cases local_functional localFirst localLast
        | selected localLast _ => cases local_functional localFirst localLast
    | selected localFirst childrenFirst =>
        cases last with
        | pending localLast => cases local_functional localFirst localLast
        | rejected localLast => cases local_functional localFirst localLast
        | ambiguous localLast => cases local_functional localFirst localLast
        | selected localLast childrenLast =>
            cases local_functional localFirst localLast
            exact congrArg _ (resolves_children_functional b r s _ _ _ childrenFirst childrenLast)
  termination_by sizeOf left

  theorem resolves_children_functional (b : SourceBoundary v) (r : v.Registry) (s : v.State)
      (left right : List Tree) (demands : List v.Demand)
      (first : All₂ (Resolves (Local b r s)) demands left)
      (last : All₂ (Resolves (Local b r s)) demands right) : left = right := by
    cases first with
    | nil => cases last; rfl
    | cons first rest =>
        cases last with
        | cons other others =>
            exact congr (congrArg List.cons (resolves_functional b r s _ _ _ first other))
              (resolves_children_functional b r s _ _ _ rest others)
  termination_by sizeOf left
end

/-- The independent four-way judgment is functional without any executor premise. -/
theorem classify_functional (first : Classify b r s d left) (last : Classify b r s d right) :
    left = right := by
  obtain ⟨tree, resolved, done⟩ := classify_tree first
  obtain ⟨other, otherResolved, otherDone⟩ := classify_tree last
  have same := resolves_functional b r s _ _ _ resolved otherResolved
  subst other
  exact B4Skeleton.completed_unique done otherDone

/-- In particular, the old pending/empty-survivor obstruction cannot recur,
even when either abstract K2 flag also holds. No emptiness premise is needed. -/
theorem pending_only (pending : b.RootPending r s d) (out : Result) :
    Classify b r s d out ↔ out = .pending := by
  constructor
  · intro derived
    exact classify_functional derived (.pending pending)
  · rintro rfl
    exact .pending pending

theorem pending_tree_only (pending : b.RootPending r s d) (tree : Tree) :
    Resolves (Local b r s) d tree ↔ tree = .pending := by
  constructor
  · intro derived
    exact resolves_functional b r s _ _ _ derived (.pending (.pending pending))
  · rintro rfl
    exact .pending (.pending pending)

/-- Exact tree execution induces exactly the partial completed classification,
without silently asserting that every diagnostic tree is complete. -/
theorem completed_exact (b : SourceBoundary v) (e : Executor v) (exact : Exact b e)
    (r : v.Registry) (checked : b.Checked r) (s : v.State) (d : v.Demand) (out : Result) :
    Completed (e.run r s d).2 out ↔ Classify b r (e.run r s d).1 d out := by
  constructor
  · intro done
    exact tree_classifies b r _ _ d out ((exact r checked s d _).mp rfl) done
  · intro derived
    obtain ⟨tree, resolved, done⟩ := classify_tree derived
    rw [(exact r checked s d tree).mpr resolved]
    exact done

end Yulang.B4TargetV3
