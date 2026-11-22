import Yulang.GeneralDeclarativeMixedTree339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedLeaf339
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeCompoundSources338 (Anchored Anchors)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeArityPlan330 (Shape)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

def Reader (s : State) (mode : Mode) (source code : Expr) : Prop :=
  ∀ t, Extends s t → ∀ n, Anchored t n source → ∃ uses, Trace t mode n code uses

theorem read_binder (s : State) (mode : Mode) (source : Expr) (n : Nat) : Reader s mode source (.variable n) :=
  fun _ _ _ _ => ⟨_,.capture⟩

theorem read_variant {s : State}
    (child : ∀ t, Extends s t → ∃ uses, Trace t mode name code uses) :
    Reader s mode (.variant tag (.variable name)) (.variant tag code) := by
  intro t grown n rhs
  obtain ⟨owner,equated,stored⟩ := rhs
  obtain ⟨uses,read⟩ := child t grown
  exact ⟨uses,.variant equated stored read⟩

theorem read_nominal {s : State}
    (kids : ∀ t, Extends s t → ∃ uses, TraceArgs t .actual names codes uses) :
    Reader s mode (.nominal tag (names.map Expr.variable)) (.nominal tag codes) := by
  intro t grown n rhs
  obtain ⟨owner,equated,stored⟩ := rhs
  obtain ⟨uses,read⟩ := kids t grown
  exact ⟨uses,.nominal equated stored read⟩

theorem read_primitive {s : State}
    (kids : ∀ t, Extends s t → ∃ uses, TraceArgs t mode names codes uses) :
    Reader s mode (.primitive tag (names.map Expr.variable)) (.primitive tag codes) := by
  intro t grown n rhs
  obtain ⟨owner,equated,stored⟩ := rhs
  obtain ⟨uses,read⟩ := kids t grown
  exact ⟨uses,.primitive equated stored read⟩

/-- The source data for the independently approved finite leaf cases:
actual lower and upper expressions, old recognized translation shape,
and their supported reads under later ordinary growth. -/
def ReadyLeaf (c : Constructors) (i : Interpretation) (s : State) (lo hi : Expr) (p : Pattern) : Prop :=
  ∃ code, translate c i (normalize p) = some code ∧ Shape code ∧
    Reader s .lower lo code ∧ Reader s .upper hi code

theorem registered_variant {c : Constructors} {i : Interpretation}
    (mode : translate c i (normalize p) = some (.variant tag (.variable n))) (s : State) :
    ReadyLeaf c i s (.variant tag (.variable left)) (.variant tag (.variable right)) p :=
  ⟨_,mode,.tagged .capture,read_variant (fun _ _ => ⟨_,.capture⟩),
    read_variant (fun _ _ => ⟨_,.capture⟩)⟩

theorem ready_leaf {s t : State} {q : Supported t done}
    (read : ReadyLeaf c i s lo hi p) (grew : Extends s (restriction q))
    (incoming : Anchors (restriction q) a lo hi) (valid : Bounds t a) :
    Matches (restriction q) c i a p ∧
      ∀ code, translate c i (normalize p) = some code → Shape code := by
  obtain ⟨code,written,shape,left,right⟩ := read
  obtain ⟨l,low⟩ := left _ grew _ incoming.1
  obtain ⟨r,high⟩ := right _ grew _ incoming.2
  exact ⟨⟨valid,code,l,r,written,low,high⟩,
    fun _ same => Option.some.inj (written.symm.trans same) ▸ shape⟩

end Yulang.GeneralDeclarativeMixedLeaf339
