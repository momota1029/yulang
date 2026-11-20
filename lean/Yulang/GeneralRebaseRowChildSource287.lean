import Yulang.GeneralRebaseRowHeadBoundary287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseRowChildSource287
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (bareRole outputRole)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev roles : Roles.RoleDecls := fun k => if k = 0 then outputRole 0 else bareRole
abbrev constructors : Constructors := fun k =>
  if k = 6 then some ⟨[.row],6⟩ else GeneralDeclarationExamples.constructors k
abbrev requirement : Clause := ⟨10,1,[.var 0],[]⟩
abbrev parentDecl : Declaration :=
  ⟨0,0,[.app 0 [.var 0]],[requirement],[⟨0,0,.app 0 [.app 0 [.var 0]]⟩],[]⟩
abbrev destructing : Declaration := ⟨1,1,[.app 6 [.var 0]],[],[],[]⟩
abbrev opaqueChild : Declaration := ⟨1,1,[.var 0],[],[],[]⟩
abbrev childDecl (useWhole : Bool) := if useWhole then opaqueChild else destructing
abbrev registry (useWhole : Bool) : Registry := ⟨constructors,roles,[parentDecl,childDecl useWhole]⟩

theorem parent_checked : DeclarationChecked constructors roles parentDecl := by
  constructor
  · simp [Declaration.Signature,Clause.Signature,roles,bareRole,Declared]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  · intro clause member; cases List.mem_singleton.mp member
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; cases List.mem_singleton.mp member
    unfold ConservativeSmaller; decide +kernel
  · intro clause member; cases List.mem_singleton.mp member
    exact unary_descent 0 0

theorem blocked_decl_checked : DeclarationChecked constructors roles destructing := by
  constructor
  · simp [Declaration.Signature,roles,bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

theorem opaque_checked : DeclarationChecked constructors roles opaqueChild := by
  constructor
  · simp [Declaration.Signature,roles,bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  · simp
  · simp
  · simp
  · simp

theorem checked (useWhole : Bool) : Checked (registry useWhole) := by
  refine ⟨by cases useWhole <;> decide +kernel,?_⟩
  intro d hd
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl
  · exact parent_checked
  · cases useWhole
    · exact blocked_decl_checked
    · exact opaque_checked

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ eq => Fin.ext eq
  rowSource := Fin.val
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ h; cases h
  intervals_sound := by intro _ _ _ h; cases h

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ h; cases h

abbrev inner : GeneralNominalState.Descriptor 3 := ⟨6,⟨[.row],6⟩,[.row (0,0)],rfl⟩
abbrev outer : GeneralNominalState.Descriptor 3 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev raw : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some inner else if slot = 1 then some outer else none
  catalogue := by
    intro slot d found
    split at found
    · cases Option.some.inj found; rfl
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  bodies_opaque := by intros; rfl
  seed := 2

abbrev interp : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun key => key == 0 || key == 6,fun _ _ => rfl⟩
abbrev ctx : GeneralNominalCandidates.Context := ⟨raw,interp⟩
abbrev root : Occurrence roles :=
  ⟨0,⟨0,fun _ => (1,1),[⟨0,2⟩],by intro o h; cases List.mem_singleton.mp h; exact ⟨none,rfl⟩⟩⟩
abbrev childAt (id : Nat) : Occurrence roles :=
  ⟨id,⟨1,fun _ => (0,0),[],by intro o h; cases h⟩⟩
abbrev before := GeneralNominalVersionedJournal232.initial ctx root

def R (r : Common.Row) : Ty := nominal 6 [.inr r]
def F (t : Ty) : Ty := nominal 0 [.inl t]
def model (row : Common.Row) : Assignment :=
  fun n => (if n = 0 then R row else if n = 1 then F (R row) else if n = 2 then F (F (R row)) else .base .int,
    if n = 0 then row else Common.rowEmpty)

theorem raw_model (row : Common.Row) : GeneralNominalState.Models raw (model row) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro _ member; cases member
  · intro _ _ found; cases found
  · intro _ member; cases member
  · intro slot d found
    change (if slot = (0 : Fin 3) then some inner else if slot = 1 then some outer else none) = some d at found
    split at found
    · rename_i same
      subst slot
      cases Option.some.inj found
      exact ⟨[.inr row],.cons ⟨Common.rowLe_refl _,Common.rowLe_refl _⟩ .nil,subtype_refl _,subtype_refl _⟩
    · split at found
      · rename_i same
        subst slot
        cases Option.some.inj found
        exact ⟨[.inl (R row)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,subtype_refl _,subtype_refl _⟩
      · cases found
  · intro _ member; cases member

theorem before_model (row : Common.Row) : GeneralNominalVersionedJournal232.Models before (model row) :=
  (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨raw_model row,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem known_child (id : Nat) : ¬ GeneralNominalState.RootPending raw (childAt id).demand := by
  rintro ⟨i,unknown⟩
  exact unknown ⟨(0 : Fin 3),rfl,Or.inr ⟨inner,rfl⟩⟩

theorem metadata (choice : Bool) : GeneralNominalRecursiveCandidates.Metadata (registry choice) ctx :=
  ⟨rfl,by intro _ _ impossible; cases impossible⟩

theorem source (choice : Bool) :
    GeneralNominalSourceFormation.InitialSource (registry choice) ctx root where
  roles_agree := rfl
  metadata := metadata choice
  linked := ⟨by intro i; change 1 ∈ GeneralNominalState.sources raw ∧ 1 ∈ GeneralNominalState.sources raw; exact ⟨by decide +kernel,by decide +kernel⟩,
    by intro out member; cases List.mem_singleton.mp member; decide +kernel⟩
  intervals := fun _ _ _ => subtype_refl _
  below_seed := by intro n member; simp [GeneralNominalState.sources,List.ofFn_succ] at member; change n ≤ 2; omega
  unallocated := rfl

end Yulang.GeneralRebaseRowChildSource287
