import Yulang.PresenceNormalForm
namespace Yulang.GeneralPresenceDefinitionRewrite244
open Core.PresenceGeneration
open PresenceNormalForm

abbrev Entry (Name : Type) := Name × TyTerm Name

def equations (target : Name) (term : TyTerm Name) : List (Atom Name) :=
 [.tyLe (.var target) term,.tyLe term (.var target)]

def atomSubst (mapping : Name → CompTerm Name) : Atom Name → Atom Name
 | .tyLe left right => .tyLe (left.subst mapping) (right.subst mapping)
 | .rowLe left right => .rowLe (left.subst mapping) (right.subst mapping)

def transform (mapping : Name → CompTerm Name) (entries : List (Entry Name)) : List (Entry Name) :=
 entries.map (fun entry => (entry.1,entry.2.subst mapping))

def block (entries : List (Entry Name)) : List (Atom Name) :=
 entries.flatMap (fun entry => equations entry.1 entry.2)

theorem equations_subst (mapping : Name → CompTerm Name) (target : Name) (term : TyTerm Name)
 (kept : (mapping target).ty = .var target) :
 (equations target term).map (atomSubst mapping) = equations target (term.subst mapping) := by
 simp only [equations,List.map_cons,List.map_nil,atomSubst,TyTerm.subst,kept]

theorem block_subst (mapping : Name → CompTerm Name) (entries : List (Entry Name))
 (kept : ∀ entry ∈ entries, (mapping entry.1).ty = .var entry.1) :
 (block entries).map (atomSubst mapping) = block (transform mapping entries) := by
 induction entries with
 | nil => rfl
 | cons entry rest ih =>
   simp only [block,List.flatMap_cons,List.map_append,transform,List.map_cons]
   rw [equations_subst mapping entry.1 entry.2 (kept entry (by simp))]
   have tail := ih (fun item member => kept item (List.mem_cons_of_mem _ member))
   simpa only [block,transform] using congrArg (fun xs => equations entry.1 (entry.2.subst mapping) ++ xs) tail

theorem atom_exact (mapping : Name → CompTerm Name) (atom : Atom Name)
 (model : Model) (assignment : Name → Comp model) :
 (atomSubst mapping atom).Holds model assignment ↔
 atom.Holds model (fun name => (mapping name).eval model assignment) := by
 cases atom <;> simp only [atomSubst,Atom.Holds,TyTerm.eval_subst,RowTerm.eval_subst]

theorem block_exact (mapping : Name → CompTerm Name) (entries : List (Entry Name))
 (kept : ∀ entry ∈ entries, (mapping entry.1).ty = .var entry.1)
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (block (transform mapping entries)) ↔
 All model (fun name => (mapping name).eval model assignment) (block entries) := by
 rw [← block_subst mapping entries kept]
 simp only [All,List.forall_mem_map,atom_exact]

/-- Target names remain literal. The row component is unrestricted: these
are type equations, and no row equation is erased by this adapter. -/
theorem targets_preserved (mapping : Name → CompTerm Name) (entries : List (Entry Name)) :
 (transform mapping entries).map Prod.fst = entries.map Prod.fst := by
 simp [transform,List.map_map]
end Yulang.GeneralPresenceDefinitionRewrite244
