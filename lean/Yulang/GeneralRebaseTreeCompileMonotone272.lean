import Yulang.GeneralRebaseCanonicalUniqueness272

namespace Yulang.GeneralRebaseTreeCompileMonotone272
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatSchemas (Schema)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseTreeExprCompile272 (Env compile many)
open GeneralRebaseTreeSchema272 (compute entry enrich enrich_sound environment)
open GeneralRebaseTreeInterpreter272 (Source Certified)
open GeneralRebaseFiniteTree272 (Tree)

def Extends (first last : Source) : Prop := ∀ id tree, first id = some tree → last id = some tree

def EnvExtends (first last : Env) : Prop :=
 ∀ mode id tree, first mode id = some tree → last mode id = some tree

theorem extends_trans {a b c : Source} (ab : Extends a b) (bc : Extends b c) :
 Extends a c := fun id t h => bc id t (ab id t h)

mutual
  theorem compile_mono (a b : Env) (more : EnvExtends a b) (mode : Mode) (term : Expr)
    (tree : Tree) (found : compile a mode term = some tree) : compile b mode term = some tree := by
    cases term with
    | «variable» id => exact more mode id tree found
    | primitive p args =>
      cases old : many a mode args with
      | none => simp [compile,old] at found
      | some xs =>
        have bigger := many_mono a b more mode args xs old
        simpa [compile,bigger] using (show (some xs).bind (GeneralRebaseTreeExprCompile272.primitive p) = _ by simpa [compile,old] using found)
    | nominal name args =>
      cases old : many a .actual args with
      | none => simp [compile,old] at found
      | some xs =>
        have bigger := many_mono a b more .actual args xs old
        simpa only [compile,bigger,Option.map_some] using (by simpa only [compile,old,Option.map_some] using found : some (GeneralRebaseTreeConstructors272.nominalTree name xs) = some tree)
    | record key body tail =>
      cases one : compile a mode body with
      | none => simp [compile,one,Bind.bind,Option.bind] at found
      | some first =>
        cases two : compile a mode tail with
        | none => simp [compile,one,two,Bind.bind,Option.bind] at found
        | some rest =>
          have left := compile_mono a b more mode body first one
          have right := compile_mono a b more mode tail rest two
          have check : GeneralRebaseTreeRecordBuild272.appendField key first rest = some tree := by
            simpa [compile,one,two,Bind.bind,Option.bind] using found
          simpa [compile,left,right,Bind.bind,Option.bind] using check
    | variant name child =>
      cases old : compile a mode child with
      | none => simp [compile,old] at found
      | some t =>
        have bigger := compile_mono a b more mode child t old
        simpa only [compile,bigger,Option.map_some] using (by simpa only [compile,old,Option.map_some] using found : some (GeneralRebaseTreeConstructors272.variantTree name t) = some tree)
    | join x y => cases found
  theorem many_mono (a b : Env) (more : EnvExtends a b) (mode : Mode) (terms : List Expr)
    (trees : List Tree) (found : many a mode terms = some trees) : many b mode terms = some trees := by
    cases terms with
    | nil => exact found
    | cons head tail =>
      cases one : compile a mode head with
      | none => simp [many,one,Bind.bind,Option.bind] at found
      | some first =>
        cases two : many a mode tail with
        | none => simp [many,one,two,Bind.bind,Option.bind] at found
        | some rest =>
          have left := compile_mono a b more mode head first one
          have right := many_mono a b more mode tail rest two
          have eq : first::rest = trees := Option.some.inj (by simpa [many,one,two,Bind.bind,Option.bind] using found)
          simp [many,left,right,Bind.bind,Option.bind,eq]
end

theorem entry_mono (a b : Env) (more : EnvExtends a b) (id : Nat)
 (eq : GeneralNominalCenteredHeadMatSchemas.Equation) (t : Tree) (found : entry a id eq = some t) :
 entry b id eq = some t := by
 unfold entry at found ⊢
 by_cases matchID : eq.target = id
 · simpa [matchID] using compile_mono a b more eq.mode eq.expression t (by simpa [matchID] using found)
 · simp [matchID] at found

theorem compute_mono_support (a b : Env) (more : EnvExtends a b) (schema : Schema)
 (id : Nat) (t : Tree) (found : compute a schema id = some t) :
 ∃ u, compute b schema id = some u := by
 obtain ⟨xs,eq,ys,whereAt,selected,_⟩ := List.findSome?_eq_some_iff.mp found
 have inSchema : eq ∈ schema.equations := by rw [whereAt]; exact List.mem_append_right _ List.mem_cons_self
 cases now : compute b schema id with
 | none =>
   have no := List.findSome?_eq_none_iff.mp now eq inSchema
   rw [entry_mono a b more id eq t selected] at no
   cases no
 | some u => exact ⟨u,rfl⟩

theorem enrich_mono (m : Assignment) (a b : Source) (more : Extends a b)
 (ac : Certified m a) (bc : Certified m b) (plan : GeneralNominalCenters.Plan roles)
 (valid : GeneralNominalVersionedPlans231.Outputs plan m) : Extends (enrich a plan) (enrich b plan) := by
 intro id t found
 have left := enrich_sound a plan m ac valid
 have right := enrich_sound b plan m bc valid
 suffices existsHit : ∃ u, enrich b plan id = some u by
   obtain ⟨u,hit⟩ := existsHit
   have e := GeneralRebaseCanonicalUniqueness272.source_agree m _ _ left right id t u found hit
   exact e.symm ▸ hit
 cases oldB : b id with
 | some val => exact ⟨val,GeneralRebaseTreeSchema272.enrich_preserves_source _ _ _ _ oldB⟩
 | none =>
   cases oldA : a id with
   | some earlier =>
     have impossible := more id earlier oldA
     rw [oldB] at impossible
     cases impossible
   | none =>
     have real : compute (environment plan a) (GeneralNominalVersionedPlans231.emittedSchema plan) id = some t := by
       simpa [enrich,oldA,Option.or] using found
     obtain ⟨val,known⟩ := compute_mono_support (environment plan a) (environment plan b)
       (fun _ _ _ h => more _ _ h) _ id t real
     exact ⟨val,by simpa [enrich,oldB,Option.or] using known⟩

end Yulang.GeneralRebaseTreeCompileMonotone272
