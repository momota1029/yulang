import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

namespace Yulang.GeneralRebaseCompoundExpr273
open GeneralNominalCenteredHeadMatExpressions
open GeneralNominalMaterialization (Mode)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier

abbrev Env := Mode → Nat → Option Ty

def Certified (env : Env) (vars : Mode → Nat → Ty) : Prop :=
 ∀ mode n t, env mode n = some t → Equivalent (vars mode n) t

mutual
def run (env : Env) (mode : Mode) : Expr → Option Ty
 | .variable name => env mode name
 | .primitive p args => (runMany env mode args).map (primitiveValue p)
 | .nominal name args => (runMany env .actual args).map (fun ts => nominal name (ts.map Sum.inl))
 | .record n body tail => do pure (record n (← run env mode body) (← run env mode tail))
 | .variant n body => (run env mode body).map (variant n)
 | .join a b => do pure (.union (← run env mode a) (← run env mode b))
def runMany (env : Env) (mode : Mode) : List Expr → Option (List Ty)
 | [] => some []
 | e::es => do pure ((← run env mode e) :: (← runMany env mode es))
end

mutual
theorem sound (env : Env) (vars : Mode → Nat → Ty) (cert : Certified env vars)
 (mode : Mode) (e : Expr) (t : Ty) (hit : run env mode e = some t) :
 Equivalent (value vars mode e) t := by
 cases e with
 | «variable» n => exact cert mode n t hit
 | primitive p es =>
   obtain ⟨ts,read,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [run] using hit)
   exact GeneralNominalCenteredHeadMatCompilerSemantics.primitive_congr p (many_sound env vars cert mode es ts read)
 | nominal n es =>
   obtain ⟨ts,read,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [run] using hit)
   exact GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr n (many_sound env vars cert .actual es ts read)
 | record n b r =>
   cases hb : run env mode b with
   | none => simp [run,hb,Bind.bind,Option.bind] at hit
   | some t1 =>
     cases hr : run env mode r with
     | none => simp [run,hb,hr,Bind.bind,Option.bind] at hit
     | some t2 =>
        have shape : record n t1 t2 = t := Option.some.inj (by simpa [run,hb,hr,Bind.bind,Option.bind] using hit)
        rw [← shape]
        have x := sound env vars cert mode b t1 hb
        have y := sound env vars cert mode r t2 hr
        exact ⟨common_record_mono n x.1 y.1,common_record_mono n x.2 y.2⟩
 | variant n e =>
   obtain ⟨s,read,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [run] using hit)
   have same := sound env vars cert mode e s read
   exact ⟨(common_variant_iff ..).mpr same.1,(common_variant_iff ..).mpr same.2⟩
 | join a b =>
   cases ha : run env mode a with
   | none => simp [run,ha,Bind.bind,Option.bind] at hit
   | some t1 =>
     cases hb : run env mode b with
     | none => simp [run,ha,hb,Bind.bind,Option.bind] at hit
     | some t2 =>
        have shape : (.union t1 t2 : Ty) = t := Option.some.inj (by simpa [run,ha,hb,Bind.bind,Option.bind] using hit)
        rw [← shape]
        have x := sound env vars cert mode a t1 ha
        have y := sound env vars cert mode b t2 hb
        exact ⟨common_union_mono x.1 y.1,common_union_mono x.2 y.2⟩
theorem many_sound (env : Env) (vars : Mode → Nat → Ty) (cert : Certified env vars)
 (mode : Mode) (es : List Expr) (ts : List Ty) (hit : runMany env mode es = some ts) :
 Aligned Equivalent (values vars mode es) ts := by
 cases es with
 | nil =>
   cases Option.some.inj hit
   exact .nil
 | cons a rest =>
   cases ha : run env mode a with
   | none => simp [runMany,ha,Bind.bind,Option.bind] at hit
   | some t =>
     cases hr : runMany env mode rest with
     | none => simp [runMany,ha,hr,Bind.bind,Option.bind] at hit
     | some tail =>
        have shape : t::tail = ts := Option.some.inj (by simpa [runMany,ha,hr,Bind.bind,Option.bind] using hit)
        rw [← shape]
        exact .cons (sound env vars cert mode a t ha) (many_sound env vars cert mode rest tail hr)
end
end Yulang.GeneralRebaseCompoundExpr273
