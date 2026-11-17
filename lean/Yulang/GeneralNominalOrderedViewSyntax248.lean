import Yulang.GeneralNominalRebaseViewSubst243
import Yulang.GeneralPresenceOrderedSyntax247
/-! Literal absorption of repeated ordered rewrites on the actual expression
raw View, including slots, heads, descriptor parameters and ordinary atoms.
The input view is fixed; adding fresh observations or changing live bodies is
not covered. This is not global solver termination. -/
namespace Yulang.GeneralNominalOrderedViewSyntax248
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSyntax247
open GeneralNominalRebaseRawView243

variable (old fresh : List (Entry Nat)) (safe : SafeOrder old) (within : TargetsWithin fresh old)
include safe within

theorem comp_absorbs (term : CompTerm Nat) :
 (term.subst (mapping old)).subst (mapping fresh) = term.subst (mapping old) := by
 cases term
 simp only [CompTerm.subst,type_absorbs old fresh safe within,row_fixed]

theorem parameter_absorbs (value : Parameter) :
 GeneralNominalRebaseViewSubst243.parameter (mapping fresh)
   (GeneralNominalRebaseViewSubst243.parameter (mapping old) value) =
 GeneralNominalRebaseViewSubst243.parameter (mapping old) value := by
 cases value <;> simp only [GeneralNominalRebaseViewSubst243.parameter,type_absorbs old fresh safe within,row_fixed]

theorem descriptor_absorbs (value : Descriptor) :
 GeneralNominalRebaseViewSubst243.descriptor (mapping fresh)
   (GeneralNominalRebaseViewSubst243.descriptor (mapping old) value) =
 GeneralNominalRebaseViewSubst243.descriptor (mapping old) value := by
 cases value
 simp only [GeneralNominalRebaseViewSubst243.descriptor,List.map_map,Function.comp_def,parameter_absorbs old fresh safe within]

theorem atom_absorbs (value : Atom) :
 atom (mapping fresh) (atom (mapping old) value) = atom (mapping old) value := by
 cases value <;> simp only [atom,type_absorbs old fresh safe within,row_fixed]

theorem view_absorbs (view : View) :
 GeneralNominalRebaseViewSubst243.subst (GeneralNominalRebaseViewSubst243.subst view (mapping old)) (mapping fresh) =
 GeneralNominalRebaseViewSubst243.subst view (mapping old) := by
 cases view
 simp only [GeneralNominalRebaseViewSubst243.subst,comp_absorbs old fresh safe within,
   List.map_map,Option.map_map,Function.comp_def,atom_absorbs old fresh safe within,
   type_absorbs old fresh safe within,descriptor_absorbs old fresh safe within]
end Yulang.GeneralNominalOrderedViewSyntax248
