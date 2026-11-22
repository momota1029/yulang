import Yulang.GeneralDeclarativeWitnessFreshness351
import Yulang.GeneralDeclarativeWitnessCatalog351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReleaseExact351
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessIdentity351 (Owned Key table writer release_exact)
open GeneralDeclarativeWitnessCatalog351 (Anchor Receipt WriteAnchor proves_writes)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessOrigins350 (support)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

theorem fixed_slot {s : State} {block : Fixed} {idx : Nat} {e : GeneralDeclarativeHead320.Equation}
    (meaning : Fixed.Meaning block s) (found : block.equations[idx]? = some e) :
    ∃ out : Output, block.demand.outputs[idx]? = some out ∧ out.target = e.left := by
  have located := congrArg (fun (ls : List Nat) => ls[idx]?) meaning.1
  simp only [List.getElem?_map,found,Option.map_some] at located
  cases output : block.demand.outputs[idx]? with
  | none => simp [output] at located
  | some request =>
    rw [output] at located
    exact ⟨request,rfl,(Option.some.inj located).symm⟩

/-- The exact ordered publisher output from the replayed trace fixes
the request name and logical target, not just a matching ordinary row. -/
theorem writes_at_request {p : Anchor} {code report} (accepted : Receipt p code report)
    {row : Owned} (listed : row ∈ accepted.owned)
    (m : Assignment) (fit : Models p.roles.current m) :
    ∃ loc ∈ p.required, ∃ fs ∈ accepted.producer.diagnostic.fixed, ∃ request,
      fs.demand.outputs[loc.ordinal]? = some request ∧ request.target = row.key.target ∧
      fs.equations[loc.ordinal]? = some row.equation ∧
      row.key = ⟨fs.path,fs.demand.role,loc.producer.version,loc.ordinal,row.equation.left⟩ ∧
      GeneralDeclarativeEntailment320.Holds m row.equation := by
  obtain ⟨loc,used,fs,known,path,role,index,key,model⟩ := proves_writes accepted m fit row listed
  obtain ⟨out,there,output⟩ := fixed_slot (accepted.producer.diagnostic.fixedMeaning fs known) index
  refine ⟨loc,used,fs,known,out,there,?_,index,?_,model⟩
  · rw [key]
    exact output
  · simpa only [path,role] using key

theorem exact_release_eligible {p : Anchor} {code report} (accepted : Receipt p code report)
    {idx : Nat} {row : Owned} (point : accepted.owned[idx]? = some row) (released : row.key ∈ p.releases) :
    row.equation ∈ (restriction (support accepted.catalogue)).equations := by
  apply GeneralDeclarativeOrigins321.from_completed (owner := idx)
  · exact writer point
  · exact (release_exact point).mpr released

/-- This is occurrence-local. The same equation may have another
authorized origin, so the absence of one release does not advertise a
global no-head result. -/
theorem release_owner_exact {p : Anchor} {code report} (accepted : Receipt p code report)
    {idx : Nat} {row : Owned} (point : accepted.owned[idx]? = some row) :
    GeneralDeclarativeOrigins321.Available
      (· ∈ (table p.authored accepted.owned p.releases).released) (.output idx) ↔ row.key ∈ p.releases := by
  constructor
  · intro a
    cases a with
    | completed known => exact (release_exact point).mp known
  · intro a
    exact .completed ((release_exact point).mpr a)

end Yulang.GeneralDeclarativeWitnessReleaseExact351
