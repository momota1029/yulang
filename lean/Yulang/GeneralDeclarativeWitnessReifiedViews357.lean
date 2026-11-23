import Yulang.GeneralDeclarativeWitnessClassifyVariance357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReifiedViews357
open GeneralDeclarativeWitnessDeclaredState357
  (Current AuthoredNominal Value Views Seen ModelsCurrent authoredRegistry evaluate)
open GeneralDeclarativeWitnessClassifyVariance357 (SourceChecked Rule Evidence dictionary_sound)
open GeneralDeclarativeWitnessModeCoverage357 (Coverage)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralSourceMetadataFiniteLookup291 (get some_complete some_sound)
open CommonRoleOutermostResolver (Classify)

def table (s : Current) := s.visible.map fun row => (row.place,row)
def body (m : Assignment) (r : AuthoredNominal) : Value := ⟨r.tag,r.name,r.arguments.map (evaluate m)⟩
def modelViews (s : Current) (m : Assignment) : Views :=
  fun key => (get key (table s)).map (body m)

theorem exact_at {s : Current} (unique : (s.visible.map AuthoredNominal.place).Nodup)
    (m : Assignment) {r : AuthoredNominal} (authored : r ∈ s.visible) :
    modelViews s m r.place = some (body m r) := by
  have alone : ((table s).map Prod.fst).Nodup := by simpa only [table,List.map_map,Function.comp_def] using unique
  have wrote : (r.place,r) ∈ table s := List.mem_map.mpr ⟨r,authored,rfl⟩
  simp only [modelViews,some_complete alone wrote,Option.map_some]

theorem no_unsourced {s : Current} {m : Assignment} {place val}
    (held : modelViews s m place = some val) :
    ∃ row ∈ s.visible,row.place = place ∧ val = body m row := by
  unfold modelViews at held
  obtain ⟨row,position,out⟩ := Option.map_eq_some_iff.mp held
  obtain ⟨written,authored,found⟩ := List.mem_map.mp (some_sound position)
  cases found
  exact ⟨row,authored,rfl,out.symm⟩

theorem models_extend {s : Current} (one : (s.visible.map AuthoredNominal.place).Nodup)
    (m : Assignment) (fit : Models s.ordinary m) : ModelsCurrent s m (modelViews s m) :=
  ⟨fit,fun _ h => ⟨_,exact_at one m h,rfl,rfl,rfl⟩⟩

theorem dictionary_every_ordinary_model {s : Current}
    (checked : SourceChecked s) (coverage : Coverage s.environment)
    (one : (s.visible.map AuthoredNominal.place).Nodup)
    (asked : Declared (authoredRegistry s) d) (selected : Classify (Rule s) d (.selected dict)) :
    ∀ m : Assignment, Models s.ordinary m →
      ModelsCurrent s m (modelViews s m) ∧ Evidence s m (modelViews s m) d dict := by
  intro m fit
  have fitted := models_extend one m fit
  exact ⟨fitted,dictionary_sound checked coverage asked selected m (modelViews s m) fitted⟩

end Yulang.GeneralDeclarativeWitnessReifiedViews357
