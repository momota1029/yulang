import Yulang.GeneralDeclarativeEndpointSelected336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointLink336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointOverlay336 (ModelsWith)
open GeneralDeclarativeEndpointSelected336 (Selected Node Clash ties_exact selected_sound)
open GeneralDeclarativeEndpointBody336 (Body)
open GeneralDeclarativeEndpointInput336 (sources)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeStableTies329 (pairOf from_use)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeProducedNames325 (exact_input)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarations (Checked)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonNominalFullCarrier (Equivalent)

/-- The actual compiled binder table, not just any model which
happens to satisfy the body, uses an equivalent center for every
projected or old syntactic occurrence. -/
theorem selected_centers {s : State} {p : Supported s done}
    (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (m) (fit : ModelsWith s sidecar m) :
    ∃ cap, Node r i m d impl cap kids w.spans ∧
      ∀ entry ∈ w.spans, Equivalent (m entry.2.center).1 (m (cap entry.1).center).1 := by
  have visible := w.chosen.viable.1.1
  have role := w.chosen.viable.1.2
  obtain ⟨body,exactSpans,_,ties⟩ := w.toGenerated.body checked covered wanted visible role
  have valid := relays_models w.receipt m fit.1
  have known : Models (tieState w.named w.spans w.fallback) m := restrict ties m valid
  have shared : EqualUses m w.spans :=
    ((ties_exact w.named sidecar w.spans w.fallback m).mp ⟨known,fit.2⟩).2
  have source := GeneralDeclarativeEndpointInput336.observed w.source
    (GeneralDeclarativeClauseBatch327.reflexive _)
    (GeneralDeclarativeGrowth327.trans (GeneralDeclarativeGrowth327.facts _ _) ties) m valid
    (fun e active => fit.2 e (w.readback active))
  obtain ⟨mBody,_⟩ := GeneralDeclarativeEndpointBody336.sound body checked covered visible role wanted m valid
  refine ⟨body.capture,⟨source,shared,mBody⟩,?_⟩
  intro entry active
  have use : pairOf entry ∈ body.spans.map pairOf :=
    List.mem_map.mpr ⟨entry,exactSpans.symm ▸ active,rfl⟩
  have meaning := from_use body.tied use m valid
  have name : entry.1 ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,
      ← (sources w.source (GeneralDeclarativeClauseBatch327.reflexive _)).2.2]
    exact List.mem_map.mpr ⟨entry,active,rfl⟩
  change Equivalent (m entry.2.center).1 (m (body.capture entry.1).center).1
  unfold Body.capture sourceNames
  rw [exact_input (checked.2 impl visible) name]
  exact meaning

theorem no_model_if_same_clash {s : State} {p : Supported s done}
    (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (bad : Clash w.named w.reads w.spans w.fallback) :
    ¬∃ m, ModelsWith s sidecar m := by
  intro ⟨m,fit⟩
  obtain ⟨b,_,_,tied⟩ := w.toGenerated.body checked covered wanted w.chosen.viable.1.1 w.chosen.viable.1.2
  exact bad.2 ⟨m,restrict tied m (relays_models w.receipt m fit.1),
    fun e active => fit.2 e (w.readback active)⟩

end Yulang.GeneralDeclarativeEndpointLink336
