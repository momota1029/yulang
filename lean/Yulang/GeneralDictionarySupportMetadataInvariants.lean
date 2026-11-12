import Yulang.GeneralDictionarySupportSourceInvariants

/-! Actual support transitions preserve the query translation metadata even
when observation descriptors and interval syntax change. -/
namespace Yulang.GeneralDictionarySupportMetadataInvariants
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

def key (context : GeneralNominalCandidates.Context) :=
  (context.state.constructors,context.interpretation)

theorem administrative_key {registry : Registry} {before after : State roles} {focus : Occurrence roles}
    (step : Administrative registry before focus after) : key after.context = key before.context := by
  cases step with
  | enqueue => rfl
  | refresh _ certificate => exact Prod.ext certificate.refines.constructors certificate.interpretation
  | equate => rfl
  | reobserve => rfl

theorem step_key {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (step : Step registry root before after) : key after.current.context = key before.current.context := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative _ _ update => exact administrative_key update
  | install packet support enabled =>
    change key packet.context = key before.current.context
    exact congrArg key enabled.1.2.1
  | merge => rfl

theorem steps_key {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) :
    key after.current.context = key before.current.context := by
  induction path with
  | refl => rfl
  | tail prior update ih => exact (step_key update).trans ih

theorem packet_key (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state) (packet : Packet roles) (member : packet ∈ state.current.packets) :
    key packet.context = key state.current.context := by
  obtain ⟨before,support,_,_,_,_,_,path⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
  exact (steps_key path).symm

/-- Any current translation is literally the same translation in the stored
context, not just an observational or model-dependent equivalence. -/
theorem packet_translate (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state) (packet : Packet roles) (member : packet ∈ state.current.packets)
    (pattern : GeneralDeclarationPatterns.Pattern) :
    GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation pattern =
    GeneralNominalInspection.translate state.current.context.state.constructors state.current.context.interpretation pattern := by
  have keys := packet_key registry root state formed packet member
  have constructors := congrArg Prod.fst keys
  have interpretation := congrArg Prod.snd keys
  change packet.context.state.constructors = state.current.context.state.constructors at constructors
  change packet.context.interpretation = state.current.context.interpretation at interpretation
  rw [constructors,interpretation]

theorem packet_queries (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state) (packet : Packet roles) (member : packet ∈ state.current.packets) :
    GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
    GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation packet.declaration := by
  unfold GeneralNominalInspection.queries
  apply congrArg (fun f => packet.declaration.normalHead.map f)
  funext pattern
  exact packet_translate registry root state formed packet member pattern
end Yulang.GeneralDictionarySupportMetadataInvariants
