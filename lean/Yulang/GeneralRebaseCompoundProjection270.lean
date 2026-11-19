import Yulang.GeneralRebaseOneOutputProjection270
import Yulang.GeneralRebaseRetainedMetadata270
import Yulang.GeneralRebaseBehaviorFixture269
import Yulang.GeneralRebaseEnhancedPipeline269

namespace Yulang.GeneralRebaseCompoundProjection270
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles interpretation)
open GeneralRebaseSourceStrictFixture265 (owner owners output pool initial_projection strict)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseWeakProgress268 (Weak lull_same weak_source)
open GeneralRebaseBodyTable261 (schema)

theorem one_equation (plan : Plan roles) (reg : plan.packet.registry = registry)
 (decl : plan.packet.declaration = declaration)
 (interp : plan.packet.context.interpretation = interpretation) :
 (schema plan output).equations.length = 1 := by
 unfold schema
 rw [decl]
 change (GeneralNominalCenteredHeadMatEffects.bodySchema plan 4
    (.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩)).equations.length = 1
 unfold GeneralNominalCenteredHeadMatEffects.bodySchema GeneralNominalCenteredHeadMatEffects.compileBody
 rw [reg,interp]
 rfl

theorem all_equations (after : State roles) (path : B4Target.Steps (Step registry root) before after)
 (plan : Plan roles) (listed : plan ∈ after.plans) :
 (schema plan output).equations.length = 1 := by
 have metadata := GeneralRebaseRetainedMetadata270.from_empty registry root _ _ rfl path plan listed
 exact one_equation plan metadata.1 (List.mem_singleton.mp metadata.2.1) metadata.2.2

theorem dichotomy (after : State roles) (path : B4Target.Steps (Step registry root) before after) :
 (project owners pool after).remaining = [] ∨ (project owners pool after).remaining = Basis owners pool :=
 GeneralRebaseOneOutputProjection270.remaining_cases after owner output
   (fun plan listed _ => all_equations after path plan listed)

theorem initial_full : (project owners pool before).remaining = Basis owners pool :=
 congrArg GeneralRebaseStep258.State.remaining initial_projection

theorem initial_rank : (project owners pool before).remaining.length = 2 := by
 rw [initial_full]
 exact congrArg List.length (GeneralRebaseOneOutputProjection270.basis_two owner output)

theorem all_weak_targets (after : State roles) (weak : Weak registry root owners pool before after) :
 (project owners pool after).remaining = [] := by
 rcases dichotomy after (weak_source weak) with hit | untouched
 · exact hit
 · obtain ⟨middle,stutters,_,changed⟩ := weak
   have equal : (project owners pool after).remaining = (project owners pool middle).remaining :=
     untouched.trans (initial_full.symm.trans (congrArg GeneralRebaseStep258.State.remaining (lull_same stutters)).symm)
   exact False.elim (changed (GeneralRebaseStep258.state_ext _ _ equal))

theorem some_weak_target : Weak registry root owners pool before installed :=
 ⟨before,.refl,GeneralRebaseEnhancedPipeline269.actual_install.1,strict⟩

end Yulang.GeneralRebaseCompoundProjection270
