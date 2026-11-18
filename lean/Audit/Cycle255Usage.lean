import Yulang.GeneralDictionaryViewNormal255
import Yulang.GeneralNominalSourceBasis255
import Yulang.GeneralNominalViewFixed255
import Yulang.GeneralNominalTemplateChoices255
open Yulang
open Core.PresenceGeneration

example (keys : List (Nat × Nat)) (side : GeneralPresenceCheckedNormal252.Side) :
 GeneralNominalViewNormal255.prepare side
 (GeneralNominalPublicBasis253.basis GeneralDictionaryOutputDepth252.registry GeneralDictionaryOutputDepth252.context keys)
 GeneralDictionaryViewNormal255.view = none := GeneralDictionaryViewNormal255.var_basis_fails keys side

example (view : GeneralNominalRebaseRawView243.View) (side : GeneralPresenceCheckedNormal252.Side) :
 GeneralNominalViewNormal255.prepare side (GeneralNominalViewTypeTerms255.pool view) view =
 some (GeneralNominalViewNormal255.rewrite side (GeneralNominalViewTypeTerms255.pool view) view) :=
 GeneralNominalViewNormal255.source_pool_success side view

example (view : GeneralNominalRebaseRawView243.View) (side : GeneralPresenceCheckedNormal252.Side) (assignment) :
 (GeneralNominalViewNormal255.rewrite side (GeneralNominalViewTypeTerms255.pool view) view).Models assignment ↔ view.Models assignment :=
 GeneralNominalViewNormal255.source_pool_models side view assignment

example (state : GeneralNominalState.State) (term : TyTerm Nat)
 (present : term ∈ GeneralNominalViewTypeTerms255.pool (GeneralNominalRebaseRawView243.compile state CompTerm.var)) :
 GeneralNominalState.typeSources term ⊆ GeneralNominalState.sources state :=
 GeneralNominalSourceViewSupport255.compiled_pool state term present

example (pool : List (TyTerm Nat)) (view result : GeneralNominalRebaseRawView243.View)
 (side : GeneralPresenceCheckedNormal252.Side)
 (success : GeneralNominalViewNormal255.prepare side pool view = some result) :
 GeneralNominalViewNormal255.prepare side pool result = some result :=
 GeneralNominalViewFixed255.prepare_idempotent side pool view result success

example (pool : List (TyTerm Nat)) (side : GeneralPresenceCheckedNormal252.Side) :
 (GeneralNominalViewFixed255.candidates side pool).length = 2 ^ pool.length :=
 GeneralNominalViewFixed255.candidate_count side pool

example (pool : List (TyTerm Nat)) (variables : GeneralNominalMaterialization.Mode → Nat → TyTerm Nat)
 (mode : GeneralNominalMaterialization.Mode) (term : GeneralNominalCenteredHeadMatExpressions.Expr)
 (supported : ∀ entry ∈ GeneralNominalTemplateChoices255.reads mode term, variables entry.1 entry.2 ∈ pool) :
 GeneralNominalRebaseEffectView243.compile variables mode term ∈ GeneralNominalTemplateChoices255.choices pool term :=
 GeneralNominalTemplateChoices255.compiled_mem pool variables mode term supported
