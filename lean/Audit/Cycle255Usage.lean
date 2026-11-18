import Yulang.GeneralDictionaryViewNormal255
import Yulang.GeneralNominalSourceBasis255
import Yulang.GeneralNominalViewFixed255
import Yulang.GeneralNominalTemplateChoices255
import Yulang.GeneralNominalCanonicalBasis255
import Yulang.GeneralNominalSourceTemplateMenu255
import Yulang.GeneralNominalTemplateSupport255
import Yulang.GeneralNominalNormalizedDepth255
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

example (keys : List (Nat × Nat)) :
 (GeneralNominalCanonicalBasis255.basis GeneralDictionaryOutputDepth252.sourceRegistry GeneralDictionaryOutputDepth252.context keys).Nodup :=
 GeneralNominalCanonicalBasis255.basis_unique _ _ keys

example (keys : List (Nat × Nat)) (side : GeneralPresenceCheckedNormal252.Side) (assignment) :
 (GeneralNominalViewNormal255.rewrite side
   (GeneralNominalCanonicalBasis255.basis GeneralDictionaryOutputDepth252.sourceRegistry GeneralDictionaryOutputDepth252.context keys)
   GeneralDictionaryViewNormal255.view).Models assignment ↔ GeneralNominalState.Models GeneralDictionaryOutputDepth252.snapshot assignment :=
 GeneralNominalCanonicalBasis255.source_models _ _ keys side assignment

example (keys : List (Nat × Nat)) (invocation key purpose binder position : Nat) (privatePurpose : purpose ≤ 1)
 (term : TyTerm Nat) (present : term ∈ GeneralNominalCanonicalBasis255.basis GeneralDictionaryOutputDepth252.sourceRegistry GeneralDictionaryOutputDepth252.context keys) :
 GeneralNominalPublicBasis253.privateName GeneralDictionaryOutputDepth252.snapshot.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources term :=
 GeneralNominalCanonicalBasis255.separated GeneralDictionaryOutputDepth252.source keys invocation key purpose binder position privatePurpose term present

example (side : GeneralPresenceCheckedNormal252.Side) :
 GeneralPresenceCheckedNormal252.normalize side
 (GeneralNominalCanonicalBasis255.basis GeneralDictionaryOutputDepth252.sourceRegistry GeneralDictionaryOutputDepth252.context []) (.var 2) = .var 2 := by
 cases side <;> decide +kernel

example : GeneralNominalState.typeSources (.arrow (.var 0) (.var 9) (.var 1) (.var 10)) = [0,9,1,10] := rfl

example : GeneralNominalTemplateNormal255.prepare (fun _ => .lower) [.var 0]
 (fun mode _ => match mode with | .actual => .var 0 | _ => .pair (.var 0) (.var 0)) .lower
 (.nominal 7 [.variable 3]) = some (.nominal 7 [.source (.var 0)]) := rfl

example : GeneralNominalTemplateNormal255.prepare (fun _ => .lower) [.var 0]
 (fun mode _ => match mode with | .actual => .var 0 | _ => .pair (.var 0) (.var 0)) .lower
 (.record 7 (.variable 3) (.variable 3)) = none := rfl

example (side : GeneralPresenceCheckedNormal252.Side) (basis : List (TyTerm Nat)) (term : TyTerm Nat) :
 GeneralNominalExprDepth253.typeDepth (GeneralPresenceCheckedNormal252.normalize side basis term) ≤
 GeneralNominalNormalizedDepth255.leafBound basis := GeneralNominalNormalizedDepth255.normalized_depth side basis term

example (policy : GeneralNominalMaterialization.Mode → GeneralPresenceCheckedNormal252.Side)
 (basis : List (TyTerm Nat)) (variables : GeneralNominalTemplateNormal255.Variables)
 (mode : GeneralNominalMaterialization.Mode) (template : GeneralNominalTemplateChoices255.Raw) :
 GeneralNominalExprDepth253.materializedDepth (GeneralNominalTemplateNormal255.rewrite policy basis variables mode template) ≤
 GeneralNominalExprDepth253.rawDepth template + GeneralNominalNormalizedDepth255.leafBound basis :=
 GeneralNominalNormalizedDepth255.rewritten_depth policy basis variables mode template

example (policy : GeneralNominalMaterialization.Mode → GeneralPresenceCheckedNormal252.Side)
 (basis : List (TyTerm Nat)) (variables : GeneralNominalTemplateNormal255.Variables)
 (mode : GeneralNominalMaterialization.Mode) (template : GeneralNominalTemplateChoices255.Raw) (privateName : Nat)
 (separated : ∀ atom ∈ basis, privateName ∉ GeneralPresenceSubstitutionSupport244.typeSources atom) :
 privateName ∉ GeneralNominalTemplateSupport255.reads (GeneralNominalTemplateNormal255.rewrite policy basis variables mode template) :=
 GeneralNominalTemplateSupport255.rewritten_private_free policy basis variables mode template privateName separated
