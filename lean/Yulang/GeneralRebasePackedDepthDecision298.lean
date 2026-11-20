import Yulang.GeneralRebasePackedDecision298
import Yulang.GeneralRebaseRefreshCode298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebasePackedDepthDecision298
open GeneralDictionaryOutputDepth252 (initial model plan reachable)
open GeneralDictionaryOutputDepthInstall252 (smallModel)
open GeneralRebaseSignedDepth297 (positive negative nested)
open GeneralRebasePreInstallReplay297 (after candidate source_reachable xs retained_answers signs_preserved)
open GeneralRebaseSignedModels297 (Sign Test)
open GeneralRebaseExecutableJournal298 renaming compile → journal
open GeneralRebaseSymbolicQuestions298 (compile)
open GeneralRebaseQuestionFootprint298 (question)
open GeneralRebasePackedAnswers298 (Vector fill retain)
open GeneralRebasePackedDecision298 (Judge answer Covered encode reduce)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (CompTerm)
open GeneralRebasePartialBool268 (Reflect)

def base := journal after CompTerm.var
def body (sign : Sign) := compile after CompTerm.var (.install candidate sign)
abbrev shape (sign : Sign) := question base (body sign)

def fallback : Assignment := fun _ => (.bottom,Common.rowEmpty)

def ask (sign : Sign) (v : Vector (shape sign)) : Option Bool :=
  let a := fill (shape sign) v fallback
  some (match sign with | .pass => nested a | .reject => !(nested a))

theorem output_read (sign : Sign) : 3 ∈ (shape sign).types := by cases sign <;> decide +kernel

theorem answer_bits (sign : Sign) : reduce (ask sign) (encode base (body sign) xs) = some true := by
  cases sign <;> decide +kernel

theorem all_packed_rows_reflect (sign : Sign) (v : Vector (shape sign))
    (row : v ∈ encode base (body sign) xs) : Reflect (Judge base (body sign) fallback v) (ask sign v) := by
  obtain ⟨a,member,rfl⟩ := List.mem_map.mp row
  have cert := (GeneralRebasePackedAnswers298.check_same base (body sign) a fallback).trans
    (GeneralRebaseSymbolicQuestions298.compile_holds source_reachable CompTerm.var (.install candidate sign) a)
  have same : (fill (shape sign) (GeneralRebasePackedAnswers298.pack (shape sign) a) fallback 3).1 = (a 3).1 :=
    (retain (shape sign) a fallback).1 3 (output_read sign)
  have passes : nested (fill (shape sign) (GeneralRebasePackedAnswers298.pack (shape sign) a) fallback) = nested a := by
    unfold nested
    rw [same]
  have rows : a = model ∨ a = smallModel := by
    change a ∈ [model,smallModel] at member
    simpa using member
  cases sign <;> simp only [ask,passes] <;> rcases rows with rfl | rfl
  · exact cert.mpr signs_preserved.1
  · exact fun h => signs_preserved.2.2 (cert.mp h).2
  · exact fun h => (cert.mp h).2 signs_preserved.1.2
  · exact cert.mpr signs_preserved.2

theorem packed_cover (sign : Sign) : Covered ((body sign).Holds base) xs := by
  intro _
  have source (m : Assignment) :=
    GeneralRebaseSymbolicQuestions298.compile_holds source_reachable CompTerm.var (.install candidate sign) m
  cases sign
  · exact ⟨model,List.mem_cons_self ..,(source model).mpr signs_preserved.1⟩
  · exact ⟨smallModel,List.mem_cons_of_mem _ (List.mem_cons_self ..),(source smallModel).mpr signs_preserved.2⟩

theorem exact_answer (sign : Sign) :
    Reflect (∃ a, Test after candidate sign a) (reduce (ask sign) (encode base (body sign) xs)) :=
  GeneralRebasePartialFinite268.transfer
    (exists_congr (GeneralRebaseSymbolicQuestions298.compile_holds source_reachable CompTerm.var (.install candidate sign)))
    (answer base (body sign) fallback xs (ask sign) (packed_cover sign) (all_packed_rows_reflect sign))

end Yulang.GeneralRebasePackedDepthDecision298
