import Yulang.GeneralNominalExprDepth253
namespace Yulang.GeneralNominalRawFinite253
open Core.PresenceGeneration (TyTerm)
open GeneralNominalMaterialization (Mode)
open GeneralNominalExprDepth253 (Raw Materialized)
open GeneralNominalRebaseEffectView243 (compile compileMany)

def combine (first : List α) (last : List β) (f : α → β → γ) : List γ :=
 first.flatMap fun one => last.map (f one)

theorem combine_mem (first : List α) (last : List β) (f : α → β → γ)
 (one : α) (two : β) (a : one ∈ first) (b : two ∈ last) : f one two ∈ combine first last f :=
 List.mem_flatMap.mpr ⟨one,a,List.mem_map.mpr ⟨two,b,rfl⟩⟩

/- Enumerate raw expressions over a finite source-term pool. This is not an
expanded readback enumeration. In the opaque-reference specialization every
leaf in the pool is a variable. Different occurrences may choose independently. -/
mutual
 def choices (pool : List (TyTerm Nat)) : Raw → List Materialized
 | .variable _ => pool.map .source
 | .primitive constructor args => (manyChoices pool args).map (.primitive constructor)
 | .nominal name args => (manyChoices pool args).map (.nominal name)
 | .record label first last => combine (choices pool first) (choices pool last) (.record label)
 | .variant tag term => (choices pool term).map (.variant tag)
 | .join first last => combine (choices pool first) (choices pool last) .join
 def manyChoices (pool : List (TyTerm Nat)) : List Raw → List (List Materialized)
 | [] => [[]]
 | first :: rest => combine (choices pool first) (manyChoices pool rest) List.cons
end

mutual
 theorem compile_mem (pool : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat)
 (bounded : ∀ mode name, variables mode name ∈ pool) (mode : Mode) (term : Raw) :
 compile variables mode term ∈ choices pool term := by
 cases term with
 | «variable» name => exact List.mem_map.mpr ⟨variables mode name,bounded mode name,rfl⟩
 | primitive constructor args => exact List.mem_map.mpr ⟨compileMany variables mode args,compileMany_mem pool variables bounded mode args,rfl⟩
 | nominal name args => exact List.mem_map.mpr ⟨compileMany variables .actual args,compileMany_mem pool variables bounded .actual args,rfl⟩
 | record label first last => exact combine_mem _ _ _ _ _ (compile_mem pool variables bounded mode first) (compile_mem pool variables bounded mode last)
 | variant tag term => exact List.mem_map.mpr ⟨compile variables mode term,compile_mem pool variables bounded mode term,rfl⟩
 | join first last => exact combine_mem _ _ _ _ _ (compile_mem pool variables bounded mode first) (compile_mem pool variables bounded mode last)
 theorem compileMany_mem (pool : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat)
 (bounded : ∀ mode name, variables mode name ∈ pool) (mode : Mode) (terms : List Raw) :
 compileMany variables mode terms ∈ manyChoices pool terms := by
 cases terms with
 | nil => exact List.mem_cons_self
 | cons first rest => exact combine_mem _ _ _ _ _ (compile_mem pool variables bounded mode first) (compileMany_mem pool variables bounded mode rest)
end

def templateChoices (pool : List (TyTerm Nat)) (templates : List Raw) : List Materialized :=
 templates.flatMap (choices pool)

theorem template_mem (pool : List (TyTerm Nat)) (templates : List Raw)
 (variables : Mode → Nat → TyTerm Nat) (bounded : ∀ mode name, variables mode name ∈ pool)
 (mode : Mode) (term : Raw) (member : term ∈ templates) :
 compile variables mode term ∈ templateChoices pool templates :=
 List.mem_flatMap.mpr ⟨term,member,compile_mem pool variables bounded mode term⟩

theorem opaque_reference_mem (names : List Nat) (templates : List Raw)
 (references : Mode → Nat → Nat) (bounded : ∀ mode name, references mode name ∈ names)
 (mode : Mode) (term : Raw) (member : term ∈ templates) :
 compile (fun mode name => .var (references mode name)) mode term ∈
 templateChoices (names.map TyTerm.var) templates := by
 apply template_mem _ templates _ _ mode term member
 intro mode name
 exact List.mem_map.mpr ⟨references mode name,bounded mode name,rfl⟩

theorem combine_count (first : List α) (last : List β) (f : α → β → γ) :
 (combine first last f).length = first.length * last.length := by
 induction first with
 | nil => simp [combine]
 | cons one rest ih =>
   simp only [combine,List.flatMap_cons,List.length_append,List.length_map,List.length_cons,Nat.add_mul,Nat.one_mul] at *
   omega

mutual
 def variableCount : Raw → Nat
 | .variable _ => 1
 | .primitive _ args | .nominal _ args => variableCounts args
 | .record _ first last | .join first last => variableCount first + variableCount last
 | .variant _ term => variableCount term
 def variableCounts : List Raw → Nat
 | [] => 0
 | first :: rest => variableCount first + variableCounts rest
end

mutual
 theorem choices_count (pool : List (TyTerm Nat)) (term : Raw) :
 (choices pool term).length = pool.length ^ variableCount term := by
 cases term with
 | «variable» => simp only [choices,List.length_map,variableCount,Nat.pow_one]
 | primitive => simp only [choices,List.length_map,variableCount,manyChoices_count]
 | nominal => simp only [choices,List.length_map,variableCount,manyChoices_count]
 | record => simp only [choices,combine_count,choices_count,variableCount,Nat.pow_add]
 | variant => simp only [choices,List.length_map,choices_count,variableCount]
 | join => simp only [choices,combine_count,choices_count,variableCount,Nat.pow_add]
 theorem manyChoices_count (pool : List (TyTerm Nat)) (terms : List Raw) :
 (manyChoices pool terms).length = pool.length ^ variableCounts terms := by
 cases terms with
 | nil => rfl
 | cons => simp only [manyChoices,combine_count,choices_count,manyChoices_count,variableCounts,Nat.pow_add]
end
end Yulang.GeneralNominalRawFinite253
