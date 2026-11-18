import Yulang.GeneralDeclarationExamples
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
set_option backward.isDefEq.respectTransparency false
/-! A checked finite source with input Foo(Int), an unconstrained output slot,
and associated template Foo(Foo(a)). Its actual packet has a model and the
ground-expanded output exceeds max(input depth, template depth). Initial source
reachability is proved; no operational installation Step is asserted. This is
a bound obstruction for expanded readbacks, not for unexpanded references. -/
namespace Yulang.GeneralDictionaryOutputDepth252
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (constructors bareRole)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev roles : Roles.RoleDecls := fun _ => GeneralDeclarationExamples.outputRole 0
abbrev declaration : Declaration := ⟨0,0,[.var 0],[],[⟨0,0,.app 0 [.app 0 [.var 0]]⟩],[]⟩
abbrev sourceRegistry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
 constructor
 · simp [Declaration.Signature, Declared]
 · simp [Declaration.Identified,Declaration.outputNames]
 · simp [Declaration.Produced]
 · simp [Declaration.OutputOnly,Declaration.outputNames]
 · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
 · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
 · intro clause member; cases member
 · intro clause member; cases member
 · intro clause member; cases member
 · intro clause member; cases member

theorem source_checked : Checked sourceRegistry := by
 refine ⟨by simp,?_⟩
 intro d member
 cases List.mem_singleton.mp member
 exact declaration_checked

theorem checked : Checked registry := GeneralNominalCenteredHeadAllocEncoding.registry_checked source_checked
abbrev equations : List (Fin 4 × TyTerm (Fin 4)) := [(0,.base .int),(1,.base .int)]
abbrev atoms := equations.flatMap fun p => GeneralSourceState.equationAtoms p.1 p.2
abbrev base : GeneralSourceState.State where
 slots := 4
 source := Fin.val
 source_injective := fun _ _ h => Fin.ext h
 rowSource := Fin.val
 ordinary := atoms
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ h; cases h
 intervals_sound := by intro _ _ _ h; cases h
abbrev view : GeneralNormalizedObservation.Snapshot base where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ h; cases h
abbrev foo : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev snapshot : GeneralNominalState.State where
 base := base
 view := view
 constructors := constructors
 nominals := fun slot => if slot = 2 then some foo else none
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · cases found
 bodies_opaque := by intro _ _ _; rfl
 seed := 3
abbrev interpretation : GeneralNominalInspection.Interpretation where
 primitives := fun name => if name = 2 then some (.scalar .int) else none
 invariantNominal := fun name => name == 0 || name == 5
 disjoint := by intro name yes; simp_all; omega
abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
abbrev root : Occurrence roles := ⟨0,⟨0,fun _ => (2,2),[⟨0,3⟩],by intro output h; cases List.mem_singleton.mp h; exact ⟨none,rfl⟩⟩⟩
abbrev initial := GeneralNominalVersionedJournal232.initial context root
abbrev S : Ty := .base .int
abbrev F : Ty := nominal 0 [.inl S]
abbrev P : Ty := nominal 0 [.inl (nominal 0 [.inl F])]
def value : Nat → Ty | 0 | 1 => S | 2 => F | 3 => P | _ => F
def model : Assignment := fun source => (value source,Common.rowEmpty)

theorem base_models : GeneralNominalCommonBridge.Models base model := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 intro atom member
 simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
   GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem source_model : GeneralNominalState.Models snapshot model := by
 refine ⟨base_models,?_,by intro _ h; cases h⟩
 intro slot d found
 change (if slot = 2 then some foo else none) = some d at found
 split at found
 · rename_i same; subst slot; cases Option.some.inj found
   exact ⟨[.inl S],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
 · cases found

theorem metadata : GeneralNominalRecursiveCandidates.Metadata sourceRegistry context := by
 refine ⟨rfl,?_⟩
 intro name primitive found
 change (if name = 2 then some (.scalar .int) else none) = some primitive at found
 split at found
 · rename_i same; subst name; cases Option.some.inj found; exact ⟨_,rfl,rfl⟩
 · cases found

theorem source : GeneralNominalSourceFormation.InitialSource sourceRegistry context root where
 roles_agree := rfl
 metadata := metadata
 linked := ⟨by intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ],by intro output h; cases List.mem_singleton.mp h; simp [GeneralNominalState.sources,List.ofFn_succ]⟩
 intervals := fun _ _ _ => subtype_refl _
 below_seed := by intro identity member; simp [GeneralNominalState.sources,List.ofFn_succ] at member; change identity ≤ 3; omega
 unallocated := rfl

theorem initial_model : GeneralNominalVersionedJournal232.Models initial model := by
 apply (GeneralNominalVersionedJournal232.initial_models context root model).mpr
 exact ⟨source_model,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩


abbrev scalarTerm : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
abbrev fooTerm : GeneralNominalOriginTerms.Expr Nat := .node (.nominal 0 1) (fun _ => scalarTerm)
abbrev rootTerm := fooTerm
abbrev rootPattern : Pattern := .app 0 [.app 2 []]
theorem root_closed : GeneralNominalGroundAccessibility.ClosedTerm context rootPattern rootTerm := by
 refine ⟨?_,?_,?_⟩
 · simp [normalize,normalizeArgs,
     GeneralNominalInspection.translate,
     GeneralNominalCompoundReadback.quote,List.ofFn_succ,GeneralNominalOriginTerms.arity]
 · simp [GeneralNominalOriginTerms.Expr.leaves,List.ofFn_succ,GeneralNominalOriginTerms.arity]
 · exact ⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩
theorem root_denote : GeneralNominalFiniteMeaning.denote (fun _ => .bottom) rootTerm = F := by
 simp [GeneralNominalFiniteMeaning.denote, GeneralNominalFiniteMeaning.build, List.ofFn_succ, GeneralNominalOriginTerms.arity, F, S]

theorem scalar_fixed (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 0).1 S := by
 constructor
 · exact valid.1.1 (.tyLe (.var 0) (.base .int)) (by simp [atoms,GeneralSourceState.equationAtoms])
 · exact valid.1.1 (.tyLe (.base .int) (.var 0)) (by simp [atoms,GeneralSourceState.equationAtoms])
theorem foo_fixed (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Equivalent (m 2).1 F := by
 obtain ⟨values,fits,equal⟩ := valid.2.1 2 foo rfl
 change GeneralNominalState.FitsAll base m [.type (0,0)] values at fits
 cases fits with
 | @cons _ a _ rest fit remaining =>
   cases remaining
   cases a with
   | inr => cases fit
   | inl a =>
     have s := scalar_fixed m valid
     have e : Equivalent a S := ⟨subtype_trans fit.2 s.1,subtype_trans s.2 fit.1⟩
     have lifted := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons e .nil)
     exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] := by
 refine ⟨rfl,?_⟩
 intro index
 have zero : index = 0 := Subsingleton.elim _ _
 subst index
 refine ⟨rootTerm,root_closed,?_⟩
 intro m valid
 rw [root_denote]
 exact foo_fixed m valid
theorem coverage : GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation := by
 constructor
 · intro d member
   cases List.mem_singleton.mp member
   simp [GeneralNominalCenteredHeadWFSource.DeclarationCovered,
     GeneralNominalCenteredHeadWFSource.PatternsCovered,GeneralNominalCenteredHeadWFSource.PatternCovered,
     GeneralNominalCenteredHeadWFSource.ConstructorUse, interpretation, constructors]
 · intro role name body found
   change (if name = 0 then some none else none) = some (some body) at found
   split at found <;> cases found
theorem initial_source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial :=
 ⟨GeneralNominalCenteredHeadMatStepJournal.initial context root,
   ⟨context,[rootPattern],source,(fun _ => rfl),ground,coverage,rfl⟩,rfl⟩
theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root initial :=
 ⟨initial,initial_source,.refl⟩



open GeneralNominalCenters
open GeneralNominalCenteredHeadMatExpressions
abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(2,2)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
abbrev rhs : Expr := .nominal 0 [.nominal 0 [.variable 0]]
theorem bindings_exact : packet.bindings = [(0,2,2)] := by decide +kernel
theorem emitted_exact : GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[⟨3,.actual,rhs⟩],false⟩ := by
 have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
 unfold GeneralNominalVersionedPlans231.emittedSchema GeneralNominalVersionedPlans231.emittedRequests
 simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical]
 rfl

theorem binder_exact : GeneralNominalVersionedFrame231.binder plan 0 = 2 := by
 unfold GeneralNominalVersionedFrame231.binder GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
 rw [bindings_exact]
 rfl
theorem rhs_value : GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual rhs = P := by
 simp only [GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values]
 change nominal 0 [.inl (nominal 0 [.inl (model (GeneralNominalVersionedFrame231.binder plan 0)).1])] = P
 rw [binder_exact]
 rfl
theorem output_valid : GeneralNominalVersionedPlans231.Outputs plan model := by
 unfold GeneralNominalVersionedPlans231.Outputs
 rw [emitted_exact]
 change ∀ equation ∈ ([⟨3,.actual,rhs⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _
 intro equation member
 cases List.mem_singleton.mp member
 change Equivalent P (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs)
 rw [rhs_value]
 exact ⟨subtype_refl _,subtype_refl _⟩

/- Ordinary syntax constructor depth; variable leaves have depth zero. -/
mutual
 def depth : Pattern → Nat
 | .var _ => 0
 | .app _ args => 1 + depths args
 | .record _ payload tail => 1 + max (depth payload) (depth tail)
 | .variant _ payload => 1 + depth payload
 | .join first last => 1 + max (depth first) (depth last)
 def depths : List Pattern → Nat
 | [] => 0
 | first :: rest => max (depth first) (depths rest)
end
abbrev template : Pattern := .app 0 [.app 0 [.var 0]]
abbrev expanded : Pattern := template.subst (fun _ => rootPattern)
theorem depth_input : depth rootPattern = 2 := rfl
theorem depth_template : depth template = 2 := rfl
theorem depth_expanded : depth expanded = 4 := rfl
theorem exceeds_max : max (depth rootPattern) (depth template) < depth expanded := by decide +kernel
theorem associated_template : declaration.associated = [⟨0,0,template⟩] := rfl
theorem translated_template : translate constructors interpretation template = some rhs := rfl
/-- Ground expansion corresponds to the actual emitted RHS under this source model. -/
theorem expanded_value :
 GeneralNominalCenteredHeadMatPatternSemantics.eval
   (GeneralNominalCenteredHeadMatCompilerSemantics.algebra constructors interpretation)
   (fun _ => S) expanded = P := rfl


open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
abbrev calculated : Report snapshot where
 captures := [⟨0,(2,2),none⟩]
 checked := [(2,2),(2,2)]
theorem report_exact : report context declaration [(2,2)] = calculated := by
 simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,inspectMany,inspect,Report.append,calculated]
theorem projection : ProjectionModels snapshot (GeneralNominalPacketSupport.report packet) model := by
 change ProjectionModels snapshot (report context declaration [(2,2)]) model
 rw [report_exact]
 refine ⟨(by intro _ h; cases h),(by intro _ h; cases h),?_,?_⟩
 · intro first one last two _ ref located
   cases List.mem_singleton.mp one
   cases located
 · intro first one last two _ a b located
   cases List.mem_singleton.mp one
   cases located

theorem ordinary : GeneralNominalVersionedPlans231.Ordinary packet model := by
 refine ⟨?_,?_,?_⟩
 · rw [bindings_exact]
   intro first one last two _
   cases List.mem_singleton.mp one
   cases List.mem_singleton.mp two
   exact subtype_refl _
 · rw [bindings_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model model []
   exact PresenceNormalForm.all_nil _ _
 · change PresenceNormalForm.All CommonNominalFullCarrier.model model (selfChecks snapshot (report context declaration [(2,2)]))
   rw [report_exact]
   change PresenceNormalForm.All CommonNominalFullCarrier.model model [.tyLe (.var 2) (.var 2),.tyLe (.var 2) (.var 2)]
   intro atom member
   rcases List.mem_cons.mp member with rfl | member
   · exact subtype_refl _
   · cases List.mem_singleton.mp member
     exact subtype_refl _

theorem head_holds : GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model := by
 have schema : plan.headSchema = {variables := [⟨0,.source 2,.actual⟩]} := by
   simp [Plan.headSchema,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,GeneralNominalInspection.translate,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append]
   rfl
 rw [schema]
 constructor
 · intro test member; cases member
 · intro entry member
   change entry ∈ [⟨0,.source 2,.actual⟩] at member
   cases List.mem_singleton.mp member
   change GeneralNominalOriginTerms.Same model (.source 2) (.source (GeneralNominalVersionedFrame231.binder plan 0))
   rw [binder_exact]
   exact ⟨⟨_,.source 2⟩,⟨_,.source 2⟩,fun x y a b => by cases a; cases b; exact ⟨subtype_refl _,subtype_refl _⟩⟩

theorem packet_holds : GeneralNominalVersionedPlans231.Holds plan model := by
 refine ⟨source_model,⟨ordinary,projection,?_,?_,head_holds,?_,?_⟩,output_valid⟩
 · intro index; exact ⟨subtype_refl _,subtype_refl _⟩
 · intro name needed
   have equal : name = 0 := by
     rcases needed with named | ⟨clause,member,_⟩
     · simpa [Declaration.inputNames,variablesArgs,normalizeArgs,normalize,Pattern.variables] using named
     · cases member
   subst name
   rw [binder_exact]
   unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
   rw [bindings_exact]
   change Subtype F F ∧ Subtype F F
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro equation member nonactual
   rw [emitted_exact] at member
   cases List.mem_singleton.mp member
   exact False.elim (nonactual rfl)
 · intro clause member; cases member


theorem head_model : GeneralNominalVersionedPlans231.HeadModels packet model :=
 ⟨(GeneralNominalVersionedPlans231.private_models_iff packet model).mpr ⟨source_model,ordinary⟩,projection⟩
theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
 intro key member collision
 have below := source.below_seed _ collision
 change GeneralNominalIdentities.source snapshot.seed key ≤ snapshot.seed at below
 have above := GeneralNominalIdentities.source_above_seed snapshot.seed key
 omega
theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry context root declaration := by
 refine ⟨metadata,⟨source.linked.1,(by intro output member; cases member)⟩,[(2,2)],by decide +kernel,fresh,?_,model,head_model⟩
 rw [report_exact]
 exact ⟨rfl,rfl,rfl⟩
theorem frame : GeneralNominalVersionedEvidence231.Frame registry initial.core root 0 plan :=
 ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
   by decide +kernel,prepared⟩
theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
 rintro ⟨index,unknown⟩
 exact unknown ⟨2,rfl,Or.inr ⟨foo,rfl⟩⟩
theorem children_empty : GeneralNominalVersionedFrame231.children packet = [] := by
 have canonical : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by decide +kernel
 unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
 simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical]
 rfl
theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry context root 0 [] :=
 ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(2,2)],
   by decide +kernel,prepared,children_empty.symm⟩
theorem unique : GeneralNominalVersionedCandidates231.Unique registry context root 0 [] := by
 refine ⟨survivor,?_⟩
 intro key kids found
 have copy := found
 obtain ⟨_,d,visible,_,identity,_⟩ := found
 cases List.mem_singleton.mp visible
 cases identity
 exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩
end Yulang.GeneralDictionaryOutputDepth252
