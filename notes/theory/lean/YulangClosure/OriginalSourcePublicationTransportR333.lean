import YulangClosure.OriginalSourceEnvironmentTransportR331

/-!
R333: exact publication transport for the original R331 embedding.
The operations below are the existing SG source operations, including their
failure cases, ordered names, initializer suffixes and historical event keys.
No source judgment or target kernel law is used to establish commutation.
-/
namespace YulangClosure.OriginalSourcePublicationTransportR333
open OriginalSource OriginalSourceEnvironment OriginalSourceInterpretation
open OriginalInterfacePreservationR328 OriginalSourceEnvironmentTransportR331

variable {s : Sorts} {View G : Type}

theorem exitPath_commutes (g : G) (f : Frame (Payload s View)) :
    (frame g f).exitPath = f.exitPath.map (step g) := by
  simp only [Frame.exitPath, ActualEvent.path, frame, scopedValue, actualEvent,
    List.map_append, List.map_cons, List.map_nil, step]

theorem prefixAtShared_commutes (g : G) (env : Environment (Payload s View)) (site : Site) :
    (environment g env).prefixAtShared site = (env.prefixAtShared site).map (frame g) := by
  simp only [Environment.prefixAtShared, environment, ← List.map_reverse,
    List.dropWhile_map, Function.comp_def, frame]

def candidate (g : G) (p : PublicationId (Payload s View) × PublicationRecord (Payload s View)) :=
  (publicationId g p.1, publicationRecord g p.2)

theorem publicationCandidate_commutes (g : G) (env : Environment (Payload s View)) (site : Site) :
    (environment g env).publicationCandidate site =
      (env.publicationCandidate site).map (candidate g) := by
  classical
  have prefixEq :=  prefixAtShared_commutes g env site
  unfold Environment.publicationCandidate
  simp only [prefixEq]
  simp only [environment, List.dropWhile_map, Function.comp_def, initializer,
    List.head?_map, List.getLast?_map, ← List.map_reverse, List.find?_map, frame]
  cases ent : (env.initializers.dropWhile (fun e => e.site != site)).head? with
  | none => simp
  | some entry =>
    cases last : (env.prefixAtShared site).getLast? with
    | none => simp
    | some shared =>
      cases ret : (env.prefixAtShared site).reverse.find? (fun f =>
          f.binder.site == site && f.binder.kind == .returnRebind) with
      | none => simp
      | some returned =>
        have path : (frame g shared).entryPath = (frame g returned).exitPath ↔
            shared.entryPath = returned.exitPath := by
          rw [exitPath_commutes]
          exact (list_injective _ (step_injective g)).eq_iff
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        change (if ¬ (frame g shared).entryPath = (frame g returned).exitPath then none else _) = _
        simp only [path]
        split
        · simp_all
        · rw [exitPath_commutes]
          simp only [Option.pure_def, Option.map_some, candidate, publicationRecord, publicationId, initializer,
            List.filter_map, Function.comp_def, frame]

theorem publicationName_commutes (g : G) (env : Environment (Payload s View)) (name : Name) :
    (environment g env).publicationName name = (env.publicationName name).map (publicationId g) := by
  simp only [Environment.publicationName, environment, names, List.find?_map,
    Function.comp_def, Option.map_map]

theorem names_injective (g : G) : Function.Injective (names (s := s) (View := View) g) := by
  apply list_injective
  intro a b h
  have fst : a.1 = b.1 := congrArg (fun p : Name × PublicationId (Payload (extended s G) (Sum View Unit)) => p.1) h
  have snd := publicationId_injective g (congrArg (fun p : Name × PublicationId (Payload (extended s G) (Sum View Unit)) => p.2) h)
  exact Prod.ext fst snd

theorem initializer_injective (g : G) : Function.Injective (initializer (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [initializer] at h
  injection h with site path ns fs
  have := list_injective _ (step_injective g) path
  have := names_injective g ns
  have := list_injective _ (frame_injective g) fs
  simp_all

theorem publicationRecord_injective (g : G) : Function.Injective (publicationRecord (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [publicationRecord] at h
  injection h with ident path ns fs caps fixed init
  have := publicationId_injective g ident
  have := list_injective _ (step_injective g) path
  have := names_injective g ns
  have := list_injective _ (frame_injective g) fs
  have := names_injective g caps
  have := list_injective _ (frame_injective g) fixed
  have := list_injective _ (initializer_injective g) init
  simp_all

theorem publicationValid_iff (g : G) (env : Environment (Payload s View))
    (bindings : List (Name × Site)) :
    (environment g env).publicationValid bindings ↔ env.publicationValid bindings := by
  constructor
  · intro valid binding member
    obtain ⟨ident, rec, cand, stored⟩ := valid binding member
    rw [publicationCandidate_commutes] at cand
    obtain ⟨⟨oldId, oldRecord⟩, oldCand, same⟩ := Option.map_eq_some_iff.mp cand
    cases same
    refine ⟨oldId, oldRecord, oldCand, ?_⟩
    rw [publications_preserved] at stored
    exact option_injective _ (publicationRecord_injective g) stored
  · intro valid binding member
    obtain ⟨ident, rec, cand, stored⟩ := valid binding member
    refine ⟨publicationId g ident, publicationRecord g rec, ?_, ?_⟩
    · rw [publicationCandidate_commutes, cand]; rfl
    · rw [publications_preserved, stored]; rfl

theorem option_mapM_naturality {A B C : Type} (xs : List A) (f : A → Option B) (h : B → C) :
    xs.mapM (fun x => (f x).map h) = (xs.mapM f).map (List.map h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, ih]
    cases f x <;> cases xs.mapM f <;> rfl

theorem publish_commutes (g : G) (env : Environment (Payload s View))
    (bindings : List (Name × Site)) :
    (environment g env).publish bindings = (env.publish bindings).map (environment g) := by
  have additions :
      bindings.mapM (fun (binding : Name × Site) => do
        let c ← (environment g env).publicationCandidate binding.2
        pure (binding.1, c.1)) =
      (bindings.mapM (fun (binding : Name × Site) => do
        let c ← env.publicationCandidate binding.2
        pure (binding.1, c.1))).map (names g) := by
    have pointwise (binding : Name × Site) :
        (do let c ← (environment g env).publicationCandidate binding.2
            pure (binding.1, c.1)) =
        ((do let c ← env.publicationCandidate binding.2
             pure (binding.1, c.1)) : Option (Name × PublicationId (Payload s View))).map
          (fun p => (p.1, publicationId g p.2)) := by
      rw [publicationCandidate_commutes]
      cases env.publicationCandidate binding.2 <;> rfl
    simp only [pointwise]
    exact option_mapM_naturality bindings _ _
  unfold Environment.publish
  rw [additions]
  cases bindings.mapM (fun (binding : Name × Site) => do
    let c ← env.publicationCandidate binding.2
    pure (binding.1, c.1)) with
  | none => rfl
  | some additions =>
    simp only [Option.pure_def, Option.map_some, Option.bind_eq_bind, Option.bind_some, environment, names, List.map_append]

theorem atPublication_commutes (g : G) (env : Environment (Payload s View)) (name : Name) :
    (environment g env).atPublication name = (env.atPublication name).map (environment g) := by
  classical
  unfold Environment.atPublication
  rw [publicationName_commutes]
  cases named : env.publicationName name with
  | none => rfl
  | some ident =>
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, publications_preserved]
    cases stored : env.publications ident with
    | none => rfl
    | some record =>
      simp only [Option.map_some, Option.bind_some, publicationRecord,
        (publicationId_injective g).eq_iff, List.all_map, Function.comp_def, frame]
      split
      · rfl
      · exact congrArg some (restore_commutes g env record).symm

theorem aliasPublication_commutes (g : G) (env : Environment (Payload s View))
    (original aliasName : Name) :
    (environment g env).aliasPublication original aliasName =
      (env.aliasPublication original aliasName).map (environment g) := by
  unfold Environment.aliasPublication
  rw [publicationName_commutes]
  cases env.publicationName original with
  | none => rfl
  | some ident => rfl

/-! Actual parent constructor applications. The child premise is precisely the
structural induction hypothesis; these theorems supply the publication part
of that induction, not a replacement kernel or a whole-language theorem. -/

theorem judgment_publishGroup (g : G)
    (oldKernel : Kernel (Payload s View))
    (newKernel : Kernel (Payload (extended s G) (Sum View Unit)))
    (env : Environment (Payload s View)) (bindings : List (Name × Site)) (body : RuleTree)
    (children : ∀ next, Judgment oldKernel next body → Judgment newKernel (environment g next) body)
    (original : Judgment oldKernel env (.publishGroup bindings body)) :
    Judgment newKernel (environment g env) (.publishGroup bindings body) := by
  cases original with
  | publishGroup valid next constructed proof =>
    apply Judgment.publishGroup ((publicationValid_iff g env bindings).mpr valid) (environment g next)
    · rw [publish_commutes, constructed]; rfl
    · exact children next proof

theorem judgment_atPublication (g : G)
    (oldKernel : Kernel (Payload s View))
    (newKernel : Kernel (Payload (extended s G) (Sum View Unit)))
    (env : Environment (Payload s View)) (name : Name) (body : RuleTree)
    (children : ∀ next, Judgment oldKernel next body → Judgment newKernel (environment g next) body)
    (original : Judgment oldKernel env (.atPublication name body)) :
    Judgment newKernel (environment g env) (.atPublication name body) := by
  cases original with
  | atPublication restored found proof =>
    apply Judgment.atPublication (environment g restored)
    · rw [atPublication_commutes, found]; rfl
    · exact children restored proof

theorem judgment_aliasPublication (g : G)
    (oldKernel : Kernel (Payload s View))
    (newKernel : Kernel (Payload (extended s G) (Sum View Unit)))
    (env : Environment (Payload s View)) (originalName aliasName : Name) (body : RuleTree)
    (children : ∀ next, Judgment oldKernel next body → Judgment newKernel (environment g next) body)
    (original : Judgment oldKernel env (.aliasPublication originalName aliasName body)) :
    Judgment newKernel (environment g env) (.aliasPublication originalName aliasName body) := by
  cases original with
  | aliasPublication aliased found proof =>
    apply Judgment.aliasPublication (environment g aliased)
    · rw [aliasPublication_commutes, found]; rfl
    · exact children aliased proof

end YulangClosure.OriginalSourcePublicationTransportR333
