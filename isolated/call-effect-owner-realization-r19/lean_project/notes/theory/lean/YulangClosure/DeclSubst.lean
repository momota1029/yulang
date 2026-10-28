import YulangClosure.PaperTypeFormation

/-!
Declaration-consistent ambient substitution for paper operation instances.
This is a substitution-algebra result toward the typing-substitution lemma;
it does not establish executor preservation or inference correctness.
-/
namespace YulangClosure.PaperTypes

private theorem operationInstance_ext (left right : OperationInstance)
    (hid : left.identity = right.identity)
    (hargs : left.typeArguments = right.typeArguments)
    (hpayload : left.payloadType = right.payloadType)
    (hresponse : left.responseType = right.responseType) : left = right := by
  cases left
  cases right
  simp_all

private theorem lookupTypeArgument_some_of_lt (arguments : List Ty) (i : Nat)
    (hi : i < arguments.length) :
    ∃ argument, lookupTypeArgument arguments i = some argument := by
  induction arguments generalizing i with
  | nil => simp at hi
  | cons head tail ih =>
      cases i with
      | zero => exact ⟨head, rfl⟩
      | succ i =>
          have hi' : i < tail.length := by simpa using hi
          obtain ⟨argument, hget⟩ := ih i hi'
          exact ⟨argument, hget⟩

theorem argsSyntax_subst (σ : Nat → Ty) (arguments : List Ty) :
    subst σ (argsSyntax arguments) = argsSyntax (mapOperationArguments σ arguments) := by
  induction arguments with
  | nil => rfl
  | cons head tail ih => simp [argsSyntax, mapOperationArguments, subst, ih]

private theorem shifted_instantiation_is_identity (arguments : List Ty) (n : Nat)
    (hlen : arguments.length = n) :
    (fun i => instantiateSubstitution arguments (i + n)) = idSub := by
  funext i
  have hge : arguments.length ≤ i + n := by omega
  have hnone := lookupTypeArgument_none_of_ge arguments (i + n) hge
  simp [instantiateSubstitution, hnone, hlen, idSub]

theorem instantiateSubstitution_commutes (arguments : List Ty) (σ : Nat → Ty)
    (n : Nat) (hlen : arguments.length = n) :
    (fun i => subst σ (instantiateSubstitution arguments i)) =
      (fun i => subst (instantiateSubstitution (mapOperationArguments σ arguments))
        (liftSubN n σ i)) := by
  funext i
  by_cases hi : i < arguments.length
  · obtain ⟨argument, hget⟩ := lookupTypeArgument_some_of_lt arguments i hi
    have hin : i < n := by omega
    rw [show subst σ (instantiateSubstitution arguments i) = subst σ argument by
      simp [instantiateSubstitution, hget]]
    rw [liftSubN_bound n σ i hin]
    change subst σ argument =
      instantiateSubstitution (mapOperationArguments σ arguments) i
    unfold instantiateSubstitution
    rw [lookupTypeArgument_map σ arguments i]
    simp [hget]
  · have hge : n ≤ i := by omega
    have hleft : i - arguments.length = i - n := by omega
    rw [show instantiateSubstitution arguments i = .var (i - arguments.length) by
      simp [instantiateSubstitution, lookupTypeArgument_none_of_ge arguments i (Nat.le_of_not_lt hi)]]
    rw [liftSubN_free n σ i hge]
    rw [subst_mapVars]
    rw [shifted_instantiation_is_identity (mapOperationArguments σ arguments) n
      (by simp [mapOperationArguments, hlen])]
    rw [subst_id]
    simp [subst, hleft]

theorem operation_declaration_instantiation_subst (declaration : OperationDeclaration)
    (arguments : List Ty) (σ : Nat → Ty)
    (harity : arguments.length = declaration.typeArity) :
    (declaration.instantiate arguments).subst σ =
      (declaration.substAmbient σ).instantiate (mapOperationArguments σ arguments) := by
  rcases declaration with ⟨identity, arity, payload, response⟩
  have hcomm := instantiateSubstitution_commutes arguments σ arity harity
  simp only [OperationDeclaration.instantiate, OperationInstance.subst,
    OperationDeclaration.substAmbient]
  apply operationInstance_ext
  · rfl
  · exact argsSyntax_subst σ arguments
  · calc
      subst σ (subst (instantiateSubstitution arguments) payload) =
          subst (fun i => subst σ (instantiateSubstitution arguments i)) payload :=
        subst_comp (instantiateSubstitution arguments) σ payload
      _ = subst (fun i =>
          subst (instantiateSubstitution (mapOperationArguments σ arguments))
            (liftSubN arity σ i)) payload := by rw [hcomm]
      _ = subst (instantiateSubstitution (mapOperationArguments σ arguments))
          (subst (liftSubN arity σ) payload) :=
        (subst_comp (liftSubN arity σ)
          (instantiateSubstitution (mapOperationArguments σ arguments)) payload).symm
  · calc
      subst σ (subst (instantiateSubstitution arguments) response) =
          subst (fun i => subst σ (instantiateSubstitution arguments i)) response :=
        subst_comp (instantiateSubstitution arguments) σ response
      _ = subst (fun i =>
          subst (instantiateSubstitution (mapOperationArguments σ arguments))
            (liftSubN arity σ i)) response := by rw [hcomm]
      _ = subst (instantiateSubstitution (mapOperationArguments σ arguments))
          (subst (liftSubN arity σ) response) :=
        (subst_comp (liftSubN arity σ)
          (instantiateSubstitution (mapOperationArguments σ arguments)) response).symm


theorem operation_instance_instantiates_subst (op : OperationInstance)
    (declaration : OperationDeclaration) (arguments : List Ty) (σ : Nat → Ty)
    (hinst : op.Instantiates declaration arguments) :
    (op.subst σ).Instantiates (declaration.substAmbient σ)
      (mapOperationArguments σ arguments) := by
  rcases hinst with ⟨harity, hop⟩
  constructor
  · simp [mapOperationArguments, OperationDeclaration.substAmbient, harity]
  · calc
      op.subst σ = (declaration.instantiate arguments).subst σ := by rw [hop]
      _ = (declaration.substAmbient σ).instantiate
          (mapOperationArguments σ arguments) :=
        operation_declaration_instantiation_subst declaration arguments σ harity

theorem operation_instance_instantiatesIn_subst (op : OperationInstance)
    (declarations : List OperationDeclaration) (arguments : List Ty) (σ : Nat → Ty)
    (hinst : op.InstantiatesIn declarations arguments) :
    (op.subst σ).InstantiatesIn
      (declarations.map (fun declaration => declaration.substAmbient σ))
      (mapOperationArguments σ arguments) := by
  rcases hinst with ⟨declaration, hmember, hin⟩
  refine ⟨declaration.substAmbient σ, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨declaration, hmember, rfl⟩
  · exact operation_instance_instantiates_subst op declaration arguments σ hin

end YulangClosure.PaperTypes
