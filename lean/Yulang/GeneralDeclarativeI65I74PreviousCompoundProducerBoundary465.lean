import Yulang.GeneralDeclarativeI65DeriveCompoundOutput394
namespace Yulang.GeneralDeclarativeI65.NativeProducer394Boundary465
mutual
inductive PlainSource : SourceRhsCode394 → Prop where
  | «variable» : PlainSource (.variable n c)
  | nominal : PlainArguments args → PlainSource (.nominal ctor args)
inductive PlainArgument : SourceRhsArg394 → Prop where
  | valueSlot : PlainArgument (.valueSlot n b)
  | rowSlot : PlainArgument (.rowSlot n b)
  | valueExpression : PlainSource rhs → PlainArgument (.valueExpression rhs)
inductive PlainArguments : List SourceRhsArg394 → Prop where
  | nil : PlainArguments []
  | cons : PlainArgument a → PlainArguments as → PlainArguments (a::as)
end

mutual
theorem plain_endpoint_has_exact_recursive_source_fragment (c : SourceRhsCode394) :
    (∃ e, plainEndpoint394 c = some e) ↔ PlainSource c := by
  cases c with
  | «variable» n c => exact ⟨fun _ => .variable, fun _ => ⟨_,rfl⟩⟩
  | nominal key args =>
    constructor
    · intro h
      cases atArgs : plainArgs394 args with
      | none => simp [plainEndpoint394,atArgs] at h
      | some as =>
        exact .nominal ((plain_arguments_have_exact_recursive_source_fragment args).mp ⟨as,atArgs⟩)
    · intro h
      cases h with
      | nominal read =>
        obtain ⟨xs,ok⟩ := (plain_arguments_have_exact_recursive_source_fragment args).mpr read
        exact ⟨.nominal key xs,by simp [plainEndpoint394,ok]⟩
  | record => exact ⟨by simp [plainEndpoint394], by intro x; cases x⟩
  | variant => exact ⟨by simp [plainEndpoint394], by intro x; cases x⟩
  | join => exact ⟨by simp [plainEndpoint394], by intro x; cases x⟩
termination_by sizeOf c

theorem plain_argument_has_exact_recursive_source_fragment (a : SourceRhsArg394) :
    (∃ e, plainArg394 a = some e) ↔ PlainArgument a := by
  cases a with
  | valueSlot => exact ⟨fun _ => .valueSlot, fun _ => ⟨_,rfl⟩⟩
  | rowSlot => exact ⟨fun _ => .rowSlot, fun _ => ⟨_,rfl⟩⟩
  | valueExpression rhs =>
    constructor
    · intro h
      cases read : plainEndpoint394 rhs with
      | none => simp [plainArg394,read] at h
      | some e =>
        exact .valueExpression ((plain_endpoint_has_exact_recursive_source_fragment rhs).mp ⟨e,read⟩)
    · intro h
      cases h with
      | valueExpression witness =>
        obtain ⟨e,found⟩ := (plain_endpoint_has_exact_recursive_source_fragment rhs).mpr witness
        exact ⟨.inl (.point e),by simp [plainArg394,found]⟩
termination_by sizeOf a

theorem plain_arguments_have_exact_recursive_source_fragment (xs : List SourceRhsArg394) :
    (∃ es, plainArgs394 xs = some es) ↔ PlainArguments xs := by
  cases xs with
  | nil => exact ⟨fun _ => .nil, fun _ => ⟨[],rfl⟩⟩
  | cons a as =>
    constructor
    · intro h
      cases head : plainArg394 a with
      | none => simp [plainArgs394,head,Option.bind] at h
      | some x =>
        cases rest : plainArgs394 as with
        | none => simp [plainArgs394,head,rest,Option.bind] at h
        | some xs =>
          exact .cons ((plain_argument_has_exact_recursive_source_fragment a).mp ⟨x,head⟩)
            ((plain_arguments_have_exact_recursive_source_fragment as).mp ⟨xs,rest⟩)
    · intro h
      cases h with
      | cons head rest =>
        obtain ⟨x,first⟩ := (plain_argument_has_exact_recursive_source_fragment a).mpr head
        obtain ⟨xs,more⟩ := (plain_arguments_have_exact_recursive_source_fragment as).mpr rest
        exact ⟨x::xs,by simp [plainArgs394,first,more,Option.bind]⟩
termination_by sizeOf xs
end

inductive ProjectableLiteral : SourceRhsCode394 → Prop where
  | nominal : PlainArguments args → ProjectableLiteral (.nominal ctor args)
  | tagged : PlainArguments args → ProjectableLiteral (.variant tag (.nominal ctor args))

theorem existing_literal_write_projection_has_exact_source_fragment (target : Nat) (code : SourceRhsCode394) :
    (∃ e, projectOldNativeLiteral394 target code = some e) ↔ ProjectableLiteral code := by
  cases code with
  | «variable» => exact ⟨by simp [projectOldNativeLiteral394],by intro h; cases h⟩
  | record => exact ⟨by simp [projectOldNativeLiteral394],by intro h; cases h⟩
  | join => exact ⟨by simp [projectOldNativeLiteral394],by intro h; cases h⟩
  | nominal ctor args =>
    constructor
    · intro h
      cases read : plainArgs394 args with
      | none => simp [projectOldNativeLiteral394,read] at h
      | some xs => exact .nominal ((plain_arguments_have_exact_recursive_source_fragment _).mp ⟨xs,read⟩)
    · intro h
      cases h with
      | nominal p =>
        obtain ⟨xs,r⟩ := (plain_arguments_have_exact_recursive_source_fragment _).mpr p
        exact ⟨.declared target (SourceRhsCode394.nominal ctor args).source xs,by simp [projectOldNativeLiteral394,r]⟩
  | variant tag inner =>
    cases inner with
    | nominal ctor args =>
      constructor
      · intro h
        cases read : plainArgs394 args with
        | none => simp [projectOldNativeLiteral394,read] at h
        | some xs => exact .tagged ((plain_arguments_have_exact_recursive_source_fragment _).mp ⟨xs,read⟩)
      · intro h
        cases h with
        | tagged p =>
          obtain ⟨xs,r⟩ := (plain_arguments_have_exact_recursive_source_fragment _).mpr p
          exact ⟨.declared target (SourceRhsCode394.variant tag (.nominal ctor args)).source xs,by simp [projectOldNativeLiteral394,r]⟩
    | «variable» | record | variant | join =>
      exact ⟨by simp [projectOldNativeLiteral394],by intro h; cases h⟩
theorem an_actual_associated_receipt_projects_iff_its_code_is_literal
    {s q f i} (out : OriginalCompoundOutput394 (s := s) (q := q) f i) :
    (∃ w, projectOldNativeLiteral394 out.emit.requested.target out.emit.rhs = some w) ↔
      ProjectableLiteral out.code :=
  existing_literal_write_projection_has_exact_source_fragment _ _

end Yulang.GeneralDeclarativeI65.NativeProducer394Boundary465
