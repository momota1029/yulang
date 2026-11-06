import Yulang.CoreEffectGeneration

namespace Yulang.Core.EffectTyping
open Inference (Model Comp)
open RowInference (RowAlgebra RowView)
variable {s : Core.Signature} {m : Model} {algebra : RowAlgebra s.Key s.Scope}
variable {view : RowView m algebra} {contract : Contract s m}

/-- Semantic generation exactness, uniformly over all model/row interfaces.
No success, fuel, solver, runtime validity or closedness premise occurs. -/
theorem generate_models_iff_typing (e : Core.Expr s) (sΓ : SchemeEnv m)
    (Γ : List (Binding m s)) (c : Comp m)
    (henv : EnvRel (view := view) (contract := contract) sΓ Γ) :
    generate view contract sΓ e c ↔ Typing m view contract Γ e c := by
  cases e
  case var n =>
      change lookup sΓ n c ↔ _
      rw [henv]
      exact ⟨fun ⟨_, h, hb⟩ => .var h hb, fun h => by cases h; exact ⟨_, ‹_›, ‹_›⟩⟩
  case lit b => exact ⟨Typing.lit, fun h => by cases h; assumption⟩
  case emptyRecord => exact ⟨Typing.emptyRecord, fun h => by cases h; assumption⟩
  case lam body =>
      have ih := generate_models_iff_typing body
      constructor
      · rintro ⟨a, b, hb, bound⟩
        exact .lam ((ih _ _ _ (henv.mono a)).mp hb) bound
      · intro h; cases h with
        | lam hb bound => exact ⟨_, _, (ih _ _ _ (henv.mono _)).mpr hb, bound⟩
  case app f x =>
      have ihf := generate_models_iff_typing f
      have ihx := generate_models_iff_typing x
      constructor
      · rintro ⟨a, b, ef, hf, hx, bound⟩
        exact .app ((ihf _ _ _ henv).mp hf) ((ihx _ _ _ henv).mp hx) bound
      · intro h; cases h with
        | app hf hx bound => exact ⟨_, _, _, (ihf _ _ _ henv).mpr hf, (ihx _ _ _ henv).mpr hx, bound⟩
  case letE hint v body =>
      have ihv := generate_models_iff_typing v
      have ihb := generate_models_iff_typing body
      cases hint with
      | some name => exact ⟨False.elim, fun h => by cases h⟩
      | none =>
        have poly : EnvRel (view := view) (contract := contract)
            ((fun d => generate view contract sΓ v (Comp.pure m d.1) ∧ m.subRow m.empty d.2) :: sΓ)
            (.poly v Γ :: Γ) := by
          apply henv.cons
          intro d
          rw [ihv _ _ _ henv]
          exact ⟨fun ⟨hv, hr⟩ => .poly hv hr, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
        constructor
        · intro h
          rcases h with ⟨value, a, hv, hb⟩ | ⟨a, b, hv, hb, bound⟩
          · exact .letValue value ((ihv _ _ _ henv).mp hv) ((ihb _ _ _ poly).mp hb)
          · exact .letComputed ((ihv _ _ _ henv).mp hv) ((ihb _ _ _ (henv.mono _)).mp hb) bound
        · intro h; cases h with
          | letValue value hv hb => exact Or.inl ⟨value, _, (ihv _ _ _ henv).mpr hv, (ihb _ _ _ poly).mpr hb⟩
          | letComputed hv hb bound => exact Or.inr ⟨_, _, (ihv _ _ _ henv).mpr hv, (ihb _ _ _ (henv.mono _)).mpr hb, bound⟩
  case branch g y n =>
      have ihg := generate_models_iff_typing g
      have ihy := generate_models_iff_typing y
      have ihn := generate_models_iff_typing n
      constructor
      · rintro ⟨eg, a, b, hg, hy, hn, bound⟩
        exact .branch ((ihg _ _ _ henv).mp hg) ((ihy _ _ _ henv).mp hy) ((ihn _ _ _ henv).mp hn) bound
      · intro h; cases h with
        | branch hg hy hn bound => exact ⟨_, _, _, (ihg _ _ _ henv).mpr hg, (ihy _ _ _ henv).mpr hy, (ihn _ _ _ henv).mpr hn, bound⟩
  case pair x y =>
      have ihx := generate_models_iff_typing x
      have ihy := generate_models_iff_typing y
      constructor
      · rintro ⟨a, b, hx, hy, bound⟩
        exact .pair ((ihx _ _ _ henv).mp hx) ((ihy _ _ _ henv).mp hy) bound
      · intro h; cases h with
        | pair hx hy bound => exact ⟨_, _, (ihx _ _ _ henv).mpr hx, (ihy _ _ _ henv).mpr hy, bound⟩
  case fst x =>
      have ih := generate_models_iff_typing x
      constructor
      · rintro ⟨a, b, er, hx, bound⟩
        exact .fst ((ih _ _ _ henv).mp hx) bound
      · intro h; cases h with
        | fst hx bound => exact ⟨_, _, _, (ih _ _ _ henv).mpr hx, bound⟩
  case snd x =>
      have ih := generate_models_iff_typing x
      constructor
      · rintro ⟨a, b, er, hx, bound⟩
        exact .snd ((ih _ _ _ henv).mp hx) bound
      · intro h; cases h with
        | snd hx bound => exact ⟨_, _, _, (ih _ _ _ henv).mpr hx, bound⟩
  case record l x rest =>
      have ihx := generate_models_iff_typing x
      have ihr := generate_models_iff_typing rest
      constructor
      · rintro ⟨a, b, hx, hr, record, bound⟩
        exact .record ((ihx _ _ _ henv).mp hx) ((ihr _ _ _ henv).mp hr) record bound
      · intro h; cases h with
        | record hx hr record bound => exact ⟨_, _, (ihx _ _ _ henv).mpr hx, (ihr _ _ _ henv).mpr hr, record, bound⟩
  case field l x =>
      have ih := generate_models_iff_typing x
      constructor
      · rintro ⟨a, er, hx, bound⟩
        exact .field ((ih _ _ _ henv).mp hx) bound
      · intro h; cases h with
        | field hx bound => exact ⟨_, _, (ih _ _ _ henv).mpr hx, bound⟩
  case variant l x =>
      have ih := generate_models_iff_typing x
      constructor
      · rintro ⟨a, hx, bound⟩
        exact .variant ((ih _ _ _ henv).mp hx) bound
      · intro h; cases h with
        | variant hx bound => exact ⟨_, (ih _ _ _ henv).mpr hx, bound⟩
  case request op payload =>
      have ih := generate_models_iff_typing payload
      constructor
      · rintro ⟨ι, er, hp, ht, hr⟩
        exact .request ((ih _ _ _ henv).mp hp) ht hr
      · intro h; cases h with
        | request hp ht hr => exact ⟨_, _, (ih _ _ _ henv).mpr hp, ht, hr⟩
  case boundary boundary body =>
      have ih := generate_models_iff_typing body
      constructor
      · rintro ⟨input, hb, ht, hr⟩
        exact .boundary ((ih _ _ _ henv).mp hb) ht hr
      · intro h; cases h with
        | boundary hb ht hr => exact ⟨_, (ih _ _ _ henv).mpr hb, ht, hr⟩
  case handler op action onReturn onOperation =>
      have iha := generate_models_iff_typing action
      have ihr := generate_models_iff_typing onReturn
      have iho := generate_models_iff_typing onOperation
      constructor
      · rintro ⟨permission, input, returned, operated, ha, hr, ho, ht, he⟩
        exact .handler permission ((iha _ _ _ henv).mp ha) ((ihr _ _ _ (henv.mono _)).mp hr)
          (fun ι => (iho _ _ _ ((henv.mono _).mono _)).mp (ho ι)) ht he
      · intro h; cases h with
        | handler permission ha hr ho ht he =>
          exact ⟨permission, _, _, _, (iha _ _ _ henv).mpr ha, (ihr _ _ _ (henv.mono _)).mpr hr,
            fun ι => (iho _ _ _ ((henv.mono _).mono _)).mpr (ho ι), ht, he⟩
  case multiHandler ops action onReturn bodies =>
      have iha := generate_models_iff_typing action
      have ihr := generate_models_iff_typing onReturn
      have iho := fun i => generate_models_iff_typing (bodies i)
      constructor
      · rintro ⟨permission, input, returned, operated, ha, hr, ho, ht, he⟩
        exact .multiHandler permission ((iha _ _ _ henv).mp ha) ((ihr _ _ _ (henv.mono _)).mp hr)
          (fun ι i => (iho i _ _ _ ((henv.mono _).mono _)).mp (ho ι i)) ht he
      · intro h; cases h with
        | multiHandler permission ha hr ho ht he =>
          exact ⟨permission, _, _, _, (iha _ _ _ henv).mpr ha, (ihr _ _ _ (henv.mono _)).mpr hr,
            fun ι i => (iho i _ _ _ ((henv.mono _).mono _)).mpr (ho ι i), ht, he⟩
  case partialHandler arms action onReturn bodies =>
      have iha := generate_models_iff_typing action
      have ihr := generate_models_iff_typing onReturn
      have iho := fun i => generate_models_iff_typing (bodies i)
      constructor
      · rintro ⟨permission, input, returned, operated, ha, hr, ho, ht, he⟩
        exact .partialHandler permission ((iha _ _ _ henv).mp ha) ((ihr _ _ _ (henv.mono _)).mp hr)
          (fun ι i => (iho i _ _ _ ((henv.mono _).mono _)).mp (ho ι i)) ht he
      · intro h; cases h with
        | partialHandler permission ha hr ho ht he =>
          exact ⟨permission, _, _, _, (iha _ _ _ henv).mpr ha, (ihr _ _ _ (henv.mono _)).mpr hr,
            fun ι i => (iho i _ _ _ ((henv.mono _).mono _)).mpr (ho ι i), ht, he⟩
  all_goals try exact ⟨False.elim, fun h => by cases h⟩
termination_by structural e

/-- Every closed Core term, including nested total and partial handlers; no
support premise is needed because unsupported terms are false on both sides. -/
theorem principal_exact (e : Core.Expr s) (c : Comp m) :
    generate view contract [] e c ↔ Core.Typing (model m view contract) [] e c :=
  generate_models_iff_typing e [] [] c EnvRel.nil

end Yulang.Core.EffectTyping
