import «TypedAssembly».LambdaF.Term

inductive Value : {Γ : Ctx Δ} → {t : Δ ⊢F⋆ ⋆} → (Γ ⊢F t) → Prop where
  | v_int  : Value (.int i)
  | v_unit : Value .unit
  | v_fix  : Value (.fix e)
  | v_Λ    : Value e → Value (.Λ e)
  | v_pair : Value e₁ → Value e₂ → Value (.pair e₁ e₂)

inductive Step : {Δ : Ctxt} → {Γ : Ctx Δ} → {t : Δ ⊢F⋆ ⋆} → (Γ ⊢F t) → (Γ ⊢F t) → Prop
  | app_exec   : Value a → Step (.app (.fix e) a) (e.[weaken a].[.fix e])
  | app_right  : Value a → Step b b' → Step (.app a b) (.app a b')
  | app_left   : Step a a' → Step (.app a e) (.app a' e)
  
  | Λ_steps    : Step e e' → Step (.Λ e) (.Λ e')

  | sub_exec   : Value e → Step (.sub (.Λ e) t) (e⋆[t])
  | sub_steps  : Step e e' → Step (.sub e t) (.sub e' t)

  | prim_exec  : Step (.prim (.int i₁) p (.int i₂)) (.int (interp p i₁ i₂))
  | prim_right : Step b b' → Step (.prim (.int i) p b) (.prim (.int i) p b')
  | prim_left  : Step a a' → Step (.prim a p b) (.prim a' p b)
  
  | pair_left  : Step a a' → Step f⟪ (!a, !b) ⟫ f⟪ (!a', !b) ⟫
  | pair_right : Value a → Step b b' → Step f⟪ (!a, !b) ⟫ f⟪ (!a, !b') ⟫

  | fst_exec   : Step f⟪ π₁(!e, !e') ⟫ e
  | fst_steps  : Step e e' →  Step (.fst e) (.fst e')

  | snd_exec   : Step f⟪ π₂(!e', !e) ⟫ e
  | snd_steps  : Step e e' →  Step (.snd e) (.snd e')

  | if0_exec   : Step f⟪ if0 0 then !b else !c end ⟫ b
  | ifn0_exec  : n ≠ 0 → Step f⟪ if0 !(.int n) then !b else !c end ⟫ c
  | if_steps   : Step a a' → Step f⟪ if0 !a then !b else !c end ⟫ f⟪ if0 !a' then !b else !c end ⟫

namespace Step 
  infixr:90 " ==> " => Step
end Step
open Step

inductive MultiStep {Δ} {Γ : Ctx Δ} {t : Δ ⊢F⋆ ⋆} : (Γ ⊢F t) → (Γ ⊢F t) → Prop 
  | refl {a} : MultiStep a a
  | step {a b c} : a ==> b → MultiStep b c → MultiStep a c

namespace MultiStep 
  infixr:90 " ==>* " => MultiStep
end MultiStep
open MultiStep

example : f⟪ if0 0 then 1 + 1 * 1 else 5 * 1 end ⟫ ==>* (f⟪ 2 ⟫ : ∅ ⊢F .int) := by
  repeat constructor

example : f⟪ if0 1 then 1 + 1 * 1 else 5 * 1 end ⟫ ==>* (f⟪ 5 ⟫ : ∅ ⊢F .int) := by
  repeat constructor
  · intros contra; contradiction
  · repeat constructor

open Examples in
example : f⟪ !fact 0 ⟫ ==>* f⟪ 1 ⟫ := by
  repeat constructor

open Examples in
example : f⟪ !fact 3 ⟫ ==>* f⟪ 6 ⟫ := by
  unfold fact
  apply MultiStep.step
  · apply Step.app_exec
    constructor
  · apply MultiStep.step
    · simp [subs_one, conv_ent, subs, extend]
      apply Step.ifn0_exec
      intros contra; contradiction
    · constructor
      · constructor
        apply Step.app_right
        · constructor
        · constructor
      · apply MultiStep.step
        · apply Step.prim_right
          repeat constructor
        · simp [subs_one, conv_ent, subs, extend]
          apply MultiStep.step
          · apply Step.prim_right
            apply Step.ifn0_exec
            intros contra; contradiction
          · constructor
            apply Step.prim_right
            apply Step.prim_right
            apply Step.app_right
            · constructor
            · constructor
            · constructor
              · apply Step.prim_right
                apply Step.prim_right
                apply Step.app_exec
                constructor
              · simp [subs_one, conv_ent, subs, extend]
                constructor
                apply Step.prim_right
                · apply Step.prim_right
                  apply Step.ifn0_exec
                  intros contra; contradiction
                · constructor
                  apply Step.prim_right
                  · apply Step.prim_right
                    apply Step.prim_right
                    apply Step.app_right
                    constructor
                    constructor
                  · constructor
                    · apply Step.prim_right
                      apply Step.prim_right
                      apply Step.prim_right
                      apply Step.app_exec
                      constructor
                    · constructor
                      apply Step.prim_right
                      apply Step.prim_right
                      apply Step.prim_right
                      simp [subs_one, conv_ent, subs]
                      apply Step.if0_exec
                      repeat constructor <;> repeat constructor

open Examples in
example : f⟪ !intid 6 ⟫ ==>* f⟪ 6 ⟫ := by
  unfold intid
  constructor
  · apply Step.app_left
    apply Step.sub_exec
    constructor
  constructor 
  · apply Step.app_exec
    constructor
  · simp [subs_one, conv_ent, subs]
    constructor

open Examples in
example : f⟪ ((!twice)[int] !intid) 6 ⟫ ==>* f⟪ 6 ⟫ := by
  unfold intid
  unfold twice
  unfold polyid
  constructor
  · apply Step.app_left
    · apply Step.app_left
      · apply Step.sub_exec
        constructor
  · constructor
    · apply Step.app_left
      · apply Step.app_right
        simp [tsubs_one, subs]
        constructor
        constructor
        constructor
    · constructor
      · apply Step.app_left
        · apply Step.app_exec
          simp [tsubs_one, subs]
          constructor
      · simp [subs_one, conv_ent, subs]
        constructor
        · apply Step.app_exec
          constructor
        · simp [subs_one, conv_ent, subs]
          constructor
          · apply Step.app_right
            constructor
            · apply Step.app_exec
              constructor
          · constructor
            · apply Step.app_exec
              simp [subs_one, conv_ent, subs]
              constructor
            · simp_all!
              simp [subs_one, conv_ent, subs]
              apply MultiStep.refl
