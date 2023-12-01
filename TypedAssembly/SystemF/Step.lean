import «TypedAssembly».SystemF.Term

abbrev interp : Prim → (Int → Int → Int)
  | .plus => Int.add
  | .minus => Int.sub
  | .times => Int.mul

inductive Step {Δ Γ} : (Δ ∣ Γ ⊢ t) → (Δ ∣ Γ ⊢ t) → Prop

  | prim_exec  : Step (.prim (.int n₁) p (.int n₂)) (.int (interp p n₁ n₂))
  | prim_left  : Step a a' → Step (.prim a p b) (.prim a' p b)
  | prim_right : Step b b' → Step (.prim (.int n) p b) (.prim (.int n) p b')

  | fst_exec   : Step ⟪ π₁(!e, !_) ⟫ e
  | fst_steps  : Step e e' →  Step (.fst e) (.fst e')

  | snd_exec   : Step ⟪ π₂(!_, !e) ⟫ e
  | snd_steps  : Step e e' →  Step (.snd e) (.snd e')

  | if0_exec   : Step ⟪ if0 0 then !b else !c end ⟫ b
  | ifn0_exec  : n ≠ 0 → Step ⟪ if0 !(.int n) then !b else !c end ⟫ c
  | if_steps   : Step a a' → Step ⟪ if0 !a then !b else !c end ⟫ ⟪ if0 !a' then !b else !c end ⟫

inductive MultiStep {Δ Γ t} : (Δ ∣ Γ ⊢ t) → (Δ ∣ Γ ⊢ t) → Prop 
  | refl {a} : MultiStep a a
  | step {a b c} : Step a b → MultiStep b c → MultiStep a c

theorem «1+1 -->* 2» : MultiStep (Δ := 0) (Γ := ∅) ⟪ if0 0 then 1 + 1 else 5 end ⟫ ⟪ 2 ⟫ :=
  by repeat constructor

