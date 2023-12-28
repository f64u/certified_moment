
import «TypedAssembly».Common.TypEnv

/-- A Renτ Δ₁ Δ₂ is a a function that transforms a typ variable. -/
@[reducible]
def Renτ (Δ₁ Δ₂ : Ctxt) : Type :=
  ∀ {j}, (Δ₁ ∋⋆ j) → (Δ₂ ∋⋆ j)

/-- liftτ takes a Renτ and returns a different Renτ that does not
    alter the first variable but all other variables are further
    shifted right and have the Renτ applied to the shifted-left
    version of them.

    This transformation is helpful for renaming
    under the binders (namely ∀.) -/
def liftτ {Δ₁ Δ₂} : Renτ Δ₁ Δ₂ → ∀ {k},  Renτ (Δ₁ ,⋆ k) (Δ₂ ,⋆ k)
  |  _, _, _, .here => .here
  | rt, _, _, .there a => .there (rt a)

theorem liftτ_id : ∀ {Δ j k} {a : Δ ,⋆ k ∋⋆ j}, liftτ id a = a := by
  intros Δ j k a
  cases a <;> simp [liftτ]

theorem liftτ_comp : ∀ {Δ₁ Δ₂ Δ₃} {rt₁ : Renτ Δ₁ Δ₂} {rt₂ : Renτ Δ₂ Δ₃} {j k} {a : Δ₁ ,⋆ k ∋⋆ j},
                     liftτ (rt₂ ∘ rt₁) a = liftτ rt₂ (liftτ rt₁ a) := by
  intros Δ₁ Δ₂ Δ₃ rt₁ rt₂ j k a
  cases a <;> simp [liftτ]

