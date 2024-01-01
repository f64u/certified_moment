import «TypedAssembly».LambdaF.Typ

inductive Ctx : Ctxt → Type where
  | nil       : Ctx Ø
  | snoc_kind : Ctx Δ → ∀ j, Ctx (Δ ,⋆ j)
  | snoc_typ  : Ctx Δ → Δ ⊢F⋆ ⋆ → Ctx Δ

namespace Ctx
  infixl:50 " ,, " => Ctx.snoc_typ
  infixl:50 " ,,⋆ " => Ctx.snoc_kind
  notation " ∅ " => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx Δ → Δ ⊢F⋆ ⋆ → Type where
  | here  {Γ : Ctx Δ} {t : Δ ⊢F⋆ ⋆}     : Lookup (Γ ,, t) t
  | there {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : Lookup Γ t₁ → Lookup (Γ ,, t₂) t₁
  | move  {Γ : Ctx Δ} {t : Δ ⊢F⋆ ⋆} {k} : Lookup Γ t →
                                          Lookup (Γ ,,⋆ k) (weakenτ t)

namespace Lookup
  infix:40 " ∋ " => Lookup

  def toNat : Γ ∋ t → Nat × Nat
    | .here => (0, 0)
    | .there x => 
      let (n, m) := x.toNat 
      (n + 1, m)
    | .move x => 
      let (n, m) := x.toNat 
      (n, m + 1)

  def repr (x : Γ ∋ t) : String :=
    let (n, m) := x.toNat
    s!"#{m.repeat (· ++ "⊹") ""}{n}"
end Lookup
open Lookup

instance : Repr (Γ ∋ t) where
  reprPrec x _ := x.repr

def conv_ni {Δ Γ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : t₁ = t₂ → (Γ ∋ t₁) → Γ ∋ t₂
  | rfl, a => a

