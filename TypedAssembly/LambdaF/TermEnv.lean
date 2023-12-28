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
deriving Repr

namespace Lookup
  infix:40 " ∋ " => Lookup
end Lookup
open Lookup

def conv_ni {Δ Γ} {t₁ t₂ : Δ ⊢F⋆ ⋆} : t₁ = t₂ → (Γ ∋ t₁) → Γ ∋ t₂
  | rfl, a => a

