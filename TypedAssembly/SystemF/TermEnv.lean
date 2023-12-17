import «TypedAssembly».SystemF.Typ

inductive Ctx : Ctxt → Type where
  | nil       : Ctx Ø
  | snoc_kind : Ctx Δ → ∀ j, Ctx (Δ ,⋆ j)
  | snoc_typ  : Ctx Δ → Δ ⊢⋆ ⋆ → Ctx Δ

namespace Ctx
  infixl:50 " ,, " => Ctx.snoc_typ
  infixl:50 " ,,⋆ " => Ctx.snoc_kind
  notation " ∅ " => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx Δ → Δ ⊢⋆ ⋆ → Type where
  | here  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆}     : Lookup (Γ ,, t) t
  | there {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢⋆ ⋆} : Lookup Γ t₁ → Lookup (Γ ,, t₂) t₁
  | move  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆} {k} : Lookup Γ t →
                                         Lookup (Γ ,,⋆ k) (weakenτ t)
deriving Repr

namespace Lookup
  infix:40 " ∋ " => Lookup
end Lookup
open Lookup

def conv_ni {Δ Γ} {t₁ t₂ : Δ ⊢⋆ ⋆} : t₁ = t₂ → (Γ ∋ t₁) → Γ ∋ t₂
  | rfl, a => a

