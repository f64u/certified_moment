inductive Typ : Nat → Type where
  | var     : (x : Fin n) → Typ n
  | int     : Typ n
  | arrow   : Typ n → Typ n → Typ n
  | prod    : Typ n → Typ n → Typ n
  | for_all : Typ (n + 1) → Typ n
  deriving BEq, DecidableEq, Repr

namespace Typ
  postfix:90 " ⊢⋆ " => Typ
  prefix:max " ♯ " => Typ.var
  example : Typ 10 := ♯2

  declare_syntax_cat typ
  syntax "!" term:max : typ
  syntax:10 "∀. " typ : typ
  syntax:50 typ (" → " <|> " -> ") typ : typ
  syntax:50 typ " × " typ : typ
  syntax:90 "♯" num : typ
  syntax " int " : typ
  syntax " ⋆⟪ " typ " ⟫ " : term

  syntax " ( " typ " ) " : typ
  
  macro_rules 
  | `( ⋆⟪ !$t ⟫) => `($t)
  | `( ⋆⟪ int ⟫ ) => `(Typ.int)
  | `( ⋆⟪ ♯$n ⟫ ) => `(♯$n)
  | `( ⋆⟪ $t₁:typ → $t₂:typ ⟫ ) => `(Typ.arrow ⋆⟪ $t₁ ⟫ ⋆⟪ $t₂ ⟫)
  | `( ⋆⟪ $t₁:typ × $t₂:typ ⟫ ) => `(Typ.prod ⋆⟪ $t₁ ⟫ ⋆⟪ $t₂ ⟫)
  | `( ⋆⟪ ∀. $t:typ ⟫) => `(Typ.for_all ⋆⟪ $t ⟫)
  | `( ⋆⟪ ( $t )  ⟫ ) => `(⋆⟪ $t ⟫)

  def polyidt : n ⊢⋆ := ⋆⟪ ∀. ♯0 → ♯0 ⟫

end Typ
open Typ

@[simp, reducible] def liftTT (d : Nat) : n ⊢⋆ → (n + 1) ⊢⋆
  | .var ix => 
    if d <= ix then
      (.var (ix.succ))
    else .var (Fin.ofNat ix.val)
  | .int => .int
  | .arrow t₁ t₂ => .arrow (liftTT d t₁) (liftTT d t₂)
  | .prod t₁ t₂ => .prod (liftTT d t₁) (liftTT d t₂)
  | .for_all t => .for_all (liftTT d.succ t)

example : liftTT 0 ⋆⟪ ♯0 → ♯0 ⟫ = (⋆⟪ ♯1 → ♯1 ⟫ : 2 ⊢⋆) := rfl
example : liftTT 1 ⋆⟪ ♯0 → ♯0 ⟫ = (⋆⟪ ♯0 → ♯0 ⟫ : 3 ⊢⋆) := rfl
example : liftTT 1 ⋆⟪ ♯0 → ♯1 ⟫ = (⋆⟪ ♯0 → ♯2 ⟫ : 3 ⊢⋆) := rfl
example : liftTT 0 (@polyidt 1) = (@polyidt 2)          := rfl 

@[reducible] def substTT (d : Fin (n + 1)) (u : n ⊢⋆) : (n + 1) ⊢⋆ → n ⊢⋆
  | .var ix => 
    if h₀ : d.val = ix.val then
      u
    else if h₁ : ix.val >= d then by
      cases ix
      cases d 
      simp at *
      rename_i valix isLtix vald isLtd
      unfold GE.ge at h₁
      have a1 := Nat.lt_of_le_of_ne h₁ h₀
      simp_arith at *
      have a2 : vald + 1 ≤ n := Nat.le_trans a1 isLtix
      have : n > 0 := by
        unfold GT.gt
        have a3 : vald < n := a2
        exact (Nat.zero_lt_of_lt a3)
      exact (.var (Fin.ofNat' (valix - 1) this))
    else by
      rw [Nat.not_ge_eq] at h₁
      cases ix
      cases d 
      simp at *
      rename_i valix isLtix vald isLtd
      simp_arith at *
      clear isLtix h₀
      have w : valix + 1 ≤ n := by
        apply Nat.le_trans
        case m => exact vald 
        · assumption
        · assumption
      simp_arith at w
      have : n > 0 := by
        unfold GT.gt
        have : valix < n := w
        exact (Nat.zero_lt_of_lt this)
      exact (.var (Fin.ofNat' valix this))
  | .int => .int
  | .arrow t₁ t₂ => .arrow (substTT d u t₁) (substTT d u t₂)
  | .prod t₁ t₂ => .prod (substTT d u t₁) (substTT d u t₂)
  | .for_all t => .for_all (substTT d.succ (liftTT 0 u) t)
     
example : substTT 0 .int (⋆⟪ ♯0 → ♯0 ⟫ : 1 ⊢⋆) = ⋆⟪ int → int ⟫ := rfl
example : substTT 1 .int (⋆⟪ ♯0 → ♯0 ⟫ : 2 ⊢⋆) = ⋆⟪ ♯0 → ♯0 ⟫ := rfl
example : substTT 1 .int (⋆⟪ ♯0 → ♯1 ⟫ : 2 ⊢⋆) = ⋆⟪ ♯0 → int ⟫ := rfl
example : substTT 1 ♯0 (⋆⟪ ♯0 → ♯1 ⟫ : 2 ⊢⋆) = ⋆⟪ ♯0 → ♯0 ⟫ := rfl


theorem liftTT_liftTT : ∀ n n' k (t : k ⊢⋆), 
  liftTT n (liftTT (n + n') t) =
  liftTT (1 + (n + n')) (liftTT n t) := by
  intros n n' k t
  unfold liftTT
  admit

