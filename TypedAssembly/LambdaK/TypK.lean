import «TypedAssembly».Common.TypEnv
import «TypedAssembly».Common.SubstOne

inductive TypK : Ctxt → Kind → Type where
  | var {j}    : Δ ∋⋆ j → TypK Δ j
  | int        : TypK Δ ⋆
  | unit       : TypK Δ ⋆ -- To call functions that take no arguments
  | for_all    : (Δ' : Ctxt) → TypK (Δ.extend Δ') ⋆ → TypK Δ ⋆  -- If you need multiple arguments, pass a product; abstract later
  | prod       : TypK Δ ⋆ → TypK Δ ⋆ → TypK Δ ⋆
namespace TypK
  infixl:90 " ⊢K⋆ " => TypK

  declare_syntax_cat typk
  syntax "!" term:max : typk
  syntax:90 "♯" num : typk
  syntax " int " : typk
  syntax "()" : typk
  syntax:50 typk:50 " × " typk:51 : typk
  syntax:20 ("∀ " " [ " term "].")? "( " (typk)? ") → void" : typk
  syntax:10 " () " " → " " void" : typk
  syntax " k⋆⟪ " typk " ⟫ " : term

  syntax " ( " typk " ) " : typk
  
  macro_rules 
  | `( k⋆⟪ !$t ⟫) => `($t)
  | `( k⋆⟪ int ⟫ ) => `(TypK.int)
  | `( k⋆⟪ () ⟫ ) => `(TypK.unit)
  | `( k⋆⟪ ♯$n ⟫ ) => `(TypK.var (by get_elem $n))
  | `( k⋆⟪ ∀[$c].($t) → void ⟫ ) => `(TypK.for_all $c k⋆⟪ $t ⟫)
  | `( k⋆⟪ ($t) → void ⟫ ) => `(TypK.for_all Ø k⋆⟪$t⟫)
  | `( k⋆⟪ () → void ⟫ ) => `(TypK.for_all Ø .unit)
  | `( k⋆⟪ $t₁ × $t₂ ⟫ ) => `(TypK.prod k⋆⟪ $t₁ ⟫ k⋆⟪ $t₂ ⟫)
  | `( k⋆⟪ ( $t ) ⟫ ) => `(k⋆⟪ $t ⟫)


  syntax "♯" num : term
  macro_rules
  | `(♯$n) => `(by get_elem $n)

  example : Ø ,⋆ ⋆ ,⋆ ⋆ ,⋆ ⋆ ⊢K⋆ ⋆ := k⋆⟪ ♯2 ⟫
  example : Ø                ⊢K⋆ ⋆ := k⋆⟪ () → void ⟫
  example : Ø                ⊢K⋆ ⋆ := k⋆⟪ (int × int × int) → void ⟫
  example : Ø ,⋆ ⋆           ⊢K⋆ ⋆ := k⋆⟪ ∀[Ø ,⋆ ⋆].(♯1 × int) → void ⟫

  example : k⋆⟪ (()) → void ⟫ =
           (k⋆⟪  ()  → void ⟫ : Δ ⊢K⋆ ⋆) := rfl
end TypK
open TypK
