import «TypedAssembly».SystemF.Typ

inductive Ctx : Ctxt → Type where
  | nil       : Ctx Ø
  | snoc_kind : Ctx Δ → ∀ j, Ctx (Δ ,⋆ j)
  | snoc_typ  : Ctx Δ → Δ ⊢⋆ ⋆ → Ctx Δ

namespace Ctx
  infixl:50 " ,, " => Ctx.snoc_typ
  infixl:50 " ,,⋆ " => Ctx.snoc_kind
  notation "∅" => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx Δ → Δ ⊢⋆ ⋆ → Type where
  | here  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆}     : Lookup (Γ ,, t) t
  | there {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢⋆ ⋆} : Lookup Γ t₁ → Lookup (Γ ,, t₂) t₁
  | move  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆} {k} : Lookup Γ t →
                                   Lookup (Γ ,,⋆ k) (weakent t)
deriving Repr

namespace Lookup
  infix:40 " ∋ " => Lookup
end Lookup
open Lookup

inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq, DecidableEq

inductive Term : {Δ : Ctxt} → Ctx Δ → Δ ⊢⋆ ⋆ → Type where
  | int  {Γ : Ctx Δ} : Int → Term Γ .int
  | var  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆} : Γ ∋ t → Term Γ t

  | fix  {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢⋆ ⋆} : Term (Γ ,, t₁ ,, ⋆⟪ !t₁ → !t₂ ⟫) t₂ → Term Γ ⋆⟪ !t₁ → !t₂ ⟫
  | app  {Γ : Ctx Δ} {t₁ t₂ : Δ ⊢⋆ ⋆} : Term Γ ⋆⟪ !t₁ → !t₂ ⟫ → Term Γ t₁ → Term Γ t₂

  | Λ    {Γ : Ctx Δ} {k} {t : Δ ,⋆ k ⊢⋆ ⋆} : Term (Γ ,,⋆ k) t → Term Γ ⋆⟪ ∀. !t ⟫
  | sub  {Γ : Ctx Δ} {k} {t₁ : Δ ,⋆ k ⊢⋆ ⋆} : Term Γ ⋆⟪ ∀. !t₁ ⟫ → (t₂ : Δ ⊢⋆ k) → Term Γ (t₁[t₂]⋆)

  | prim {Γ : Ctx Δ} : Term Γ .int → Prim → Term Γ .int → Term Γ .int
  | pair {Γ : Ctx Δ} : Term Γ t₁ → Term Γ t₂ → Term Γ ⋆⟪ !t₁ × !t₂ ⟫
  | fst  {Γ : Ctx Δ} : Term Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term Γ t₁
  | snd  {Γ : Ctx Δ} : Term Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term Γ t₂
  | if0  {Γ : Ctx Δ} {t : Δ ⊢⋆ ⋆} : Term Γ .int → Term Γ t → Term Γ t → Term Γ t
  deriving Repr

namespace Term 
  notation:10 Γ " ⊢ " t => Term Γ t

  syntax "get_elem'" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem' $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.here)
  | n+1 => `(tactic| apply Lookup.there; get_elem' $(Lean.quote n))

  macro "# " n:term:90 : term => `(Term.var (by get_elem' $n))

  example : (∅ ,, ⋆⟪ int → int ⟫ ,, .int) ⊢ ⋆⟪ int ⟫ := #0
  example : (∅ ,, ⋆⟪ int → int ⟫ ,, .int) ⊢ ⋆⟪ int → int ⟫ := #1
  
  declare_syntax_cat trm
  syntax "!" term:max : trm
  syntax num : trm 
  syntax "#" num : trm
  syntax " λ. " trm : trm
  syntax trm trm : trm
  syntax " Λ. " trm : trm
  syntax trm "[ " typ " ] " : trm
  syntax:20 trm:20 " + " trm:21 : trm
  syntax:20 trm:20 " - " trm:21 : trm
  syntax:30 trm:30 " * " trm:31 : trm
  syntax " ( " trm ", " trm " ) " : trm
  syntax "π₁" trm : trm
  syntax "π₂" trm : trm
  syntax "if0 " trm " then " trm " else " trm " end " : trm
  syntax "if0 " " ( " trm " , " trm " , " trm " ) " : trm

  syntax " ( " trm " ) " : trm
  syntax " ⟪ " trm " ⟫" : term

  macro_rules
    | `( ⟪ !$t ⟫) => `($t)
    | `( ⟪ $i:num ⟫ ) => `(Term.int $i)
    | `( ⟪ #$i:num ⟫ ) => `(#$i)
    | `( ⟪ λ. $e ⟫ ) => `(Term.fix ⟪ $e ⟫)
    | `( ⟪ $e₁ $e₂  ⟫) => `(Term.app ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ )
    | `( ⟪ Λ. $e ⟫ ) => `(Term.Λ ⟪ $e ⟫ )
    | `( ⟪ $e[$t] ⟫ ) => `(Term.sub ⟪ $e ⟫ ⋆⟪ $t ⟫)
    | `( ⟪ $e₁ + $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.plus ⟪ $e₂ ⟫ )
    | `( ⟪ $e₁ - $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.minus ⟪ $e₂ ⟫ )
    | `( ⟪ $e₁ * $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.times ⟪$e₂ ⟫ )
    | `( ⟪ ($e₁, $e₂) ⟫) => `(Term.pair ⟪ $e₁ ⟫ ⟪$e₂ ⟫ )
    | `( ⟪ π₁ $e ⟫) => `(Term.fst ⟪ $e ⟫ )
    | `( ⟪ π₂ $e ⟫) => `(Term.snd ⟪ $e ⟫ )
    | `( ⟪ if0 $e₁ then $e₂ else $e₃ end ⟫ ) => `(Term.if0 ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ ⟪ $e₃ ⟫ )
    | `( ⟪ if0 ($e₁, $e₂, $e₃) ⟫ ) => `(Term.if0 ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ ⟪ $e₃ ⟫ )

    | `( ⟪ ( $e ) ⟫ ) => `( ⟪ $e ⟫ ) 
end Term
open Term

def fact :  ∅ ⊢ ⋆⟪ int → int ⟫ :=
  Term.fix (.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (Term.prim (.var (.there .here)) .minus (.int 1)))))

def fact' : ∅ ⊢ ⋆⟪ int → int ⟫ := 
  ⟪ λ. if0 #1 then
         1
       else
         #1 * (#0 (#1 - 1))
       end ⟫

theorem fact_eq_fact' : fact = fact' := rfl

def sixfact := ⟪ !fact 6 ⟫

def freeid : (∅ ,,⋆ ⋆) ⊢ ⋆⟪ ♯0 → ♯0 ⟫ :=
  ⟪ λ. #1 ⟫

def intid : ∅ ⊢ ⋆⟪ int → int ⟫ :=
  ⟪ (Λ. !freeid)[int] ⟫


