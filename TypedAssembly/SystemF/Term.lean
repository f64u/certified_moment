import «TypedAssembly».SystemF.Typ

inductive Ctx : Nat → Type where
  | nil : Ctx n
  | snoc_kind : Ctx n → Ctx (n + 1)
  | snoc_typ : Ctx n → n ⊢⋆ → Ctx n

namespace Ctx
  infixl:50 " ‘ " => Ctx.snoc_typ
  notation "∅" => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx n → n ⊢⋆ → Type where
  | here  {Γ : Ctx n} {t : n ⊢⋆} : Lookup (Γ ‘ t) t
  | there {Γ : Ctx n} {t : n ⊢⋆} : Lookup Γ t → Lookup (Γ ‘ t') t
  | move  {Γ : Ctx n} {t : n ⊢⋆} : Lookup Γ t →
                                   Lookup Γ.snoc_kind (liftTT 0 t)
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

inductive Term : (n : Nat) → Ctx n → Typ n → Type where
  | int  {Γ : Ctx n} : Int → Term n Γ .int
  | var  {Γ : Ctx n} {t : n⊢⋆} : Γ ∋ t → Term n Γ t

  | fix  {Γ : Ctx n} {t₁ t₂ : n⊢⋆} : Term n (Γ ‘ t₁ ‘ ⋆⟪ !t₁ → !t₂ ⟫) t₂ → Term n Γ ⋆⟪ !t₁ → !t₂ ⟫
  | app  {Γ : Ctx n} {t₁ t₂ : n⊢⋆} : Term n Γ ⋆⟪ !t₁ → !t₂ ⟫ → Term n Γ t₁ → Term n Γ t₂

  | Λ    {Γ : Ctx n} {t  : (n + 1)⊢⋆} : Term (n + 1) Γ.snoc_kind t → Term n Γ ⋆⟪ ∀. !t ⟫
  | sub  {Γ : Ctx n} {t' : (n + 1)⊢⋆} : Term n Γ ⋆⟪ ∀. !t' ⟫ → (t : n ⊢⋆) →
                                        Term n Γ (substTT 0 t t')

  | prim {Γ : Ctx n} : Term n Γ .int → Prim → Term n Γ .int → Term n Γ .int
  | pair {Γ : Ctx n} : Term n Γ t₁ → Term n Γ t₂ → Term n Γ ⋆⟪ !t₁ × !t₂ ⟫
  | fst  {Γ : Ctx n} : Term n Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term n Γ t₁
  | snd  {Γ : Ctx n} : Term n Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term n Γ t₂
  | if0  {Γ : Ctx n} {t : n⊢⋆} : Term n Γ .int → Term n Γ t → Term n Γ t → Term n Γ t
  deriving Repr

namespace Term 
  notation:10 Δ " ∣ " Γ " ⊢ " t => Term Δ Γ t

  syntax "get_elem'" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem' $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.here)
  | n+1 => `(tactic| apply Lookup.there; get_elem' $(Lean.quote n))

  macro "# " n:term:90 : term => `(Term.var (by get_elem' $n))

  example : 0 ∣ (∅ ‘ (@Typ.arrow 0 .int .int) ‘ (@Typ.int 0)) ⊢ ⋆⟪ int ⟫ := #0
  example : 0 ∣ (∅ ‘ (@Typ.arrow 0 .int .int) ‘ (@Typ.int 0)) ⊢ ⋆⟪ int → int ⟫ := #1
  
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

def fact : 0 ∣ ∅ ⊢ ⋆⟪ int → int ⟫ :=
  Term.fix (.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (Term.prim (.var (.there .here)) .minus (.int 1)))))

def fact' : 0 ∣ ∅ ⊢ ⋆⟪ int → int ⟫ := 
  ⟪ λ. if0 #1 then
         1
       else
         #1 * (#0 (#1 - 1))
       end ⟫

theorem fact_eq_fact' : fact = fact' := rfl

def sixfact := ⟪ !fact 6 ⟫

def freeid : 1 ∣ ∅.snoc_kind ⊢ ⋆⟪ ♯0 → ♯0 ⟫ :=
  ⟪ λ. #1 ⟫

def intid : 0 ∣ ∅ ⊢ ⋆⟪ int → int ⟫ :=
  ⟪ (Λ. !freeid)[int] ⟫

