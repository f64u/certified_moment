import «TypedAssembly».Util 

import Std.Data.List.Basic
import Lean.Data.AssocList
open Lean (AssocList)

inductive TCtx where
  | nil : TCtx
  | more : TCtx → TCtx
  deriving BEq, DecidableEq, Repr

namespace TCtx
  notation "∅⋆" => TCtx.nil
  prefix:max "⊹" => TCtx.more
end TCtx

open TCtx

inductive TypVar : TCtx → Type where
  | here : TypVar ⊹Δ
  | there : TypVar Δ → TypVar ⊹Δ
  deriving BEq, DecidableEq, Repr

namespace TypVar 
  postfix:max "✓" => TypVar 
end TypVar

open TypVar

inductive Typ : TCtx → Type where
  | var : Δ✓ → Typ Δ
  | int : Typ Δ
  | arrow : Typ Δ → Typ Δ → Typ Δ
  | for_all : Typ ⊹Δ → Typ Δ
  deriving BEq, DecidableEq, Repr

namespace Typ
  postfix:max " ⊢⋆ " => Typ

  declare_syntax_cat typvar
  syntax num : typvar
  syntax "♯" term : term

  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact TypVar.here)
  | n+1 => `(tactic| apply TypVar.there; get_elem $(Lean.quote n))

  macro "♯ " n:term:90 : term => `(Typ.var (by get_elem $n))

  def _x : Typ ⊹⊹⊹∅⋆ := ♯2
  #eval _x

  declare_syntax_cat typ
  syntax:10 "∀. " typ : typ
  syntax:50 typ (" → " <|> " -> ") typ : typ
  syntax:90 "♯" num : typ
  syntax " int " : typ
  syntax " ⋆⟪ " typ " ⟫ " : term

  syntax " ( " typ " ) " : typ
  
  macro_rules 
  | `( ⋆⟪ int ⟫ ) => `(Typ.int)
  | `( ⋆⟪ ♯$n ⟫ ) => `(♯$n)
  | `( ⋆⟪ $t₁:typ → $t₂:typ ⟫ ) => `(Typ.arrow ⋆⟪ $t₁ ⟫ ⋆⟪ $t₂ ⟫)
  | `( ⋆⟪ ∀. $t:typ ⟫) => `(Typ.for_all ⋆⟪ $t ⟫)
  | `( ⋆⟪ ( $t )  ⟫ ) => `(⋆⟪ $t ⟫)
end Typ

def polyidty : Typ ∅⋆ := ⋆⟪ ∀. ♯0 → ♯0 ⟫
#eval polyidty

@[reducible]
def Ren c₁ c₂ :=  c₁✓ → c₂✓

@[reducible]
def lift {c₁ c₂} : Ren c₁ c₂ → Ren ⊹c₁ ⊹c₂ 
  | _, .here => .here
  | r, .there a => .there (r a)

@[reducible]
def ren {c₁ c₂} : Ren c₁ c₂ → c₁⊢⋆ → c₂⊢⋆
  | _, .int => .int
  | r, .var a => .var (r a)
  | r, .arrow a b => .arrow (ren r a) (ren r b)
  | r, .for_all b => .for_all (ren (lift r) b)

@[reducible]
def weaken {c} : c⊢⋆ → (⊹c)⊢⋆ := ren TypVar.there

@[reducible]
def Subs c₁ c₂ := c₁✓ → c₂⊢⋆

@[reducible]
def lifts {c₁ c₂} : Subs c₁ c₂ → Subs ⊹c₁ ⊹c₂
  | _, .here => .var .here
  | s, .there a => weaken (s a)

@[reducible]
def subs {c₁ c₂} : Subs c₁ c₂ → c₁⊢⋆ → c₂⊢⋆
  | _, .int => .int
  | s, .var a => s a
  | s, .arrow a b => .arrow (subs s a) (subs s b)
  | s, .for_all b => .for_all (subs (lifts s) b)

@[reducible]
def inst {c₁ c₂} : Subs c₁ c₂ → c₂⊢⋆ → Subs ⊹c₁ c₂ 
  | _, t, TypVar.here => t
  | s, _, TypVar.there a => s a

macro b:term:80 "[" a:term:80 "]⋆" : term =>  `(subs (inst .var $a) $b)

#eval (⋆⟪ ♯0 → ♯0 ⟫ : @Typ ⊹∅⋆ )[.int]⋆

inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq, DecidableEq

inductive Ctx : TCtx → Type where
  | nil : Ctx Δ
  | cons_kind : Ctx Δ → Ctx ⊹Δ
  | cons_typ : Ctx Δ → c⊢⋆ → Ctx Δ

namespace Ctx
  infixl:50 " ‘ " => Ctx.cons_typ
  notation "∅" => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx Δ → Δ⊢⋆ → Type where
| here : Lookup (Γ ‘ t) t
| there : Lookup Γ t → Lookup (Γ ‘ t') t
| move : Lookup Γ t → Lookup Γ.cons_kind (weaken t)
deriving Repr

namespace Lookup
  infix:40 " ∋ " => Lookup
end Lookup
open Lookup

inductive Term : {Δ : TCtx} → Ctx Δ → Typ Δ → Type where
  | int {Γ : Ctx Δ} : Int → Term Γ .int
  | var {Γ : Ctx Δ} {t : Δ⊢⋆} : Γ ∋ t → Term Γ t
  | fix {Γ : Ctx Δ} {t₁ t₂ : Δ⊢⋆} : Term (Γ ‘ t₁ ‘ (.arrow t₁ t₂)) t₂ → Term Γ (.arrow t₁ t₂)
  | app {Γ : Ctx Δ} {t₁ t₂ : Δ⊢⋆} : Term Γ (.arrow t₁ t₂) → Term Γ t₁ → Term Γ t₂

  | Λ   {Γ : Ctx Δ} {t : (⊹Δ)⊢⋆} : Term Γ.cons_kind t → Term Γ (.for_all t)
  | sub {Γ : Ctx Δ} {t' : (⊹Δ)⊢⋆} : Term Γ (.for_all t') → (t : Δ⊢⋆) → Term Γ (t'[t]⋆)

  | prim  {Γ : Ctx Δ} : Term Γ .int → Prim → Term Γ .int → Term Γ .int
  | if0 {Γ : Ctx Δ} {t : Δ⊢⋆}: Term Γ .int → Term Γ t → Term Γ t → Term Γ t
  deriving Repr

namespace Term 
  infix:40 " ⊢ " => Term

  syntax "get_elem'" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem' $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.here)
  | n+1 => `(tactic| apply Lookup.there; get_elem' $(Lean.quote n))

  macro "# " n:term:90 : term => `(Term.var (by get_elem' $n))

  def _x : @Term ∅⋆ (∅ ‘ (@Typ.int ∅⋆) ‘ (@Typ.int ∅⋆)) .int := #1
  #eval _x
  
  declare_syntax_cat trm
  syntax num : trm 
  syntax "#" num : trm
  syntax " λ. " trm : trm
  syntax trm trm : trm
  syntax " Λ. " trm : trm
  syntax trm "[ " typ " ] " : trm
  syntax:20 trm:20 " + " trm:21 : trm
  syntax:20 trm:20 " - " trm:21 : trm
  syntax:30 trm:30 " * " trm:31 : trm
  syntax "if0 " trm " then " trm " else " trm " end " : trm

  syntax " ( " trm " ) " : trm

  syntax " ⟪ " trm " ⟫" : term

  macro_rules
    | `( ⟪ $i:num ⟫ ) => `(Term.int $i)
    | `( ⟪ #$i:num ⟫ ) => `(#$i)
    | `( ⟪ λ. $e ⟫ ) => `(Term.fix ⟪ $e ⟫)
    | `( ⟪ $e₁ $e₂  ⟫) => `(Term.app ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ )
    | `( ⟪ Λ. $e ⟫ ) => `(Term.Λ ⟪ $e ⟫ )
    | `( ⟪ $e[$t] ⟫ ) => `(Term.sub ⟪ $e ⟫ ⋆⟪ $t ⟫)
    | `( ⟪ $e₁ + $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.plus ⟪ $e₂ ⟫ )
    | `( ⟪ $e₁ - $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.minus ⟪ $e₂ ⟫ )
    | `( ⟪ $e₁ * $e₂ ⟫ ) => `(Term.prim ⟪ $e₁ ⟫ Prim.times ⟪$e₂ ⟫ )
    | `( ⟪ if0 $e₁ then $e₂ else $e₃ end ⟫ ) => `(Term.if0 ⟪ $e₁ ⟫ ⟪ $e₂ ⟫ ⟪ $e₃ ⟫ )

    | `( ⟪ ( $e ) ⟫ ) => `( ⟪ $e ⟫ )
end Term
open Term

def fact : @Term ∅⋆ ∅ ⋆⟪ int → int ⟫ :=
  Term.fix (Term.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (Term.prim (.var (.there .here)) .minus (.int 1)))))

def fact' Δ Γ : @Term Δ Γ ⋆⟪ int → int ⟫ := 
  ⟪ λ. if0 #1 then
         1
       else
         #1 * (#0 (#1 - 1))
       end ⟫
           

#eval fact

def sixfact := Term.app fact (.int 6)
#eval sixfact

def freeid : @Term ⊹∅⋆ ∅.cons_kind ⋆⟪ ♯0 → ♯0 ⟫ :=
 ⟪ λ. #1 ⟫

def intid : @Term ∅⋆ ∅ ⋆⟪ int → int ⟫ := 
  Term.sub (Term.Λ freeid) .int

#eval intid


