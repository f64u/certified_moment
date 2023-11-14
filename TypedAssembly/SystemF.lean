import «TypedAssembly».Util 

import Std.Data.List.Basic
import Lean.Data.AssocList
open Lean (AssocList)

inductive TCtx where
  | nil : TCtx
  | more : TCtx → TCtx
  deriving BEq, DecidableEq, Repr

namespace TCtx
  notation "∅" => TCtx.nil
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
end Typ

def polyidty : Typ ∅ := .for_all (.arrow (.var .here) (.var .here))
#eval polyidty

def Ren c₁ c₂ :=  c₁✓ → c₂✓

def lift {c₁ c₂} : Ren c₁ c₂ → Ren ⊹c₁ ⊹c₂ 
  | _, .here => .here
  | r, .there a => .there (r a)

def ren {c₁ c₂} : Ren c₁ c₂ → c₁⊢⋆ → c₂⊢⋆
  | _, .int => .int
  | r, .var a => .var (r a)
  | r, .arrow a b => .arrow (ren r a) (ren r b)
  | r, .for_all b => .for_all (ren (lift r) b)

def weaken {c} : c⊢⋆ → (⊹c)⊢⋆ := ren TypVar.there

def Subs c₁ c₂ := c₁✓ → c₂⊢⋆

def lifts {c₁ c₂} : Subs c₁ c₂ → Subs ⊹c₁ ⊹c₂
  | _, .here => .var .here
  | s, .there a => weaken (s a)

def subs {c₁ c₂} : Subs c₁ c₂ → c₁⊢⋆ → c₂⊢⋆
  | _, .int => .int
  | s, .var a => s a
  | s, .arrow a b => .arrow (subs s a) (subs s b)
  | s, .for_all b => .for_all (subs (lifts s) b)

def inst {c₁ c₂} : Subs c₁ c₂ → c₂⊢⋆ → Subs ⊹c₁ c₂ 
  | _, t, TypVar.here => t
  | s, _, TypVar.there a => s a

macro b:term:80 "[" a:term:80 "]⋆" : term =>  `(subs (inst .var $a) $b)

#eval (@Typ.arrow ⊹∅ (.var .here) (.var .here))[.int]⋆


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
  | int : Int → Term Γ .int
  | var : Γ ∋ t → Term Γ t
  | fix : Term (Γ ‘ t₁ ‘ (.arrow t₁ t₂)) t₂ → Term Γ (.arrow t₁ t₂)
  | app : Term Γ (.arrow t₁ t₂) → Term Γ t₁ → Term Γ t₂
  | Λ   : Term Γ.cons_kind t → Term Γ (.for_all t)
  | sub : (t' : (⊹Δ)⊢⋆) → Term Γ (.for_all t') → (t : Δ⊢⋆) → Term Γ (t'[t]⋆)
  | prim : Term Γ .int → Prim → Term Γ .int → Term Γ .int
  | if0 : Term Γ .int → Term Γ t → Term Γ t → Term Γ t
  deriving Repr

namespace Term 
  infix:40 " ⊢ " => Term
end Term
open Term

def fact : @Term ∅ Ctx.nil (.arrow .int .int) :=
  Term.fix (Term.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (Term.prim (.var (.there .here)) .minus (.int 1)))))

#eval fact

def sixfact := Term.app fact (.int 6)
#eval sixfact

def freeid Γ : @Term ⊹∅ Γ (.arrow (.var .here) (.var .here)) :=
  Term.fix (.var (.there .here))

def intid : @Term ∅ Ctx.nil (.arrow .int .int) := 
  Term.sub (.arrow (.var .here) (.var .here)) (Term.Λ (freeid _)) .int

#eval intid
