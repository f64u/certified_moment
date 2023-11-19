
/-- A TCtx is essentally a Nat, representing the size of our
    typing context -/
inductive TCtx where
  | nil : TCtx
  | more : TCtx → TCtx
  deriving BEq, DecidableEq, Repr

namespace TCtx
  notation "∅⋆" => TCtx.nil
  prefix:max "⊹" => TCtx.more
end TCtx

open TCtx

/-- A TypVar is essentially a Fin n, i.e., a pointer inside a Nat -/
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
  | prod : Typ Δ → Typ Δ → Typ Δ
  | for_all : Typ ⊹Δ → Typ Δ
  deriving BEq, DecidableEq, Repr

namespace Typ
  postfix:90 " ⊢⋆ " => Typ

  declare_syntax_cat typvar
  syntax num : typvar
  syntax "♯" term : term

  syntax "get_elem" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem $n) => match n.1.toNat with
  | 0 => `(tactic | exact TypVar.here)
  | n+1 => `(tactic| apply TypVar.there; get_elem $(Lean.quote n))

  macro "♯ " n:term:90 : term => `(Typ.var (by get_elem $n))

  example :
    Typ.var (TypVar.there (TypVar.there (TypVar.here))) = (♯2 : Typ ⊹⊹⊹∅⋆) := rfl 

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

  def polyidty : ∅⋆ ⊢⋆ := ⋆⟪ ∀. ♯0 → ♯0 ⟫
end Typ
open Typ


/-- A Ren⋆ Δ₁ Δ₂ is a funciton that takes a typ variable and moves it
    from the first typing context to the second -/
@[reducible]
def Rent Δ₁ Δ₂ := Δ₁✓ → Δ₂✓

/-- lift⋆ takes a Ren⋆ and returns a different Ren⋆ that operates in a typing context
    where the meaning of the first typvar is unaffected but all later typ variable
    are shifted by 1 position -/
@[reducible]
def liftt {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → Rent ⊹Δ₁ ⊹Δ₂ 
  | _, .here => .here
  | r, .there a => .there (r a)

/-- ren⋆ takes a Ren⋆ and a typ and moves all the typ variables in that typ to the
    new context -/
@[reducible]
def rent {Δ₁ Δ₂} : Rent Δ₁ Δ₂ → Δ₁⊢⋆ → Δ₂⊢⋆
  | _, .int => .int
  | r, .var a => .var (r a)
  | r, .arrow a b => .arrow (rent r a) (rent r b)
  | r, .prod a b => .prod (rent r a) (rent r b)
  | r, .for_all b => .for_all (rent (liftt r) b)

/-- weaken⋆ shifts over all typ variables in a variable by 1 position,
    e.g. ⋆⟪ ♯0 → ♯0 ⟫ : ⊹∅⋆ ⊢⋆ becomes ⋆⟪ ♯1 → ♯1 ⟫ : ⊹⊹∅⋆ ⊢⋆ -/
@[reducible]
def weakent {c} : c⊢⋆ → (⊹c)⊢⋆ := rent TypVar.there

/-- A Subs⋆ Δ₁ Δ₂ is a function that takes a typ variable and returns 
    a typ (in a possibly modified context) that should be in its place -/
def Subst Δ₁ Δ₂ := Δ₁✓ → Δ₂⊢⋆

/-- lifts⋆ takes a Subs⋆ and returns a different Subs⋆ that operates in a typing context where
    the meaning of the first typevar is unaffected but all later type variables are shifted by 1 position -/
@[reducible, simp]
def liftst {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → Subst ⊹Δ₁ ⊹Δ₂
  | _, .here => .var .here
  | s, .there a => weakent (s a)

/-- subs⋆ takes a Subs⋆ and a type and replaces the relevant type variable with that type, 
    returning a new type (in a possibly modified context) -/
@[reducible, simp]
def subst {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → Δ₁⊢⋆ → Δ₂⊢⋆
  | _, .int => .int
  | s, .var a => s a
  | s, .arrow a b => .arrow (subst s a) (subst s b)
  | s, .prod a b => .prod (subst s a) (subst s b)
  | s, .for_all b => .for_all (subst (liftst s) b)

/-- inst⋆ takes a Subs⋆ and a type and returns a Subs⋆ that
    replaces the position 0 type variables with that type, otherwise 
    it applies the first Subs⋆ to a shifted down typevar -/
@[reducible]
def instt {Δ₁ Δ₂} : Subst Δ₁ Δ₂ → Δ₂⊢⋆ → Subst ⊹Δ₁ Δ₂ 
  | _, t, TypVar.here => t
  | s, _, TypVar.there a => s a

macro b:term:80 "[" a:term:80 "]⋆" : term =>
  -- .var is indeed the identity Subs⋆, so this replaces ♯0
  -- with $a, otherwise makes ♯n ♯(n-1)
  `(subst (instt .var $a) $b) 

theorem «.var is identity subst» : ∀ (t : Δ⊢⋆), subst .var t = t := by
  intros t
  induction t <;>
    try rfl 
  case arrow =>
    simp
    constructor <;> assumption
  case prod =>
    simp
    constructor <;> assumption

  case for_all Δ' t' t_ih =>
    simp only [subst]
    congr
    have : @liftst Δ' Δ' Typ.var = Typ.var := by
          simp
          funext x 
          cases x <;> rfl
    rw [this]
    assumption

example : ⋆⟪ ♯0 → ♯0 ⟫[.int]⋆ = (⋆⟪ int → int ⟫ : Typ ∅⋆) := rfl

inductive Prim where
  | plus
  | minus
  | times
  deriving Repr, BEq, DecidableEq

inductive Ctx : TCtx → Type where
  | nil : Ctx Δ
  | snoc_kind : Ctx Δ → Ctx ⊹Δ
  | snoc_typ : Ctx Δ → c⊢⋆ → Ctx Δ

namespace Ctx
  infixl:50 " ‘ " => Ctx.snoc_typ
  notation "∅" => Ctx.nil
end Ctx
open Ctx

inductive Lookup : Ctx Δ → Δ⊢⋆ → Type where
| here : Lookup (Γ ‘ t) t
| there : Lookup Γ t → Lookup (Γ ‘ t') t
| move : Lookup Γ t → Lookup Γ.snoc_kind (weakent t)
deriving Repr

namespace Lookup
  infix:40 " ∋ " => Lookup
end Lookup
open Lookup

inductive Term : (Δ : TCtx) → Ctx Δ → Typ Δ → Type where
  | int  {Γ : Ctx Δ} : Int → Term Δ Γ .int
  | var  {Γ : Ctx Δ} {t : Δ⊢⋆} : Γ ∋ t → Term Δ Γ t

  | fix  {Γ : Ctx Δ} {t₁ t₂ : Δ⊢⋆} : Term Δ (Γ ‘ t₁ ‘ ⋆⟪ !t₁ → !t₂ ⟫) t₂ → Term Δ Γ ⋆⟪ !t₁ → !t₂ ⟫
  | app  {Γ : Ctx Δ} {t₁ t₂ : Δ⊢⋆} : Term Δ Γ ⋆⟪ !t₁ → !t₂ ⟫ → Term Δ Γ t₁ → Term Δ Γ t₂

  | Λ    {Γ : Ctx Δ} {t : (⊹Δ)⊢⋆} : Term ⊹Δ Γ.snoc_kind t → Term Δ Γ ⋆⟪ ∀. !t ⟫
  | sub  {Γ : Ctx Δ} {t' : (⊹Δ)⊢⋆} : Term Δ Γ ⋆⟪ ∀. !t' ⟫ → (t : Δ⊢⋆) → Term Δ Γ (t'[t]⋆)

  | prim {Γ : Ctx Δ} : Term Δ Γ .int → Prim → Term Δ Γ .int → Term Δ Γ .int
  | pair {Γ : Ctx Δ} : Term Δ Γ t₁ → Term Δ Γ t₂ → Term Δ Γ ⋆⟪ !t₁ × !t₂ ⟫
  | fst {Γ : Ctx Δ} : Term Δ Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term Δ Γ t₁
  | snd {Γ : Ctx Δ} : Term Δ Γ ⋆⟪ !t₁ × !t₂ ⟫ → Term Δ Γ t₂
  | if0  {Γ : Ctx Δ} {t : Δ⊢⋆}: Term Δ Γ .int → Term Δ Γ t → Term Δ Γ t → Term Δ Γ t
  deriving Repr

namespace Term 
  notation:10 Δ " ∣ " Γ " ⊢ " t => Term Δ Γ t

  syntax "get_elem'" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem' $n) => match n.1.toNat with
  | 0 => `(tactic | exact Lookup.here)
  | n+1 => `(tactic| apply Lookup.there; get_elem' $(Lean.quote n))

  macro "# " n:term:90 : term => `(Term.var (by get_elem' $n))

  example : ∅⋆ ∣ (∅ ‘ (@Typ.arrow ∅⋆ .int .int) ‘ (@Typ.int ∅⋆)) ⊢ ⋆⟪ int ⟫ := #0
  example : ∅⋆ ∣ (∅ ‘ (@Typ.arrow ∅⋆ .int .int) ‘ (@Typ.int ∅⋆)) ⊢ ⋆⟪ int → int ⟫ := #1
  
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

def fact : ∅⋆ ∣ ∅ ⊢ ⋆⟪ int → int ⟫ :=
  Term.fix (.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (Term.prim (.var (.there .here)) .minus (.int 1)))))
#eval fact

def fact' : ∅⋆ ∣ ∅ ⊢ ⋆⟪ int → int ⟫ := 
  ⟪ λ. if0 #1 then
         1
       else
         #1 * (#0 (#1 - 1))
       end ⟫

#eval fact'

theorem fact_eq_fact' : fact = fact' := rfl

def sixfact := ⟪ !fact 6 ⟫

def freeid : ⊹∅⋆ ∣ ∅.snoc_kind ⊢ ⋆⟪ ♯0 → ♯0 ⟫ :=
 ⟪ λ. #1 ⟫

def intid := ⟪ (Λ. !freeid)[int] ⟫
#eval intid

@[reducible]
def Ren : ∀ {Δ₁ Δ₂}, Ctx Δ₁ → Ctx Δ₂ → Rent Δ₁ Δ₂ → Type := 
  fun Γ₁ Γ₂ rt => {a : _ ⊢⋆} → Γ₁ ∋ a → Γ₂ ∋ rent rt a


@[reducible]
def lift : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Rent Δ₁ Δ₂}, 
          Ren Γ₁ Γ₂ rt → {b : Δ₁ ⊢⋆} → Ren (Γ₁ ‘ b) (Γ₂ ‘ rent rt b) rt := 
    fun r _ b x => 
      match x with
      | .here => .here
      | .there x' => .there (r x')

def convninf {Δ Γ} {a₁ a₂ : Δ ⊢⋆} :  
              a₁ = a₂ → Γ ∋ a₁ → Γ ∋ a₂
      | rfl, x => x

@[reducible]
def tlift : ∀ {Δ₁ Δ₂ Γ₁ Γ₂} {rt : Rent Δ₁ Δ₂}, 
            Ren Γ₁ Γ₂ rt → {b : Δ₁ ⊢⋆} → Ren Γ₁.snoc_kind Γ₂.snoc_kind (liftt rt) := by
    intros Δ₁ Δ₂ Γ₁ Γ₂ rt r b a v
    cases v with
    | move v => admit

abbrev interp : Prim → (Int → Int → Int)
  | .plus => Int.add
  | .minus => Int.sub
  | .times => Int.mul

inductive Step {Δ Γ} : (Δ ∣ Γ ⊢ t) → (Δ ∣ Γ ⊢ t) → Prop
  | prim_exec  : Step (.prim (.int n₁) p (.int n₂)) (.int (interp p n₁ n₂))
  | prim_left  : Step a a' → Step (.prim a p b) (.prim a' p b)
  | prim_right : Step b b' → Step (.prim (.int n) p b) (.prim (.int n) p b')

  | fst_exec   : Step ⟪ π₁(!e, !_) ⟫ e
  | fst_steps  : Step e e' →  Step (.fst e) (.fst e')

  | snd_exec   : Step ⟪ π₂(!_, !e) ⟫ e
  | snd_steps  : Step e e' →  Step (.snd e) (.snd e')

  | if0_exec   : Step ⟪ if0 0 then !b else !c end ⟫ b
  | ifn0_exec  : n ≠ 0 → Step ⟪ if0 !(.int n) then !b else !c end ⟫ c
  | if_steps   : Step a a' → Step ⟪ if0 !a then !b else !c end ⟫ ⟪ if0 !a' then !b else !c end ⟫

inductive MultiStep {Δ Γ t} : (Δ ∣ Γ ⊢ t) → (Δ ∣ Γ ⊢ t) → Prop 
  | refl {a} : MultiStep a a
  | step {a b c} : Step a b → MultiStep b c → MultiStep a c

theorem «1+1 -->* 2» : MultiStep (Δ := ∅⋆) (Γ := ∅) ⟪ if0 0 then 1 + 1 else 5 end ⟫ ⟪ 2 ⟫ := by repeat constructor
