import «TypedAssembly».SystemF.TypNf
import «TypedAssembly».SystemF.Typ
import «TypedAssembly».SystemF.Prim

inductive CtxNf : Ctxt → Type where
  | nil       : CtxNf Ø
  | snoc_kind : CtxNf Δ → ∀ j, CtxNf (Δ ,⋆ j)
  | snoc_typ  : CtxNf Δ → Δ ⊢nf⋆ ⋆ → CtxNf Δ

namespace CtxNf
  infixl:50 " ,, " => CtxNf.snoc_typ
  infixl:50 " ,,⋆ " => CtxNf.snoc_kind
  notation "∅" => CtxNf.nil
end CtxNf
open CtxNf

inductive LookupNf : CtxNf Δ → Δ ⊢nf⋆ ⋆ → Type where
  | here  {Γ : CtxNf Δ} {t : Δ ⊢nf⋆ ⋆}     : LookupNf (Γ ,, t) t
  | there {Γ : CtxNf Δ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : LookupNf Γ t₁ → LookupNf (Γ ,, t₂) t₁
  | move  {Γ : CtxNf Δ} {t : Δ ⊢nf⋆ ⋆} {k} : LookupNf Γ t →
                                         LookupNf (Γ ,,⋆ k) (weakent_nf t)
deriving Repr

namespace LookupNf
  infix:40 " ∋nf " => LookupNf
end LookupNf
open LookupNf

inductive TermNf : {Δ : Ctxt} → CtxNf Δ → Δ ⊢nf⋆ ⋆ → Type where
  | int  {Γ : CtxNf Δ} : Int → TermNf Γ .int
  | var  {Γ : CtxNf Δ} {t : Δ ⊢nf⋆ ⋆} : Γ ∋nf t → TermNf Γ t

  | fix  {Γ : CtxNf Δ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : TermNf (Γ ,, t₁ ,, nf⋆⟪ !t₁ → !t₂ ⟫) t₂ → TermNf Γ nf⋆⟪ !t₁ → !t₂ ⟫
  | app  {Γ : CtxNf Δ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : TermNf Γ nf⋆⟪ !t₁ → !t₂ ⟫ → TermNf Γ t₁ → TermNf Γ t₂

  | Λ    {Γ : CtxNf Δ} {k} {t : Δ ,⋆ k ⊢nf⋆ ⋆} : TermNf (Γ ,,⋆ k) t → TermNf Γ nf⋆⟪ ∀. !t ⟫
  | sub  {Γ : CtxNf Δ} {k} {t₁ : Δ ,⋆ k ⊢nf⋆ ⋆} : TermNf Γ nf⋆⟪ ∀. !t₁ ⟫ → (t₂ : Δ ⊢nf⋆ k) → TermNf Γ (t₁[t₂]nf⋆)

  | prim {Γ : CtxNf Δ} : TermNf Γ .int → Prim → TermNf Γ .int → TermNf Γ .int
  | pair {Γ : CtxNf Δ} : TermNf Γ t₁ → TermNf Γ t₂ → TermNf Γ nf⋆⟪ !t₁ × !t₂ ⟫
  | fst  {Γ : CtxNf Δ} : TermNf Γ nf⋆⟪ !t₁ × !t₂ ⟫ → TermNf Γ t₁
  | snd  {Γ : CtxNf Δ} : TermNf Γ nf⋆⟪ !t₁ × !t₂ ⟫ → TermNf Γ t₂
  | if0  {Γ : CtxNf Δ} {t : Δ ⊢nf⋆ ⋆} : TermNf Γ .int → TermNf Γ t → TermNf Γ t → TermNf Γ t
  deriving Repr

namespace TermNf
  notation:10 Γ " ⊢nf " t => TermNf Γ t

  syntax "get_elem''" (ppSpace term) : tactic
  macro_rules | `(tactic| get_elem'' $n) => match n.1.toNat with
  | 0 => `(tactic | exact LookupNf.here)
  | n+1 => `(tactic| apply LookupNf.there; get_elem'' $(Lean.quote n))

  
  declare_syntax_cat trmnf
  syntax "!" term:max : trmnf
  syntax num : trmnf
  syntax "#" num : trmnf
  syntax " λ. " trmnf : trmnf
  syntax trmnf trmnf : trmnf
  syntax " Λ. " trmnf : trmnf
  syntax trmnf "[ " typnf " ] " : trmnf
  syntax:20 trmnf:20 " + " trmnf:21 : trmnf
  syntax:20 trmnf:20 " - " trmnf:21 : trmnf
  syntax:30 trmnf:30 " * " trmnf:31 : trmnf
  syntax " ( " trmnf ", " trmnf " ) " : trmnf
  syntax "π₁" trmnf : trmnf
  syntax "π₂" trmnf : trmnf
  syntax "if0 " trmnf " then " trmnf " else " trmnf " end " : trmnf
  syntax "if0 " " ( " trmnf " , " trmnf " , " trmnf " ) " : trmnf

  syntax " ( " trmnf " ) " : trmnf
  syntax " nf⟪ " trmnf " ⟫" : term

  macro_rules
    | `( nf⟪ !$t ⟫) => `($t)
    | `( nf⟪ $i:num ⟫ ) => `(TermNf.int $i)
    | `( nf⟪ #$i:num ⟫ ) => `(TermNf.var $ by get_elem'' $i)
    | `( nf⟪ λ. $e ⟫ ) => `(TermNf.fix nf⟪ $e ⟫)
    | `( nf⟪ $e₁ $e₂  ⟫) => `(TermNf.app nf⟪ $e₁ ⟫ nf⟪ $e₂ ⟫ )
    | `( nf⟪ Λ. $e ⟫ ) => `(TermNf.Λ nf⟪ $e ⟫ )
    | `( nf⟪ $e[$t] ⟫ ) => `(TermNf.sub nf⟪ $e ⟫ nf⋆⟪ $t ⟫)
    | `( nf⟪ $e₁ + $e₂ ⟫ ) => `(TermNf.prim nf⟪ $e₁ ⟫ Prim.plus nf⟪ $e₂ ⟫ )
    | `( nf⟪ $e₁ - $e₂ ⟫ ) => `(TermNf.prim nf⟪ $e₁ ⟫ Prim.minus nf⟪ $e₂ ⟫ )
    | `( nf⟪ $e₁ * $e₂ ⟫ ) => `(TermNf.prim nf⟪ $e₁ ⟫ Prim.times nf⟪$e₂ ⟫ )
    | `( nf⟪ ($e₁, $e₂) ⟫) => `(TermNf.pair nf⟪ $e₁ ⟫ nf⟪$e₂ ⟫ )
    | `( nf⟪ π₁ $e ⟫) => `(TermNf.fst nf⟪ $e ⟫ )
    | `( nf⟪ π₂ $e ⟫) => `(TermNf.snd nf⟪ $e ⟫ )
    | `( nf⟪ if0 $e₁ then $e₂ else $e₃ end ⟫ ) => `(TermNf.if0 nf⟪ $e₁ ⟫ nf⟪ $e₂ ⟫ nf⟪ $e₃ ⟫ )
    | `( nf⟪ if0 ($e₁, $e₂, $e₃) ⟫ ) => `(TermNf.if0 nf⟪ $e₁ ⟫ nf⟪ $e₂ ⟫ nf⟪ $e₃ ⟫ )

    | `( nf⟪ ( $e ) ⟫ ) => `( nf⟪ $e ⟫ ) 

  example : (∅ ,, nf⋆⟪ int → int ⟫ ,, .int) ⊢nf nf⋆⟪ int ⟫ := nf⟪ #0 ⟫
  example : (∅ ,, nf⋆⟪ int → int ⟫ ,, .int) ⊢nf nf⋆⟪ int → int ⟫ := nf⟪ #1 ⟫
end TermNf
open TermNf

def fact :  ∅ ⊢nf nf⋆⟪ int → int ⟫ :=
  TermNf.fix (.if0 (.var (.there .here))
            (.int 1)
            (.prim (.var (.there .here)) .times (.app (.var .here) (.prim (.var (.there .here)) .minus (.int 1)))))

def fact' : ∅ ⊢nf nf⋆⟪ int → int ⟫ := 
  nf⟪ λ. if0 #1 then
         1
       else
         #1 * (#0 (#1 - 1))
       end ⟫

theorem fact_eq_fact' : fact = fact' := rfl

def sixfact := nf⟪ !fact 6 ⟫

def freeid : (∅ ,,⋆ ⋆) ⊢nf nf⋆⟪ ♯0 → ♯0 ⟫ :=
  nf⟪ λ. #1 ⟫

def intid : ∅ ⊢nf nf⋆⟪ int → int ⟫ :=
  nf⟪ (Λ. !freeid)[int] ⟫

def conv_ni_nf {Δ Γ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : t₁ = t₂ → Γ ∋nf t₁ → Γ ∋nf t₂
  | rfl, a => a

def conv_ent_nf {Δ Γ} {t₁ t₂ : Δ ⊢nf⋆ ⋆} : t₁ = t₂ → (Γ ⊢nf t₁) → (Γ ⊢nf t₂)
  | rfl , a => a


